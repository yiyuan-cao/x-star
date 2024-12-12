/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import * as vscode from 'vscode';
import { workspace, ExtensionContext, Position } from 'vscode';
import {SymResult, SymfileResult, HoverfileResult, HoverfileResult_} from './types';
import * as fs from 'fs';

import {
	integer,
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind
} from 'vscode-languageclient/node';
import { exec, execSync, spawn  } from 'child_process';

let client: LanguageClient;

function convertStringToUTCDate(dateString: string): Date {
	const localDate = new Date(dateString);
	const utcDate = new Date(localDate.getTime() - (localDate.getTimezoneOffset() * 60000));
	return utcDate;
}

// Variables to store inserted lines
const insertedLinesStack: { start: number; count: number }[] = [];

export function activate(context: ExtensionContext) {
	/************************* CStar Client ******************************/

	// CStar config
	const config = workspace.getConfiguration('cstaride');
	const lsppath = config.get<string>('hollitepath');
	const executable = {command: lsppath + "cstarc/_build/default/cstarlsp/cstarlsp.exe" };
	// const executable = {command: "/mnt/d/ZGC_Lab/cstar-ide/vscode-extension-samples/lsp-sample/cstarserver/cstarlsp.exe"};
	const cstarserverOptions: ServerOptions = {
		run: executable,
		debug: executable,
	};	
	
	// Options to control the language client
	const clientOptions: LanguageClientOptions = {
		// Register the server for plain text documents
		documentSelector: [{ scheme: 'file', language: 'cstar' }],
		synchronize: {
			// Notify the server about file changes to '.clientrc files contained in the workspace
			fileEvents: workspace.createFileSystemWatcher('**/.clientrc')
		},
		initializationOptions: config
	};

	// Create the language client and start the client.
	client = new LanguageClient(
		'cstar',
		'CStar IDE',
		cstarserverOptions,
		clientOptions
	);

	/************************* params def ******************************/

	// activeTextEditor
	let editor = vscode.window.activeTextEditor;

	// render decoration
	const backgroundColor = new vscode.ThemeColor('cstar.inlineGhostBackgroundColor');
	const color = new vscode.ThemeColor('cstar.inlineGhostForegroundColor');
	const ghostlines = ["Hello CStar!", "Hello VST-A!"];
	let decorations: vscode.DecorationOptions[] = []; // sym lines, recreate everytime
	const decorationType_stack: vscode.TextEditorDecorationType[] = []; // stack

	// .csv file changetime
	const hoverfile: HoverfileResult = {filepath:"", lasttime: new Date(0)};

	/************************* command and communication ******************************/

	// registerCommand showsym
	context.subscriptions.push(vscode.commands.registerCommand('cstar.showsym', function () {
		if(!editor) return;
		client.sendNotification("cstar/showsym", {filepath: editor.document.uri.path, line: editor.selection.end.line});
		// client.sendRequest("cstar/showsym", {document: editor.document.getText(), uri: editor.document.uri.path, line: editor.selection.end.line + 1 });
		// render(ghostlines);
	}));

	// onNotification symResult
	client.onNotification("cstar/symResult", (symresult: SymResult) => {
		// create decoration
		render(symresult.ghostlines);
	});

	// registerCommand hidesym
	context.subscriptions.push(vscode.commands.registerCommand('cstar.hidesym', () => {
		const decorationType_top = decorationType_stack.pop();
		if (decorationType_top) {
			decorationType_top.dispose(); 
			editor.setDecorations(decorationType_top, decorations);
		}
		// Remove the inserted blank lines
		const insertedLines = insertedLinesStack.pop();
		if (insertedLines) {
			const endLine = insertedLines.start + insertedLines.count;
			editor.edit((editBuilder) => {
				editBuilder.delete(new vscode.Range(insertedLines.start, 0, endLine, 0));
			});
			editor.document.save();
		}
	}));

	// registerCommand showsymfile
	context.subscriptions.push(vscode.commands.registerCommand('cstar.showsymfile', () => {
		client.sendNotification("cstar/showsymfile", {filepath: editor.document.uri.path});
	}));

	// onNotification symfileResult
	client.onNotification("cstar/symfileResult", async (symresult: SymfileResult) => {
		const filepath = symresult.filepath;
		const uri = vscode.Uri.file(filepath);
		vscode.window.showInformationMessage('[CStar IDE] Symbolic Executing...');
		const fileExists = await vscode.workspace.fs.stat(uri).then(() => true, () => false);
		if (fileExists) {
			vscode.window.showTextDocument(uri, {
				viewColumn: vscode.ViewColumn.Two,
				preserveFocus: true
			});
		} else {
			const checkInterval = setInterval(() => {
				vscode.workspace.fs.stat(uri).then(() => {
					clearInterval(checkInterval);
					vscode.window.showTextDocument(uri, {
						viewColumn: vscode.ViewColumn.Two,
						preserveFocus: true
					});
					console.log("[CStar IDE] Post File Generated!");
				}, () => {console.log("[CStar IDE] Post File Generating!");});
			}, 1000);
		}
	});

	// onNotification hoverfileTime
	client.onNotification("cstar/hoverfileTime", (params: HoverfileResult_) => {
		hoverfile.filepath = params.filepath;
		hoverfile.lasttime = convertStringToUTCDate(params.lasttime);
	});


	// registerCommand startlcfserver
	context.subscriptions.push(vscode.commands.registerCommand('cstar.startlcfserver', () => {
		exec("docker run --rm -v " + lsppath + ":/x-star --name cstar cstar:lastest /bin/bash -c 'cd /x-star && make run' tail -f /dev/null > /dev/null 2>&1");
	}));
	// docker run --rm -v /mnt/d/ZGC_Lab/hol-lite/:/hol-lite --name cstar wybxc/hol-lite /bin/bash -c 'cd /hol-lite && make run' tail -f /dev/null 2>&1
	// docker logs cstar

	// registerCommand stoplcfserver
	context.subscriptions.push(vscode.commands.registerCommand('cstar.stoplcfserver', () => {
		const output = exec("docker stop cstar");
	}));

	context.subscriptions.push(workspace.onDidChangeConfiguration(event => {
		if(event.affectsConfiguration('cstaride')) {
			const newconfig = workspace.getConfiguration('cstaride');
			client.sendNotification("workspace/didChangeConfiguration", {settings: newconfig});
		}
		
	}));

	/************************* functions ******************************/

	// render function
	function render(ghostlines) {
		// init
		decorations = [];
		let curlineofghost = 0;
		const startline = editor.selection.end.line + 1;
		const cstarlines = editor.document.getText().split('\n');
		const decorationType = vscode.window.createTextEditorDecorationType({
			after: {
				backgroundColor,
				color,
				fontStyle: "italic",
			}
		});
		decorationType_stack.push(decorationType);

		// insert blank lines
		for (let i = 0; i < ghostlines.length; i++) {
			cstarlines.splice(startline + i, 0, '');
		}
		const newText = cstarlines.join('\n');
		editor.edit((editBuilder) => {
			editBuilder.replace(new vscode.Range(0, 0, cstarlines.length, 0), newText);
		});

		// Store the range of inserted lines
		insertedLinesStack.push({
			start: startline,
			count: ghostlines.length
		});
		editor.document.save();

		// insert ghostlines
		for (const line of ghostlines) {
			const contentText = "▷ " + line;
			decorations.push({
				range: new vscode.Range(startline + curlineofghost, 0, startline + curlineofghost, 0),
				renderOptions: {
					after: {
						contentText
					},
				}
			});
			curlineofghost += 1;
		}
		editor.setDecorations(decorationType, decorations);
	}	

	function checkFileUpdate(filePath: string): boolean {
		try {
			const stats = fs.statSync(filePath);
			const lastModifiedTime = stats.mtime;
			if (lastModifiedTime.getTime() > hoverfile.lasttime.getTime() + 3000) {
				return true;
			} else {
				return false;
			}
		} catch (error) {
			if (error.code === 'ENOENT') {
				return false;
			} else {
				throw error;
			}
		}
	}

	/************************* window event ******************************/

	// change editor
	vscode.window.onDidChangeActiveTextEditor(neweditor => {
		editor = neweditor;
		// keep decorations around file
		// if (editor) {render();}
		// delete blank lines
		// sendRequest("find blank lines in functions",editor.document).then(delete(result));
	}, null, context.subscriptions);

	// save file to get hover_file(.csv)
	vscode.workspace.onDidSaveTextDocument(document => {

		if (document.languageId === 'cstar') {
			const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right);
			context.subscriptions.push(statusBarItem);
		
			statusBarItem.text = '[CStar IDE] Generating Theorem Logs For Hover';
			statusBarItem.show();
		
			const checkIsFinished = () => {
				return new Promise<void>((resolve, reject) => {
					if (checkFileUpdate(hoverfile.filepath)) {
						console.log("[CStar Client] Hover Files Generated!");
		
						statusBarItem.text = '[CStar IDE] Theorem Logs Generated';
		
						// 可选：一段时间后隐藏状态栏信息
						setTimeout(() => {
							statusBarItem.hide();
						}, 5000);
		
						resolve();
					} else {
						console.log("[CStar Client] Hover Files Generating...");
						setTimeout(() => {
							checkIsFinished().then(resolve).catch(reject);
						}, 3000);
					}
				});
			};
		
			// 开始检查
			checkIsFinished();
		}

	}, null, context.subscriptions);

	// Start the client. This will also launch the server
	client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}

