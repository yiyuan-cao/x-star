/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import * as vscode from 'vscode';
import { workspace, ExtensionContext, Position } from 'vscode';
import {PostResult, PostfileResult, HoverfileResult, HoverfileResult_} from './types';
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

export function activate(context: ExtensionContext) {
	/************************* CStar Client ******************************/

	// CStar config
	const config = workspace.getConfiguration('cstaride');
	const lsppath = config.get<string>('hollitepath');
	const executable = {command: lsppath + "cstarc/_build/default/cstarlsp/cstarlsp.exe" };
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
	let decorations: vscode.DecorationOptions[] = []; // post lines, recreate everytime
	const decorationType_stack: vscode.TextEditorDecorationType[] = []; // stack

	// .csv file changetime
	const hoverfile: HoverfileResult = {filepath:"", lasttime: new Date(0)};

	/************************* command and communication ******************************/

	// registerCommand showpost
	context.subscriptions.push(vscode.commands.registerCommand('cstar.showpost', function () {
		if(!editor) return;
		client.sendNotification("cstar/showpost", {filepath: editor.document.uri.path, line: editor.selection.end.line});
		// client.sendRequest("cstar/showpost", {document: editor.document.getText(), uri: editor.document.uri.path, line: editor.selection.end.line + 1 });
		// render(ghostlines);
	}));

	// onNotification postResult
	client.onNotification("cstar/postResult", (postresult: PostResult) => {
		// create decoration
		render(postresult.ghostlines);
	});

	// registerCommand hidepost
	context.subscriptions.push(vscode.commands.registerCommand('cstar.hidepost', () => {
		const decorationType_top = decorationType_stack.pop();
		if (decorationType_top) {
			decorationType_top.dispose(); 
			editor.setDecorations(decorationType_top, decorations);
		}
	}));

	// registerCommand showpostfile
	context.subscriptions.push(vscode.commands.registerCommand('cstar.showpostfile', () => {
		client.sendNotification("cstar/showpostfile", {filepath: editor.document.uri.path});
	}));

	// onNotification postfileResult
	client.onNotification("cstar/postfileResult", (postresult: PostfileResult) => {
		const uri = vscode.Uri.file(postresult.filepath);
		vscode.window.showTextDocument(uri, {
			viewColumn: vscode.ViewColumn.Two,
			preserveFocus: true
		});
	});

	// onNotification hoverfileTime
	client.onNotification("cstar/hoverfileTime", (params: HoverfileResult_) => {
		hoverfile.filepath = params.filepath;
		hoverfile.lasttime = convertStringToUTCDate(params.lasttime);
	});


	// registerCommand starthollite
	context.subscriptions.push(vscode.commands.registerCommand('cstar.starthollite', () => {
		exec("docker run --rm -v " + lsppath + ":/hol-lite --name cstar wybxc/hol-lite /bin/bash -c 'cd /hol-lite && make run' tail -f /dev/null > /dev/null 2>&1");
	}));
	// docker run --rm -v /mnt/d/ZGC_Lab/hol-lite/:/hol-lite --name cstar wybxc/hol-lite /bin/bash -c 'cd /hol-lite && make run' tail -f /dev/null > /dev/null 2>&1
	// docker logs cstar

	// registerCommand stophollite
	context.subscriptions.push(vscode.commands.registerCommand('cstar.stophollite', () => {
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
		// editor.document.save();

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
			vscode.window.showInformationMessage('[CStar IDE] Generating Theorem Logs For Hover');

			const checkIsFinished = () => {
				return new Promise<void>((resolve, reject) => {
					if (checkFileUpdate(hoverfile.filepath)) {
						console.log("[CStar Client] Hover Files Generated!");
						resolve();
					} else {
						console.log("[CStar Client] Hover Files Generating...");
						setTimeout(() => {
							checkIsFinished().then(resolve).catch(reject);
						}, 3000);
					}
				});
			};
	
			checkIsFinished().then(() => {
				console.log("[CStar IDE] Generated!");
				vscode.window.showInformationMessage('[CStar IDE] Generated!');
			}).catch((error) => {
				console.error("[CStar IDE] Generating Error: ", error);
				vscode.window.showErrorMessage('[CStar IDE] Generating Error');
			});
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

