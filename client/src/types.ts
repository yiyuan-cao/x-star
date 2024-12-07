import { integer, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Position, Range, Uri } from "vscode";

export interface SymResult {
	linenum: integer;
    ghostlines: string[];
}

export interface SymfileResult {
	filepath: string;
}

export interface HoverfileResult {
	filepath: string;
	lasttime: Date;
}
// for receive
export interface HoverfileResult_ {
	filepath: string;
	lasttime: string;
}