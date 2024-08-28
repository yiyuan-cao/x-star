import { integer, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Position, Range, Uri } from "vscode";

export interface PostResult {
	linenum: integer;
    ghostlines: string[];
}

export interface PostfileResult {
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