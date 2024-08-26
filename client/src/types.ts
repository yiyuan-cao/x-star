import { integer, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Position, Range, Uri } from "vscode";

export interface PostResult {
	linenum: integer;
    ghostlines: string[];
}

export interface PostfileResult {
	filepath: string;
}