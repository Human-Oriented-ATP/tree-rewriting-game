import * as React from 'react';
import { CodeWithInfos, DocumentPosition, InteractiveCode } from '@leanprover/infoview';
import { Rule, renderRule } from './treeRuleDisplay'; 

type LibraryEntry = { name : string, rule : Rule }
type Library = { entries : Array<LibraryEntry> }

function renderLibraryEntry (pos : DocumentPosition, entry : LibraryEntry) : JSX.Element {
    return (
        <details>
            <summary>{entry.name}</summary>
            {renderRule({pos : pos, rule : entry.rule})}
        </details>
    )
}

function renderLibrary (pos : DocumentPosition, library : Library ) : JSX.Element[] {
    const entries = library.entries
    if (!Array.isArray(entries)) {
        throw new Error("Error on Typescript side: The given library entries are not an array !")
    }    
    if (entries.length == 0) {
        throw new Error("Error on Typescript side: The given library has length zero!")
    }
    return entries.map(function (entry) {return renderLibraryEntry(pos, entry)})
 }

export default function ({ pos, library }: 
    { pos: DocumentPosition, library: Library }) {
    return (
    <div className="ml1">
        <h3>Library rules</h3>
        {renderLibrary(pos, library)}
    </div>
    )
}