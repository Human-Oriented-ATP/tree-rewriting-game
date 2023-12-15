import * as React from 'react';
import Tree from 'react-d3-tree';
import { CodeWithInfos, DocumentPosition, InteractiveCode } from '@leanprover/infoview';
import type { RawNodeDatum, CustomNodeElementProps } from 'react-d3-tree/lib/types/types/common';
import { DisplayTree, renderDisplayTree } from './treeDisplay'; 

type Rule = { lhs : DisplayTree, rhs : DisplayTree }


export default function renderRule({ pos, rule }: 
    { pos: DocumentPosition, rule: Rule }) {
    const r1 = React.useRef<HTMLDivElement>(null)
    const r2 = React.useRef<HTMLDivElement>(null)
    return (
    <div
      style={{
        height: '400px',
        display: 'inline-flex',
        minWidth: '600px',
        border: '1px solid rgba(100, 100, 100, 0.2)',
        overflow: 'hidden', 
        resize: 'both',
        opacity: '0.9',
      }}
    >
    <div ref={r1}>
      {renderDisplayTree( {pos : pos, tree: rule.lhs, r : r1} )}
    </div><div style={{
        display: 'flex',
        alignItems: 'center',
        fontSize: '50px',
    }}>
    {"→"}
    </div><div ref={r2} >
      {renderDisplayTree( {pos : pos, tree: rule.rhs, r : r2} )}
    </div>
    </div>
)
}