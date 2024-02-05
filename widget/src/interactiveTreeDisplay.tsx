import * as React from 'react';
import Tree from 'react-d3-tree';
import { LocationsContext, CodeWithInfos, DocumentPosition, InteractiveCode, GoalsLocation, PanelWidgetProps } from '@leanprover/infoview';
import { Range } from 'vscode-languageserver-protocol';
import type { RawNodeDatum, CustomNodeElementProps } from 'react-d3-tree/lib/types/types/common';

export type DisplayTree =
  { node: { label?: CodeWithInfos, children: Array<DisplayTree> } }

export type TreeNodeDatum = RawNodeDatum & { label?: CodeWithInfos }

export type DisplayTreeProps = PanelWidgetProps & { tree : DisplayTree, divStyle : object, range : Range }

function treeToData(tree: DisplayTree): TreeNodeDatum {
    const { label, children } = tree.node
    if (!Array.isArray(children)) {
        throw new Error("Children are not an array")
    }    
    if (children.length == 0) {
        return {
            name: 'node',
            label: label
          }          
    } else {
        const childrenAsTrees = children.map(treeToData)
        return {
            name: 'node',
            label: label,
            children: childrenAsTrees
        }
    }  
}

function renderForeignObjectNode({ nodeDatum }: CustomNodeElementProps, _: DocumentPosition,
  foreignObjectProps: React.SVGProps<SVGForeignObjectElement>): JSX.Element {
  const nodeDatum_ = nodeDatum as TreeNodeDatum
  return (
    <g>
      <rect x="-50" y="-10" width="100" height="20" fill="aqua" style={{ border: "black" }} />
      <foreignObject {...foreignObjectProps} style={{ textAlign: "center" }}>
        {nodeDatum_.label && <InteractiveCode fmt={nodeDatum_.label} />}
      </foreignObject>
    </g>
  )
}

function centerTree (r : React.RefObject<HTMLDivElement>, t : any, setT : React.Dispatch<any>) {
    React.useLayoutEffect(() => {
        const elt = r.current
        if (elt == null) { return }
        if (t != null) { return }
        const b = elt.getBoundingClientRect()
        if (!b.width || !b.height) { return }
        setT({ x: b.width / 2, y: 20 })
    })
}

export default function RenderDisplayTree(props : DisplayTreeProps): JSX.Element {
    const nodeSize = { x: 120, y: 40 }
    const foreignObjectProps = { width: 100, height: 30, y: -10, x: -50 }
    const [t, setT] = React.useState<any | null>(null)
    const r = React.useRef<HTMLDivElement>(null)
    centerTree(r, t, setT)
    return (
      <div style={props.divStyle} ref={r}>
        <Tree
          data={treeToData(props.tree)}
          translate={t ?? { x: 0, y: 0 }}
          nodeSize={nodeSize}
          renderCustomNodeElement={rd3tProps =>
            renderForeignObjectNode(rd3tProps, props.pos, foreignObjectProps)}
          orientation='vertical'
          pathFunc={'straight'} />
      </div>
    )
}