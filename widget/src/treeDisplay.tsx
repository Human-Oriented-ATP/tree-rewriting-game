import * as React from 'react';
import Tree from 'react-d3-tree';
import { CodeWithInfos, DocumentPosition, InteractiveCode } from '@leanprover/infoview';
import type { RawNodeDatum, CustomNodeElementProps } from 'react-d3-tree/lib/types/types/common';

type DisplayTree =
  { node: { label: string, children: Array<DisplayTree> } }

type MyNodeDatum = RawNodeDatum & { label?: string }

function treeToData(tree: DisplayTree): MyNodeDatum {
    console.log(tree)
    console.log(tree.node)
    const { label, children } = tree.node
    console.log(children)
    console.log(label)
    if (!Array.isArray(children)) {
        console.log(children)
        throw new Error("Children are not an array")
    }    
    if (children.length == 0) {
        return {
            name: 'node',
            label: label
          }          
    } else {
        console.log(children)
        const childrenAsTrees = children.map(treeToData)
        console.log(childrenAsTrees)
        return {
            name: 'node',
            label: label,
            children: childrenAsTrees
        }
    }  
}

function renderForeignObjectNode({ nodeDatum }: CustomNodeElementProps, pos: DocumentPosition,
  foreignObjectProps: React.SVGProps<SVGForeignObjectElement>): JSX.Element {
  const nodeDatum_ = nodeDatum as MyNodeDatum
  return (
    <g>
      <rect x="-50" y="-10" width="100" height="20" fill="white" style={{ border: "black" }} />
      <foreignObject {...foreignObjectProps} style={{ textAlign: "center" }}>
        {nodeDatum_.label}
      </foreignObject>
    </g>
  )
}

export default function ({ pos, tree }: { pos: DocumentPosition, tree: DisplayTree }) {
  const nodeSize = { x: 120, y: 40 }
  const foreignObjectProps = { width: 100, height: 30, y: -10, x: -50 }
  const r = React.useRef<HTMLDivElement>(null)
  const [t, setT] = React.useState<any | null>(null)
  React.useLayoutEffect(() => {
    const elt = r.current
    if (elt == null) { return }
    if (t != null) { return }
    const b = elt.getBoundingClientRect()
    if (!b.width || !b.height) { return }
    console.log("b: ", b)
    setT({ x: b.width / 2, y: 20 })

  })
  return (
    <div
      style={{
        height: '400px',
        display: 'inline-flex',
        minWidth: '600px',
        border: '1px solid rgba(100, 100, 100, 0.2)',
      }}
      ref={r}
    >
      <Tree
        data={treeToData(tree)}
        translate={t ?? { x: 0, y: 0 }}
        nodeSize={nodeSize}
        renderCustomNodeElement={rd3tProps =>
          renderForeignObjectNode(rd3tProps, pos, foreignObjectProps)}
        orientation='vertical'
        pathFunc={'straight'} />
    </div>
  )
}