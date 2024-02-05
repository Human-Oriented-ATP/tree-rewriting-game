import * as React from 'react';
import { LocationsContext, CodeWithInfos, RpcContext, mapRpcError, DocumentPosition, InteractiveCode, GoalsLocation, PanelWidgetProps, useAsyncPersistent } from '@leanprover/infoview';
import { Range } from 'vscode-languageserver-protocol';
import RenderDisplayTree from './interactiveTreeDisplay';
import {DisplayTreeProps, DisplayTree} from './interactiveTreeDisplay';
import HtmlDisplay, { Html, renderHtml } from './htmlDisplay';

export type InteractionProps = PanelWidgetProps & { range : Range }

function DisplayTreePropsToInteractionProps(props:DisplayTreeProps) : InteractionProps {
    return {
        pos : props.pos,
        termGoal : props.termGoal,
        selectedLocations : props.selectedLocations,
        goals : props.goals,
        range : props.range
    }
}

export default function RenderDisplay(props: DisplayTreeProps) : JSX.Element {
    const pos = props.pos
    const [selectedLocs, setSelectedLocs] = React.useState<GoalsLocation[]>([]);
    const rs = React.useContext(RpcContext);
    const locs = React.useMemo(() => ({
        isSelected: (l : GoalsLocation) => selectedLocs.some(v => GoalsLocation.isEqual(v, l)),
        setSelected: (l : GoalsLocation, act : any) => setSelectedLocs(ls => {
            // We ensure that `selectedLocs` maintains its reference identity if the selection
            // status of `l` didn't change.
            const newLocs = ls.filter(v => !GoalsLocation.isEqual(v, l));
            const wasSelected = newLocs.length !== ls.length;
            const isSelected = typeof act === 'function' ? act(wasSelected) : act;
            if (isSelected)
                newLocs.push(l);
            return wasSelected === isSelected ? ls : newLocs;
        }),
        subexprTemplate: { mvarId: 'dummyMVarId', loc: { target: '' }}
    }), [selectedLocs]);
    React.useEffect(() => setSelectedLocs([]), [pos.uri, pos.line, pos.character]);

    const selectionResponseState = useAsyncPersistent(async function() : Promise<JSX.Element> {
        const html = await rs.call<InteractionProps, Html>('allowedTreeRewrites', DisplayTreePropsToInteractionProps({...props, selectedLocations: selectedLocs}));
        return renderHtml(rs, props.pos, html);
        }, [selectedLocs])

    const selectionResponse = 
        (selectionResponseState.state === 'resolved') ?
            selectionResponseState.value :
        (selectionResponseState.state === 'rejected') ?
            <span className="red">Error rendering HTML: {mapRpcError(selectionResponseState.error).message}</span> :
        <></>

    return (
    <div>
        <LocationsContext.Provider value={locs}>
            {RenderDisplayTree(props)}
        </LocationsContext.Provider>
        <hr />
        { selectionResponse }
    </div>
    )
}