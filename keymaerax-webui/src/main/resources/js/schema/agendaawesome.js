/**
 * Created by bbohrer on 12/3/15.
 */
/*
 * {proofTree:
 *  {id: proofId
 *   nodes: List[
 *     {id: nodeId
 *      sequent:
 *        {ante: List[{id: formulaId formula: rec t. {name: string, children: Option[List[t]]}}]
 *         succ: <same>}
 *      children: List[nodeId]
 *      parent: Option[nodeId]}
 *   root: nodeId}
 *  agendaItems:
 *  {<the nodeId>:
 *    {id: itemId
 *     name: String
 *     proofId: proofId
 *     goal: nodeId
 *     path: List[Something??]
 *  */

{
    "title" : "ProofAgendaResponse",
    "type" : "array",
    "items" : {
    "type" : "object",
        "properties" : {
        "proofTree" : {
            "type" : "object",
                "description" : "Partial proof tree, includes root and all leaves"
        },
        "agendaItems" : {
            "type" : "array",
                "description": "Tasks remaining to be done"
        }}
    ,
    "required" : ["proofTree", "agendaItems"]
}
}