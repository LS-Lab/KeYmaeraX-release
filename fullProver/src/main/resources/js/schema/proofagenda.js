{
    "title" : "ProofAgendaResponse",
    "type" : "array",
    "items" : {
        "type" : "object",
        "properties" : {
            "proofId" : {
                "type" : "string",
                "description" : "Identifies the proof"
            },
            "nodeId" : {
                "type" : "string",
                "description": "Identifies the node in the proof. A node ID equal to the proof ID identifies the root node."
            },
            "proofNode" : {
                "type" : "object",
                "description" : "The actual proof node, including the goal sequent. TODO: refer to a schema."
            }
        },
        "required" : ["proofId","nodeId","proofNode"]
    }
}