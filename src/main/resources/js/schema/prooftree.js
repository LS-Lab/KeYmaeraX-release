{
  "title": "k4tree",
  "type": "object",
  "properties": {
    "id": {
      "type": "string"
    },
    "sequent": {
      "type": "object",
      "$ref": "#/definitions/sequent"
    },
    "children": {
      "type": "array",
      "items": { "$ref": "#/definitions/node" }
    }
  },
  "required": ["id", "sequent", "children"],
  "definitions" : {
      "sequent" : {
        "type": "object",
        "properties": {
          "nodeId": {
            "type": "string"
          },
          "ante": {
            "type": "array",
            "items" : {
                "type": "object",
                "properties": {
                  "nodeId": {
                    "type": "string",
                    "description": "Identifies the parent proof node"
                  },
                  "id": {
                    "type": "string",
                    "description": "Identifies the node, prefixed with 'ante:'"
                  },
                  "formula": { "$ref": "#/definitions/formula" }
                }
            }
          },
          "succ": {
            "type": "array",
            "items" : {
                "type": "object",
                "properties": {
                  "nodeId": {
                    "type": "string",
                    "description": "Identifies the parent proof node"
                  },
                  "id": {
                    "type": "string",
                    "description": "Identifies the node, prefixed with 'succ:'"
                  },
                  "formula": { "$ref": "#/definitions/formula" }
                }
            }
          }
        }
      },
      "node" : {
         "type": "object",
         "properties": {
           "rule": {
               "type": "string",
               "description": "The rule which produced this node"
           },
           "children": {
               "type": "array",
               "items": { "$ref": "#" }
           }
         }
      },
      "formula" : {
          "type": "object",
          "properties": {
            "nodeId": {
              "type": "string",
              "description": "Identifies the parent proof node"
            },
            "id": {
              "type": "string",
              "description": "Identifies the formula within the node"
            },
            "name": {
              "type": "string",
              "description": "The actual formula"
            },
            "children" : {
                "type": "array",
                "items": { "$ref": "#/definitions/formula" }
            }
          }
      }
  }
}
