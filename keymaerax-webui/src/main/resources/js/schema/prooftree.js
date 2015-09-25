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
  "required": ["id", "children"],
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
        },
        "required" : [ "nodeId", "ante", "succ" ]
      },
      "node" : {
         "type": "object",
         "properties": {
           "rule": {
               "type": "object",
               "oneOf": [
                { "$ref": "#/definitions/positionRule" },
                { "$ref": "#/definitions/assumptionRule" },
                { "$ref": "#/definitions/twoPositionRule" },
                { "$ref": "#/definitions/unspecificRule" }
               ],
               "description": "The rule which produced this node"
           },
           "children": {
               "type": "array",
               "items": { "$ref": "#" }
           }
         },
         "required" : [ "rule" ]
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
          },
          "required" : [ "nodeId", "id", "name" ]
      },
      "unspecificRule" : {
          "type" : "object",
          "properties" : {
              "name" : { "type" : "string" },
              "kind" : { "enum" : [ "UnspecificRule" ] }
          },
          "required" : [ "name", "kind" ]
      },
      "positionRule" : {
        "type" : "object",
        "properties" : {
            "name" : { "type" : "string" },
            "kind" : { "enum" : [ "PositionRule" ] },
            "pos" : { "$ref" : "#/definitions/position" }
        },
        "required" : [ "name", "kind", "pos" ]
      },
      "assumptionRule" : {
          "type" : "object",
          "properties" : {
              "name" : { "type" : "string" },
              "kind" : { "enum" : [ "AssumptionRule" ] },
              "pos" : { "$ref" : "#/definitions/position" },
              "assumption" : { "$ref" : "#/definitions/position"}
          },
          "required" : [ "name", "kind", "pos", "assumption" ]
      },
      "twoPositionRule" : {
        "type" : "object",
        "properties" : {
            "name" : { "type" : "string" },
            "kind" : { "enum" : [ "TwoPositionRule" ] },
            "pos1" : { "$ref" : "#/definitions/position" },
            "pos2" : { "$ref" : "#/definitions/position"}
        },
        "required" : [ "name", "kind", "pos1", "pos2" ]
      },
      "position" : {
        "type" : "object",
        "properties" : {
            "kind" : { "type" : "string" },
            "index" : { "type" : "number"},
            "inExpr" : { "type" : "string" }
        },
        "required" : [ "kind", "index", "inExpr" ]
      }
  }
}
