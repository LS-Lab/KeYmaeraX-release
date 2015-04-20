/*
This definition is out of date - nrf 10/8/2014.
    "name" -> JsString(proof.name),
    "description" -> JsString(proof.description),
    "date" -> JsString(proof.date),
    "modelId" -> JsString(proof.modelId),
    "stepCount" -> JsNumber(proof.stepCount),
    "status" -> JsBoolean(proof.closed)

*/
{
  "title": "proofnode",
  "type": "object",
  "properties": {
    "id": {
      "type": "string"
    },
    "name": {
      "type": "string"
    },
    "description": {
        "type" : "string"
    },
    "date": {
        "type" : "string"
    },
    "modelId" : {
        "type" : "string"
    },
    "stepCount" : {
        "type" : "number"
    },
    "status" : {
        "type" : "boolean"
    },
    "sequent": {
      "$ref": "/js/schema/sequent.js" //???
    },
    "children" : {
        "type" : "array",
        "items" : {"$ref" : "js/schema/proof.js"}
    },
    "links": {
      "type": "array",
      "items": {"$ref": "/js/schema/link.js" }
    }
  },
  "required": ["id", "type", "children"]
}

