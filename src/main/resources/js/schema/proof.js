/*
This definition is out of date - nrf 10/8/2014.
*/
{
  "title": "proof",
  "type": "object",
  "properties": {
    "id": {
      "type": "string"
    },
    "type": {
      "type": "string"
    },
    "nodes": {
      "type": "array",
      "items": { "$ref": "/js/schema/sequent.js" }
    },
    "links": {
      "type": "array",
      "items": {"$ref": "/js/schema/link.js" }
    }
  },
  "required": ["id", "type", "nodes"]
}

