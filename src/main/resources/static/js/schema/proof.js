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
      "items": { "$ref": "sequent" }
    },
    "links": {
      "type": "array",
      "items": {"$ref": "link"}
    }
  },
  "required": ["id", "type", "nodes"]
}

