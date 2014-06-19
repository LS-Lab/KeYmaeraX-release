{
  "title": "sequent",
  "type": "object",
  "properties": {
    "id": {
      "type": "string"
    },
    "type": {
      "type": "string"
    },
    "antecedent": {
      "type": "array",
      "items": {"$ref": "/js/schema/formula.js"}
    },
    "succedent": {
      "type": "array",
      "items": {"$ref": "/js/schema/formula.js"}
    },
    "links": {
      "type": "array",
      "items": {"$ref": "/js/schema/link.js"}
    }
  },
  "required": ["id", "type", "antecedent", "succedent", "links"]
}
