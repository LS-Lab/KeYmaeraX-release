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
      "items": {"$ref": "http://nfulton.org/hydra_spec/formula.js"}
    },
    "succedent": {
      "type": "array",
      "items": {"$ref": "http://nfulton.org/hydra_spec/formula.js"}
    },
    "links": {
      "type": "array",
      "items": {"$ref": "http://nfulton.org/hydra_spec/link.js"}
    }
  },
  "required": ["id", "type", "antecedent", "succedent", "links"]
}
