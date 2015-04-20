{
  "title": "modelList",
  "type": "object",
  "properties": {
    "type": {
      "type": "string"
    },
    //Models are an array of arrays of strings: [ [modelName, date, keyFile], ...]
    "models": {
      "type": "array",
      "items": {
        "type" : "array"
        "items" : {
            "type" : "string"
        }
      }
    },
    "links": {
      "type": "array",
      "items": {"$ref": "/js/schema/link.js" }
    }
  },
  "required": ["id", "type", "models"]
}

