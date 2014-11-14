{
  "title": "prooflist",
  "type": "array",
  "items": {
    "type" : "object",
        "properties": {
          "id": {
            "type": "string"
          },
          "modelName": {
            "type": "string"
          },
          "name": {
            "type": "string"
          },
          "date": {
            "type": "string"
          },
          "stepCount": {
            "type" : "number"
          },
          "status": {
            "type" : "boolean"
          },
          "loadStatus": {
            "type" : "string"
          }
        },
        "required" : ["id", "name", "date", "stepCount", "status", "loadStatus"]
  }
}