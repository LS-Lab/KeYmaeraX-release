{
  "title": "prooflist",
  "type": "array",
  "items" : {
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
          }
        },
        "required" : ["id", "name", "date", "stepCount", "status"]
  }
}