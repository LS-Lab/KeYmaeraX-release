/**
 * Javascript client for the Hydra API
 * Nathan Fulton
 * 2014
 *
 * Dependencies:
 *  - JQuery
 */

function getRequest(resource, callbackFn) {
  $.ajax({
    url: "http://" + this.server + "/" + resource,
    type: "GET",
    data: {sessionName: this.sessionName},
    callback: callbackFn
  })
}


var HydraClient = {
  //Danger: never change this value directly! Instead, use startSession.
  sessionName : "Default",
  server      : "localhost",
  port        : "8080",
  startSession: getRequest("startSession", function(resp) {
    this.sessionName = resp.sessionName;
  }),

  processUpdates: getRequest("getUpdates", function(updates) {
    //TODO-nrf prcoess each update.
  })
}
