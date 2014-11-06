/*
 * A Javascript client for the Hydra REST API.
 * See the README.md file in the Hydra directory for a specification,
 * or resources/specs/api.js for a spec of the API.
 *
 * Nathan Fulton 2014
 * Jan-David Quesel 2014
 * Stefan Mitsch 2014
 */
var ServerInfo = {
  hostname: "localhost",
  port:     8090,
}

// TODO Deprecated, we use AngularJS now

var ApiClient = {
  /**
   * @param resource - The name of a resource (e.g. proofs/root)
   * @return URL to the resource.
   */
  url: function(resource) {
    return "http://" + ServerInfo.hostname + ":" +
           ServerInfo.port + "/" + resource;
  },

  /**
   * This is the function which should be passed to all AJAX requests
   */
  ajaxErrorHandler: function(request, textStatus, errorThrown) {
    console.log("Error: " + textStatus + ". Error trace following...")
    console.log(errorThrown)
    alert("Ajax error! See console log for details.")
  },


  /**
   * Update Requests should always return an empty array; return values are
   * sent to the client via the event loop (see the event handler in
   * EventHandler.js).
   *
   * @param resource - absolute path to the resource.
   * @param type - the HTTP request type.
   */
  sendUpdateRequest: function(resource, type, callbackFn) {
    //Choose a generic callback function if none is provided.
    if(!callbackFn) {
      callbackFn = function(resp) {}
    }

    $.ajax({
      type: type,
      dataType: "json",
      contentType: "application/json",
      async: true,
      url: this.url(resource),
      success: callbackFn,
      error: this.ajaxErrorHandler
    });
  },

  //////////////////////////////////////////////////////////////////////////////
  // Begin API calls
  //////////////////////////////////////////////////////////////////////////////


  //////////////////////////////////////////////////////////////////////////////
  // USERS
  //////////////////////////////////////////////////////////////////////////////
  createNewUser: function(username, password, callback) {
    $.ajax({
      type: "POST",
      dataType: "json",
      contentType: "application/json",
      async: false,
      url: this.url("user/" + username + "/" + password),
      success: callback,
      error: this.ajaxErrorHandler
    });
  },

  login: function(username, password) {
    $.ajax({
      type: "GET",
      dataType: "json",
      contentType: "application/json",
      async: false,
      url: this.url("user/" + username + "/" + password),
      success: eventHandler,
      error: this.ajaxErrorHandler
    });
  },

//  listUsers : function() {
//    sendUpdateRequest("/users/", "GET");
//  },

  //////////////////////////////////////////////////////////////////////////////
  // MODELS
  //////////////////////////////////////////////////////////////////////////////

  getModelList : function(callbackFn) {
    $.ajax({
      type: "GET",
      dataType: "json",
      contentType: "application/json",
      async: false,
      url: this.url("models/user"),
      success: callbackFn,
      error: this.ajaxErrorHandler
    });
  },

    //////////////////////////////////////////////////////////////////////////////
    // OLD UI
    //////////////////////////////////////////////////////////////////////////////

  /// /proofs/<userid>
  listUserProofs: function(userid) {
    this.sendUpdateRequest("/proofs/"+userid, "GET");
  },

  createNewProof: function(userid, source, callback) {
    $.ajax({
      url: this.url("proofs/" + userid),
      type: "POST",
      data: source,
      async: true,
      dataType: 'json',
      contentType: 'application/json',
      success: callback,
      error: this.ajaxErrorHandler
    });
    //this.sendUpdateRequest("/proofs/" + userid, "POST");
  },

  getProof: function(userid, proofid, callback) {
    $.ajax({
        url: this.url("proofs/" + userid + "/" + proofid),
        type: "GET",
        async: true,
        dataType: 'json',
        contentType: 'application/json',
        success: callback,
        error: this.ajaxErrorHandler
      });
  },

  runGlobalTactic: function(userid, tacticId, proofid, nodeid, callback) {
    $.ajax({
      url: this.url("user/" + userid + "/proofs/" + proofid + "/node/" +nodeid + "/tactic/" + tacticId),
      type: "POST",
      async: true,
      dataType: 'json',
      contentType: 'application/json',
      success: callback,
      error: this.ajaxErrorHandler
    });
  },

  runTactic: function(userid, tacticId, proofid, nodeid, formulaId, callback) {
    $.ajax({
      url: this.url("user/" + userid + "/proofs/" + proofid + "/node/" +nodeid + "/formula/" + formulaId + "/tactic/" + tacticId),
      type: "POST",
      async: true,
      dataType: 'json',
      contentType: 'application/json',
      success: callback,
      error: this.ajaxErrorHandler
    });
  },

  /// /proofs/<userid>/<proofid>
  loadProof: function(userid, proofid) {
    this.sendUpdateRequest("/proofs/"+userid+"/"+proofid, "GET");
  },

  /**
   * The current count for the eventQueue.
   * This is mutable and is updated by getUpdates.
   */
  currentId: 0,

  /// /proofs/<userid>/<proofid>/updates
  getUpdates: function(userid) {
    var client = ApiClient;
    if(client.currentId == undefined) {
        client.currentId = 0;
    }
    $.ajax({
      url: this.url("user/"+userid+"/getUpdates/" + client.currentId),
      type: "POST",
      dataType: 'json',
      contentType: 'application/json',
      async: true,
      success: function(evt) {
        var resp = evt.events;
        var updates = resp.events;
        var newCount = resp.newCount;
        client.currentId = newCount;
        if(updates instanceof Array && updates.length > 0) {
          if(window.DEBUG_MODE) {
            console.log("Received updates from the server: ");
            console.log(updates);
          }
          for(i=0; i<updates.length; i++) {
            HydraEventHandler(updates[i], client); //defined in EventHandler.js
          }
        }
      },
      error: this.ajaxErrorHandler
    });
  }

}

