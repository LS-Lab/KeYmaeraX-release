/**
 * Javascript client for the Hydra API
 * Nathan Fulton
 * 2014
 *
 * Dependencies:
 *  - JQuery
 */

var hydraServerInfo = {
  sessionName: "Default",
  server: "localhost",
  port: 8080
}

function HydraClient(serverarg, portarg) {
  //Default values for the parameters.
  if(typeof(serverarg) === 'undefined') serverarg = "localhost";
  if(typeof(portarg) === 'undefined') portarg = 8080;

  //Create instead varaibles based upon the arguments provided. Blah.
  this.server = serverarg;
  this.port = portarg;

  this.sessionName = "default"; //default value.
  
  this.makeUrl = function(resource) { 
    return "http://" + hydraServerInfo.server + ":" + hydraServerInfo.port + "/" + resource
  };

  //////////////////////////////////////////////////////////////////////////////
  // Begin API calls
  //////////////////////////////////////////////////////////////////////////////

  this.ajaxErrorHandler = function (request, textStatus, errorThrown) {
    console.log(request.responseText);
    console.log(textStatus);
    console.log(errorThrown);
    alert("error during AJAX call: " + textStatus + " (see console for more information)");
  }
 
  this.get = function(resourceName, callbackFunction) {
    $.ajax({
      type: "GET",
      dataType: "json",
      contentType: "application/javascript",
      async: false,
      url: 'http://' + this.server + ":" + this.port + "/" + resourceName,
      success: callbackFunction,
      error: this.ajaxErrorHandler
    });
  }

  //Session management.
  this.startSession = function() {
    //TODO-nrf lock client here.
    var client = this;
    this.get("startSession", function(resp) { client._resetSessionState(resp.sessionName) });
    //TODO-nrf unlock client here.
  }
  this._resetSessionState = function(newName) {
    this.sessionName = newName;
    //TODO-nrf clear the gui.
  }

  //create new problem.
  //text = contents of .key file.
  this.startNewProblem = function(text) {
    $.ajax({
      type: "POST",
      dataType: "json",
      contentType: "applicaiton/javascript",
      async: "false",
      url: 'http://' + this.server + ":" + this.port + "/startNewProblem" + "?sessionName=" + this.sessionName,
      data: text,
      callback: function(resp) {
        //Doesn't matter.
      },
      error: this.ajaxErrorHandler
    });
  }

  this.formulaToString = function(f) {
    if(f.uid) {
      var result = "";
      $.ajax({
        type: 'GET',
        dataType: 'json',
        async: false,
        url: 'http://' + this.server + ":" + this.port + "/formulaToString" + "?sessionName=" + this.sessionName + "&uid=" + f.uid,
        success: function(resp) {
          result = resp[0].string;
        }
      });
      return result;
    }
    else {
      console.error("formulaToString requires its argument to have a defined uid.");
    }
  }

  this.formulaToInteractiveString = function(f) {
    var result = "";
    if(f.uid) {
      var result = "";
      $.ajax({
        type: "GET",
        dataType: "json",
        async: false,
        url: 'http://' + this.server + ":" + this.port + "/formulaToInstractiveString" + "?sessionNAme=" + this.sessionName + "&uid=" + f.uid,
        success: function(resp) {
          result = resp[0].html;
        },
        error: this.ajaxErrorHandler
      });
      return result;
    }
    else {
      throw "formulaToInteractiveString requires f to have uid defined."
    }
  }

  this.getUpdates = function() {
    var client = this;
    $.ajax({
      type: "GET",
      datatype: "json",
      contentType: "application/javascript",
      async: "true",
      url: "http://" + this.server + ":" + this.port + "/getUpdates" + "?sessionName=" + this.sessionName,
      success: function(updates) {
        if(updates instanceof Array && updates.length > 0) {
          console.log("Recieved updates from the server: ");
          console.log(updates);
          for(i = 0; i < updates.length; i++) {
            HydraEventHandler(updates[i], client);
          }
        }
      },
      error: this.ajaxErrorHandler
    })
  }
}
