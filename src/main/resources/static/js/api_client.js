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
  
  //End "Constructor" logic.

  this.setServerStatus = function(up) {
    document.getElementById("status").innerHTML = "hydra://" + hydraServerInfo.server + ":" + hydraServerInfo.port
    if(up) {
      //document.getElementById("status").style.backgroundColor = null;
      document.getElementById("status").style.backgroundColor = "#005500";
    }
    else {
      document.getElementById("status").style.backgroundColor = "#FF0000";
    }
  }

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
  var client_instance = this; //For the inside of AJAX callbacks.

  this.ajaxErrorHandler = function (request, textStatus, errorThrown) {
    console.error(request.responseText);
    console.error(textStatus);
    console.error(errorThrown);
    client_instance.setServerStatus(false);
    //alert("error during AJAX call: " + textStatus + " (see console for more information)");
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

  this.formulaFromUid = function(uid) {
    var result = "";
    if(uid) {
      var result = "";
      $.ajax({
        type: "GET",
        dataType: "json",
        async: false,
        url: 'http://' + this.server + ":" + this.port + "/formulaFromUid" + "?sessionName=" + this.sessionName + "&uid=" + uid,
        success: function(resp) {
          result = resp[0].formula;
        },
        error: this.ajaxErrorHandler
      });
      return result;
    }
    else {
      throw "Expected a defined uid"
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
        client.setServerStatus(true);
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
