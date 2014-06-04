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

function HydraClient(serverarg, portarg, count) {
  //Default values for the parameters.
  if(typeof(serverarg) === 'undefined') serverarg = hydraServerInfo.server;
  if(typeof(portarg) === 'undefined') portarg = hydraServerInfo.port;
 
  this.count = 0;

  //End "Constructor" logic.
  
  //Assertions
  this.requireAll = function(array) {
    if(!(array instanceof Array))
      throw "Argument to requireAll should be an array."
    for(var i = 0 ; i < array.length; i++) {
      if(array[i] == null || array[i] === null) {
        throw "All arguments are required but argument " + i + " was null.";
      }
    }
  }
  
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
    var errorSpan = document.getElementById("errors")
    var report = document.createElement("div")
    report.setAttribute("class", "errorMessage")
    report.innerHTML = "Ajax error (" + textStatus + ": " + request.responseText + ")"
    errorSpan.appendChild(report)

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
      return result.replace("<","&lt;").replace(">","&gt;");
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

  this.runTactic = function(tacticName, sequent, parentId) {
    this.requireAll([tacticName, sequent, parentId]);
    if(sequent.uid) {
      $.ajax({
        type: "GET",
        dataType: "json",
        async: true,
        url: "http://" + this.server + ":" + this.port + "/runTactic?sessionName="+ this.sessionName + "&tacticName=" + tacticName + "&uid=" + sequent.uid + "&parentId=" + parentId,
        error: this.ajaxErrorHandler
      });
    }
    else {
      throw "Expected the sequent to have a uid.";
    }
  }


  //Called from the main event loop.
  this.getUpdates = function() {
    var client = this;
    $.ajax({
      type: "GET",
      datatype: "json",
      contentType: "application/javascript",
      async: "true",
      url: "http://" + this.server + ":" + this.port + "/getUpdates" + "?sessionName=" + this.sessionName + "&count=" + this.count,
      success: function(updateInfo) {
        client.setServerStatus(true);
        var updates = updateInfo.events
        var newCount = updateInfo.newCount; 
        client.count = newCount
        if(updates instanceof Array && updates.length > 0) {
          if(window.DEBUG_MODE) {
            console.log("Received updates from the server: ");
            console.log(updateInfo);
          }
          for(i = 0; i < updates.length; i++) {
            HydraEventHandler(updates[i], client);
          }
        }
      },
      error: this.ajaxErrorHandler
    })
  }


}
