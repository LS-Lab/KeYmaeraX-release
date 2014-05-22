var HydraEventListeners = {
  treeViews : [],
}

function HydraEventHandler(evt, client) {

  var proverSpan = document.getElementById("provercontents")
  if(!(evt.eventType)) {
    alert("Non-event found in event stream.");
    console.log("non-event found in event stream: ");
    console.log(evt);
    return;
  }

  else if(evt.eventType === "ErrorResponse") {
    if(evt.message === "parse failed.") {
      console.error("KeYmaera could not parse your file.")
    }
    else {
      console.error("Unrecognized error: " + evt.message)
    }

    console.error("Hydra server returned an ErrorResponse: ");
    console.log(evt);
  }

  else if(evt.eventType === "CreateRootNode") {
    console.log("Root node for this problem: ");
    console.log(evt);
    $("#provercontents").html(
        SequentGUI.staticView(client, evt.sequent)
    );
  }

  else if(evt.eventType === "AddNode") {
    console.log("AddNode event: ");
    console.log(evt);
    //Pass the event along to all of the tree listeners.
    HydraEventListeners.treeViews.map(function(child) {
      child.addNode(evt.parentId, evt.node);
    });

    //Show an error message if there are no trees listening.
    if(HydraEventListeners.treeViews.length === 0) {
      console.error("Recieved an add node event, but there are no tree views to process the event.");
    }
  }

  else if(evt.eventType === "TacticFinished") {
    console.log("TacticFinished event: ");
    console.log(evt);
    GenericGUI.greenFlash(evt.uid);
  }


  //Add ignore cases for all syncronous calls.
  else if(evt.eventType === "FormulaToStringResponse") {}
  else if(evt.eventType === "FormulaToInteractiveStringResponse") {}
  else if(evt.eventType === "FormulaFromUid") {}

  //Add error case
  else {
    throw "HydraEventHandler received an event with unhandled type: " + evt.eventType;
  }
}

