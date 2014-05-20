function HydraEventHandler(evt, client) {
  function showError(msg) {
    alert(msg); //todo
  }

  var proverSpan = document.getElementById("prover")
  if(!(evt.eventType)) {
    alert("Non-event found in event stream.");
    console.log("non-event found in event stream: ");
    console.log(evt);
    return;
  }

  else if(evt.eventType === "ErrorResponse") {
    if(evt.message === "parse failed.") {
      showError("KeYmaera could not parse your file.")
    }
    else {
      showError("Unrecognized error: " + evt.message)
    }

    console.error("Hydra server returned an ErrorResponse: ");
    console.log(evt);
  }

  else if(evt.eventType === "CreateRootNode") {
    console.log(evt.sequent);
    proverSpan.innerHTML = SequentGUI.toString(client, evt.sequent);
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

