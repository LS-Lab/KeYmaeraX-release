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
    window.s = evt.sequent;
    proverSpan.innerHTML = SequentGUI.toString(client, evt.sequent);
  }

  else if(evt.eventType === "FormulaToStringResponse") {
    //Ignore -- formula to string should be called synchronously.
  }
  else {
    alert("Event type not found: " + evt.eventType);
  }
}

