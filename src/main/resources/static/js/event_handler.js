function HydraEventHandler(evt, client) {
  if(!(evt.eventType)) {
    alert("Non-event found in event stream.");
    console.log("non-event found in event stream: ");
    console.log(evt);
    return;
  }

  if(evt.eventType === "ErrorResponse") {
    alert("Hydra returned an error: " + evt.message);
    console.log("Hydra's returned error: ");
    console.log(evt);
  }
  else if(evt.eventType === "CreateRootNode") {
    console.log(evt.sequent);
    //TODO-nrf  
  }
  else {
    alert("Event type not found: " + evt.eventType);
  }

}

