function HydraEventHandler(evt) {
  alert("Event " + JSON.stringify(evt));
  if(evt.type === "update") {
    alert("Proof tree was updated. " + JSON.stringify(evt.events)); //TODO-nrf
  }
  else {
    UI.showError("Received event with no defined handler: " + evt.type, evt);
  }

}

