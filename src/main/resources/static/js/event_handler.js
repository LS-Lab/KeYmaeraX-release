function HydraEventHandler(evt) {
  if(evt.type === "proof") {
    alert("Proof tree was updated."); //TODO-nrf 
  }
  else {
    UI.showError("Received event with no defined handler: " + evt.type, evt)
  }

}

