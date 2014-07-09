function HydraEventHandler(evt) {
  alert("Event " + JSON.stringify(evt));
  if(evt.type === "proof") {
    evt.tree.x0 = 0;
    evt.tree.y0 = 0;
    /*evt.tree.model.proofid = resp.proofid;
    evt.tree.model.userid = userid;*/
    update(root = evt.tree);
  }
  else {
    UI.showError("Received event with no defined handler: " + evt.type, evt);
  }

}

