var UI = {
  showError : function(error, text) {
    var messageDiv = document.createElement("div")
    messageDiv.setAttribute("class", "errorMessage")
    messageDiv.innerHTML = text
    document.getElementById("errors").appendChild(messageDiv)
    console.error(error)
  },

  //TODO-nrf use some layout manager for this functionality.
  appendToProver : function(element) {
    document.getElementById("prover").appendChild(element)
  },

  insertKeyTreeView : function(element, sequent, client) {
    var tree = new Tree(sequent, null);
    var treeView = new KeYTreeView(tree, client, element);
    treeView.redrawIn(element);
    HydraEventListeners.treeViews.push(treeView);
  },
  
  getInput : function(message, value) {
    if(value === null) value = ""
    return window.prompt(message, value);
  }

}
