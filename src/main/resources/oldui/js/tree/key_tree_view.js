/**
 * KeYTreeView
 * 
 * Ids:
 *    stv[n]
 *    stv - the containing span.
 *
 * classes:
 *    stvnode
 *    stvmain
 *
 * Nathan Fulton 2014
 */

function KeYTreeView(tree, client) {
  this.tree   = tree;
  this.client = client;
 
  this.containerBackgroundColor = document.getElementById("prover").style.backgroundColor;

  this.onAdd = function(parentId, node) {
    if(node.id == null) {
      UI.showError("Tree view initialized incorrectly: expected node to have an id field.");
      console.error(node)
      return;
    }
    if(document.getElementById('ktv-span-' + node.id) != null) {
      //Should not be an error because executing the same tactic twice is a
      //valid action.
      console.log("Skipping KeYTreeView.onAdd action for node with id " + node.id + " because an element already exists");
      return;
    }

    var newNode = document.createElement("li");
    newNode.setAttribute('id', "ktv-li-" + node.id);
    newNode.style.backgroundColor = this.containerBackgroundColor;

    //Add text to the node.
    var newSpan = document.createElement("span");
    newSpan.setAttribute('id', 'ktv-span-' + node.id);
    newSpan.setAttribute("class", "folder");
    newSpan.appendChild(SequentGUI.staticView(client, node.sequent))
    $(newNode).html(node.text); //TODO-nrf 
    newSpan.style.backgroundColor = this.containerBackgroundColor;
    newNode.appendChild(newSpan);

    //Add children to the node.
    var newUl = document.createElement('ul');
    newUl.setAttribute('id', 'ktv-ul-' + node.id);
    newUl.style.backgroundColor = this.containerBackgroundColor;
    newNode.appendChild(newUl);

    //Add node to the parent's children.
    var parentHtmlId;
    if(parentId === "ktvmain") parentHtmlId = "ktvmain";
    else parentHtmlId = 'ktv-ul-' + parentId;
    
    var appended = $(newNode).appendTo("#"+parentHtmlId);
    $("#ktvmain").treeview({ add: newNode });
  }

  this.onDelete = function(targetId) {
    $("#t" + targetId).remove();
  }

  this.redraw = function() {
    return this.redrawIn('prover');
  }

  this.redrawIn = function(elementId) {
    this.containerBackgroundColor = document.getElementById(elementId).style.backgroundColor;
    document.getElementById(elementId).style.textAlign = "left"
    var elem = document.createElement('ul');
    elem.setAttribute("class", "filetree treeview-famfamfam treeview");
    elem.setAttribute('id', 'ktvmain');
    $('#'+elementId).html(elem.outerHTML);
    $("#ktvmain").treeview({})
    this.onAdd('ktvmain', this.tree); //add everything to the gui
  }

//  this.showOpenNodes = function() {
//  }
//
//  this.collapseNode = function() {
//  }
//
//  this.expandNode = function() {
//  }
}

KeYTreeView.prototype = new TreeView();

