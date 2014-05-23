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

		
  
  this.onAdd = function(parentId, node) {
    var newNode = document.createElement("li");
    newNode.setAttribute('id', "ktv-li-" + node.uid);
    
    //Add text to the node.
    var newSpan = document.createElement("span");
    newSpan.setAttribute('id', 'ktv-span-' + node.uid);
    newSpan.setAttribute("class", "folder");
    newSpan.appendChild(SequentGUI.staticView(client, node.sequent))
    $(newNode).html(node.text); //TODO-nrf 
    newNode.appendChild(newSpan);

    //Add children to the node.
    var newUl = document.createElement('ul');
    newUl.setAttribute('id', 'ktv-ul-' + node.uid);
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

SimpleTreeView.prototype = new TreeView();

