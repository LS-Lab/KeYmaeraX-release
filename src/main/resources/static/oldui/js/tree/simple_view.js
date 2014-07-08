/**
 * SimpleTreeView
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
function SimpleTreeView(tree, client) {
  this.tree   = tree;
  this.client = client;

  this.onAdd = function(parentId, node) {
    var newSpan = document.createElement("span");
    newSpan.setAttribute('id', 'stv'+node.id);
    newSpan.setAttribute('class', 'stvnode');
    newSpan.appendChild(SequentGUI.staticView(client, node.sequent));

    //Add to the parent span.
    document.getElementById('stv'+parentId).appendChild(newSpan);

    //recurse on children.
    var v = this;
    node.children.map(function(child) { 
      if(v.onAdd) {
        v.onAdd(child, node.id) 
      }
      else {
        throw "onAdd is not defined for this, even though it should be."
      }
    });
  }

  this.onDelete = function(targetId) {
    $("#t" + targetId).remove();
  }

  this.redraw = function() {
    return this.redrawIn('prover');
  }

  this.redrawIn = function(elementId) {
    var elem = document.createElement('span');
    elem.setAttribute('id', 'stvmain');
    $('#'+elementId).html(elem.outerHTML);
    this.onAdd('main', this.tree); //add everything to the gui
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

