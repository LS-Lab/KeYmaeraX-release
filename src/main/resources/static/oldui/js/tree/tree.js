//trees and nodes are the same thing.
function Tree(sequent, children) {
  if(sequent.uid == null) {
    alert("Sequent did not have a uid")
  }

  this.id      = sequent.uid; 
  this.sequent = sequent;

  if(!children)                      this.children = new Array();
  else if(children instanceof Array) this.children = children;
  else throw "Expected an Array of children but was passed something else.";
  
  // Searches the tree for a subtree with the correct id.
  this.byId = function(id) {
    if(this.id === id) return this;
    else {
      for(var i = 0; i < this.children.length; i++) {
        var recursiveResult = this.children[i].byId(id);
        if(recursiveResult) return recursiveResult;
      }
    }
    //Not found -- return null.
    return null;
  }

  this.addChild = function(node) {
    this.children.push(node);
  }

  this.deleteChild = function(targetId) {
    //Recurse on all children.
    var newChildren = this.children.map(function(child) {
      return child.deleteChild(targetId);
    });
    //Remove all children matching the id.
    this.children = newChildren.filter(function(child) {
      return child.id != targetId;
    });
  }
}

function TreeView(tree) {
  this.addNode = function(parentId, node) {
    var parentTree = this.tree.byId(parentId);
    if(parentTree) {
      parentTree.addChild(node);
      try {
        this.onAdd(parentId, node);
      }
      catch(err) {
        this.redraw();
      }
    }
    else {
      throw "parentId not found in this tree view's model: " + parentId;
    }
  }

  this.deleteNode = function(nodeId) {
    this.tree.deleteChild(nodeId);
    try {
      this.onDelete(nodeId);
    } catch(err) {
      this.redraw();
    }
  }

  // Updateo perations.
  // These can be called instead of the redraw.
  // If they throw an error, then redraw is called instead.
  this.onAdd         = function(parentId, tree) { throw "unimplemented"; }
  this.onDelete      = function(nodeId) { throw "unimplemented."; }
  this.redraw        = function() { throw "unimplemented."; }
  this.redrawIn      = function(elementId) { throw "unimplemented."; }

  // View actions.
  this.showOpenNodes = function() { throw "unimplemented."; }
  this.collapseNode  = function(nodeId) { throw "unimplemented."; }
  this.expandNode    = function(nodeId) { throw "unimplemented."; }
}

