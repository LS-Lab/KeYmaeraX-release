/*
 * This file contains definitions of the Tree and TreeView classes.
 * You can inherit from these classes, or simply use them as guidelines when
 * implementing specific trees.
 */

/**
 * Operates on the data structures passed down from the server. See js/specs.
 */
var ProofTree {
  typeCheck: function(node) {
    if(node.hasOwnProperty(type) &&
       node.type === "Node" &&
       node.hasOwnProperty(nodes)
  }
}


var TreeModel {
  /**
   * Adds a node to its appropriate place in the root subtree.
   */
  addNode: function(root, nodeToAdd) {
    this.typeCheck(root); this.typeCheck(nodeToAdd);
  },

  removeNode: function(root, nodeToRemove) {
    this.typeCheck(root); this.typeCheck(nodeToRemove);
    if(root == nodeToRemove) {
      UI.clearMain();
    }
    else {
      //TODO-nrf how to do recursion?
    }
  },

  onUpdate: function(root) {
    Node.typeCheck(root);
  },
}


//This is the problem with the schemas that we've defined so far... 
