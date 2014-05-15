/**
 * KeYmaera Javascript Frontend Library
 * Nathan Fulton
 * 2014
 *
 * This file contains: 
 *    - Front-end representations of differential dynamic logic exprs and prfs
 *    - Functions implementing API calls (see the Hydra README.md for docs)
 *    - Functions for displaying pretty versions of DL exprs and prfs 
 *
 * Every term, formula and sequent has a unique identifier generated on the 
 * Scala side. These unique identifiers are used to identify unique spans
 * containing each element:
 *    i<uid> : the interactive span (e.g. with high-lighting, click, etc.)
 *        The interactive view can be used either on the top of a tree, or
 *        in a popup.
 *    s<uid> : the static span (used in tree view)
 * Apologies, I have no idea how to write good Javascript.
 */ 

////////////////////////////////////////////////////////////////////////////////
// Expressions
////////////////////////////////////////////////////////////////////////////////

/**
 * The Javascript data structure for expressions is considerably less
 * expressive than the Scala data structure. Formulas are distinguished
 * by shape; for instance, ->, \/ and /\ are all ConnectiveFormulas.
 *
 * Expressions are distinguished only the basis of how they are printed and
 * what actions should be available.
 *
 * The types follow:
 *    Atomic   - basically only numbers and variables.
 *    Binding  - Quantifiers.
 *    Grouping - formula groupings, program groupings, modalities.
 *    Connective -- this includes both formulas (f->g) and terms (x+y).
 *
 * The uid of the formula is used to query for available actions; that logic
 * is implemented on the Scala side.
 */

function Atomic(uid) {}
function Grouping(uid, inner) {} //note: it's possible that uid=inner.uid
function Binding(uid, variable, body) {}
function Connective(left, connective, right) {}

//// API Calls for Formulas
var FormulaAPI = {
  toString : function(formula) {
  },

  getOptions : function(formula) {
  }
};

var FormulaGUI = {
  staticView : function(formula) {
    var div = document.createElement('span');
    div.setAttribute('id', "s" + formula.uid);
    div.innerHTML = FormulaAPI.toString(formula);
    return div;
  },

  interactiveView : function(formula) {
    //TODO-nrf!
  },
  
  onClick : function(formula) {
    var options = getOptions(formula)
    if(options.length == 0) {
      //TODO-nrf error message saying no options.
    }
    else if(options.length == 1) {
      //TODO-nrf just do the only option.
    }
    else {
      //TODO-nrf show the menu.
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
// Sequents
////////////////////////////////////////////////////////////////////////////////

function Sequent(uid, parentSequent, left, right) {}

var SequentGUI = {
  //Prints the sequent to the element with id ``id"
  //TODO-nrf this needs to be better.
  staticView : function(sequent) {
    var div = document.createElement('span');
    div.setAttribute('id', "s"+sequent.uid);
    div.innerHTML = FormulaGUI.staticView(sequent.left) + 
                    "&#x22A2"                           + 
                    FormulaGUI.staticView(sequent.right);
    return div;
  },

  interactiveView : function(sequent) {
    //TODO-nrf support interactive view.
  },

  onClick : function(sequent) {
    //TODO-nrf  
  },

  //Adds sequent to the object with id ``id". 
  //The interactive flag determines if the view should be static or
  //interactive.
  show : function(sequent, id, interactive) {
    var target = document.getElementById(id);
    var newChild = interactive ? 
                   SequentGUI.interactiveView(sequent) : 
                   SequentGUI.staticView(sequent);
    target.appendChild(newChild);
  }
}
