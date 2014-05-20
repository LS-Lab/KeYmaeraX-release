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

function Atomic(uid, str) { this.uid = uid; this.str = str; }

function Prefix(uid, child, pre_symbol) {
  this.uid = uid;
  this.child = child;
  this.pre_symbol = pre_symbol;
}

function Postfix(uid, child, post_symbol) {
  this.uid = uid;
  this.child = child;
  this.post_symbol = post_symbol;
}

function Grouping(uid, inner, left_symbol, right_symbol) {
  this.uid = uid;
  this.inner = inner;
  this.left_symbol = left_symbol;
  this.right_symbol = right_symbol;
} //note: it's possible that uid=inner.uid

function Modality(uid, program, formula, open, close) {
  this.uid = uid;
  this.formula = formula;
  this.program = program;
  this.open = open;
  this.close = close;
}

function Binding(uid, bind_symbol, variables, child) {
  this.uid = uid
  this.variables = variables
  this.child = child
  this.bind_symbol = bind_symbol
}

function Connective(uid, left, connective, right) {
  this.uid = uid
  this.left = left
  this.connective = connective
  this.right = right
}

function Ternary(uid, fst,snd,thd,pre,inf,post) {
  this.uid = uid;
  this.fst = fst;
  this.snd = snd;
  this.thd = thd;
  this.pre = pre
  this.inf = inf;
  this.post = post;
}


// Logic for converting plain old objects into instances
// This makes pattern matching-style logic cleaner.
// Think of this method as a method for determining the type of a formula
// based upon the names of its fields.
function formulaToInstance(f) {
  var rec_on = formulaToInstance //shorthand.
  if(f.str)              new Atomic(f.uid, f.str)
  else if(f.pre_symbol)  new Prefix(f.uid, rec_on(f.child), f.pre_symbol)
  else if(f.post_symbol) new Postfix(f.uid, rec_on(f.child), f.post_symbol)
  else if(f.left_symbol) 
    new Grouping(f.uid, rec_on(f.inner), f.left_symbol, f.right_symbol)
  else if(f.program)     
    new Modality(f.uid, rec_on(f.program), rec_on(f.formula), f.open, f.close)
  else if(f.bind_symbol) {
    var rec_variables = new Array();
    for(var i=0; i<f.variables.length; i++) {
      rec_variables.push(rec_on(f.variables[i]));
    }
    new Binding(f.uid, f.bind_symbol, rec_variables, rec_on(f.child))
  }
  else if(f.connective)  
    new Connective(f.uid, rec_on(f.left), f.connective, rec_on(f.right))
  else if(f.thd)         
    new Ternary(f.uid,
        rec_on(f.fst),rec_on(f.snd),rec_on(f.thd),
        f.pre,f.inf,f.post)
  else
    null
}

// Pattern matching for formuals.
function formulaMatch(formula, atomicF, prefixF, postfixF, groupingF, 
    modalityF, bindingF, connectiveF, ternaryF) 
{
  if(formula) {
    if(formula instanceof Atomic) atomicF(formula);
    else if(formula instanceof Prefix) prefixF(formula);
    else if(formula instanceof Postfix) postfixF(formula);
    else if(formula instanceof Grouping) groupingF(formula);
    else if(formula instanceof Modality) modalityF(formula);
    else if(formula instanceof Binding) bindingF(formula);
    else if(formula instanceof Connective) connectiveF(formula);
    else if(formula instanceof Ternary) connectiveF(formula);
    else formulaMatch(formulaToInstance(formula)); //returns null on fail.
  }
  else {
    throw "Formula did not match any type."
  }
}

//// API Calls for Formulas
var FormulaAPI = {
  getOptions : function(formula) {
  }
}


var FormulaGUI = {
  toString : function(client, formula) {
    return client.formulaToString(formula);
  },

  // Writes a simple string to the static span for this formula, or creates
  // such a span if it does not yet exist. Returns the modified span.
  staticView : function(client, formula) {
    var span;
    if(document.getElementById("s" + formula.uid)) {
      span = document.getElementById("s" + formula.uid);
    }
    else {
      span = document.createElement('span');
      span.setAttribute('id', "s" + formula.uid);
    }

    span.innerHTML = client.formulaToString(formula);
    return span;
  },

  interactiveView : function(client, div, formula) {
    var span;
    if(document.getElementById("i" + formula.uid)) {
      span = document.getElementById("i" + formula.uid);
    }
    else {
      span = document.createElement('span');
      span.setAttribute('id', "i" + formula.uid);
    }
    span.innerHTML = client.formulaToInteractiveString(formula);
    return span;
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

function Sequent(uid, pref, ante, succ) {
  this.uid = uid
  this.pref = pref
  this.ante = ante
  this.succ = succ
}

var SequentGUI = {
  sequentSymbol : "&#x22A2",

  toString : function(client, sequent) {
    var result = "";

    if(sequent.ante) {
      for(var i=0; i < sequent.ante.length; i++) {
        var f = sequent.ante[i];
        result += FormulaGUI.toString(client, f);
      }
    }
    result += " " + this.sequentSymbol + " "; //spaces necessary to prevent []
    if(sequent.succ) {
      for(var i=0; i < sequent.succ.length; i++) {
        var f = sequent.succ[i];
        result += FormulaGUI.toString(client, sequent.succ[i]);
      }
    }

    return result;
  },

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

////////////////////////////////////////////////////////////////////////////////
// Nodes
////////////////////////////////////////////////////////////////////////////////

function Node(uid, parentUid, sequent) {
  this.uid = uid
  this.parentUid = parentUid
  this.sequent = sequent
}
