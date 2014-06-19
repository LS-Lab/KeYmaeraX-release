/*
 * Tactics relevant to the use interface
 * Nathan Fulton 2014
 */

/*
 * This is a list of Tactics and InputTactics. To add a new tactic to the UI,
 * add it to this list. The last argument to any constructor should be true
 * if the tactic is a position tactic.
 *
 * Logic for displaying lists of tactics and for initiating API calls is
 * defined in expression.js
 *
 * See the definitions of Tactic and InputTactic for instructions if these 
 * examples do not clearly indicate how to add a tactic.
 */
var tacticList = [
  new Tactic("default"),
  new Tactic("closeT"),
  new Tactic("ptac1", true),
  new InputTactic("itac1", ["input"]),
]

/*
 * A tactic which takes no user input. These are displayed when a sequent
 * symbol is selected.
 */
function Tactic(name, isPositionTactic) {
  this.name = name;
  this.isPositionTactic;
  if(isPositionTactic == true) this.isPositionTactic = true 
  else this.isPositionTactic = false
}

/*
 * A tactic which takes some user input. These are displayed when a subformula
 * is selected during interactive mode. You may require arbitrarily many input
 * fields. The fieldLabels will be used as argument names in the API call, so
 * these should be valid parameter names.
 *
 * helpMessages is associated with fieldLabels, and will be printed along with
 * the fieldLabel during input elicitation if defined.
 *
 * fields : Array of field names if this is an interactive tactics
 */
function InputTactic(name, fieldLabels, isPositionTactic) {
  if(fieldLabels != null) {
    if(!(fieldLabels instanceof Array)) throw "fieldLabels argument (2) should be an array"
    this.helpMessages = fieldLabels.map(function() { return null }) //By default, there is no help message.
  }
  this.name = name
  this.fieldLabels = fieldLabels //todo check that these are valid parameter names.
  this.isPositionTactic = isPositionTactic;
  if(this.isPositionTactic == null) {
    this.isPositionTactic = false;
  }
}

var TacticLibrary = {
  getSequentTactics : function() {
    var result = tacticList.filter(function(x) {return !x.isPositionTactic})
    if(result === null) {
      return new Array();
    }
    else {
      return result
    }
  },

  getPositionTactics : function() {
    var result = tacticList.filter(function(x) { return x.isPositionTactic })
    if(result === null) {
      return new Array();
    }
    else {
      return result
    }
  },

  isInputTactic : function(x) { x instanceof InputTactic },

  getInputs : function(t) {
    if(!(t instanceof InputTactic)) {
      throw "Attempting to get inputs for a non-input tactic"
    }
    if(t.fieldLabels.length != t.helpMessages.length) {
      throw "fieldLabels and helpMessages are no the same length. Please don't" +
        " append to the fieldLabels or helpMessages variables after InputTactic" +
        " contruction."
    }
    else {
      var inputs = [];
      for(var i = 0 ; i < t.fieldLabels.length; i++) {
        var label = t.fieldLabels[i];
        var msg   = t.helpMessages[i];
        if(msg === null) msg = "";
        var input = UI.getInput(msg + "\n" + label + ":");
        if(input === null) throw "Input value should not be null."
        inputs.push(input);
      }
      return inputs;
    }
  }
}
