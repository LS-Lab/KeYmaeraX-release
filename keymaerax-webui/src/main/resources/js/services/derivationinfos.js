angular.module('keymaerax.services').factory('derivationInfos', ['$http', function($http) {
  var serviceDef = {
    formulaDerivationInfos: function(userId, proofId, nodeId, formulaId) {
      var promise = $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/' + formulaId + '/list')
        .then(function(response) {
          // return value gets picked up by 'then' in the controller using this service
          return {
            data: $.map(response.data, function(info, i) {
              return serviceDef.convertTacticInfo(info, true);
            })
          };
        });
      return promise;
    },

    byName: function(userId, proofId, nodeId, name) {
      //@todo cache
      var promise = $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/derivationInfos/' + name)
        .then(function(response) {
          // return value gets picked up by 'then' in the controller using this service
          return {
            data: $.map(response.data, function(info, i) {
              //@note by name means literally -> so stick to returned info and don't reduce branching by default
              return serviceDef.convertTacticInfo(info, false);
            })
          };
        });
      return promise;
    },

    convertTacticInfo: function(info, reduceBranchingByDefault) {
      info.standardDerivation = serviceDef.convertTactic(info.standardDerivation);
      if (info.comfortDerivation !== undefined) {
        info.comfortDerivation = serviceDef.convertTactic(info.comfortDerivation);
      }
      info.selectedDerivation = function() {
        return info.reduceBranching ? info.comfortDerivation : info.standardDerivation;
      }
      info.reduceBranching = reduceBranchingByDefault && info.comfortDerivation !== undefined;
      info.isOpen = (info.selectedDerivation().derivation.input !== undefined &&
        info.selectedDerivation().derivation.input !== null &&
        info.selectedDerivation().derivation.input.length > 0);
      return info;
    },

    convertTactic: function(tactic) {
      if (tactic.derivation.type === 'sequentrule') {
        return serviceDef.convertSequentRuleToInput(tactic);
      } else if (tactic.derivation.type === 'axiom') {
        return tactic;
      } else if (tactic.derivation.type === 'tactic') {
        return tactic;
      } else {
        console.log("Unknown deduction type '" + tactic.derivation.type + "'");
      }
    },

    convertSequentRuleToInput: function(tactic) {
      tactic.derivation.premise = $.map(tactic.derivation.premise, function(premise, i) {
        return {
          ante: serviceDef.convertToInput(premise.ante, tactic),
          succ: serviceDef.convertToInput(premise.succ, tactic),
          isClosed: premise.isClosed
        };
      });
      return tactic;
    },

    convertToInput: function(formulas, tactic) {
      //@note double-wrap array so that it doesn't get flattened
      return $.map(formulas, function(formula, i) { return [serviceDef.convertFormulaToInput(formula, tactic)]; });
    },

    convertFormulaToInput: function(formula, tactic) {
      var result = [];
      if (tactic.derivation.input === undefined || tactic.derivation.input === null) {
        tactic.derivation.input = [];
      }
      var inputs = $.grep(tactic.derivation.input, function(input, i) { return formula.indexOf(input.param) >= 0; });
      var inputBoundaries = $.map(inputs, function(input, i) {
        var inputStart = formula.indexOf(input.param);
        return {start: inputStart, end: inputStart + input.param.length };
      }).sort(function(a, b) { a.start <= b.start ? -1 : 1; });

      if (inputBoundaries.length > 0) {
        result[0] = {text: formula.slice(0, inputBoundaries[0].start), isInput: false};
        result[1] = serviceDef.createInput(formula, tactic, inputBoundaries[0]);
        for (var i = 1; i < inputBoundaries.length; i++) {
          result[2*i] = {text: formula.slice(inputBoundaries[i-1].end, inputBoundaries[i].start), isInput: false};
          result[2*i+1] = serviceDef.createInput(formula, tactic, inputBoundaries[i]);
        }
        result[2*inputBoundaries.length] = {
          text: formula.slice(inputBoundaries[inputBoundaries.length-1].end, formula.length),
          isInput: false
        }
      } else {
        result[0] = {text: formula, isInput: false};
      }
      return result;
    },

    createInput: function(formula, tactic, inputBoundary) {
      var inputId = formula.slice(inputBoundary.start, inputBoundary.end);
      return {
        text: inputId,
        isInput: true,
        placeholder: inputId,
        value: function(newValue) {
          //@note check arguments.length to determine if we're called as getter or as setter
          return arguments.length ?
            ($.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0].value = newValue) :
             $.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0].value;
        }
      };
    }
  }
  return serviceDef;
}])