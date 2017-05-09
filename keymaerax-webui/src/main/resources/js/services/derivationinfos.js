angular.module('keymaerax.services').factory('derivationInfos', ['$http', '$rootScope', '$q', function($http, $rootScope, $q) {
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
    sequentSuggestionDerivationInfos: function(userId, proofId, nodeId) {
      var promise = $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/listStepSuggestions')
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
      info.isOpen = false;
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
          numInputs: tactic.derivation.input.length,
          isClosed: premise.isClosed
        };
      });
      tactic.missingInputNames = function() {
        var missingInputs = $.grep(tactic.derivation.input, function(input, idx) { return input.value == undefined; });
        return $.map(missingInputs, function(val, i) { return val.param; });
      };
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
        var occurrences = [];
        while (inputStart >= 0) {
          occurrences.push({start: inputStart, end: inputStart + input.param.length });
          inputStart = formula.indexOf(input.param, inputStart + input.param.length);
        }
        return occurrences;
      }).sort(function(a, b) { return a.start - b.start; });

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
      var inputObject = {
        text: inputId,
        isInput: true,
        placeholder: inputId,
        value: $.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0].value,
        saveValue: function(userId, proofId, nodeId, newValue) {
          var input = $.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0];
          input.value = newValue;
          var d = $q.defer();
          var uri = 'proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/checkInput/' + tactic.id;
          $http.get(uri, {params: input}).then(function(response) {
            if (response.data.success) d.resolve();
            else d.resolve("Warning: executing tactic may fail, because " + response.data.errorText);
          })
          .catch(function(err) {
            d.resolve(err.data);
          });
          return d.promise;
        }
      };
      // auto-update all input elements that are scattered around different parts of the premise
      $rootScope.$watch(
        // what to watch
        function(scope) { return $.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0].value; },
        // what to do on change
        function(newVal, oldVal) { inputObject.value = newVal; }
      );
      $rootScope.$watch(
        function(scope) { return inputObject.value; },
        function(newVal, oldVal) {
          $.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0].value = newVal;
        }
      );
      return inputObject;
    }
  }
  return serviceDef;
}])