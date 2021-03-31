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

    allLemmasCache: undefined,
    allDerivationsCache: undefined,

    allLemmas: function(userId) {
      if (serviceDef.allLemmasCache) {
        return $q(function(resolve, reject) { resolve({data: serviceDef.allLemmasCache}); });
      } else {
        var promise = $http.get('lemmas/users/' + userId)
          .then(function(response) {
            // return value gets picked up by 'then' in the controller using this service
            serviceDef.allLemmasCache = response.data;
            return {
              data: serviceDef.allLemmasCache
            };
          });
        return promise;
      }
    },

    allDerivationInfos: function(userId, proofId, nodeId) {
      if (serviceDef.allDerivationsCache) {
        return $q(function(resolve, reject) { resolve({data: serviceDef.allDerivationsCache}); });
      } else {
        var promise = $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/derivationInfos/')
          .then(function(response) {
            // return value gets picked up by 'then' in the controller using this service
            serviceDef.allDerivationsCache = $.map(response.data, function(info, i) {
              return serviceDef.convertTacticInfo(info, true);
            });
            return {
              data: serviceDef.allDerivationsCache
            };
          });
        return promise;
      }
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
    sequentApplicableDefinitions: function(userId, proofId, nodeId) {
      var promise = $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/listDefinitions')
        .then(function(response) {
          // return value gets picked up by 'then' in the controller using this service
          return response.data;
        });
      return promise;
    },
    setDefinition: function(userId, proofId, what, repl) {
      var data = { what: what, repl: repl };
      var promise = $http.post('proofs/user/' + userId + '/' + proofId + '/definitions', data)
        .then(function(response) {
          // return value gets picked up by 'then' in the controller using this service
          return response.data;
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
      if (tactic == undefined) {
        return tactic;
      } else if (tactic.derivation.type === 'sequentrule') {
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
      tactic.derivation.conclusion = {
        ante: serviceDef.convertToInput(tactic.derivation.conclusion.ante, tactic),
        succ: serviceDef.convertToInput(tactic.derivation.conclusion.succ, tactic),
        numInputs: tactic.derivation.input.length
      };
      tactic.missingInputNames = function() {
        var missingInputs = $.grep(tactic.derivation.input, function(input, idx) {
          return !input.type.startsWith('option[') && input.value == undefined;
        });
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
      //@note search inputs that occur in formula, sorted by length descending
      var inputs = $.grep(tactic.derivation.input, function(input, i) { return formula.indexOf(input.param) >= 0; }).
        sort(function(a, b){ return b.param.length - a.param.length; });
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
        var filteredInputBoundaries = [ inputBoundaries[0] ];
        for (var i = 1; i < inputBoundaries.length; i++) {
          var curr = inputBoundaries[i];
          if (curr.start > filteredInputBoundaries[filteredInputBoundaries.length-1].end) {
            filteredInputBoundaries.push(curr);
          } // else boundaries overlap, i.e., axiom info argument occurs as substring in another, e.g., \exists x j(x), keep only the longer argument
        }

        result[0] = {text: formula.slice(0, filteredInputBoundaries[0].start), isInput: false};
        result[1] = serviceDef.createInput(formula, tactic, filteredInputBoundaries[0]);
        for (var i = 1; i < filteredInputBoundaries.length; i++) {
          result[2*i] = {text: formula.slice(filteredInputBoundaries[i-1].end, filteredInputBoundaries[i].start), isInput: false};
          result[2*i+1] = serviceDef.createInput(formula, tactic, filteredInputBoundaries[i]);
        }
        result[2*filteredInputBoundaries.length] = {
          text: formula.slice(filteredInputBoundaries[filteredInputBoundaries.length-1].end, formula.length),
          isInput: false
        }
      } else {
        result[0] = {text: formula, isInput: false};
      }
      return result;
    },

    sanitizeValue: function(value) {
      //@note used to remove () on inputs for uniform appearance x vs. x(), but has surprising effects when user wants
      //      to insist on function symbol (e.g., when instantiating quantifiers)
      return value;
    },

    createInput: function(formula, tactic, inputBoundary) {
      var inputId = formula.slice(inputBoundary.start, inputBoundary.end);
      var inputObject = {
        text: inputId,
        isInput: true,
        placeholder: inputId,
        value: serviceDef.sanitizeValue($.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0].value),
        saveValue: function(userId, proofId, nodeId, newValue) {
          var input = $.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0];
          input.value = newValue;
          var d = $q.defer();
          var uri = 'proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/checkInput/' + tactic.id;
          $http.post(uri, input).then(function(response) {
            if (response.data.success) d.resolve();
            else d.resolve("Warning: tactic may fail, because " + response.data.errorText);
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
        function(scope) { return serviceDef.sanitizeValue($.grep(tactic.derivation.input, function(elem, i) { return elem.param === inputId; })[0].value); },
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