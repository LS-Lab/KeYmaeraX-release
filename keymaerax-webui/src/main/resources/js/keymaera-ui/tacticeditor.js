angular.module('keymaerax.ui.tacticeditor', ['ngSanitize', 'ngTextcomplete'])
  .directive('k4TacticEditor', ['$http', 'derivationInfos', 'Textcomplete', 'sequentProofData',
      function($http, derivationInfos, Textcomplete, sequentProofData) {
    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            onTactic: '&',     // onTactic(formulaId, tacticId)
            onTacticScript: '&'
        },
        link: function(scope, elem, attr) {
          scope.tactic = sequentProofData.tactic;

          var combinators = ['*', '|', '&', '<'];
          var tacticContent = elem.find('#tacticcontent');
          var textComplete = new Textcomplete(tacticContent, [
            // combinators
            {
              match: /\B:(\w*)$/,
              search: function (term, callback) {
                callback($.map(combinators, function (element) {
                    return element.indexOf(term) === 0 ? element : null;
                }));
              },
              index: 1,
              replace: function (element) { return element; }
            },
            // positions 1.0.tactic
            {
                match: /(((\-?[1-9]([0-9]*)\.)([0-1]\.)*)(\w*))$/,
                search: function (term, callback) {
                  var dotPos = term.lastIndexOf('.');
                  var keyword = term.substring(dotPos + 1);
                  this.position = term.substring(0, dotPos);
                  // other code for some reason uses , as separator
                  var formulaId = this.position.replace(/\./g, ',');
                  sequentProofData.formulas.highlighted = formulaId.indexOf(',') >= 0 ? formulaId : formulaId + ','; //@note top-level formula IDs end in ','
                  //console.log("Matched term " + term + ", searching for keyword " + keyword + "; position " + this.position);
                  $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + formulaId + '/list')
                       .success(function(data) {
                    sequentProofData.tactic.currentSuggestions = data;
                    callback($.map(data, function (element) {
                      return element.standardDerivation.id.indexOf(keyword) === 0 ? element.standardDerivation.id : null;
                    }));
                  });
                },
                index: 2,
                replace: function (element) {
                  var di = $.grep(sequentProofData.tactic.currentSuggestions, function(e, i) { return e.standardDerivation.id === element })[0];
                  sequentProofData.tactic.currentSuggestions = undefined;
                  sequentProofData.formulas.highlighted = undefined;

                  if (di.standardDerivation.derivation.input == undefined || di.standardDerivation.derivation.input.length == 0) {
                    // tactic without inputs -> execute right away
                    //scope.onTactic({formulaId: this.position, tacticId: element});
                    //return ['<' + element + '>', '</' + element + '>'];
                    return element + "(" + this.position + ")";
                  } else {
                    // tactic with input -> postpone and wait for arguments
                    var inputStrings = $.map(di.standardDerivation.derivation.input, function(e, i) {
                      return "{`" + e.param + ":" + e.type + "`}";
                    });
                    var inputString = inputStrings[0];
                    for (i = 1; i < inputStrings.length; i++) { inputString = inputString + ", " + inputStrings[i]; }
                    return [ element + "(" + inputString, ", " + this.position + ")"];
                  }
                }
            }
          ]);

          scope.executeTacticDiff = function() {
            scope.onTacticScript({tacticText: scope.tactic.tacticDiff});
          };

          scope.$watch('tactic.tacticText', function(newValue, oldValue) {
            var newText = jQuery('<p>'+newValue+'</p>').text(); // strip HTML tags
            var oldText = jQuery('<p>'+oldValue+'</p>').text();
            if (oldText !== newText && scope.tactic.lastExecutedTacticText !== undefined && scope.tactic.tacticText !== undefined) {
              //@note compute diff
              var diffInput = { 'old' : scope.tactic.lastExecutedTacticText, 'new' : newText };
              $http.post('proofs/user/' + scope.userId + '/' + scope.proofId + '/tacticDiff', diffInput)
                .then(function(response) {
                  $('#tacticcontent>span.k4-tacticeditor-error').removeClass('k4-tacticeditor-error');
                  //@todo multiple diffs
                  scope.tactic.tacticDiff = response.data.replNew.length > 0 ? response.data.replNew[0].repl : "";
                })
                .catch(function(response) {
                  if (response.data !== undefined) {
                    var errorText = response.data.textStatus;
                    var location = response.data.location; // { column: Int, line: Int }
                    var unparsableStart = newText.split('\n', location.line-1).join('\n').length + location.column-1;

                    //@todo location end
                    scope.tactic.tacticText = newText.substring(0, unparsableStart) +
                      '<span class="k4-tacticeditor-error" title="' + errorText + '">' +
                      newText.substring(unparsableStart, newText.length) + '</span>'
                  }
                });
            }
          });

          $(textComplete).on({
            'textComplete:select': function(e, value) {
              scope.$apply(function() {
                sequentProofData.tactic.tacticText = value
              })
            },
            'textComplete:show': function(e) {
              $(this).data('autocompleting', true);
            },
            'textComplete:hide': function(e) {
              $(this).data('autocompleting', false);
            }
          });
        },
        template: '<div class="row k4-tacticeditor"><div class="col-md-12">' +
                    '<div contenteditable id="tacticcontent" class="k4-tacticeditor" ng-model="tactic.tacticText" ng-shift-enter="executeTacticDiff()"></div>' +
                  '</div></div>'
    };
  }]);
