angular.module('keymaerax.ui.tacticeditor', ['ngSanitize', 'ngTextcomplete', 'diff-match-patch'])
  .directive('k4TacticEditor', ['$http', 'derivationInfos', 'Textcomplete', 'sequentProofData', '$window',
      function($http, derivationInfos, Textcomplete, sequentProofData, $window) {
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

          var DiffMatchPatch = $window.diff_match_patch;

          var combinators = ['*', '|', '&', '<'];
          var ta = elem.find('textarea');
          var textcomplete = new Textcomplete(ta, [
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
            dmp = new DiffMatchPatch();
            diffs = dmp.diff_main(scope.tactic.lastExecutedTacticText, scope.tactic.tacticText);
            dmp.Diff_EditCost = scope.diffOptions.editCost;
            dmp.diff_cleanupEfficiency(diffs);

            var intros = $.grep(diffs, function(e, i) {
              /* e is of the form Array[type,text], where type==0 means equal, type==1 means intro */
              return e[0] == 1;
            });

            intros = $.map(intros, function(e, i) {
              var trimmed = e[1].trim();
              return trimmed.charAt(0) == '&' ? trimmed.substring(1, trimmed.length) : trimmed;
            })

            //@todo what if more than 1 intro?
            scope.onTacticScript({tacticText: intros[0]});
          };

          scope.diffOptions = {
            editCost: 4,
            attrs: {
              insert: {
                'data-attr': 'insert',
                'class': 'insertion'
              },
              delete: {
                'data-attr': 'delete'
              },
              equal: {
                'data-attr': 'equal'
              }
            }
          };

//          rangy.init();
//
//          var savedSel = {};
//          var listener = function listener() {
//            console.log("Diff HTML changed")
//            if (savedSel.element !== undefined && savedSel.range !== undefined) {
//              rangy.getSelection().restoreCharacterRanges(savedSel.element, savedSel.range);
//            }
//          };
//
//          scope.$watch('tactic.diffHtml', listener);
//
//          scope.tacticChange = function(event) {
//            //@todo does not work with deletions
//            //@todo cursor flickering
//            savedSel.element = event.target;
//            savedSel.range = rangy.getSelection().saveCharacterRanges(event.target);
//            sequentProofData.tactic.tacticText = event.target.innerText;
//          }

          $(textcomplete).on({
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
                    '<textarea class="k4-tacticeditor" ng-model="tactic.tacticText" rows="10" ng-shift-enter="executeTacticDiff()"></textarea>' +
                      '</div></div>' +
                      '<div class="row k4-tacticeditor"><div class="col-md-12">' +
                      '<pre class="textdiff" processing-diff left-obj="tactic.lastExecutedTacticText" right-obj="tactic.tacticText" options="diffOptions"></pre>' +
                  '</div></div>' +
                  '<div class="row"><div class="col-md-12"><button class="btn btn-default" ng-click="executeTacticDiff()">Run</button></div></div>'
    };
  }]);
