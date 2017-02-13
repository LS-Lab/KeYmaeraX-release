angular.module('formula', ['ngSanitize']);

/** Renders a formula into hierarchically structured spans */
angular.module('formula')
  .directive('k4Formula', ['$compile', '$http', '$sce', '$q', 'derivationInfos', 'sequentProofData', function($compile, $http, $sce, $q, derivationInfos, sequentProofData) {
    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            formula: '=',
            highlight: '=',
            collapsed: '=?',
            onTactic: '&',     // onTactic(formulaId, tacticId)
            onTwoPositionTactic: '&',
            onInputTactic: '&' // onInputTactic(formulaId, tacticId, input)
        },
        link: function(scope, element, attrs) {
            scope.formulaAxiomsMap = {};

            scope.fetchFormulaAxioms = function(formulaId, axiomsHandler) {
              if (scope.formulaAxiomsMap[formulaId] === undefined) {
                // axioms not fetched yet
                derivationInfos.formulaDerivationInfos(scope.userId, scope.proofId, scope.nodeId, formulaId)
                  .then(function(response) {
                    scope.formulaAxiomsMap[formulaId] = response.data;
                    axiomsHandler.call();
                  });
              } else {
                // tactic already cached
                axiomsHandler.call();
              }
            }

            scope.editClick = function(formulaId, event) {
              if (sequentProofData.formulas.mode == 'edit') {
                // avoid event propagation to parent span (otherwise: multiple calls with a single click since nested spans)
                event.stopPropagation();
                $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + formulaId + '/prettyString').
                  then(function(response) {
                    scope.editFormulaPopover.open(formulaId, response.data.prettyString);
                  });
              }
            }

            scope.formulaClick = function(formulaId, event) {
              if (sequentProofData.formulas.mode == 'prove') {
                // avoid event propagation to parent span (otherwise: multiple calls with a single click since nested spans)
                event.stopPropagation();
                $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + formulaId + '/whatStep').
                  then(function(response) {
                    if (response.data.length > 0) {
                      scope.onTactic({formulaId: formulaId, tacticId: "StepAt"});
                    } else {
                      scope.fetchFormulaAxioms(formulaId, function() {
                        scope.tacticPopover.open(formulaId);
                      });
                    }
                });
              }
            }

            scope.formulaRightClick = function(formulaId, event) {
              event.stopPropagation();
              if (sequentProofData.formulas.mode == 'prove') {
                scope.fetchFormulaAxioms(formulaId, function() {
                  scope.tacticPopover.open(formulaId);
                });
              }
            }

            scope.applyTactic = function(formulaId, tacticId) {
              scope.tacticPopover.close();
              scope.onTactic({formulaId: formulaId, tacticId: tacticId});
            }

            scope.applyInputTactic = function(formulaId, tactic) {
              scope.tacticPopover.close();
              //@note have to declare local variables with exactly the names of the event arguments,
              //      otherwise the event parameters are undefined in the listener :-O
              var tacticId = tactic.id;
              var input = tactic.derivation.input;
              scope.onInputTactic({formulaId: formulaId, tacticId: tacticId, input: input});
            }

            scope.input = function(formula, tactic) {
              return $.grep(tactic.derivation.input, function(elem, i) { return elem.param === formula; })[0].value;
            }

            scope.tacticPopover = {
              openFormulaId: undefined,
              isOpen: function(formulaId) { return sequentProofData.formulas.mode=='prove' && scope.tacticPopover.openFormulaId !== undefined && scope.tacticPopover.openFormulaId === formulaId; },
              open: function(formulaId) { scope.tacticPopover.openFormulaId = formulaId; },
              formulaId: function() { return scope.tacticPopover.openFormulaId; },
              close: function() { scope.tacticPopover.openFormulaId = undefined; }
            }

            scope.editFormulaPopover = {
              openFormulaId: undefined,
              formula: undefined,
              isOpen: function(formulaId) { return sequentProofData.formulas.mode=='edit' && scope.editFormulaPopover.openFormulaId !== undefined && scope.editFormulaPopover.openFormulaId === formulaId; },
              open: function(formulaId, formulaText) { scope.editFormulaPopover.openFormulaId = formulaId; scope.editFormulaPopover.formula = formulaText; },
              formulaId: function() { return scope.editFormulaPopover.openFormulaId; },
              close: function() { scope.editFormulaPopover.openFormulaId = undefined; },
              edit: function() {
                scope.onInputTactic({
                  formulaId: scope.editFormulaPopover.openFormulaId,
                  tacticId: 'transform',
                  input: [{
                    'param': 'toFormula',
                    'value': scope.editFormulaPopover.formula
                  }]
                });
                scope.editFormulaPopover.openFormulaId = undefined;
                if (!sequentProofData.formulas.stickyEdit) sequentProofData.formulas.mode = 'prove';
              }
            }

            scope.dndTooltip = {
              openFormulaId: undefined,
              data: undefined,
              isOpen: function(formulaId) { return this.openFormulaId !== undefined && this.openFormulaId === formulaId; },
              open: function(formulaId) { this.openFormulaId = formulaId; },
              formulaId: function() { return this.openFormulaId; },
              close: function() { this.openFormulaId = undefined; }
            }

            dndSinks = {};
            scope.dndSink = function(sinkFormulaId) {
              if (dndSinks[sinkFormulaId] === undefined) {
                dndSinks[sinkFormulaId] = {
                  requestTimeout: undefined,
                  formulaDrop: function(dragData) {
                    if (this.requestTimeout !== undefined) this.requestTimeout.resolve();
                    scope.dndTooltip.close();
                    if (sinkFormulaId !== dragData) {
                      var fml1Id = dragData;
                      var fml2Id = sinkFormulaId;
                      scope.onTwoPositionTactic({fml1Id: fml1Id, fml2Id: fml2Id, tacticId: 'step'});
                    }
                  },
                  formulaDragEnter: function(dragData) {
                    if (!sinkFormulaId.startsWith(dragData)) {
                      this.requestTimeout = $q.defer();
                      $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + dragData + '/' + sinkFormulaId + '/twoposlist', {timeout: this.requestTimeout.promise})
                        .then(function(response) {
                          if (response.data.length > 0) {
                            var tactic = response.data[0];
                            scope.dndTooltip.data = derivationInfos.convertTacticInfo(tactic);
                          } else {
                            scope.dndTooltip.data = undefined;
                          }
                          scope.dndTooltip.open(sinkFormulaId);
                        });
                    }
                  },
                  formulaDragLeave: function(dragData) {
                    if (this.requestTimeout !== undefined) this.requestTimeout.resolve();
                    scope.dndTooltip.close();
                  }
                }
              }
              return dndSinks[sinkFormulaId];
            }

            scope.highlightFormula = function(event, formulaId, onMode) {
              if (sequentProofData.formulas.mode == onMode) {
                event.stopPropagation();
                sequentProofData.formulas.highlighted = formulaId;
              }
            }

            scope.modeIsProve = function() {
              return sequentProofData.formulas.mode == 'prove';
            }

            scope.modeIsEdit = function() {
              return sequentProofData.formulas.mode == 'edit';
            }

            scope.isProveFormulaHighlighted = function(formulaId) {
              return scope.highlight && sequentProofData.formulas.highlighted == formulaId && sequentProofData.formulas.mode == 'prove';
            }

            scope.isEditFormulaHighlighted = function(formulaId) {
              return scope.highlight && sequentProofData.formulas.highlighted == formulaId && sequentProofData.formulas.mode == 'edit';
            }

            var fmlMarkup = scope.collapsed ? scope.formula.string : scope.formula.html;
            // compile template, bind to scope, and add into DOM
            if (scope.collapsed) {
              //@note if collapsed we don't have any listeners, no need to compile
              element.append('<span class="k4-formula-preformat">' + fmlMarkup + '</span>');
            } else {
              var template = '<span ng-class="{\'k4-abbreviate\': collapsed, \'k4-formula-preformat\': true}">' + fmlMarkup + '</span>';
              element.append($compile(template)(scope));
            }

        }
    };
  }]);
