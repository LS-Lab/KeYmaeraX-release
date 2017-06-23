angular.module('formula', ['ngSanitize']);

/** Renders a formula into hierarchically structured spans */
angular.module('formula')
  .directive('k4Formula', ['$compile', '$http', '$sce', '$q', 'derivationInfos', 'sequentProofData', 'spinnerService',
      function($compile, $http, $sce, $q, derivationInfos, sequentProofData, spinnerService) {
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
        templateUrl: 'templates/formula.html',
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

            scope.saveValue = function(input, newValue) {
              return input.saveValue(scope.userId, scope.proofId, scope.nodeId, newValue);
            }

            scope.exprMouseOver = function(event, step, editable) {
              if (scope.modeIsEdit() && editable=='editable') {
                event.stopPropagation();
                $(event.currentTarget).addClass("k4-edit-hover");
              } else if (scope.modeIsProve() && step=='has-step') {
                event.stopPropagation();
                $(event.currentTarget).addClass("k4-prove-hover");
              }
            }

            scope.exprMouseOut = function(event) {
              $(event.currentTarget).removeClass("k4-edit-hover");
              $(event.currentTarget).removeClass("k4-prove-hover");
            }

            scope.exprClick = function(event, formulaId, step, editable) {
              if (scope.modeIsProve() && formulaId && formulaId !== '' && step == 'has-step') {
                // avoid event propagation once a span with an ID is found
                event.stopPropagation();
                spinnerService.show('tacticExecutionSpinner');
                $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + formulaId + '/whatStep').
                  then(function(response) {
                    if (response.data.length > 0) {
                      scope.onTactic({formulaId: formulaId, tacticId: "StepAt"});
                    } else {
                      scope.fetchFormulaAxioms(formulaId, function() {
                        spinnerService.hide('tacticExecutionSpinner')
                        scope.tacticPopover.open(formulaId);
                      });
                    }
                });
              } else if (scope.modeIsEdit() && formulaId && formulaId !== '' && editable == 'editable') {
                // not used
              }
            }

            scope.exprRightClick = function(event, formulaId, step, editable) {
              if (scope.modeIsProve() && formulaId && formulaId !== '' && step == 'has-step') {
                event.stopPropagation();
                scope.fetchFormulaAxioms(formulaId, function() {
                  scope.tacticPopover.open(formulaId);
                });
              } else if (scope.modeIsEdit() && formulaId && formulaId !== '' && editable == 'editable') {
                // not used
              }
            }

            scope.editExpr = function(exprId, newExpr) {
              scope.onInputTactic({formulaId: exprId, tacticId: 'edit', input: [{'param': 'to', 'value': newExpr}]});
              var tacticResult = $q.defer();
              scope.$on('proof.message', function(event, data) {
                if (data.textStatus && data.textStatus != "") {
                  tacticResult.resolve(data.textStatus + "\nDetails:" + data.causeMsg);
                } else {
                  tacticResult.resolve();
                }
              });
              return tacticResult.promise;
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
              isOpen: function(formulaId) { return scope.modeIsProve() && scope.tacticPopover.openFormulaId && scope.tacticPopover.openFormulaId === formulaId; },
              open: function(formulaId) { scope.tacticPopover.openFormulaId = formulaId; },
              formulaId: function() { return scope.tacticPopover.openFormulaId; },
              close: function() { scope.tacticPopover.openFormulaId = undefined; }
            }

            scope.editFormulaPopover = {
              openFormulaId: undefined,
              formula: undefined,
              formulaOrAbbrv: undefined,
              abbrv: false,
              tooltip: 'Abbreviate',
              isOpen: function(formulaId) { return scope.modeIsEdit() && scope.editFormulaPopover.openFormulaId && scope.editFormulaPopover.openFormulaId === formulaId; },
              open: function(formulaId, formulaText) {
                scope.editFormulaPopover.openFormulaId = formulaId;
                scope.editFormulaPopover.formula = formulaText;
                scope.editFormulaPopover.abbrvMode(false);
              },
              formulaId: function() { return scope.editFormulaPopover.openFormulaId; },
              close: function() { scope.editFormulaPopover.openFormulaId = undefined; },
              edit: function() {
                scope.onInputTactic({
                  formulaId: scope.editFormulaPopover.openFormulaId,
                  tacticId: (scope.editFormulaPopover.abbrv ? 'abbrv': 'transform'),
                  input: (scope.editFormulaPopover.abbrv ? [
                    {'param': 't',
                     'value': scope.editFormulaPopover.formula},
                    {'param': 'v',
                     'value': scope.editFormulaPopover.formulaOrAbbrv},
                  ] : [
                    {'param': 'to',
                     'value': scope.editFormulaPopover.formulaOrAbbrv}
                  ])
                });
                scope.editFormulaPopover.openFormulaId = undefined;
                if (!sequentProofData.formulas.stickyEdit) sequentProofData.formulas.mode = 'prove';
              },
              abbrvMode: function(abbrv) {
                scope.editFormulaPopover.abbrv = abbrv;
                if (abbrv) {
                  scope.editFormulaPopover.formulaOrAbbrv = undefined,
                  scope.editFormulaPopover.tooltip = 'Cancel abbreviation';
                } else {
                  scope.editFormulaPopover.formulaOrAbbrv = scope.editFormulaPopover.formula;
                  scope.editFormulaPopover.tooltip = 'Abbreviate';
                }
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

            scope.modeIsProve = function() {
              return sequentProofData.formulas.mode == 'prove';
            }

            scope.modeIsEdit = function() {
              return sequentProofData.formulas.mode == 'edit';
            }

//            console.log("Compiling formula")
//            var fmlMarkup = scope.collapsed ? scope.formula.string : scope.formula.html;
//            // compile template, bind to scope, and add into DOM
//            if (scope.collapsed) {
//              //@note if collapsed we don't have any listeners, no need to compile
//              element.append('<span class="k4-formula-preformat">' + fmlMarkup + '</span>');
//            } else {
//              var template = '<span ng-class="{\'k4-abbreviate\': collapsed, \'k4-formula-preformat\': true}">' + fmlMarkup + '</span>';
//              element.append($compile(template)(scope));
//            }
//            console.log("Done compiling")
        }
    };
  }]);
