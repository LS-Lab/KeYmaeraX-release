angular.module('formula', ['ngSanitize']);

/** Renders a formula into hierarchically structured spans */
angular.module('formula')
  .directive('k4Formula', ['$compile', '$http', '$sce', '$q', '$uibModal', 'derivationInfos', 'sequentProofData',
             'spinnerService',
      function($compile, $http, $sce, $q, $uibModal, derivationInfos, sequentProofData, spinnerService) {
    return {
        restrict: 'AE',
        scope: {
            userId: '@',
            proofId: '@',
            nodeId: '@',
            formula: '=',
            highlight: '=',
            collapsed: '=?',
            onExprRightClick: '&',
            onTactic: '&',     // onTactic(formulaId, tacticId)
            onTwoPositionTactic: '&',
            onInputTactic: '&' // onInputTactic(formulaId, tacticId, input)
        },
        templateUrl: 'templates/formula.html',
        link: function(scope, element, attrs) {

            scope.saveValue = function(input, newValue) {
              return input.saveValue(scope.userId, scope.proofId, scope.nodeId, newValue);
            }

            scope.exprMouseOver = function(event, step, editable) {
              if (scope.modeIsEdit() && editable=='editable') {
                event.stopPropagation();
                $(event.currentTarget).addClass("k4-edit-hover");
              } else if (scope.modeIsProve() && !event.altKey && step === 'has-step') {
                event.stopPropagation();
                $(event.currentTarget).addClass("k4-prove-hover");
              } else if (scope.modeIsProve() && event.altKey && step === 'has-step') {
                event.stopPropagation();
                $(event.currentTarget).addClass("k4-chase-hover");
              } else if (scope.modeIsSelect() && !event.altKey && step === 'has-step') {
                event.stopPropagation();
                $(event.currentTarget).addClass("k4-select-hover");
              } else if (scope.modeIsSelect() && event.altKey && event.currentTarget.id.length > 4) {
                // with option pressed, any formula or term with an ID is selectable (fml_#)
                event.stopPropagation();
                $(event.currentTarget).addClass("k4-select-hover");
              }
            }

            scope.exprMouseOut = function(event) {
              $(event.currentTarget).removeClass("k4-edit-hover");
              $(event.currentTarget).removeClass("k4-prove-hover");
              $(event.currentTarget).removeClass("k4-chase-hover");
              $(event.currentTarget).removeClass("k4-select-hover");
            }

            scope.exprClick = function(event, formulaId, step, editable) {
              //@note do not execute click on text selection (copy-paste)
              if (event.view.getSelection().toString().length == 0) {
                if (scope.modeIsProve() && formulaId && formulaId !== '' && step === 'has-step') {
                  // avoid event propagation once a span with an ID is found
                  event.stopPropagation();
                  spinnerService.show('tacticExecutionSpinner');
                  if (event.altKey) {
                    // chase
                    scope.onTactic({formulaId: formulaId, tacticId: 'chaseAt'})
                  } else {
                    // step
                    $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + formulaId + '/whatStep').
                      then(function(response) {
                        if (response.data.length > 0) {
                          scope.onTactic({formulaId: formulaId, tacticId: "StepAt"});
                        } else {
                          spinnerService.hide('tacticExecutionSpinner');
                          scope.onExprRightClick({formulaId: formulaId});
                        }
                    });
                  }
                } else if (scope.modeIsEdit() && formulaId && formulaId !== '' && editable === 'editable') {
                  // not used
                } else if (scope.modeIsSelect() && formulaId && formulaId !== ''
                    && (step === 'has-step' || event.altKey)) {
                  event.stopPropagation();
                  $(".k4-select-selected").removeClass("k4-select-selected");
                  $(event.currentTarget).removeClass("k4-select-hover");
                  $(event.currentTarget).addClass("k4-select-selected");
                  scope.onTactic({formulaId: formulaId, tacticId: undefined});
                }
              }
            }

            scope.exprRightClick = function(event, formulaId, step, editable) {
              if (scope.modeIsProve() && formulaId && formulaId !== '' && step == 'has-step') {
                event.stopPropagation();
                scope.onExprRightClick({formulaId: formulaId});
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
              scope.onTactic({formulaId: formulaId, tacticId: tacticId});
            }

            scope.applyInputTactic = function(formulaId, tacticId, input) {
              scope.onInputTactic({formulaId: formulaId, tacticId: tacticId, input: input});
            }

            scope.input = function(formula, tactic) {
              return $.grep(tactic.derivation.input, function(elem, i) { return elem.param === formula; })[0].value;
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
              return sequentProofData.formulas.mode === 'prove';
            }

            scope.modeIsEdit = function() {
              return sequentProofData.formulas.mode === 'edit';
            }

            scope.modeIsSelect = function() {
              return sequentProofData.formulas.mode === 'select';
            }

            scope.trustedHtml = function(html) {
              return $sce.trustAsHtml(html);
            }

            scope.replaceSpecialNotation = function(html) {
              return html.replace(/(\w+)(?:(\(\))|(\(\|\|\))|({\|\^@\|}))/g,
                function(match, name, fnParens, fnctlParens, sysParens, offset, string) {
                  if (name.startsWith('A__')) return name.replace(/A__(\d+)/g,
                    function(match, i, offset, string) { return '<span class="k4-assumptions-cart fa fa-shopping-cart small text-muted"><sub>' + i + '</sub></span>'; })
                  else if (fnParens) return '<span class="k4-nullary-fn">' + name + '</span>';
                  else if (fnctlParens) return '<span class="k4-functional">' + name + '</span>';
                  else if (sysParens) return '<span class="k4-system-const">' + name + '</span>';
                  else return html;
                });
            }

            scope.replacePlainSpecialNotation = function(text) {
              return text.replace(/(\w+)(?:(\(\))|({\|\^@\|}))/g, function(match, name, fnParens, sysParens, offset, string) {
                return name;
              });
            }

            scope.subscriptIndex = function(html) {
              return html;
              //@note disabled for now for proper copy-paste behavior
//              return html.replace(/_(\d+)/g, function(match, idx, parens, offset, string) {
//                return '<sub>' + idx + '</sub>';
//              });
            }
        }
    };
  }]);
