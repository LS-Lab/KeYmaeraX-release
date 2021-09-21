angular.module('sequent', ['ngSanitize', 'formula', 'ui.bootstrap', 'ngCookies', 'angularSpinners'])
  .directive('k4Sequent', ['$rootScope', '$uibModal', '$http', 'spinnerService', 'sequentProofData', 'derivationInfos',
      function($rootScope, $uibModal, $http, spinnerService, sequentProofData, derivationInfos) {
    return {
        restrict: 'AE',
        scope: {
            userId: '@',
            proofId: '@',
            nodeId: '@',
            sequent: '=',
            readOnly: '=?',
            inClosedProof: '=?',
            collapsed: '=?',
            abbreviate: '=?',
            onApplyTactic: '&',
            onApplyInputTactic: '&',
            onApplyTwoPositionTactic: '&'
        },
        link: function(scope, elem, attr) {
            scope.sequentSuggestions = [];

            if (!scope.readOnly) {
              derivationInfos.sequentSuggestionDerivationInfos(scope.userId, scope.proofId, scope.nodeId)
                .then(function(response) {
                  scope.sequentSuggestions = response.data;
                });
            }

            //@todo duplicate with provingawesome.js#getCounterExample
            scope.getCounterExample = function(additionalAssumptions) {
                //@todo timeout request canceller
                spinnerService.show('counterExampleSpinner');
                var nodeId = sequentProofData.agenda.selectedId();
                var node = sequentProofData.proofTree.node(nodeId);
                var selected = sequentProofData.formulas.selectedIndicesIn(node.getSequent());
                var additional = additionalAssumptions ? additionalAssumptions : {};
                var url = 'proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/counterExample'
                $http.get(url, { params: { assumptions: additional, fmlIndices: JSON.stringify(selected) } })
                    .then(function(response) {
                      var dialogSize = (response.data.result === 'cex.found') ? 'lg' : 'md';
                      var modalInstance = $uibModal.open({
                        templateUrl: 'templates/counterExample.html',
                        controller: 'CounterExampleCtrl',
                        size: dialogSize,
                        resolve: {
                          result: function() { return response.data.result; },
                          origFormula: function() { return response.data.origFormula; },
                          cexFormula: function() { return response.data.cexFormula; },
                          cexValues: function() { return response.data.cexValues; },
                          speculatedValues: function() { return response.data.speculatedValues; }
                        }
                      });
                      modalInstance.result.then(
                        function(result) {
                          // dialog closed with request to recalculate using additional assumptions
                          $scope.getCounterExample(result);
                        },
                        function() { /* dialog cancelled */ }
                      );
                    })
                    .catch(function(err) {
                      $uibModal.open({
                        templateUrl: 'templates/parseError.html',
                        controller: 'ParseErrorCtrl',
                        size: 'md',
                        resolve: {
                          model: function () { return undefined; },
                          error: function () { return err.data; }
                      }});
                    })
                    .finally(function() { spinnerService.hide('counterExampleSpinner'); });
            }

            scope.onTactic = function(formulaId, tacticId) {
              scope.tacticPopover.close();
              scope.onApplyTactic({formulaId: formulaId, tacticId: tacticId});
            }

            scope.onInputTactic = function(formulaId, tacticId, input) {
              scope.tacticPopover.close();
              scope.onApplyInputTactic({formulaId: formulaId, tacticId: tacticId, input: input});
            }

            scope.onTwoPositionTactic = function(fml1Id, fml2Id, tacticId) {
              scope.tacticPopover.close();
              scope.onApplyTwoPositionTactic({fml1Id: fml1Id, fml2Id: fml2Id, tacticId: tacticId});
            }

            scope.onDragStart = function(event) {
              angular.element(event.target.firstChild.firstChild).removeClass('hlhover'); // remove hover effect on drag
            }

            scope.openTacticPosInputDialog = function(tacticName) {
              var tactics = derivationInfos.byName(scope.userId, scope.proofId, scope.nodeId, tacticName)
                .then(function(response) {
                  return response.data;
                });

              var modalInstance = $uibModal.open({
                templateUrl: 'templates/derivationInfoDialog.html',
                controller: 'DerivationInfoDialogCtrl',
                size: 'lg',
                resolve: {
                  tactics: function() { return tactics; },
                  readOnly: function() { return false; },
                  userId: function() { return undefined; },
                  proofId: function() { return undefined; },
                  defaultPositionLocator: function() { return undefined; },
                  sequent: function() { return undefined; }
                }
              });

              modalInstance.result.then(function(data) {
                scope.onInputTactic(data.position, tacticName, data.input);
              })
            }

            scope.turnstileDrop = function(dragData) {
              var formulas = $.grep(scope.sequent.ante, function(e, i) { return e.id === dragData; });
              if (formulas.length == 1) {
                var formula = formulas[0];
                if (formula.formula.name === 'equals') {
                  scope.onApplyTactic({formulaId: formula.id, tacticId: 'allL2R'})
                } else {
                  $rootScope.$emit('proof.message', { textStatus: 'Drop formulas of the form "lhs=rhs" only', errorThrown: "" })
                }
              } else {
                $rootScope.$emit('proof.message', { textStatus: 'Drop antecedent formulas only', errorThrown: "" })
              }
            }

            scope.areAllFmlsUsed = function() {
              return sequentProofData.formulas.areAllFmlsUsed(scope.sequent);
            }

            scope.toggleAllFmls = function() {
              sequentProofData.formulas.toggleUseAllFmls(scope.sequent);
            }

            scope.isFOL = function(formula) {
              //@todo implement
              return true;
            }

            scope.formulaAxiomsMap = {};
            scope.tacticPopover = {
              openFormulaId: undefined,
              isOpen: function(formulaId) {
                // open if formulaId is prefix of openFormulaId (prefix elements separated by ,)
                return scope.tacticPopover.openFormulaId &&
                  (scope.tacticPopover.openFormulaId.length == formulaId.length ||
                   scope.tacticPopover.openFormulaId.charAt(formulaId.length) == ',') &&
                  scope.tacticPopover.openFormulaId.startsWith(formulaId);
              },
              open: function(formulaId) { scope.tacticPopover.openFormulaId = formulaId; },
              formulaId: function() { return scope.tacticPopover.openFormulaId; },
              close: function() { scope.derivationInfos.infos = []; scope.tacticPopover.openFormulaId = undefined; }
            }

            scope.fetchFormulaAxioms = function(formulaId, axiomsHandler) {
              if (scope.formulaAxiomsMap[formulaId] === undefined) {
                // axioms not fetched yet
                derivationInfos.formulaDerivationInfos(scope.userId, scope.proofId, scope.nodeId, formulaId)
                  .then(function(response) {
                    // first tactic entry in popover should be open by default
                    if (response.data.length > 0) response.data[0].isOpen = true
                    scope.formulaAxiomsMap[formulaId] = response.data;
                    axiomsHandler.call();
                  });
              } else {
                // tactic already cached
                axiomsHandler.call();
              }
            }

            scope.fetchApplicableDefinitions = function() {
              derivationInfos.sequentApplicableDefinitions(scope.userId, scope.proofId, scope.nodeId).then(function(defs) {
                scope.definitions = defs;
              });
            }

            scope.lemma = {
              selected: undefined,
              allInfos: function(formulaId, partialLemmaName) {
                if (partialLemmaName && partialLemmaName.length > 0) {
                  var url = 'proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' +
                            formulaId + '/lemmas/' + encodeURIComponent(partialLemmaName);
                  return $http.get(url).then(function(response) { return response.data.lemmas; });
                } else return [];
              },
              select: function(item, model, label, event) {
                scope.lemma.selected = item;
              },
              apply: function(formulaId) {
                scope.onInputTactic(formulaId, 'useAt',
                                    [{param: 'axiom', value: scope.lemma.selected.name },
                                     {param: 'key', value: '' + scope.lemma.selectedKeyPos() }]);
              },
              selectedKeyPos: function() {
                var s = scope.lemma.selected;
                return s.selectedKeyPos ? s.selectedKeyPos : s.defaultKeyPos;
              }
            }

            scope.onExprRightClick = function(formulaId) {
              scope.fetchFormulaAxioms(formulaId, function() {
                scope.tacticPopover.open(formulaId);
              });
            }

            scope.derivationInfos = {
              filter: undefined,
              order: 'standardDerivation.name',
              infos: [],
              lemmas: []
            };

            scope.browseTactics = function() {
              scope.axiomsLoading = true;
              derivationInfos.allDerivationInfos(scope.userId, scope.proofId, scope.nodeId).then(function(response) {
                scope.derivationInfos.infos = response.data;
                scope.axiomsLoading = false;
              });
            };

            scope.browseLemmas = function() {
              scope.lemmasLoading = true;
              derivationInfos.allLemmas(scope.userId).then(function(response) {
                scope.derivationInfos.lemmas = response.data;
                scope.lemmasLoading = false;
              });
            };

            //@see lemmaBrowser.js/useLemma
            scope.useLemma = function(formulaId, lemma) {
              if (lemma.useLemmaTac && lemma.useLemmaTac != "verbatim") {
                var tactic = lemma.useLemmaTac ? (lemma.useLemmaTac != "custom" ? lemma.useLemmaTac : lemma.customTac) : undefined;
                var input = [{ type: "string", param: "lemma", value: lemma.name},
                             { type: "string", param: "tactic", value: tactic }];
                scope.onApplyInputTactic({formulaId: formulaId, tacticId: "useLemma", input: input});
              } else {
                var input = [{ type: "string", param: "lemma", value: lemma.name}];
                scope.onApplyInputTactic({formulaId: formulaId, tacticId: "useLemma", input: input});
              }
            }

            turnstileTooltipOpen = false;
            scope.turnstileDragEnter = function(dragData) { turnstileTooltipOpen = true; }
            scope.turnstileDragLeave = function(dragData) { turnstileTooltipOpen = false; }
            scope.isTurnstileTooltipOpen = function() {return turnstileTooltipOpen;}

            scope.fetchApplicableDefinitions();
        },
        templateUrl: 'partials/collapsiblesequent.html'
    };
  }]);
