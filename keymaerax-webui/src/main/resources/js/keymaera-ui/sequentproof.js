angular.module('sequentproof', ['ngSanitize','sequent','formula','angularSpinners'])
  /**
   * A sequent deduction view focused on a single path through the deduction, with links to sibling goals when
   * branching occurs.
   * {{{
   *      <k4-sequentproof userId="1" proofId="35" nodeId="N1"
                           deductionRoot="..." agenda="..." read-only="false"></k4-sequentproof>
   * }}}
   * @param userId          The user ID; for interaction with the server.
   * @param proofId         The current proof; for interaction with the server.
   * @param nodeId          The node (=task); for interaction with the server.
   * @param goalId          The goal (sequent) for cross-referencing agenda items.
   * @param deductionPath   Identifies the path to the goal (as far as loaded); Array[goalId]
   * @param proofTree       The proof tree, see provingawesome.js for schema.
   * @param agenda          The agenda, see provingawesome.js for schema.
   * @param readOnly        Indicates whether or not the proof steps should allow interaction (optional).
   */
  .directive('k4Sequentproof', ['$http', '$uibModal', '$q', '$timeout', '$compile',
                                'ProofTree', 'Agenda', 'sequentProofData', 'spinnerService', 'derivationInfos',
      function($http, $uibModal, $q, $timeout, $compile, ProofTree, Agenda,
               sequentProofData, spinnerService, derivationInfos) {
    /* The directive's internal control. */
    function link(scope, element, attrs) {

      //@todo move relevant functionality into sequentproofservice.js

      scope.fetchBranchRoot = function(sectionIdx) {
        let section = scope.deductionPath.sections[sectionIdx];
        let sectionEnd = section.path[section.path.length-1];
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + sectionEnd + '/branchroot').success(function(data) {
          addBranchRoot(data, scope.agenda.itemsMap[scope.nodeId], sectionIdx);
        });
      }

      scope.isProofRootVisible = function() {
        let root = scope.proofTree.nodesMap[scope.proofTree.root];
        return scope.deductionPath.sections[scope.deductionPath.sections.length - 1].path.indexOf(root.id) >= 0;
      }

      scope.showProofRoot = function() {
        let root = scope.proofTree.nodesMap[scope.proofTree.root];
        if (scope.deductionPath.sections[scope.deductionPath.sections.length - 1].path.indexOf(root.id) < 0) {
          addBranchRoot(root, scope.agenda.itemsMap[scope.nodeId], scope.deductionPath.sections.length-1);
        }
      }

      scope.fetchPathAll = function(sectionIdx) {
        let section = scope.deductionPath.sections[sectionIdx];
        sequentProofData.fetchPathAll(scope.userId, scope.proofId, scope.agenda, scope.proofTree, section);
      }

      /** Adds a proof tree node and updates the agenda sections. */
      scope.updateProof = function(agenda, proofTree, proofTreeNode) {
        sequentProofData.updateProof(agenda, proofTree, proofTreeNode);
      }

      /**
       * Adds the specified proof tree node as branch root to the specified section.
       */
      let addBranchRoot = function(proofTreeNode, agendaItem, sectionIdx) {
        scope.proofTree.addNode(proofTreeNode);
        scope.agenda.updateSection(scope.proofTree, proofTreeNode, agendaItem, sectionIdx);

        // append parent to the appropriate section in all relevant agenda items
        if (proofTreeNode.children != null) {
          let items = $.map(proofTreeNode.children, function(e) { return scope.agenda.itemsByProofStep(e); });
          $.each(items, function(i, v) {
            let childSectionIdx = scope.agenda.childSectionIndex(v.id, proofTreeNode);
            scope.agenda.updateSection(scope.proofTree, proofTreeNode, v, childSectionIdx);
          });
        }
      }

      scope.siblings = function(nodeId) {
        let node = scope.proofTree.nodesMap[nodeId];
        let parent = node ? scope.proofTree.nodesMap[node.parent] : undefined;
        return (parent ? parent.children : []).filter(function(id) { return id !== nodeId; });
      }

      /** Filters sibling candidates: removes this item's goal and path */
      scope.siblingsWithAgendaItem = function(candidates) {
        let item = scope.agenda.itemsMap[scope.nodeId];
        let fp = flatPath(item);
        return (candidates != null ? candidates.filter(function(e) { return fp.indexOf(e) < 0 && scope.agenda.itemsByProofStep(e).length > 0; }) : []);
      }

      /** Applies the tactic 'tacticId' without input at the formula 'formulaId' */
      scope.onApplyTactic = function(formulaId, tacticId) {
        scope.onTactic({formulaId: formulaId, tacticId: tacticId});
      }

      /** Applies the tactic 'tacticId' with input at the formula 'formulaId' */
      scope.onApplyInputTactic = function(formulaId, tacticId, input) {
        scope.onInputTactic({formulaId: formulaId, tacticId: tacticId, input: input});
      }

      scope.onApplyTwoPositionTactic = function(fml1Id, fml2Id, tacticId) {
        scope.onTwoPositionTactic({fml1Id: fml1Id, fml2Id: fml2Id, tacticId: tacticId});
      }

      scope.fetchParentRightClick = function(event) {
        //@note dispatch popover-trigger (see singletracksequentproof.html)
        event.target.dispatchEvent(new Event("rightClick"));
      }

      scope.proofStepRightClick = function(event) {
        //@note dispatch popover-trigger (see singletracksequentproof.html)
        event.target.dispatchEvent(new Event("rightClick"));
      }

      scope.proofStepParent = function(childId) {
        let parentId = scope.proofTree.nodesMap[childId].parent;
        return scope.proofTree.nodesMap[parentId];
      }

      scope.proofStepChildren = function(parentId) {
        return scope.proofTree.node(parentId).children;
      }

      scope.stepAxiom = function() {
        if (scope.explanationNodeId) {
          let node = scope.proofTree.node(scope.explanationNodeId)
          return [node.rule];
        } else return [];
      }

      scope.highlightStepPosition = function(nodeId, highlight) {
        scope.explanationNodeId = highlight ? nodeId : undefined;
        scope.proofTree.highlightNodeStep(nodeId, highlight);
      }

      let flatPath = function(item) {
        let result = [];
        $.each(item.deduction.sections, function(i, v) { $.merge(result, v.path); });
        return result;
      }

      /**
       * Fetches the parent of goal 'goalId' and updates the agenda item 'nodeId' to show an extended sequent
       * (parent appended as previous proof step below deduction view).
       */
      scope.fetchSectionParent = function(section) {
        let nodeId = section.path[section.path.length - 1];
        scope.fetchParent(nodeId);
      }
      scope.fetchParent = function(nodeId) {
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + nodeId + '/parent').success(function(data) {
          scope.proofTree.addNode(data);
          sequentProofData.updateProof(data);
        });
      }

      /** Prunes the proof tree and agenda/deduction path below the specified step ID. */
      scope.prune = function(nodeId) {
        sequentProofData.prune(scope.userId, scope.proofId, nodeId);
      }

      scope.justification = function(proofId, nodeId) {
        return sequentProofData.justifications.get(proofId, nodeId);
      }

      scope.rulehelp = {}
      scope.fetchJustificationHelp = function(codeName) {
        scope.rulehelp.codeName = codeName;
        // return name of the ng-template in singletracksequentproof.html
        return 'rulehelp.html';
      }

      scope.justificationNode = function(nodeId) {
        //@note cannot use index verbatim since spoonfeeding interpreter and sequential interpreter create branches in different order
        let branchId = parseInt(nodeId.split(",")[1][0], 10);
        let outer = scope.proofTree.node(nodeId).rule;
        let items = scope.justification(scope.proofId, nodeId).details.agenda.items()
        //@todo send labels with agenda items and order by labels
        if (outer.codeName === "loop") {
          branchId = branchId === 0 ? 2 : branchId === 1 ? 0 : 1;
        } else if (outer.codeName === "dI" && items.length > 1) {
          branchId = branchId === 0 ? 1 : 0;
        }
        let node = scope.agenda.itemsMap[nodeId];
        console.log("Look up by node ID returns same node: " + node === items[branchId])
        return items[branchId];
      }

      scope.stepInto = function(proofId, nodeId, event) {
        //@todo check that proof step didn't change either
        if (!sequentProofData.justifications.get(proofId, nodeId)) {
          spinnerService.show('magnifyingglassSpinner')
          if (!scope.proofTree.node(nodeId)) {
            scope.fetchSectionParent(scope.deductionPath.sections[0]);
          }
          $http.get('proofs/user/' + scope.userId + '/' + proofId + '/' + nodeId + '/expand?strict=' + (event && event.altKey)).then(function(response) {
            scope.deductionPath.isCollapsed=false;
            if (response.data.proofTree.nodes !== undefined) {
              let justification = {
                kind: 'tactic',
                visible: true,
                details: {
                  proofId: response.data.detailsProofId,
                  tactic: response.data.tactic.stepsTactic,
                  //@todo access the correct one that fits the displayed goal
                  goalSequent: response.data.goalSequents[0],
                  backendGoal: response.data.backendGoals[0],
                  proofTree: new ProofTree(),
                  agenda: new Agenda()
                }
              }
              justification.details.proofTree.nodesMap = response.data.proofTree.nodes;
              justification.details.proofTree.root = response.data.proofTree.root;
              justification.details.agenda.itemsMap = response.data.openGoals;
              $.each(response.data.proofTree.nodes, function(i, v) { makeLazyNode($http, scope.userId, proofId, v); });

              let paths = justification.details.proofTree.paths(justification.details.proofTree.rootNode());
              $.each(paths.reverse(), function(i, v) { scope.updateProof(justification.details.agenda, justification.details.proofTree, v); });

              sequentProofData.justifications.add(proofId, nodeId, justification);
            } else {
              let tacticName = response.data.tactic.parent;
              derivationInfos.byName(scope.userId, proofId, nodeId, tacticName).then(function(response) {
                let justification = {
                  kind: response.data[0].standardDerivation.derivation.type,
                  visible: true,
                  details: response.data[0]
                }
                sequentProofData.justifications.add(proofId, nodeId, justification);
              });
            }
          })
          .finally(function() {
            spinnerService.hide('magnifyingglassSpinner');
          });
        } else {
          let justification = sequentProofData.justifications.get(proofId, nodeId)
          justification.visible = !justification.visible;
          if (justification.visible) scope.deductionPath.isCollapsed=false;
        }
      }

      scope.getInnerCounterExample = function(proofId, node, additionalAssumptions) {
        let requestCanceller = $q.defer();
        let p = scope.$parent;
        // find the parent that maintains running requests
        while (p && !p.runningRequest) { p = p.$parent; }
        if (p) {
          p.runningRequest.canceller = requestCanceller;
          spinnerService.show('counterExampleSpinner');
          let nodeId = node.deduction.sections[0].path[0];
          let additional = additionalAssumptions ? additionalAssumptions : {};
          let url = 'proofs/user/' + scope.userId + '/' + proofId + '/' + nodeId + '/counterExample'
          $http.get(url, { params: { assumptions: additional }, timeout: requestCanceller.promise })
            .then(function(response) {
              let dialogSize = (response.data.result === 'cex.found') ? 'lg' : 'md';
              let modalInstance = $uibModal.open({
                templateUrl: 'templates/counterExample.html',
                controller: 'CounterExampleCtrl',
                size: dialogSize,
                resolve: {
                  result: function() { return response.data.result; },
                  assumptions: function() { return response.data.additionalAssumptions; },
                  origFormula: function() { return response.data.origFormula; },
                  cexFormula: function() { return response.data.cexFormula; },
                  cexValues: function() { return response.data.cexValues; },
                  speculatedValues: function() { return response.data.speculatedValues; }
                }
              });
              modalInstance.result.then(
                function(result) {
                  // dialog closed with request to recalculate using additional assumptions
                  scope.getInnerCounterExample(proofId, node, result);
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
      }

      /* Indicates whether the section has a parent (if its last step has a parent, and the section is not complete) */
      scope.hasParent = function(section) {
        let step = section.path[section.path.length - 1];
        return scope.proofTree.nodesMap[step].parent !== null && (!section.isComplete || section.isCollapsed);
      }

      // inner steps are readOnly, show them all
      scope.deductionPath.isCollapsed = !scope.readOnly;
      // fetch child if top node is false to show additional proof line
      scope.proofTree.node(scope.nodeId).getSequent(function(sequent) {
        let nodeIsFalse = (sequent.ante ? sequent.ante.length : 0 === 0) &&
          (sequent.succ ? sequent.succ.length : 0 === 1) && sequent.succ[0].formula.json.plain === "false";
        if (nodeIsFalse && scope.deductionPath.sections[0].path.length <= 1) scope.fetchParent(scope.nodeId);
      });


      scope.manyDigits = '|123456789'.repeat(15);
      scope.characterWidthSequent = {
        ante: [ { formula: { json: { plain: scope.manyDigits, text: scope.manyDigits }, string: scope.manyDigits } } ],
        succ: [ { formula: { json: { plain: scope.manyDigits, text: scope.manyDigits }, string: scope.manyDigits } } ]
      };

      scope.characterMeasure = sequentProofData.characterMeasure;

      // compile on demand avoids recursive template infinite loop
      let template = '<div ng-include="\'partials/singletracksequentproof.html\'"></div>';
      let $template = angular.element(template);
      $compile($template)(scope);
      element.append($template);
    }

    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            deductionPath: '=',
            proofTree: '=',
            agenda: '=',
            readOnly: '=?',
            collapsed: '=?',
            onTactic: '&',
            onInputTactic: '&',
            onTwoPositionTactic: '&'
        },
        link: link
        // do not use templateUrl (infinite loop because singletracksequentproof.html is a recursive template)
    };
  }])
  /**
   * A sequent deduction view focused on a single path through the deduction, with links to sibling goals when
   * branching occurs.
   * {{{
   *      <k4-browse-sequentproof userId="1" proofId="35" nodeId="N1"
                           deductionRoot="..." agenda="..." read-only="false"></k4-sequentproof>
   * }}}
   * @param userId          The user ID; for interaction with the server.
   * @param proofId         The current proof; for interaction with the server.
   * @param nodeId          The node (=task); for interaction with the server.
   * @param deductionPath   Identifies the path to the goal (as far as loaded); Array[goalId]
   * @param proofTree       The proof tree, see provingawesome.js for schema.
   * @param agenda          The agenda, see provingawesome.js for schema.
   */
  .directive('k4BrowseSequentproof', ['$http', '$uibModal', '$q', '$timeout', 'sequentProofData', 'spinnerService', 'derivationInfos',
      function($http, $uibModal, $q, $timeout, sequentProofData, spinnerService, derivationInfos) {
    /* The directive's internal control. */
    let link = function(scope) {
      scope.isProofRootVisible = function() {
        let root = scope.proofTree.nodesMap[scope.proofTree.root];
        return scope.deductionPath.sections[scope.deductionPath.sections.length - 1].path.indexOf(root.id) >= 0;
      }

      /**
       * Adds a proof tree node and updates the agenda sections.
       */
      let updateProof = function(proofTreeNode) {
        scope.proofTree.addNode(proofTreeNode);

        // append parent to the appropriate section in all relevant agenda items
        let items = $.map(proofTreeNode.children, function(e) { return scope.agenda.itemsByProofStep(e); }); // JQuery flat map
        $.each(items, function(i, v) {
          let childSectionIdx = scope.agenda.childSectionIndex(v.id, proofTreeNode);
          if (childSectionIdx >= 0) {
            scope.agenda.updateSection(scope.proofTree, proofTreeNode, v, childSectionIdx);
          }
        });
      }

      scope.fetchNodeChildren = function(userId, proofId, nodeId) {
        spinnerService.show('tacticExecutionSpinner')
        $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/browseChildren')
          .then(function(response) {
            //$rootScope.$broadcast('proof.message', { textStatus: "", errorThrown: "" });
            sequentProofData.updateAgendaAndTree(userId, response.data.proofId, response.data);
            //sequentProofData.tactic.fetch($scope.userId, response.data.proofId);
          })
          .finally(function() { spinnerService.hide('tacticExecutionSpinner'); });
      }

      scope.siblings = function(nodeId) {
        let node = scope.proofTree.nodesMap[nodeId];
        let parent = node ? scope.proofTree.nodesMap[node.parent] : undefined;
        return (parent ? parent.children : []).filter(function(id) { return id !== nodeId; });
      }

      /** Filters sibling candidates: removes this item's goal and path */
      scope.siblingsWithAgendaItem = function(candidates) {
        let item = scope.agenda.itemsMap[scope.nodeId];
        let fp = flatPath(item);
        return (candidates != null ? candidates.filter(function(e) { return fp.indexOf(e) < 0 && scope.agenda.itemsByProofStep(e).length > 0; }) : []);
      }

      scope.proofStepChildren = function(parentId) {
        return sequentProofData.proofTree.node(parentId).children;
      }

      scope.explainStep = function(nodeId, highlight) {
        scope.explanationNodeId = highlight ? nodeId : undefined;
      }

      scope.stepAxiom = function() {
        if (scope.explanationNodeId) {
          let node = sequentProofData.proofTree.node(scope.explanationNodeId)
          return [node.rule];
        } else return [];
      }

      scope.highlightStepPosition = function(nodeId, highlight) {
        sequentProofData.proofTree.highlightNodeStep(nodeId, highlight);
      }

      let flatPath = function(item) {
        let result = [];
        $.each(item.deduction.sections, function(i, v) { $.merge(result, v.path); });
        return result;
      }

      scope.stepInto = function(proofId, nodeId) {
        spinnerService.show('magnifyingglassSpinner')
        $http.get('proofs/user/' + scope.userId + '/' + proofId + '/' + nodeId + '/expand').then(function(response) {
          if (response.data.proofTree.nodes !== undefined) {
            $uibModal.open({
              templateUrl: 'templates/magnifyingglass.html',
              controller: 'MagnifyingGlassDialogCtrl',
              scope: scope,
              size: 'fullscreen',
              resolve: {
                proofInfo: function() {
                  return {
                    userId: scope.userId,
                    proofId: proofId,
                    nodeId: nodeId,
                    detailsProofId: response.data.detailsProofId
                  }
                },
                tactic: function() { return response.data.tactic; },
                proofTree: function() { return response.data.proofTree; },
                openGoals: function() { return response.data.openGoals; }
              }
            });
          } else {
            let tacticName = response.data.tactic.parent;
            let tactics = derivationInfos.byName(scope.userId, scope.proofId, nodeId, tacticName)
              .then(function(response) {
                return response.data;
              });

            $uibModal.open({
              templateUrl: 'templates/derivationInfoDialog.html',
              controller: 'DerivationInfoDialogCtrl',
              size: 'md',
              resolve: {
                tactics: function() { return tactics; },
                readOnly: function() { return true; },
                userId: function() { return undefined; },
                proofId: function() { return undefined; },
                nodeId: function() { return undefined; },
                defaultPositionLocator: function() { return undefined; },
                sequent: function() { return undefined; }
              }
            });
          }
        })
        .finally(function() {
          spinnerService.hide('magnifyingglassSpinner');
        });
      }
    }

    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            deductionPath: '=',
            proofTree: '=',
            agenda: '=',
            isAutoPlaying: '='
        },
        link: link,
        templateUrl: 'partials/browsesingletracksequentproof.html'
    };
  }])
  .filter('childRuleName', function () {
    return function (input, scope) {
      if (input !== undefined) {
        let node = scope.proofTree.nodesMap[input];
        if (node !== undefined) {
          let loaded = $.grep(node.children, function(e, i) { return scope.proofTree.nodeIds().indexOf(e) >= 0; });
          let rule = loaded.length > 0 ? scope.proofTree.nodesMap[loaded[0]].rule : undefined;
          return rule ? rule.name : (node.rule ? node.rule.name : undefined);
        }
      }
      return undefined;
    };
  })
  .filter('childMaker', function () {
    return function (input, scope) {
      if (input !== undefined) {
        let node = scope.proofTree.nodesMap[input];
        if (node !== undefined) {
          let loaded = $.grep(node.children, function(e, i) { return scope.proofTree.nodeIds().indexOf(e) >= 0; });
          let rule = loaded.length > 0 ? scope.proofTree.nodesMap[loaded[0]].rule : undefined;
          return rule ? rule.maker : undefined;
        }
      }
      return undefined;
    };
  })
  .filter('ruleName', function () {
    return function (input, scope) {
      if (input !== undefined) {
        let node = scope.proofTree.nodesMap[input];
        let rule = node ? node.rule : undefined;
        return rule ? rule.name : undefined;
      }
      return undefined;
    };
  })
  .filter('maker', function () {
    return function (input, scope) {
      if (input !== undefined) {
        let node = scope.proofTree.nodesMap[input];
        return node ? node.rule.maker : undefined;
      }
      return undefined;
    };
  })
  .controller('MagnifyingGlassDialogCtrl', function ($scope, $uibModalInstance, Agenda, ProofTree, proofInfo, tactic, proofTree, openGoals) {
    $scope.proofInfo = proofInfo;
    $scope.tactic = tactic;

    $scope.agenda = new Agenda();
    $scope.proofTree = new ProofTree();

    $scope.agenda.itemsMap = openGoals;
    $scope.proofTree.nodesMap = proofTree.nodes;
    $scope.proofTree.root = proofTree.root;
    if ($scope.agenda.items().length > 0) {
      // select first task if nothing is selected yet
      if ($scope.agenda.selectedId() === undefined) $scope.agenda.select($scope.agenda.items()[0]);
    }

    let updateProof = function(proofTreeNode) {
      let items = $.map(proofTreeNode.children, function(e) { return $scope.agenda.itemsByProofStep(e); }); // JQuery flat map
      $.each(items, function(i, v) {
        let childSectionIdx = $scope.agenda.childSectionIndex(v.id, proofTreeNode);
        if (childSectionIdx >= 0) {
          $scope.agenda.updateSection($scope.proofTree, proofTreeNode, v, childSectionIdx);
        }
      });
    }

    let paths = $scope.proofTree.paths($scope.proofTree.rootNode());

    $.each(paths.reverse(), function(i, v) { updateProof(v); });
    //$.each(paths, function(i, v) { $.each(v.reverse, function(ii, vv) { updateProof(vv); });  });

    $scope.close = function () { $uibModalInstance.close(); };
  });
