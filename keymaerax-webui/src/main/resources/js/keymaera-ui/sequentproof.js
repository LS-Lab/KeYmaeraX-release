angular.module('sequentproof', ['ngSanitize','sequent','formula'])
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
  .directive('k4Sequentproof', ['$http', function($http) {
    /* The directive's internal control. */
    function link(scope, element, attrs) {
      /**
       * Fetches the parent of goal 'goalId' and updates the agenda item 'nodeId' to show an extended sequent
       * (parent appended as previous proof step below deduction view).
       */
      scope.fetchParent = function(goalId) {
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + goalId + '/parent').success(function(data) {
          addProofTreeNode(data);
        });
      }

      scope.fetchBranchRoot = function(goalId) {
      }

      scope.fetchTreeRoot = function(goalId) {
        // nothing to do here, already have tree root
      }

      scope.fetchPathAll = function(goalId) {
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + goalId + '/pathall').success(function(data) {
          // TODO use numParentsUntilComplete to display some information
          $.each(data.path, function(i, ptnode) { addProofTreeNode(ptnode); });
        });
      }

      addProofTreeNode = function(proofTreeNode) {
        // add node to proof tree if not already present; otherwise, update node with fetched rule and children
        if (scope.proofTree.nodesMap[proofTreeNode.id] === undefined) {
          scope.proofTree.nodesMap[proofTreeNode.id] = proofTreeNode;
        } else {
          scope.proofTree.nodesMap[proofTreeNode.id].children = proofTreeNode.children;
          scope.proofTree.nodesMap[proofTreeNode.id].rule = proofTreeNode.rule;
        }

        // append parent at the end of the deduction path of all relevant agenda items
        var items = $.map(proofTreeNode.children, function(e) { return scope.agenda.itemsByProofStep(e); }); // JQuery flat map
        $.each(items, function(i, v) {
          if (proofTreeNode.children.indexOf(v.path[v.path.length - 1].id) < 0) {
            console.error('Expected last path element to be a child of ' + proofTreeNode.id + ', but agenda item ' + v.id +
              ' has ' + v.path[v.path.length - 1].id + ' as last path element');
          } else v.path.push({id: proofTreeNode.id, isCollapsed: false}); });
      }

      /** Pretty prints sequent JSON into HTML */
      scope.tooltip = function(sequent) {
        // TODO call the pretty printer
        return sequent;
      }

      /** Filters sibling candidates: removes this item's goal and path */
      scope.siblingCandidates = function(candidates) {
        var item = scope.agenda.itemsMap[scope.nodeId];
        return candidates.filter(function(e) {
          return $.grep(item.path, function(pe, i) { return pe.id === e; }).length <= 0;
        });
      }

      scope.onUseAt = function(formulaId, axiomId) {
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + scope.deductionPath[0].id + '/' + formulaId + '/use/' + axiomId).success(function(data) {
          scope.proofTree.nodesMap[data.id] = data;
          scope.proofTree.nodesMap[data.parent].children = [data.id];
          scope.proofTree.nodesMap[data.parent].rule = data.byRule;
          // prepend new open goal to deduction path
          scope.agenda.itemsMap[scope.nodeId].path.unshift({id: data.id, isCollapsed: false});
        });
      }

      scope.isConclusionCollapsed = function(conclusionIdx) {
        // a conclusion is collapsed, if it is itself collapsed or if any of its children is collapsed
        // first element in deduction path is goal
        for (var i = 1; i < conclusionIdx+2; i++) {
          if (scope.deductionPath[i].isCollapsed) return true;
        }
        return false;
      }
      scope.setConclusionCollapsed = function(conclusionIdx, collapsed) {
        scope.deductionPath[conclusionIdx+1].isCollapsed = collapsed;
      }
      scope.minCollapsedIndex = function() {
        // there is no fast JQuery implementation for this
        for (var i = 1; i < scope.deductionPath.length; i++) {
          if (scope.deductionPath[i].isCollapsed) return i-1;
        }
        return scope.deductionPath.length-1;
      }

      scope.fetchParentRightClick = function(event) {
        event.stopPropagation();
        // emulate hoverable popover (to come in later ui-bootstrap version) with hide on blur (need to focus for blur)
        event.target.focus();
      }

      scope.deductionPath = $.map(scope.deductionPath, function(v, i) { return {id: v, isCollapsed: false}; });
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
            readOnly: '=?'
        },
        link: link,
        templateUrl: 'partials/singletracksequentproof.html'
    };
  }]);