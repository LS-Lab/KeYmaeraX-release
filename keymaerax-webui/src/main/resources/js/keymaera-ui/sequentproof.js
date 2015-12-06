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

      scope.fetchBranchRoot = function(goalId) {
      }

      scope.fetchTreeRoot = function(goalId) {
        // nothing to do here, already have tree root
      }

      scope.fetchPathAll = function(goalId) {
        // TODO adapt to sections
        var item = scope.agenda.itemsMap[scope.nodeId];
        if (item.path[item.path.length-1].id !== scope.proofTree.root) {
          $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + goalId + '/pathall').success(function(data) {
            // TODO use numParentsUntilComplete to display some information
            $.each(data.path, function(i, ptnode) { ptnode.isCollapsed = false; });
            $.each(data.path, function(i, ptnode) { addProofTreeNode(ptnode); });
          });
        } else {
          $.each(item.path, function(i, v) { v.isCollapsed = false; });
        }
      }

      /**
       * Adds a proof tree node and updates the agenda sections.
       */
      addProofTreeNode = function(proofTreeNode) {
        // add node to proof tree if not already present; otherwise, update node with fetched rule and children
        if (scope.proofTree.nodesMap[proofTreeNode.id] === undefined) {
          scope.proofTree.nodesMap[proofTreeNode.id] = proofTreeNode;
        } else {
          scope.proofTree.nodesMap[proofTreeNode.id].children = proofTreeNode.children;
          scope.proofTree.nodesMap[proofTreeNode.id].rule = proofTreeNode.rule;
        }
        // update parent pointer of children
        $.each(proofTreeNode.children, function(i, v) { scope.proofTree.nodesMap[v].parent = proofTreeNode.id; });

        // append parent at the end of the deduction path of all relevant agenda items
        var items = $.map(proofTreeNode.children, function(e) { return scope.agenda.itemsByProofStep(e); }); // JQuery flat map
        $.each(items, function(i, v) {
          var childSectionIdx = childSectionIndex(v, proofTreeNode);
          if (proofTreeNode.children.length > 1) {
            if (childSectionIdx+1 >= v.deduction.sections.length || v.deduction.sections[childSectionIdx+1].path[0] !== proofTreeNode.id) {
              // start new section with parent, parent section is complete if parent is root
              v.deduction.sections.splice(childSectionIdx+1, 0, {path: [proofTreeNode.id], isCollapsed: false, isComplete: proofTreeNode.parent === proofTreeNode.id});
            } // else: parent already has its own section, see fetchBranchRoot
            // in any case: child's section is now loaded completely
            v.deduction.sections[childSectionIdx].isComplete = true;
          } else {
            // parent has exactly 1 child, append parent to child's section
            if (childSectionIdx === -1) {
              console.error('Expected a unique path section ending in a child of ' + proofTreeNode.id + ', but agenda item ' + v.id +
                ' has ' + v.path + ' as path sections');
            } else {
              v.deduction.sections[childSectionIdx].path.push(proofTreeNode.id);
              v.deduction.sections[childSectionIdx].isComplete = proofTreeNode.parent === proofTreeNode.id;
            }
          }
        });
      }

      /**
       *  Returns the index of the specified proof tree node's child that is referred to in agendaItem (only a unique
       *  such child exists).
       */
      childSectionIndex = function(agendaItem, proofTreeNode) {
        for (var i = 0; i < agendaItem.deduction.sections.length; i++) {
          var section = agendaItem.deduction.sections[i];
          if (proofTreeNode.children.indexOf(section.path[section.path.length - 1]) >= 0) return i;
        }
        return -1;
      }

      /** Pretty prints sequent JSON into HTML */
      scope.tooltip = function(sequent) {
        // TODO call the pretty printer
        return sequent;
      }

      /** Filters sibling candidates: removes this item's goal and path */
      scope.siblingCandidates = function(candidates) {
        var item = scope.agenda.itemsMap[scope.nodeId];
        var fp = flatPath(item);
        return candidates.filter(function(e) { return fp.indexOf(e) === -1; });
      }

      scope.onUseAt = function(formulaId, axiomId) {
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + scope.deductionPath.sections[0].path[0] + '/' + formulaId + '/use/' + axiomId).success(function(data) {
          scope.proofTree.nodesMap[data.id] = data;
          scope.proofTree.nodesMap[data.parent].children = [data.id];
          scope.proofTree.nodesMap[data.parent].rule = data.byRule;
          // prepend new open goal to deduction path
          scope.agenda.itemsMap[scope.nodeId].deduction.sections[0].path.unshift(data.id);
        });
      }

      scope.fetchParentRightClick = function(event) {
        event.stopPropagation();
        // emulate hoverable popover (to come in later ui-bootstrap version) with hide on blur (need to focus for blur)
        event.target.focus();
      }

      flatPath = function(item) {
        var result = [];
        $.each(item.deduction.sections, function(i, v) { $.merge(result, v.path); });
        return result;
      }

      /**
       * Fetches the parent of goal 'goalId' and updates the agenda item 'nodeId' to show an extended sequent
       * (parent appended as previous proof step below deduction view).
       */
      scope.fetchSectionParent = function(section) {
        var goalId = section.path[section.path.length - 1];
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + goalId + '/parent').success(function(data) {
          addProofTreeNode(data);
        });
      }

      scope.deductionPath.sections = $.map(scope.deductionPath.sections, function(v, i) { return {path: v, isCollapsed: false}; });
      scope.deductionPath.isCollapsed = false;
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