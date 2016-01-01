angular.module('keymaerax.services').factory('sequentProofData', ['$http', '$rootScope', function($http, $rootScope) {
  return {
    /** The agenda model */
    agenda: {
      itemsMap: {},           // { id: { id: String, name: String, isSelected: Bool, path: [ref PTNode] } }, ... }
      selectedId: undefined,  // ref Item
      itemIds: function() { return Object.keys(this.itemsMap); },
      items: function() {
        return $.map(this.itemsMap, function(v) {return v;});
      },
      select: function(item) {
        //@note bootstrap tab directive sends a select on remove -> only change selection if the item is still on the agenda
        if (this.itemsMap[item.id] !== undefined) {
          if (this.selectedId !== undefined && this.itemsMap[this.selectedId] !== undefined) {
            this.itemsMap[this.selectedId].isSelected = false;
          }
          this.selectedId = item.id;
          item.isSelected = true;
        }
      },
      selectById: function(itemId) { this.select(this.itemsMap[itemId]); },
      itemsByProofStep: function(ptNodeId) {
        return $.grep(this.items(), function(e) {
          return $.grep(e.deduction.sections, function(v, i) { return v.path.indexOf(ptNodeId) >= 0; }).length > 0; });
      },
      /** Returns the deduction index of the specified proof tree node in agendaItem (Object { section, pathStep} ). */
      deductionIndexOf: function(itemId, ptNodeId) {
        var agendaItem = this.itemsMap[itemId];
        for (var i = 0; i < agendaItem.deduction.sections.length; i++) {
          var section = agendaItem.deduction.sections[i];
          var j = section.path.indexOf(ptNodeId);
          if (j >= 0) return { sectionIdx: i, pathStepIdx: j };
        }
        return { sectionIdx: -1, pathStepIdx: -1 };
      },
      /** Returns the section index of the specified proof tree node's child that is referred to in the agenda item (child is unique). */
      childSectionIndex: function(itemId, proofTreeNode) {
        var agendaItem = this.itemsMap[itemId];
        for (var i = 0; i < agendaItem.deduction.sections.length; i++) {
          var section = agendaItem.deduction.sections[i];
          if (proofTreeNode.children.indexOf(section.path[section.path.length - 1]) >= 0) return i;
        }
        return -1;
      }
    },

    /** The proofTree model */
    proofTree: {
      root: undefined, // ref PTNode, i.e., String
      nodesMap: {}, // Map[String, PTNode], i.e., { id: { id: String, children: [ref PTNode], parent: ref PTNode } }
      nodeIds: function() { return Object.keys(this.nodesMap); },
      nodes: function() { return $.map(this.nodesMap, function(v) {return v;}); },

      /** Prunes below the specified node */
      pruneBelow: function(nodeId) {
        var theProofTree = this;
        var node = theProofTree.nodesMap[nodeId];
        if (node.children.length > 0) {
          $.each(node.children, function(i, c) {
            theProofTree.pruneBelow(c);
            delete theProofTree.nodesMap[c];
          });
          node.children.splice(0, node.children.length);
        }
      },
      /** Adds a node to this tree if not already present; otherwise, updates the node with fetched rule and children */
      addNode: function(node) {
        if (this.nodesMap[node.id] === undefined) {
          this.nodesMap[node.id] = node;
        } else {
          this.nodesMap[node.id].children = node.children;
          this.nodesMap[node.id].rule = node.rule;
        }
      }
    },

    /** Prunes the proof tree at the specified goal */
    prune: function(userId, proofId, nodeId, goalId) {
      //@note make model available in closure of function success
      var theProofTree = this.proofTree;
      var theAgenda = this.agenda;
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/' + goalId + '/pruneBelow').success(function(data) {
        // prune proof tree
        theProofTree.pruneBelow(goalId);

        // update agenda: prune deduction paths
        var agendaItems = theAgenda.itemsByProofStep(goalId);
        $.each(agendaItems, function(i, item) {
          var deductionIdx = theAgenda.deductionIndexOf(item.id, goalId);
          var section = item.deduction.sections[deductionIdx.sectionIdx];
          section.path.splice(0, deductionIdx.pathStepIdx);
          item.deduction.sections.splice(0, deductionIdx.sectionIdx);
        });

        // sanity check: all agendaItems should have the same deductions (top item should be data.agendaItem.deduction)
        var newTop = data.agendaItem.deduction.sections[0].path[0];
        $.each(agendaItems, function(i, item) {
          var oldTop = item.deduction.sections[0].path[0];
          if (oldTop !== newTop) {
            console.log("Unexpected deduction start after pruning: expected " + newTop + " but have " + oldTop +
              " at agenda item " + item.id)
          }
          //@todo additionally check that deduction.sections are all the same (might be expensive, though)
        });

        // update agenda: copy already cached deduction path into the remaining agenda item (new top item)
        data.agendaItem.deduction = agendaItems[0].deduction;
        theAgenda.itemsMap[data.agendaItem.id] = data.agendaItem;

        // delete previous items
        //@todo preserve previous tab order
        $.each(agendaItems, function(i, item) {
          delete theAgenda.itemsMap[item.id];
        });

        // select new top item (@todo does not work with step back)
        theAgenda.select(data.agendaItem);
      });
    },

    /** Fetches the agenda from the server */
    fetchAgenda: function(scope, userId, proofId) {
      var theProofTree = this.proofTree;
      var theAgenda = this.agenda;
      $http.get('proofs/user/' + userId + "/" + proofId + '/agendaawesome').success(function(data) {
        theAgenda.itemsMap = data.agendaItems;
        theProofTree.nodesMap = data.proofTree.nodes;
        theProofTree.root = data.proofTree.root;
        if (theAgenda.items().length > 0) {
          // select first task if nothing is selected yet
          if (theAgenda.selectedId === undefined) theAgenda.select(theAgenda.items()[0]);
        } else {
          // proof might be finished
          scope.$emit('agendaIsEmpty');
        }
      }).error(function(data) {
        if (data.status == 'notloaded') {
          scope.$emit('proofIsNotLoaded'); // TODO somewhere: open modal dialog and ask if proof should be loaded
        } else if (data.status == 'loading') {
          scope.proofIsLoading = $q.defer()
          scope.proofIsLoading.promise.then(function() {
            // TODO proof is now loaded, fetch tree and tasks
          })
        }
      });
    },

    /** Updates the agenda and the proof tree with new items resulting from a tactic */
    updateAgendaAndTree: function(proofUpdate) {
      var theProofTree = this.proofTree;
      var theAgenda = this.agenda;
      var oldAgendaItem = theAgenda.itemsMap[proofUpdate.parent.id];
      $.each(proofUpdate.newNodes, function(i, node) {
        // update tree
        theProofTree.nodesMap[node.id] = node;
        var parent = theProofTree.nodesMap[node.parent]
        if (parent.children === undefined || parent.children === null) parent.children = [node.id];
        else parent.children.push(node.id);
        parent.rule = node.byRule;
        // update agenda: prepend new open goal to deduction path
        var newAgendaItem = {
          id: node.id,
          name: oldAgendaItem.name + " " + i,              // inherit name from old, append child index
          deduction: $.extend(true, {}, oldAgendaItem.deduction), // object deep copy
          isSelected: i === 0 ? oldAgendaItem.isSelected : false  // first new item inherits selection from old
        }
        newAgendaItem.deduction.sections[0].path.unshift(node.id);
        theAgenda.itemsMap[newAgendaItem.id] = newAgendaItem;
      });
      delete theAgenda.itemsMap[oldAgendaItem.id];
      if (proofUpdate.newNodes.length == 0) $rootScope.$emit('agendaIsEmpty');
    }
  }
}]);
