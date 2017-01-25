angular.module('keymaerax.services').factory('Agenda', function() {
  var agenda = function() {
    return {
       itemsMap: {},           // { id: { id: String, name: String, isSelected: Bool, path: [ref PTNode] } }, ... }
       selectedId: function() {
         var selected = $.grep(this.items(), function(e, i) { return e.isSelected; });
         if (selected !== undefined && selected.length > 0) return selected[0].id;
         else return undefined;
       },
       itemIds: function() { return Object.keys(this.itemsMap); },
       items: function() {
         return $.map(this.itemsMap, function(v) {return v;});
       },
       select: function(item) {
         //@note bootstrap tab directive sends a select on remove -> only change selection if the item is still on the agenda
         if (this.itemsMap[item.id] !== undefined) {
           $.each(this.items(), function(i, e) { e.isSelected = false; });
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
       /** Returns the index of the section where any proofTreeNode's child is last (child is unique). */
       childSectionIndex: function(itemId, proofTreeNode) {
         var agendaItem = this.itemsMap[itemId];
         for (var i = 0; i < agendaItem.deduction.sections.length; i++) {
           var section = agendaItem.deduction.sections[i];
           if (proofTreeNode.children.indexOf(section.path[section.path.length - 1]) >= 0) return i;
         }
         return -1;
       },

       /**
        * Updates the specified section by adding the proof tree node. If the node has more than 1 child, a new section
        * after the specified section is started.
        * @param proofTreeNode The node to add.
        * @param sectionIdx The section where to add the proof node.
        */
       updateSection: function(proofTree, proofTreeNode, agendaItem, sectionIdx) {
         // only update if node not added previously
         if (sectionIdx+1 >= agendaItem.deduction.sections.length || agendaItem.deduction.sections[sectionIdx+1].path.indexOf(proofTreeNode.id) < 0) {
           var section = agendaItem.deduction.sections[sectionIdx];
           var sectionEnd = section.path[section.path.length-1];
           if (proofTreeNode.children != null && proofTreeNode.children.length > 1) {
             if (sectionIdx+1 >= agendaItem.deduction.sections.length || agendaItem.deduction.sections[sectionIdx+1].path[0] !== null) {
               // start new section with parent, parent section is complete if parent is root
               agendaItem.deduction.sections.splice(sectionIdx+1, 0, {path: [proofTreeNode.id], isCollapsed: false, isComplete: proofTreeNode.parent === null});
             } // else: parent already has its own section, see fetchBranchRoot
             // in any case: child's section is loaded completely if it's ending in one of the children of the proof tree node
             section.isComplete = proofTreeNode.children.indexOf(sectionEnd) >= 0;
           } else {
             // parent has exactly 1 child, append parent to child's section
             if (sectionIdx === -1) {
               //@todo client error message
//               showClientErrorMessage($uibModal, 'Expected a unique path section ending in a child of ' + proofTreeNode.id + ', but agenda item ' + agendaItem.id +
//                 ' has ' + agendaItem.sections + ' as path sections');
             } else if (proofTreeNode.parent !== null) {
               section.path.push(proofTreeNode.id);
               var parentCandidate =
                 (sectionIdx+1 < agendaItem.deduction.sections.length
                 ? proofTree.nodesMap[agendaItem.deduction.sections[sectionIdx+1].path[0]]
                 : undefined);
               section.isComplete =
                 parentCandidate !== undefined && parentCandidate.children != null && parentCandidate.children.indexOf(proofTreeNode.id) >= 0;
             } else {
               if (sectionIdx+1 < agendaItem.deduction.sections.length) {
                //@todo client error message
//                 showClientErrorMessage($uibModal, 'Received proof tree root, which can only be added to last section, but ' + sectionIdx +
//                   ' is not last section in ' + agendaItem.deduction.sections);
               } else {
                 agendaItem.deduction.sections.splice(sectionIdx+1, 0, {path: [proofTreeNode.id], isCollapsed: false, isComplete: true});
                 section.isComplete = proofTreeNode.children != null && proofTreeNode.children.indexOf(sectionEnd) >= 0;
               }
             }
           }
         }
       }
     }
  }
  return agenda;
});

angular.module('keymaerax.services').factory('ProofTree', function() {
  var proofTree = function() {
    return {
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
        },
        rootNode: function() { return this.nodesMap[this.root]; },
        node: function(nodeId) { return this.nodesMap[nodeId]; },

        paths: function(node) {
          //@todo what if we have a branching tree?
          var that = this; //@note $.map rescopes this
          if (node.children !== undefined && node.children.length > 0) {
            return $.map(node.children, function(v, i) {
              var childrenPaths = that.paths(that.node(v));
              childrenPaths.unshift(node); //@note unshift prepends in place and returns new length
              return childrenPaths;
            });
          } else return [node];
        }
      }
  }
  return proofTree;
});

angular.module('keymaerax.services').factory('sequentProofData', ['$http', '$rootScope', 'spinnerService', 'Agenda', 'ProofTree', function($http, $rootScope, spinnerService, Agenda, ProofTree) {
  return {
    /** The agenda model */
    agenda: new Agenda(),

    /** The proofTree model */
    proofTree: new ProofTree(),

    /** The tactic model */
    tactic: {
      tacticText: "",
      lastExecutedTacticText: "",
      currentSuggestions: undefined,
      tacticDiff: "",
      tacticDel: "",

      fetch: function(userId, proofId) {
        var theTactic = this;
        $http.get('proofs/user/' + userId + '/' + proofId + '/extract').then(function (response) {
          theTactic.tacticText = response.data.tacticText;
          theTactic.lastExecutedTacticText = theTactic.tacticText;
          theTactic.tacticDiff = "";
          theTactic.tacticDel = "";
        });
      },

      reset: function() {
        this.tacticText = "";
        this.lastExecutedTacticText = "";
        this.tacticDiff = "";
        this.tacticDel = "";
        this.currentSuggestions = undefined;
      }
    },

    formulas: {
      highlighted: undefined
    },

    /** Prunes the proof tree at the specified goal, executes onPruned when the tree is pruned */
    prune: function(userId, proofId, nodeId, onPruned) {
      //@note make model available in closure of function success
      var theProofTree = this.proofTree;
      var theAgenda = this.agenda;
      var theTactic = this.tactic;

      $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/pruneBelow').then(function(response) {
        // prune proof tree
        theProofTree.pruneBelow(nodeId);

        // update agenda: prune deduction paths
        var agendaItems = theAgenda.itemsByProofStep(nodeId);
        $.each(agendaItems, function(i, item) {
          var deductionIdx = theAgenda.deductionIndexOf(item.id, nodeId);
          var section = item.deduction.sections[deductionIdx.sectionIdx];
          section.path.splice(0, deductionIdx.pathStepIdx);
          item.deduction.sections.splice(0, deductionIdx.sectionIdx);
        });

        // sanity check: all agendaItems should have the same deductions (top item should be data.agendaItem.deduction)
        var newTop = response.data.agendaItem.deduction.sections[0].path[0];
        $.each(agendaItems, function(i, item) {
          var oldTop = item.deduction.sections[0].path[0];
          if (oldTop !== newTop) {
            console.log("Unexpected deduction start after pruning: expected " + newTop + " but have " + oldTop +
              " at agenda item " + item.id)
          }
          //@todo additionally check that deduction.sections are all the same (might be expensive, though)
        });

        // update agenda: copy already cached deduction path into the remaining agenda item (new top item)
        response.data.agendaItem.deduction = agendaItems[0].deduction;
        theAgenda.itemsMap[response.data.agendaItem.id] = response.data.agendaItem;

        // delete previous items
        //@todo preserve previous tab order
        $.each(agendaItems, function(i, item) {
          delete theAgenda.itemsMap[item.id];
        });

        // select new top item (@todo does not work with step back)
        theAgenda.select(response.data.agendaItem);

        // refresh tactic
        theTactic.fetch(userId, proofId);
      }).then(onPruned);
    },

    /** Fetches the agenda from the server */
    fetchAgenda: function(scope, userId, proofId) {
      var theProofTree = this.proofTree;
      var theAgenda = this.agenda;
      spinnerService.show('proofLoadingSpinner');
      this.tactic.fetch(userId, proofId);
      $http.get('proofs/user/' + userId + "/" + proofId + '/agendaawesome')
        .then(function(response) {
          theAgenda.itemsMap = response.data.agendaItems;
          theProofTree.nodesMap = response.data.proofTree.nodes;
          theProofTree.root = response.data.proofTree.root;
          if (theAgenda.items().length > 0) {
            // select first task if nothing is selected yet
            if (theAgenda.selectedId() === undefined) theAgenda.items()[0].isSelected = true;
          } else {
            // proof might be finished
            if(!theAgenda.proofStatusDisplayed) {
              theAgenda.proofStatusDisplayed == true
              $rootScope.$broadcast('agenda.isEmpty', {proofId: proofId});
              console.log("Emiting angeda.isEmpty from sequentproofservice.js 1");
            }
            else {
              console.log("Not showing agenda.isEmpty because it was already displayed.")
            }
          }
        })
        .catch(function(data) {
          $rootScope.$broadcast('agenda.loadError'); // TODO somewhere: open modal dialog and ask if proof should be loaded

        })
        .finally(function() { spinnerService.hide('proofLoadingSpinner'); });
    },

    /** Updates the agenda and the proof tree with new items resulting from a tactic */
    updateAgendaAndTree: function(proofId, proofUpdate) {
      if (proofUpdate.progress) {
        var theProofTree = this.proofTree;
        var theAgenda = this.agenda;
        var oldAgendaItem = theAgenda.itemsMap[proofUpdate.parent.id];
        $.each(proofUpdate.newNodes, function(i, node) {
          // update tree
          theProofTree.nodesMap[node.id] = node;
          var parent = theProofTree.nodesMap[node.parent]
          if (parent.children === undefined || parent.children === null) parent.children = [node.id];
          else parent.children.push(node.id);
          // update agenda: prepend new open goal to deduction path
          var newAgendaItem = {
            id: node.id,
            name: oldAgendaItem.name,                               // inherit name from old
            isSelected: i === 0 ? oldAgendaItem.isSelected : false, // first new item inherits selection from old
            deduction: $.extend(true, {}, oldAgendaItem.deduction)  // object deep copy
          }
          newAgendaItem.deduction.sections[0].path.unshift(node.id);
          theAgenda.itemsMap[newAgendaItem.id] = newAgendaItem;
        });
        delete theAgenda.itemsMap[oldAgendaItem.id];
        if (theAgenda.itemIds().length == 0 && !theAgenda.proofStatusDisplayed) {
          theAgenda.proofStatusDisplayed == true
          console.log("Emiting angeda.isEmpty from sequentproofservice.js 1");
          $rootScope.$broadcast('agenda.isEmpty', {proofId: proofId});
        }
        if(theAgenda.proofStatusDisplayed == true) {
          console.log("Not emitting agenda.isEmpty because it's already been emitted.")
        }
      } else {
        $rootScope.$broadcast('agenda.updateWithoutProgress');
      }
    }
  }
}]);
