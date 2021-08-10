/** Makes a node that fetches its sequent lazily */
makeLazyNode = function(http, userId, proofId, node) {
  if (node.sequent) {
    node.sequent.ante.forEach(function(f, i) { f.use = true; });
    node.sequent.succ.forEach(function(f, i) { f.use = true; });
  }

  /** Returns a sequent object that may be filled in later. Use callback to wait for a filled sequent. */
  node.getSequent = function(callback) {
    var theNode = node;
    if (theNode.sequent) {
      if (callback) callback(theNode.sequent);
      return theNode.sequent;
    } else {
      theNode.sequent = {};
      http.get('proofs/user/' + userId + '/' + proofId + '/' + theNode.id + '/sequent').then(function(response) {
        if (response.data.sequent != undefined) {
          theNode.sequent.ante = response.data.sequent.ante;
          theNode.sequent.succ = response.data.sequent.succ;
          theNode.sequent.ante.forEach(function(f, i) { f.use = true; });
          theNode.sequent.succ.forEach(function(f, i) { f.use = true; });
        } else {
          theNode.sequent.ante = [];
          theNode.sequent.succ = [];
        }
        if (callback) callback(theNode.sequent);
      });
      return theNode.sequent;
    }
  };
  return node;
}

angular.module('keymaerax.services').factory('Agenda', function() {
  var agenda = function() {
    return {
       itemsMap: {},           // { id: { id: String, name: String, isSelected: Bool, path: [ref PTNode] } }, ... }
       selectedTab: "()",
       clear: function() {
         this.itemsMap = {};
         this.selectedTab = "()";
       },
       selectedId: function() {
         var selected = $.grep(this.items(), function(e, i) { return e.isSelected; });
         if (selected !== undefined && selected.length > 0) return selected[0].id;
         else return undefined;
       },
       itemIds: function() { return Object.keys(this.itemsMap); },
       contains: function(id) { return $.grep(this.itemIds(), function(v) { return v === id; }).length > 0; },
       items: function() {
         //@HACK set selectedTab here because angular bootstrap v2.5.0 screws up active=selectedTab when tabs are removed
         var selected = this.selectedItem();
         if (selected !== undefined) this.selectedTab = selected.id;
         return $.map(this.itemsMap, function(v) {return v;});
       },
       selectedItem: function() {
         var theItems = $.map(this.itemsMap, function(v) {return v;});
         var selected = $.grep(theItems, function(e, i) { return e.isSelected; });
         return selected !== undefined && selected.length > 0 ? selected[0] : undefined;
       },
       deselect: function(item) { /* do not deselect item, otherwise agenda name textbox won't show */ },
       select: function(item) {
         $.each(this.items(), function(i, e) { e.isSelected = false; });
         if (item) {
           item.isSelected = true;
           this.selectedTab.tabId = item.id;
         } else {
           // select last item
           var items = this.items();
           if (items.length > 0) {
             var lastItem = items[items.length-1];
             lastItem.isSelected = true;
             this.selectedTab.tabId = lastItem.id;
           } else {
             this.selectedTab.tabId = undefined;
           }
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
       childSectionIndex: function(itemId, proofTreeNode) { return 0; },

       /**
        * Updates the specified section by adding the proof tree node. If the node has more than 1 child, a new section
        * after the specified section is started.
        * @param proofTreeNode The node to add.
        * @param sectionIdx The section where to add the proof node.
        */
       updateSection: function(proofTree, proofTreeNode, agendaItem, sectionIdx) {
         var section = agendaItem.deduction.sections[sectionIdx];
         if (section.path.indexOf(proofTreeNode.id) < 0) {
           proofTreeNode.getSequent = function() { return proofTreeNode.sequent; };
           section.path.push(proofTreeNode.id);
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
        isProved: false,

        clear: function() {
          this.root = undefined;
          this.nodesMap = {};
        },

        /** Prunes below the specified node */
        pruneBelow: function(nodeId) {
          var theProofTree = this;
          var node = theProofTree.nodesMap[nodeId];
          //@note child nodes may not be loaded yet (if pruning below root and proof was reloaded)
          if (node && node.children.length > 0) {
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
        /** Returns the proof tree root. */
        rootNode: function() { return this.nodesMap[this.root]; },
        /** Returns the node `nodeId`. */
        node: function(nodeId) { return this.nodesMap[nodeId]; },
        /** Converts the server-issued `nodeId` into an ID suitable for HTML id=... */
        htmlNodeId: function(nodeId) { return nodeId.replace(/\(|\)/g, "").replace(/,/g, "-"); },
        /** Highlights the operator where the step that created sequent/node `nodeId` was applied. */
        highlightNodeStep: function(nodeId, highlight) {
          // branching tactic: tree may include other child
          var nodeIdHead = nodeId.split(",")[0];
          var node = undefined;
          for (i = 0; i<3 && !node; i++) {
            node = this.node(nodeIdHead + "," + i + ")");
          }
          if (node) {
            node.isHighlighted = highlight;
            //@todo calculate position for search 'L, 'Llast, etc.
            var pos = node.rule.pos.replace(/\./g, "\\,");
            var element = $("#seq_" + this.htmlNodeId(node.parent) + " #fml_" + pos);
            if (highlight) {
              if (node.rule.asciiName == "WL" || node.rule.asciiName == "WR") element.addClass("k4-highlight-steppos-full");
              else element.addClass("k4-highlight-steppos");
              if (element.text().startsWith("[") || element.text().startsWith("<")) {
                if (node.rule.asciiName == "[]^" || node.rule.asciiName == "<>|") element.addClass("k4-highlight-steppos-modality-post");
                else element.addClass("k4-highlight-steppos-modality-prg");
              }
            } else element.removeClass("k4-highlight-steppos k4-highlight-steppos-full k4-highlight-steppos-modality-prg k4-highlight-steppos-modality-post");
          }
        },
        highlightedNode: function() {
          var theNodes = $.map(this.nodesMap, function(v) {return v;});
          var highlighted = $.grep(theNodes, function(e, i) { return e.isHighlighted; });
          return highlighted !== undefined && highlighted.length > 0 ? highlighted[0] : undefined;
        },

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
      nodesByLocation: undefined,
      snapshot: undefined,
      verbose: true,

      fetch: function(userId, proofId) {
        var theTactic = this;
        theTactic.synced = false;
        $http.get('proofs/user/' + userId + '/' + proofId + '/extract/' + (theTactic.verbose ? "verbose" : "succinct")).then(function (response) {
          theTactic.snapshot = response.data.tacticText;
          theTactic.tacticText = response.data.tacticText;
          theTactic.nodesByLocation = response.data.nodesByLocation;
        })
        .catch(function(data) {
          $rootScope.$broadcast('tactic.extractError', userId, proofId);
        });
      },

      nodeIdAtLoc: function(line, column) {
        var nodesAtLoc = $.grep(this.nodesByLocation, function(v) {
          return v.loc.line <= line && line <= v.loc.endLine && v.loc.column <= column && column <= v.loc.endColumn;
        });
        return nodesAtLoc.length > 0 ? nodesAtLoc[0].node : undefined;
      },

      locOfNode: function(node) {
        var nodeInfo = $.grep(this.nodesByLocation, function(v) { return v.node === node; });
        return nodeInfo.length > 0 ? nodeInfo[0].loc : undefined;
      },

      reset: function() {
        this.tacticText = "";
        this.snapshot = undefined;
      }
    },

    formulas: {
      highlighted: undefined,
      selectedIn: function(sequent) {
        return sequent.ante.filter(function(f) { return f.use; }).map(function(f) { return f.formula.json.plain; }).
        concat(sequent.succ.filter(function(f) { return f.use; }).map(function(f) { return f.formula.json.plain; }));
      },
      selectedIndicesIn: function(sequent) {
        return sequent.ante.filter(function(f) { return f.use; }).map(function(f) { return f.id; }).
        concat(sequent.succ.filter(function(f) { return f.use; }).map(function(f) { return f.id; }));
      },
      mode: 'prove',
      stickyEdit: false
    },

    characterMeasure: {
      show: false
    },

    justifications: {
      justificationsMap: {},           // { proofId: { nodeId: { ... } } }
      add: function(proofId, nodeId, justification) {
        if (!this.justificationsMap[proofId]) {
          this.justificationsMap[proofId] = {};
        }
        this.justificationsMap[proofId][nodeId] = justification;
      },
      get: function(proofId, nodeId) {
        return this.justificationsMap[proofId] ? this.justificationsMap[proofId][nodeId] : undefined;
      }
    },

    /** Prunes below node `nodeId`, ONLY IN THE UI. Updates the proof tree, agenda, and tactic. */
    uiPruneBelow: function(userId, proofId, nodeId, proofTree, agenda, tactic, newTopAgendaItem, sequentProofData) {
      // prune proof tree
      if (proofTree.nodesMap[nodeId]) {
        proofTree.pruneBelow(nodeId);

        // update agenda: prune deduction paths
        var agendaItems = agenda.itemsByProofStep(nodeId);
        $.each(agendaItems, function(i, item) {
          var deductionIdx = agenda.deductionIndexOf(item.id, nodeId);
          var section = item.deduction.sections[deductionIdx.sectionIdx];
          section.path.splice(0, deductionIdx.pathStepIdx);
          item.deduction.sections.splice(0, deductionIdx.sectionIdx);
        });

        // sanity check: all agendaItems should have the same deductions (top item should be data.agendaItem.deduction)
        var newTop = newTopAgendaItem.deduction.sections[0].path[0];
        $.each(agendaItems, function(i, item) {
          var oldTop = item.deduction.sections[0].path[0];
          if (oldTop !== newTop) {
            console.log("Unexpected deduction start after pruning: expected " + newTop + " but have " + oldTop +
              " at agenda item " + item.id)
          }
          //@todo additionally check that deduction.sections are all the same (might be expensive, though)
        });

        // delete previous items
        //@todo preserve previous tab order
        $.each(agendaItems, function(i, item) {
          delete agenda.itemsMap[item.id];
        });

        // update agenda: if available, copy already cached deduction path into the remaining agenda item (new top item)
        var topDeduction = agendaItems[0] ? agendaItems[0].deduction : newTopAgendaItem.deduction;
        newTopAgendaItem.deduction = topDeduction;
        newTopAgendaItem.isSelected = true; // add item marked as selected, otherwise step back jumps to random tab
        agenda.itemsMap[newTopAgendaItem.id] = newTopAgendaItem;

        // select new top item
        agenda.select(newTopAgendaItem);

        // refresh tactic
        tactic.fetch(userId, proofId);
      } else {
        // undo on a reloaded/partially loaded proof (proof tree does not contain node with ID `nodeId`)
        sequentProofData.clear();
        sequentProofData.fetchAgenda(userId, proofId);
      }
    },

    /** Prunes the proof tree at the specified goal, executes onPruned when the tree is pruned */
    prune: function(userId, proofId, nodeId, onPruned) {
      //@note make model available in closure of function success
      var self = this;

      $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/pruneBelow').then(function(response) {
        self.uiPruneBelow(userId, proofId, nodeId, self.proofTree, self.agenda, self.tactic, response.data.agendaItem, self);
      }).then(onPruned);
    },

    /** Undoes the last proof step, executes onPruned when the tree is pruned */
    undoLastProofStep: function(userId, proofId, onPruned) {
      //@note make model available in closure of function success
      var self = this;

      $http.get('proofs/user/' + userId + '/' + proofId + '/undoLastStep').then(function(response) {
        self.uiPruneBelow(userId, proofId, response.data.agendaItem.id, self.proofTree, self.agenda, self.tactic, response.data.agendaItem, self);
      }).then(onPruned);
    },

    /** Clears all proof data (at proof start). */
    clear: function() {
      this.proofTree.clear();
      this.agenda.clear();
    },

    /** Fetches the agenda from the server for the purpose of continuing a proof */
    fetchAgenda: function(userId, proofId) { this.doFetchAgenda(userId, proofId, 'agendaawesome'); },

    /** Fetches the agenda from the server for the purpose of browsing a proof from root to leaves */
    fetchBrowseAgenda: function(userId, proofId) { this.doFetchAgenda(userId, proofId, 'browseagenda'); },

    /** Fetches a proof's agenda of kind `agendaKind` from the server */
    doFetchAgenda: function(userId, proofId, agendaKind) {
      var theProofTree = this.proofTree;
      var theAgenda = this.agenda;
      var theTactic = this.tactic;
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + agendaKind)
        .then(function(response) {
          theTactic.fetch(userId, proofId);
          theAgenda.modelId = response.data.modelId;
          theAgenda.itemsMap = response.data.agendaItems;
          $.each(response.data.proofTree.nodes, function(i, v) {
            makeLazyNode($http, userId, proofId, v);
          });
          theProofTree.nodesMap = response.data.proofTree.nodes;
          theProofTree.root = response.data.proofTree.root;
          theProofTree.isProved = response.data.proofTree.isProved;
          var agendaItems = theAgenda.items();
          if (agendaItems.length > 0 && theAgenda.selectedId() === undefined) {
            // select first task if nothing is selected yet
            theAgenda.select(agendaItems[0]);
          }
          if (response.data.closed || agendaItems.length == 0) {
            // proof might be finished
            if(!theAgenda.proofStatusDisplayed) {
              theAgenda.proofStatusDisplayed == true
              $rootScope.$broadcast('agenda.isEmpty', {proofId: proofId});
              console.log("Emiting angeda.isEmpty from sequentproofservice.js 1");
            } else {
              console.log("Not showing agenda.isEmpty because it was already displayed.")
            }
          }
        })
        .catch(function(error) {
          $rootScope.$broadcast('agenda.loadError', userId, proofId, error.data);
        })
        .finally(function() { spinnerService.hideAll(); });
    },

    /** Updates the agenda and the proof tree with new items resulting from a tactic */
    updateAgendaAndTree: function(userId, proofId, proofUpdate) {
      if (proofUpdate.progress) {
        var theProofTree = this.proofTree;
        var theAgenda = this.agenda;
        var oldAgendaItem = theAgenda.itemsMap[proofUpdate.parent.id];
        $.each(proofUpdate.newNodes, function(i, node) {
          // update tree

          theProofTree.nodesMap[node.id] = makeLazyNode($http, userId, proofId, node);
          var parent = theProofTree.nodesMap[node.parent]
          if (parent.children === undefined || parent.children === null) parent.children = [node.id];
          else parent.children.push(node.id);
          // update agenda: prepend new open goal to deduction path
          var newAgendaItem = {
            id: node.id,
            name: node.rule.name,                        // see AgendaAwesomeRequest Goal: Conjecture:
            isSelected: i === 0 ? oldAgendaItem.isSelected : false, // first new item inherits selection from old
            deduction: $.extend(true, {}, oldAgendaItem.deduction)  // object deep copy
          }
          newAgendaItem.deduction.sections[0].path.unshift(node.id);
          theAgenda.itemsMap[newAgendaItem.id] = newAgendaItem;
        });
        if (proofUpdate.newNodes.length == 0) {
          $rootScope.$broadcast('agenda.branchClosed', {proofId: proofId});
        }
        delete theAgenda.itemsMap[oldAgendaItem.id];
        var agendaIds = theAgenda.itemIds();
        if (theAgenda.selectedId() === undefined && agendaIds.length > 0) {
          theAgenda.selectById(agendaIds[agendaIds.length-1]);
        }
        if (agendaIds.length == 0 && !theAgenda.proofStatusDisplayed) {
          theAgenda.proofStatusDisplayed == true
          console.log("Emitting agenda.isEmpty from sequentproofservice.js 1");
          $rootScope.$broadcast('agenda.isEmpty', {proofId: proofId});
        }
        if (theAgenda.proofStatusDisplayed == true) {
          console.log("Not emitting agenda.isEmpty because it's already been emitted.")
        }
      } else {
        $rootScope.$broadcast('agenda.updateWithoutProgress');
      }
    }
  }
}]);

angular.module('keymaerax.services').factory('Poller', function($http, $timeout) {
  return {
    poll: function(url, interval) {
      var data = {
        response: {},
        calls: 0,
        cancel: false
      };
      var poller = function() {
        $http.get(url).then(function(r) {
          data.response = r.data;
          data.calls++;
          if (!data.cancel) $timeout(poller, interval);
        },
        function(error) {
          // server is likely offline, poll less frequently
          data.response = error.data;
          if (!data.cancel) $timeout(poller, 10*interval);
        });
      };
      poller();

      return {
        data: data
      };
    }
  }
});
