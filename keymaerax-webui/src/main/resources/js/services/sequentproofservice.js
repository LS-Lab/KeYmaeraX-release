/** Makes a node that fetches its sequent lazily */
makeLazyNode = function(http, userId, proofId, node) {
  if (node.sequent) {
    node.sequent.ante.forEach(function(f) { f.use = true; });
    node.sequent.succ.forEach(function(f) { f.use = true; });
  }

  /** Returns a sequent object that may be filled in later. Use callback to wait for a filled sequent. */
  node.getSequent = function(callback) {
    let theNode = node;
    if (theNode.sequent) {
      if (callback) callback(theNode.sequent);
      return theNode.sequent;
    } else {
      theNode.sequent = {};
      http.get('proofs/user/' + userId + '/' + proofId + '/' + theNode.id + '/sequent').then(function(response) {
        if (response.data.sequent) {
          theNode.sequent.ante = response.data.sequent.ante;
          theNode.sequent.succ = response.data.sequent.succ;
          theNode.sequent.ante.forEach(function(f) { f.use = true; });
          theNode.sequent.succ.forEach(function(f) { f.use = true; });
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
  return function() {
    return {
       itemsMap: {},           // { id: { id: String, name: String, isSelected: Bool, path: [ref PTNode] } }, ... }
       selectedTab: "()",
       clear: function() {
         this.itemsMap = {};
         this.selectedTab = "()";
       },
       selectedId: function() {
         let selected = $.grep(this.items(), function(e) { return e.isSelected; });
         if (selected !== undefined && selected.length > 0) return selected[0].id;
         else return undefined;
       },
       itemIds: function() { return Object.keys(this.itemsMap); },
       contains: function(id) { return $.grep(this.itemIds(), function(v) { return v === id; }).length > 0; },
       items: function() {
         //@HACK set selectedTab here because angular bootstrap v2.5.0 screws up active=selectedTab when tabs are removed
         let selected = this.selectedItem();
         if (selected !== undefined) this.selectedTab = selected.id;
         return $.map(this.itemsMap, function(v) {return v;});
       },
       selectedItem: function() {
         let theItems = $.map(this.itemsMap, function(v) { return v; });
         let selected = $.grep(theItems, function(e) { return e.isSelected; });
         return selected !== undefined && selected.length > 0 ? selected[0] : undefined;
       },
       deselect: function(item) { /* do not deselect item, otherwise agenda name textbox won't show */ },
       select: function(item) {
         $.each(this.items(), function(i, e) { e.isSelected = false; });
         if (item) {
           item.isSelected = true;
           this.selectedTab = item.id;
         } else {
           // select last item
           let items = this.items();
           if (items.length > 0) {
             let lastItem = items[items.length-1];
             lastItem.isSelected = true;
             this.selectedTab = lastItem.id;
           } else {
             this.selectedTab = undefined;
           }
         }
       },
       selectById: function(itemId) { this.select(this.itemsMap[itemId]); },
       /** Selects an agenda item by index if none selected yet. */
       selectByIndex: function(index) {
         if (this.selectedId() === undefined) {
           let agendaItems = this.items();
           if (agendaItems.length > 0) this.select(agendaItems[index]);
         }
       },
       itemsByProofStep: function(ptNodeId) {
         return $.grep(this.items(), function(e) {
           return $.grep(e.deduction.sections, function(v) { return v.path.indexOf(ptNodeId) >= 0; }).length > 0; });
       },
       /** Returns the deduction index of the specified proof tree node in agendaItem (Object { section, pathStep} ). */
       deductionIndexOf: function(itemId, ptNodeId) {
         let agendaItem = this.itemsMap[itemId];
         for (let i = 0; i < agendaItem.deduction.sections.length; i++) {
           let section = agendaItem.deduction.sections[i];
           let j = section.path.indexOf(ptNodeId);
           if (j >= 0) return { sectionIdx: i, pathStepIdx: j };
         }
         return { sectionIdx: -1, pathStepIdx: -1 };
       },
       /** Returns the index of the section where any proofTreeNode's child is last (child is unique). */
       childSectionIndex: function(/*itemId, proofTreeNode*/) { return 0; },

       /**
        * Updates the specified section by adding the proof tree node. If the node has more than 1 child, a new section
        * after the specified section is started.
        * @param proofTree The proof tree.
        * @param proofTreeNode The node to add.
        * @param agendaItem The agenda item to add the node to.
        * @param sectionIdx The section in the agenda item's deduction path where to add the proof node.
        */
       updateSection: function(proofTree, proofTreeNode, agendaItem, sectionIdx) {
         let section = agendaItem.deduction.sections[sectionIdx];
         if (section.path.indexOf(proofTreeNode.id) < 0) {
           proofTreeNode.getSequent = function() { return proofTreeNode.sequent; };
           section.path.push(proofTreeNode.id);
         }
       }
     }
  };
});

angular.module('keymaerax.services').factory('ProofTree', function() {
  return function() {
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
          let theProofTree = this;
          let node = theProofTree.nodesMap[nodeId];
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
        htmlNodeId: function(nodeId) { return nodeId.replace(/[()]/g, "").replace(/,/g, "-"); },
        /** Highlights the operator where the step that created sequent/node `nodeId` was applied. */
        highlightNodeStep: function(nodeId, highlight) {
          if (!nodeId) return undefined
          // branching tactic: tree may include other child
          let nodeIdHead = nodeId.split(",")[0];
          let node = undefined;
          for (let i = 0; i<3 && !node; i++) {
            node = this.node(nodeIdHead + "," + i + ")");
          }
          if (node) {
            node.isHighlighted = highlight;
            //@todo calculate position for search 'L, 'Llast, etc.
            let pos = node.rule.pos.replace(/\./g, "\\,");
            let element = $("#seq_" + this.htmlNodeId(node.parent) + " #fml_" + pos);
            if (highlight) {
              if (node.rule.asciiName === "WL" || node.rule.asciiName === "WR") element.addClass("k4-highlight-steppos-full");
              else element.addClass("k4-highlight-steppos");
              if (element.text().startsWith("[") || element.text().startsWith("<")) {
                if (node.rule.asciiName === "[]^" || node.rule.asciiName === "<>|") element.addClass("k4-highlight-steppos-modality-post");
                else element.addClass("k4-highlight-steppos-modality-prg");
              }
            } else element.removeClass("k4-highlight-steppos k4-highlight-steppos-full k4-highlight-steppos-modality-prg k4-highlight-steppos-modality-post");
          }
          return node;
        },
        highlightedNode: function() {
          let theNodes = $.map(this.nodesMap, function(v) { return v; });
          let highlighted = $.grep(theNodes, function(e) { return e.isHighlighted; });
          return highlighted !== undefined && highlighted.length > 0 ? highlighted[0] : undefined;
        },

        paths: function(node) {
          //@todo what if we have a branching tree?
          let that = this; //@note $.map rescopes this
          if (node.children !== undefined && node.children.length > 0) {
            return $.map(node.children, function(v) {
              let childrenPaths = that.paths(that.node(v));
              childrenPaths.unshift(node); //@note unshift prepends in place and returns new length
              return childrenPaths;
            });
          } else return [node];
        }
      }
  };
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
      nodesByLocation: [],
      snapshot: undefined,
      verbose: true,

      fetch: function(userId, proofId) {
        let theTactic = this;
        $http.get('proofs/user/' + userId + '/' + proofId + '/extract/' + (theTactic.verbose ? "verbose" : "succinct")).then(function (response) {
          theTactic.snapshot = response.data.tacticText;
          theTactic.tacticText = response.data.tacticText;
          theTactic.nodesByLocation = response.data.nodesByLocation;
        })
        .catch(function() {
          $rootScope.$broadcast('tactic.extractError', userId, proofId);
        });
      },

      nodeIdAtLoc: function(line, column, offset) {
        let nodesAtLoc = $.grep(this.nodesByLocation, function(v) {
          if (offset && v.loc.line >= offset.start.row) {
            let lines = offset.end.row-offset.start.row;
            return v.loc.line+lines <= line && line <= v.loc.endLine+lines;
          } else return v.loc.line <= line && line <= v.loc.endLine;
        });
        return nodesAtLoc.length > 0 ? nodesAtLoc[0].node : undefined;
      },

      locOfNode: function(node) {
        let nodeInfo = $.grep(this.nodesByLocation, function(v) { return v.node === node; });
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
      areAllFmlsUsed: function(sequent) {
        if (sequent) {
          let anteUsed = sequent.ante ? $.grep(sequent.ante, function(e) { return e.use; }) : [];
          let succUsed = sequent.succ;
          if (anteUsed.length === (sequent.ante ? sequent.ante.length : 0)) {
            succUsed = sequent.succ ? $.grep(sequent.succ, function(e) { return e.use; }) : [];
          }
          return anteUsed.length === (sequent.ante ? sequent.ante.length : 0) &&
                 succUsed.length === (sequent.succ ? sequent.succ.length : 0);
        } else return true;
      },
      toggleUseAllFmls: function(sequent) {
        if (sequent) {
          let use = !this.areAllFmlsUsed(sequent);
          $.map(sequent.ante, function(e) { e.use = use; return e; });
          $.map(sequent.succ, function(e) { e.use = use; return e; });
        }
      },
      invertAllFmls: function(sequent) {
        if (sequent) {
          $.map(sequent.ante, function(e) { e.use = !e.use; return e; });
          $.map(sequent.succ, function(e) { e.use = !e.use; return e; });
        }
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
        let agendaItems = agenda.itemsByProofStep(nodeId);
        $.each(agendaItems, function(i, item) {
          let deductionIdx = agenda.deductionIndexOf(item.id, nodeId);
          let section = item.deduction.sections[deductionIdx.sectionIdx];
          section.path.splice(0, deductionIdx.pathStepIdx);
          item.deduction.sections.splice(0, deductionIdx.sectionIdx);
        });

        // sanity check: all agendaItems should have the same deductions (top item should be data.agendaItem.deduction)
        let newTop = newTopAgendaItem.deduction.sections[0].path[0];
        $.each(agendaItems, function(i, item) {
          let oldTop = item.deduction.sections[0].path[0];
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
        newTopAgendaItem.deduction = agendaItems[0] ? agendaItems[0].deduction : newTopAgendaItem.deduction;
        newTopAgendaItem.isSelected = true; // add item marked as selected, otherwise step back jumps to random tab
        agenda.itemsMap[newTopAgendaItem.id] = newTopAgendaItem;

        // select new top item
        agenda.select(newTopAgendaItem);

        // refresh tactic
        tactic.fetch(userId, proofId);
      } else {
        // undo on a reloaded/partially loaded proof (proof tree does not contain node with ID `nodeId`)
        sequentProofData.clear();
        sequentProofData.fetchAgenda(userId, proofId, function(agenda) {
          agenda.selectByIndex(0);
        });
      }
    },

    /** Prunes the proof tree at the specified goal, executes onPruned when the tree is pruned */
    prune: function(userId, proofId, nodeId, onPruned) {
      //@note make model available in closure of function success
      let self = this;
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/pruneBelow').then(function(response) {
        self.uiPruneBelow(userId, proofId, nodeId, self.proofTree, self.agenda, self.tactic, response.data.agendaItem, self);
      }).then(onPruned);
    },

    /** Undoes the last proof step, executes onPruned when the tree is pruned */
    undoLastProofStep: function(userId, proofId, onPruned) {
      //@note make model available in closure of function success
      let self = this;
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
    fetchAgenda: function(userId, proofId, doneCallback) { this.doFetchAgenda(userId, proofId, 'agendaawesome', doneCallback); },

    /** Fetches the agenda from the server for the purpose of browsing a proof from root to leaves */
    fetchBrowseAgenda: function(userId, proofId) { this.doFetchAgenda(userId, proofId,'browseagenda', undefined); },

    /** Fetches a proof's agenda of kind `agendaKind` from the server */
    doFetchAgenda: function(userId, proofId, agendaKind, doneCallback) {
      let theProofTree = this.proofTree;
      let theAgenda = this.agenda;
      let theTactic = this.tactic;
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
          //@todo add proof nodes to agenda
          if (response.data.closed || theAgenda.items().length === 0) {
            // proof might be finished
            $rootScope.$broadcast('agenda.isEmpty', {proofId: proofId});
          }
        })
        .catch(function(error) {
          $rootScope.$broadcast('agenda.loadError', userId, proofId, error.data);
        })
        .finally(function() { if (doneCallback) doneCallback(theAgenda, theProofTree); });
    },

    /** Updates the agenda and the proof tree with new items resulting from a tactic */
    updateAgendaAndTree: function(userId, proofId, proofUpdate) {
      if (proofUpdate.progress) {
        let theProofTree = this.proofTree;
        let theAgenda = this.agenda;
        let oldAgendaItem = theAgenda.itemsMap[proofUpdate.parent.id];
        $.each(proofUpdate.newNodes, function(i, node) {
          // update tree
          theProofTree.nodesMap[node.id] = makeLazyNode($http, userId, proofId, node);
          let parent = theProofTree.nodesMap[node.parent]
          if (parent.children === undefined || parent.children === null) parent.children = [node.id];
          else parent.children.push(node.id);
          // update agenda: prepend new open goal to deduction path
          let newAgendaItem = {
            id: node.id,
            name: node.rule.name,                        // see AgendaAwesomeRequest Goal: Conjecture:
            isSelected: i === 0 ? oldAgendaItem.isSelected : false, // first new item inherits selection from old
            deduction: $.extend(true, {}, oldAgendaItem.deduction)  // object deep copy
          }
          newAgendaItem.deduction.sections[0].path.unshift(node.id);
          theAgenda.itemsMap[newAgendaItem.id] = newAgendaItem;
        });
        if (proofUpdate.newNodes.length === 0) {
          $rootScope.$broadcast('agenda.branchClosed', {proofId: proofId});
        }
        delete theAgenda.itemsMap[oldAgendaItem.id];
        let agendaIds = theAgenda.itemIds();
        if (theAgenda.selectedId() === undefined && agendaIds.length > 0) {
          theAgenda.selectById(agendaIds[agendaIds.length-1]);
        }
        if (agendaIds.length === 0) {
          console.log("Emitting agenda.isEmpty from sequentproofservice.js 1");
          $rootScope.$broadcast('agenda.isEmpty', {proofId: proofId});
        }
      } else {
        $rootScope.$broadcast('agenda.updateWithoutProgress');
      }
    },

    /** Fetches all nodes in the section on the path to the root. */
    fetchPathAll: function(userId, proofId, agenda, proofTree, section) {
      let sectionEnd = section.path[section.path.length-1];
      let that = this
      if (sectionEnd !== proofTree.root) {
        $http.get('proofs/user/' + userId + '/' + proofId + '/' + sectionEnd + '/pathall').success(function(data) {
          // TODO use numParentsUntilComplete to display some information
          $.each(data.path, function(i, ptnode) { that.updateProof(agenda, proofTree, ptnode); });
        });
      }
    },

    /** Adds a proof tree node and updates the agenda sections. */
    updateProof: function(agenda, proofTree, proofTreeNode) {
      //@todo remove agenda and proofTree arguments
      let items = $.map(proofTreeNode.children, function(e) { return agenda.itemsByProofStep(e); });
      $.each(items, function(i, v) {
        let childSectionIdx = agenda.childSectionIndex(v.id, proofTreeNode);
        if (childSectionIdx >= 0) {
          proofTree.addNode(proofTreeNode);
          agenda.updateSection(proofTree, proofTreeNode, v, childSectionIdx);
        }
      });
    }
  }
}]);

angular.module('keymaerax.services').factory('Poller', function($http, $timeout) {
  return {
    poll: function(url, interval) {
      let data = {
        response: {},
        calls: 0,
        cancel: false
      };
      let poller = function() {
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
