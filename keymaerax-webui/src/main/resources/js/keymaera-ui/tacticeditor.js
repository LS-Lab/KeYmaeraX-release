angular.module('keymaerax.ui.tacticeditor', ['ngSanitize', 'ngTextcomplete'])
  .directive('k4TacticEditor', ['$http', '$uibModal', 'derivationInfos', 'Textcomplete', 'sequentProofData',
      function($http, $uibModal, derivationInfos, /*Textcomplete,*/ sequentProofData) {
    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            onTacticScript: '&',
            onNodeSelected: '&'
        },
        controller: ['$scope','sequentProofData', function($scope, sequentProofData) {
          $scope.aceEditor = undefined;
          $scope.tactic = sequentProofData.tactic;
          $scope.agenda = sequentProofData.agenda;
          $scope.tacticExecPopover = {
            tactic: undefined
          }
          $scope.edit = {
            activeMarker: undefined,
            todoMarkers: []
          }

          $scope.createSnapshot = function(doc) {
            if (!$scope.tactic.snapshot) $scope.tactic.snapshot = doc.getAllLines();
          }

          $scope.resetActiveEdit = function() {
            if ($scope.edit.activeMarker) {
              $scope.aceEditor.getSession().removeMarker($scope.edit.activeMarker.active);
              $scope.aceEditor.getSession().clearBreakpoint($scope.edit.activeMarker.range.start.row);
              $scope.aceEditor.getSession().addMarker($scope.edit.activeMarker.marker);
            }
            $scope.edit.activeMarker = undefined;
          }

          $scope.askSaveTacticChanges = function(nodeId) {
            var modalInstance = $uibModal.open({
              templateUrl: 'templates/modalMessageTemplate.html',
              controller: 'ModalMessageCtrl',
              size: 'md',
              resolve: {
                title: function() { return "Unsaved tactic changes"; },
                message: function() { return "Do you want to save the tactic changes?"; },
                mode: function() { return "yesnocancel"; }
              }
            });

            modalInstance.result.then(
              function(result) {
                if (result == "ok") {
                  // yes: execute tactic, but don't change tab
                  var editRange = $scope.edit.activeMarker.range;
                  var doc = $scope.aceEditor.getSession().getDocument();
                  var tactic = { text: doc.getTextRange(editRange) };
                  $scope.executeTactic(tactic, false);
                } else {
                  // no: discard tactic changes if there are any and change tab
                  $scope.tactic.tacticText = $scope.tactic.snapshot;
                  $scope.onNodeSelected({nodeId: nodeId});
                }
              },
              function() {
                // cancel: set cursor back to end of editing range, stay on tab
                if ($scope.edit.activeMarker) {
                  var endPos = $scope.edit.activeMarker.range.end.getPosition();
                  $scope.aceEditor.moveCursorToPosition(endPos);
                  $scope.aceEditor.getSelection().clearSelection();
                }
              }
            );
          }

          $scope.changeTab = function(nodeId) {
            if ($scope.edit.activeMarker) {
              var doc = $scope.aceEditor.getSession().getDocument();
              if (doc.getTextRange($scope.edit.activeMarker.range) != "todo") {
                $scope.askSaveTacticChanges(nodeId);
              } else {
                $scope.onNodeSelected({nodeId: nodeId});
              }
            } else {
              $scope.onNodeSelected({nodeId: nodeId});
            }
          }

          $scope.aceLoaded = function(editor) {
            $scope.aceEditor = editor;
            editor.on("guttermousedown", function(e) {
              var target = e.domEvent.target;
              if (target.className.indexOf("ace_gutter-cell") == -1) return;
              if (!editor.isFocused()) return;
              if (e.clientX > 25 + target.getBoundingClientRect().left) return;

              var doc = editor.getSession().getDocument();
              var activeRange = $scope.edit.activeMarker ? $scope.edit.activeMarker.range : undefined;
              if (activeRange) {
                var tactic = { text: doc.getTextRange(activeRange) };
                if (tactic.text.length > 0) $scope.executeTactic(tactic, false);
              }
              e.stop();
            });
            editor.on("click", function(e) {
              var p = e.getDocumentPosition();
              var activeRange = $scope.edit.activeMarker ? $scope.edit.activeMarker.range : undefined;
              if (activeRange && activeRange.start.row <= p.row && p.row <= activeRange.end.row) {
                e.preventDefault();
                e.stopPropagation();
              } else {
                var nodeId = $scope.tactic.nodeIdAtLoc(p.row, p.column);
                if (nodeId && nodeId != $scope.nodeId) {
                  if (sequentProofData.agenda.contains(nodeId)) {
                    // change tab
                    $scope.changeTab(nodeId);
                  } else {
                    // inspect some proof state without changing tab
                    $scope.onNodeSelected({nodeId: nodeId});
                  }
                }
              }
            });
            editor.getSelection().on("changeCursor", function(e) {
              var p = editor.getSelection().getCursor();
              var nodeId = $scope.tactic.nodeIdAtLoc(p.row, p.column);
              if (nodeId) {
                var doc = editor.getSession().getDocument();
                if (nodeId != $scope.nodeId && $scope.agenda.contains(nodeId)) {
                  $scope.changeTab(nodeId);
                } else if (nodeId != $scope.nodeId) {
                  $scope.onNodeSelected({nodeId: nodeId});
                } else if (!$scope.edit.activeMarker) {
                  $scope.edit.todoMarkers.filter(function(e) {
                    if (e.range.contains(p.row, p.column)) {
                      $scope.edit.activeMarker = e;
                      editor.getSession().removeMarker(e.marker);
                      $scope.edit.activeMarker.active = editor.getSession().addMarker($scope.edit.activeMarker.range, "k4-tactic-todo-active", "fullLine", true);
                      editor.getSession().setBreakpoint($scope.edit.activeMarker.range.start.row);
                    }
                  });
                }
              }
            });
            // fold markers are annotations
            editor.getSession().on("changeAnnotation", function(e) {
              $scope.aceEditor.getSession().foldAll(); // but foldAll only folds multiline folds
            });
            editor.commands.on("exec", function(e) {
              if (e.command.readOnly) {
                // key navigation
              } else {
                // typing
                var range = editor.selection.getRange();
                var doc = editor.getSession().getDocument();
                if ($scope.edit.activeMarker) {
                  // editing between the anchors created on unfinished tactics is allowed, but not outside
                  if (!$scope.edit.activeMarker.range.containsRange(range)) {
                    e.preventDefault();
                    e.stopPropagation();
                  }
                } else {
                  //@todo delete selected area = prune (but after a yes/no dialog confirmation); for now: prevent
                  e.preventDefault();
                  e.stopPropagation();
                }
              }
            });
          }

          $scope.allIndicesOfTodo = function(text) {
            var regex = /todo/gi;
            var result;
            var indices = [];
            while (result = regex.exec(text)) {
              indices.push(result.index);
            }
            return indices;
          }

          $scope.aceChanged = function(delta) {
            var session = $scope.aceEditor.getSession();
            var doc = session.getDocument();

            if (delta.length > 0 && delta[0] && delta[0].action == "remove" && delta[0].lines.length > 1) {
              //@note multi-line remove happens when a tactic is executed or undone, need to recalculate markers on upcoming insert
              if ($scope.edit.activeMarker) $scope.resetActiveEdit();
              $.each($scope.edit.todoMarkers, function(i, e) {
                session.removeMarker(e.marker);
              });
              $scope.edit.todoMarkers = [];
            } else if (delta[0].action == "insert" &&
                       delta[0].lines.length === doc.getAllLines().length &&
                       delta[0].lines.every(function(e,i) { return e === doc.getAllLines()[i]; } )) {
              // mark all occurrences of unfinished tactics
              var todoIndices = $scope.allIndicesOfTodo(doc.getValue());
              if ($scope.edit.todoMarkers.length == 0) {
                $.each(todoIndices, function(i,e) {
                  var pos = doc.indexToPosition(e);
                  var range = new ace.Range();
                  range.start = pos;
                  range.end = doc.createAnchor(pos.row, pos.column + "todo".length);
                  var marker = session.addMarker(range, "k4-tactic-todo-icon k4-tactic-todo", "text", true);
                  $scope.edit.todoMarkers.push({ range: range, marker: marker });
                });
              }

              // select current tab
              if (!$scope.edit.activeMarker) {
                var nodeLoc = $scope.tactic.locOfNode($scope.nodeId);
                if (nodeLoc) {
                  $scope.aceEditor.getSelection().setSelectionRange(
                    new ace.Range(nodeLoc.line, nodeLoc.column, nodeLoc.endLine, nodeLoc.endColumn), true);
                }
              } else {
                var p = $scope.aceEditor.getCursorPosition();
                var nodeId = $scope.tactic.nodeIdAtLoc(p);
                if (nodeId && nodeId != $scope.nodeId && sequentProofData.agenda.contains(nodeId)) {
                  $scope.changeTab(nodeId);
                }
              }
            }
          }

          $scope.executeTactic = function(tactic, stepwise) {
            $scope.onTacticScript({tacticText: tactic.text, stepwise: stepwise});
          }
        }],
        templateUrl: 'templates/tacticEditor.html'
    };
  }]);
