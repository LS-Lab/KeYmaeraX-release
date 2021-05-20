angular.module('keymaerax.ui.tacticeditor', ['ngSanitize', 'ngTextcomplete'])
  .directive('k4TacticEditor', ['$http', 'derivationInfos', 'Textcomplete', 'sequentProofData',
      function($http, derivationInfos, /*Textcomplete,*/ sequentProofData) {
    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            onTacticScript: '&'
        },
        controller: ['$scope','sequentProofData', function($scope, sequentProofData) {
          $scope.aceEditor = undefined;
          $scope.tactic = sequentProofData.tactic;
          $scope.tacticChanges = [];
          $scope.tacticExecPopover = {
            tactic: undefined
          }

          $scope.createSnapshot = function(doc) {
            if (!$scope.tactic.snapshot) $scope.tactic.snapshot = doc.getAllLines();
          }

          $scope.aceLoaded = function(editor) {
            $scope.aceEditor = editor;
            editor.on("mousemove", function(e) {
              var hovered = $scope.tacticChanges.filter(function(v) {
                var p = e.getDocumentPosition()
                return v.range.contains(p.row, p.column);
              });
              if (hovered.length > 0) {
                $scope.tacticExecPopover.tactic = hovered[0];
              } else {
                $scope.tacticExecPopover.tactic = undefined;
              }
            });
            editor.on("click", function(e) {
              var clicked = $scope.tacticChanges.filter(function(v) {
                var p = e.getDocumentPosition()
                return v.range.contains(p.row, p.column);
              });
              if (clicked.length > 0 && e.domEvent.altKey) {
                $scope.executeTactic(clicked[0], false);
              } else if (clicked.length > 0 && e.domEvent.shiftKey) {
                $scope.executeTactic(clicked[0], true);
              }
            });
            editor.on("mouseout", function(e) {
              $scope.tacticExecPopover.tactic = undefined;
            });
            // fold markers are annotations
            editor.getSession().on("changeAnnotation", function(e) {
              $scope.aceEditor.getSession().foldAll(); // but foldAll only folds multiline folds
            });
          }

          $scope.aceChanged = function(delta) {
            for (i = 0; i < $scope.tacticChanges.length; i++) {
              $scope.aceEditor.getSession().removeMarker($scope.tacticChanges[i].marker);
            }
            $scope.tacticChanges = [];
            var doc = $scope.aceEditor.getSession().getDocument();

            var dmp = new diff_match_patch();
            var diff = dmp.diff_main($scope.tactic.snapshot, doc.getValue());

            var offset = 0;
            for (i = 0; i < diff.length; i++) {
              var diffText = diff[i][1];
              switch (diff[i][0]) {
                case -1: // deleted: ignore (caused by undo, but also when deleting text)
                  break;
                case 0: // unchanged
                  offset += diffText.length;
                  break;
                case 1: // added
                  //@todo somewhere in ace editor API this functionality must be available
                  var start = doc.indexToPosition(offset);
                  var lines = diffText.split(doc.getNewLineCharacter());
                  var end = {
                    row: start.row + lines.length-1,
                    column: lines[lines.length-1].length + (lines.length == 1 ? start.column : 0)
                  };
                  var diffRange = ace.Range.fromPoints(start, end);
                  var marker = $scope.aceEditor.getSession().addMarker(diffRange, "k4-tactic-diff", "text", true);
                  $scope.tacticChanges.push({ text: diffText, range: diffRange, marker: marker });
                  offset += diffText.length;
                  break;
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
