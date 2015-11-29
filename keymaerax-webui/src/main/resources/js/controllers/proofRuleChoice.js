////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Controller for selecting a proof rule for execution at a specific formula in a proof node.
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').controller('ProofRuleDialogCtrl',
        function ($scope, $http, $cookies, $modalInstance, proofId, nodeId, formula, isAnte, Tactics) {
  $scope.proofId = proofId;
  $scope.nodeId = nodeId;
  $scope.formula = formula;
  $scope.isAnte = isAnte;
  $scope.ruleTactics = [];
  $scope.userTactics = [];

  var fId = ((formula !== undefined) ? formula.id : "sequent")
  var uri = 'proofs/user/' + $cookies.userId + '/' + proofId + '/nodes/' + nodeId + '/formulas/' + fId + '/tactics'

  $http.get(uri).success(function(data) {
      $scope.ruleTactics = [];
      $scope.userTactics = [];
      for (var i = 0; i < data.length; i++) {
          var tacticName = data[i].name;
          var tactic = Tactics.getRuleTactics()[tacticName];
          if (tactic !== undefined) {
//              tactic.id = data[i].id;
              var tacticInst = {
                id: data[i].id,
                name: tactic.name,
                label: tactic.label,
                tooltip: tactic.tooltip,
                input: tactic.input !== undefined ? tactic.input.slice() : tactic.input
              }
              $scope.ruleTactics.push(tacticInst);
          }
          tactic = Tactics.getUserTactics()[tacticName];
          if (tactic !== undefined) {
              tactic.id = data[i].id;
              $scope.userTactics.push(tactic);
          }
      }
  });

  var internalApplyTactics = function(t, uriPostfix, saturate) {
        var inputParams = {}
        if (t.input !== undefined) {
            for (i = 0; i < t.input.length; ++i) {
                inputParams[t.input[i].name] = t.input[i].value
            }
        }
        var saturateWhere = saturate ? '/' + ($scope.formula !== undefined ? 'saturateCurrent'
                                                                           : (isAnte ? "saturateAnte" : "saturateSucc"))
                                     : '';
        $http.post(uri + '/' + uriPostfix + saturateWhere, inputParams).success(function(data) {
            var dispatchedTacticId = data.tacticInstId;
            $modalInstance.close(dispatchedTacticId);
            Tactics.addDispatchedTactics(dispatchedTacticId);
            Tactics.getDispatchedTacticsNotificationService().broadcastDispatchedTactics(dispatchedTacticId);
        });
    }

  $scope.applyTactics = function(t) {
    internalApplyTactics(t, 'run/' + t.id, false)
  }
  $scope.applyTacticsByName = function(tName) {
    internalApplyTactics(t, 'runByName/' + tName, false)
  }
  $scope.applyTacticsFF = function(t) {
    internalApplyTactics(t, 'run/' + t.id, true)
  }
  $scope.applyTacticsByNameFF = function(tName) {
    internalApplyTactics(t, 'runByName/' + tName, true)
  }

  $scope.cancel = function () {
    $modalInstance.dismiss('cancel');
  };

});