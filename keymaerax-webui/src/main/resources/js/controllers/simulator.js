angular.module('keymaerax.controllers').controller('SimulatorCtrl',
  function($scope, $uibModal, $uibModalInstance, $http, proofId, userId, nodeId) {

  $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/setupSimulation')
    .then(function(response) {
      $scope.initialCondition = response.data.initial;
      $scope.stateRelation = response.data.stateRelation;
    })

  $scope.numSteps = 10;
  $scope.stepDuration = "1";
  $scope.busy = false;

  $scope.simulate = function() {
    $scope.busy = true;
    $http.post('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/simulate',
        {initial: $scope.initialCondition, stateRelation: $scope.stateRelation, numSteps: $scope.numSteps,
         stepDuration: $scope.stepDuration})
      .then(function(response) {
        //@todo display alternative simulations
        $scope.lineStates = response.data.lineStates[0];
        $scope.radarStates = response.data.radarStates[0];
        $scope.varNames = response.data.varNames;
        $scope.ticks = response.data.ticks;
      }).finally(function() {
        $scope.busy = false;
      })
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});