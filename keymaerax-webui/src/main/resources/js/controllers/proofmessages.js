angular.module('keymaerax.controllers').controller('ProofMessagesCtrl',
  function($rootScope, $scope) {

  $scope.proofMessage = {
    text: "",
    details: "",
    taskStepwiseRequest: undefined,
    isVisible: false
  }

  $rootScope.$on('agenda.updateWithoutProgress', function() {
    $scope.proofMessage.text = "The tactic did not make progress";
    $scope.proofMessage.isVisible = true;
  });

  $rootScope.$on('proof.message', function(event, message) {
    $scope.proofMessage.text = message.textStatus;
    $scope.proofMessage.details = message.errorThrown;
    $scope.proofMessage.taskStepwiseRequest = message.taskStepwiseRequest;
    $scope.proofMessage.isVisible = (message.textStatus !== "");
  });

})