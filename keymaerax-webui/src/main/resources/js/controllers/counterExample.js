////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Counter example
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').controller('CounterExampleCtrl',
    function($scope, $uibModalInstance, result, origFormula, assumptions, cexFormula, cexValues, speculatedValues) {

  $scope.result = result;
  $scope.origFormula = origFormula;
  $scope.cexFormula = cexFormula;
  $scope.cexValues = cexValues;
  $scope.speculatedValues = speculatedValues;
  $scope.assumptions = {
    additional: assumptions
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('ok');
  }

  $scope.counterexample = function() {
    $uibModalInstance.close($scope.assumptions);
  }

});
