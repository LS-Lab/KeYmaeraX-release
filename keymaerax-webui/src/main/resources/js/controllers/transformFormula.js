angular.module('keymaerax.controllers').controller('TransformFormulaCtrl',
    function($scope, $uibModalInstance, formula, isAnte) {

  $scope.formula = formula;
  $scope.isAnte = isAnte;
  $scope.formData = {};

  $scope.ok = function() {
    //@note format must fit to RestApi.doInputAt
    $uibModalInstance.close([{type: 'formula', param: 'toFormula', value: $scope.formData.toFormula}]);
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
