angular.module('keymaerax.controllers').controller('ModelPlexCtrl',
    function($scope, $uibModalInstance, $http, spinnerService, FileSaver, Blob, userid, modelid) {

  $scope.mxdata = {
    modelid: modelid,
    monitorkind: 'controller',
    monitorShape: 'boolean',
    generatedArtifact: undefined,
    artifact: 'sandbox',
    additionalMonitorVars: [],
    mandatoryMonitorVars: []
  }

  $http.get("user/" + userid + "/model/" + $scope.mxdata.modelid + "/modelplex/mandatoryVars")
    .then(function(response) {
      $scope.mxdata.mandatoryMonitorVars = response.data.mandatoryVars;
    })

  $scope.synthesize = function() {
    spinnerService.show('modelplexExecutionSpinner')
    $http({method: 'GET',
           url: "user/" + userid + "/model/" + $scope.mxdata.modelid + "/modelplex/generate/" +
                $scope.mxdata.artifact + "/" +
                $scope.mxdata.monitorkind + "/" + $scope.mxdata.monitorShape + "/kym",
           params: {vars: JSON.stringify($scope.mxdata.additionalMonitorVars)}})
      .then(function(response) {
        $scope.mxdata.generatedArtifact = response.data.generatedArtifact;
      })
      .finally(function() { spinnerService.hide('modelplexExecutionSpinner'); });
  }

  $scope.downloadCCode = function() {
    spinnerService.show('modelplexExecutionSpinner')
    $http({method: 'GET',
           url: "user/" + userid + "/model/" + $scope.mxdata.modelid + "/modelplex/generate/" +
            $scope.mxdata.artifact + "/" +
            $scope.mxdata.monitorkind + "/" + $scope.mxdata.monitorShape + "/c",
           params: {vars: JSON.stringify($scope.mxdata.additionalMonitorVars)}})
      .then(function(response) {
        var data = new Blob([response.data.code], { type: 'text/plain;charset=utf-8' });
        FileSaver.saveAs(data, response.data.modelname + '.c');
      })
      .finally(function() { spinnerService.hide('modelplexExecutionSpinner'); });
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
