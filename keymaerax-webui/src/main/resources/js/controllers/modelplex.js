angular.module('keymaerax.controllers').controller('ModelPlexCtrl',
    function($scope, $uibModalInstance, $http, spinnerService, FileSaver, Blob, userid, modelid) {

  $scope.mxdata = {
    modelid: modelid,
    modelname: undefined,
    generatedArtifact: {
      code: undefined,
      source: undefined
    },
    artifact: 'monitor/controller',
    additionalMonitorVars: []
  }

  $scope.language = "dL"
  $scope.sourceCollapsed = true;

  $scope.synthesize = function(language, monitorShape) {
    spinnerService.show('modelplexExecutionSpinner')
    $scope.language = language;
    $http({method: 'GET',
           url: "user/" + userid + "/model/" + $scope.mxdata.modelid + "/modelplex/generate/" +
                $scope.mxdata.artifact + "/" + monitorShape + "/" + language,
           params: {vars: JSON.stringify($scope.mxdata.additionalMonitorVars)}})
      .then(function(response) {
        $scope.mxdata.generatedArtifact.code = response.data.code;
        $scope.mxdata.modelname = response.data.modelname;
        $scope.mxdata.generatedArtifact.source = response.data.source;
      })
      .finally(function() { spinnerService.hide('modelplexExecutionSpinner'); });
  }

  $scope.download = function() {
    var data = new Blob([$scope.mxdata.generatedArtifact.code], { type: 'text/plain;charset=utf-8' });
    FileSaver.saveAs(data, $scope.mxdata.modelname + ($scope.language == 'dL' ? '.kyx' : '.c'));
  }

  $scope.open = function(what) {
    $scope.mxdata.artifact = what;
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
