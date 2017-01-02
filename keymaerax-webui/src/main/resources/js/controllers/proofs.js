/**
 * Controllers for proof lists and proof information pages.
 */
angular.module('keymaerax.controllers').controller('ModelProofCreateCtrl', function ($scope, $http, $cookies, $routeParams, $location, spinnerService) {
  $scope.createProof = function(modelId, proofName, proofDescription) {
      var uri     = 'models/users/' + $cookies.get('userId') + '/model/' + modelId + '/createProof'
      var dataObj = {proofName: proofName, proofDescription: proofDescription}

      $http.post(uri, dataObj).
          success(function(data) {
              var proofid = data.id
              // we may want to switch to ui.router
              $location.path('proofs/' + proofid);
          }).
          error(function(data, status, headers, config) {
              console.log('Error starting new proof for model ' + $routeParams.modelId)
          });
  };

  $scope.proveFromTactic = function(modelId) {
    spinnerService.show('modelListProofLoadingSpinner');
    var uri     = 'models/users/' + $cookies.get('userId') + '/model/' + modelId + '/proveFromTactic'
    $http.post(uri, {}).success(function(data) {
      var proofId = data.id;
      $location.path('proofs/' + proofId);
    }).finally(function() { spinnerService.hide('modelListProofLoadingSpinner'); });
  }

  $scope.$emit('routeLoaded', {theview: '/models/:modelId/proofs/create'})
});

/* Polling function to obtain proof status, used in proof lists to update the status in the list */
var pollProofStatus = function(proof, userId, http) {
   setTimeout(function() {
      http.get('proofs/user/' + userId + '/' + proof.id + '/status')
              .success(function(data) {
          if (data.status == undefined) {
            console.log("Continue polling proof status");
            pollProofStatus(proof, userId, http);
          } else if (data.status == 'loading') {
            console.log("Continue polling proof status");
            pollProofStatus(proof, userId, http);
          } else if (data.status == 'loaded') {
            console.log("Received proof status " + data.status);
            proof.loadStatus = data.status
          } else if(data.status == 'Error') {
            console.log("Error: " + data.error)
            showCaughtErrorMessage($uibModal, data, "Error while polling proof status")
          }
          else {
            console.error("Received unknown proof status " + data.status)
            showClientErrorMessage($uibModal, "Received unknown proof status " + data.status);
          }
      }).
      error(function(data, status, headers, config) {
            showCaughtErrorMessage($uibModal, data, "Unable to poll proof status.")
      });
  }, 1000);
}

/* Proof list (those of an individual model if the route param modelId is defined, all proofs otherwise) */
angular.module('keymaerax.controllers').controller('ProofListCtrl', function (
    $scope, $http, $cookies, $location, $routeParams, $route, FileSaver, Blob, spinnerService) {
  $scope.modelId = $routeParams.modelId;
  $scope.userId = $cookies.get('userId')

  $scope.openPrf = function(proofId) {
      $location.path('/proofs/' + proofId)
  }

  $scope.deleteProof = function(proof) {
    $http.post('user/' + $scope.userId + "/proof/" + proof.id + "/delete").success(function(data) {
       $route.reload();
    });
  };

  $scope.loadProof = function(proof) {
    proof.loadStatus = 'loading'
    $http.get('proofs/user/' + $scope.userId + "/" + proof.id).success(function(data) {
      proof.loadStatus = data.loadStatus
      // when server loads proof itself asynchronously
      if (data.loadStatus == 'loading') {
        console.log("Start polling proof status");
        pollProofStatus(proof, $scope.userId, $http);
      } else if(data.loadStatus == 'Error') {
          showMessage($uibModal, "Error encountered while attempting to load proof")
      }
    }).
    error(function(data, status, headers, config) {
      // TODO check that it is a time out
      console.log("Start polling proof status");
      //@TODO does this mean that there isn't necessarily an error here? Confused.
//        showErrorMessage($uibModal, "Encountered error shile trying to poll proof status.")
      pollProofStatus(proof, $scope.userId, $http);
    });
  }

  //@todo duplicate with provingawesome.js downloadTactic
  $scope.downloadTactic = function(proof) {
    $http.get("/proofs/user/" + $scope.userId + "/" + proof.id + "/extract").then(function(response) {
      var data = new Blob([response.data.tacticText], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, proof.name + '.kyt');
    });
  }

  //@todo duplicate with provingawesome.js downloadLemma
  $scope.downloadLemma = function(proof) {
    $http.get("/proofs/user/" + $scope.userId + "/" + proof.id + "/lemma").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, proof.name + '.kyp');
    });
  }

  //@todo duplicate with provingawesome.js downloadProofArchive
  $scope.downloadPartialProof = function(proof) {
    $http.get("/proofs/user/" + $scope.userId + "/" + proof.id + "/download").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, proof.name + '.kya');
    });
  }

  currentDateString = function() {
    var today = new Date();
    var dd = today.getDate();
    var mm = today.getMonth() + 1; //@note January is 0
    var yyyy = today.getFullYear();

    if(dd < 10) dd = '0' + dd
    if(mm < 10) mm='0'+mm
    return mm + dd + yyyy;
  }

  $scope.downloadModelProofs = function(modelId) {
    spinnerService.show('proofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/model/" + modelId + "/downloadProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, modelId + '_' + currentDateString() + '.kya');
    })
    .finally(function() { spinnerService.hide('proofExportSpinner'); });
  }

  $scope.downloadAllProofs = function() {
    spinnerService.show('proofExportSpinner');
    $http.get("/proofs/user/" + $scope.userId + "/downloadAllProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, 'allproofs_'+ currentDateString() +'.kya');
    })
    .finally(function() { spinnerService.hide('proofExportSpinner'); });
  }

  //Load the proof list and emit as a view.
  if ($scope.modelId !== undefined) {
    $http.get('models/users/' + $scope.userId + "/model/" + $scope.modelId + "/proofs").success(function(data) {
      $scope.proofs = data;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  } else {
    $http.get('models/users/' + $scope.userId + "/proofs").success(function(data) {
      $scope.proofs = data;
    });
    $scope.$emit('routeLoaded', {theview: 'allproofs'});
  }

});