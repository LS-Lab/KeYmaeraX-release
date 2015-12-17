/**
 * Controllers for proof lists and proof information pages.
 */

angular.module('keymaerax.controllers').controller('ProofInfoCtrl', function($scope, $rootScope, $http, $cookies, $uibModal, $routeParams) {
  $scope.proof = {
      proofName: "blah"
  };

  //TODO: add functions  that allow renaming.
})

angular.module('keymaerax.controllers').controller('ModelProofCreateCtrl', function ($scope, $http, $cookies, $routeParams, $location) {
  /*
   * Creates a new proof using a default name, so that the user doesn't have to enter new input.
   */
  $scope.createDefaultProofForModel = function(modelId) {
      var proofName        = "Untitled Proof"
      var proofDescription = ""
      var uri              = 'models/users/' + $cookies.get('userId') + '/model/' + modelId + '/createProof'
      var dataObj          = {proofName : proofName, proofDescription : proofDescription}

      $http.post(uri, dataObj).
          success(function(data) {
              var proofid = data.id
              // we may want to switch to ui.router
              $location.path('proofs/' + proofid);
          }).
          error(function(data, status, headers, config) {
              console.log('Error starting new proof for model ' +modelId)
          });
  };
  $scope.createDefaultProof = function() {
    $scope.createDefaultProofForModel($routeParams.modelId)
  };

  $scope.createProof = function() {
      var proofName        = $scope.proofName ? $scope.proofName : ""
      var proofDescription = $scope.proofDescription ? $scope.proofDescription : ""
      var uri              = 'models/users/' + $cookies.get('userId') + '/model/' + $routeParams.modelId + '/createProof'
      var dataObj          = {proofName : proofName, proofDescription : proofDescription}

      $http.post(uri, dataObj).
          success(function(data) {
              var proofid = data.id
              // we may want to switch to ui.router
              $location.path('proofs/' + proofid);
          }).
          error(function(data, status, headers, config) {
              console.log('Error starting new proof for model ' + $routeParams.modelId)
          });
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
            showErrorMessage($uibModal, "Received unknown proof status " + data.status)
          }
      }).
      error(function(data, status, headers, config) {
            showCaughtErrorMessage($uibModal, data, "Unable to poll proof status.")
      });
  }, 1000);
}

/* Proof list for all models belonging to a user. */
angular.module('keymaerax.controllers').controller('ProofListCtrl', function ($scope, $http, $cookies,$location, $routeParams) {
  $scope.openPrf = function(proofId) {
      $location.path('/proofs/' + proofId)
  }
  //Load the proof list and emit as a view.
  $http.get('models/users/' + $cookies.get('userId') + "/proofs").success(function(data) {
    $scope.allproofs = data;
  });

  $scope.loadProof = function(proof) {
      proof.loadStatus = 'loading'
      $http.get('proofs/user/' + $cookies.get('userId') + "/" + proof.id).success(function(data) {
          proof.loadStatus = data.loadStatus
          // when server loads proof itself asynchronously
          if (data.loadStatus == 'loading') {
            console.log("Start polling proof status");
            pollProofStatus(proof, $cookies.get('userId'), $http);
          }
          if(data.loadStatus == 'Error') {
              showCaughtErrorMessage($uibModal, data, "Error encountered while loading proof.")
          }
      }).
      error(function(data, status, headers, config) {
        // TODO check that it is a time out
        console.log("Start polling proof status");
        pollProofStatus(proof, $cookies.get('userId'), $http);
      });
  }

  $scope.$emit('routeLoaded', {theview: 'allproofs'});
});

/* Proof list for an individual model */
angular.module('keymaerax.controllers').controller('ModelProofsCtrl', function ($scope, $http, $cookies,$location, $routeParams) {
  $scope.openPrf = function(proofId) {
      $location.path('/proofs/' + proofId)
  }

  //Todo: should "inherit" this from the modelproofscreatectrl rather than copy/pasting here.
  $scope.createProof = function() {
      var proofName        = $scope.proofName ? $scope.proofName : ""
      var proofDescription = $scope.proofDescription ? $scope.proofDescription : ""
      var uri              = 'models/users/' + $cookies.get('userId') + '/model/' + $routeParams.modelId + '/createProof'
      var dataObj          = {proofName : proofName, proofDescription : proofDescription}

      $http.post(uri, dataObj).
          success(function(data) {
              var proofid = data.id
              // we may want to switch to ui.router
              $location.path('proofs/' + proofid);
          }).
          error(function(data, status, headers, config) {
              console.log('Error starting new proof for model ' + $routeParams.modelId)
          });
  }

  $scope.loadProof = function(proof) {
    proof.loadStatus = 'loading'
    $http.get('proofs/user/' + $cookies.get('userId') + "/" + proof.id).success(function(data) {
      proof.loadStatus = data.loadStatus
      // when server loads proof itself asynchronously
      if (data.loadStatus == 'loading') {
        console.log("Start polling proof status");
        pollProofStatus(proof, $cookies.get('userId'), $http);
      }
      else if(data.loadStatus == 'Error') {
          showErrorMessage($uibModal, "Error encountered while attempting to load proof")
      }
    }).
    error(function(data, status, headers, config) {
      // TODO check that it is a time out
      console.log("Start polling proof status");
      //@TODO does this mean that there isn't necessarily an error here? Confused.
//        showErrorMessage($uibModal, "Encountered error shile trying to poll proof status.")
      pollProofStatus(proof, $cookies.get('userId'), $http);
    });
  }
  //Load the proof list and emit as a view.
  $http.get('models/users/' + $cookies.get('userId') + "/model/" + $routeParams.modelId + "/proofs").success(function(data) {
    $scope.proofs = data;
  });
  $scope.$emit('routeLoaded', {theview: 'proofs'});
});