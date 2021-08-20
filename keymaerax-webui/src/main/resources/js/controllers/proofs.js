/**
 * Controllers for proof lists and proof information pages.
 */
angular.module('keymaerax.controllers').controller('ModelProofCreateCtrl', function ($scope, $http,
    $routeParams, $location, sessionService, spinnerService, Proofs) {
  /** User data and helper functions. */
  $scope.user = {
    /** Returns true if the user is a guest, false otherwise. */
    isGuest: function() { return sessionService.isGuest(); }
  };

  /** Create a new proof for model 'modelId' with 'proofName' and 'proofDescription' (both optional: empty ""). */
  $scope.createProof = function(modelId, proofName, proofDescription) {
    Proofs.createProof(sessionService.getUser(), modelId, proofName, proofDescription);
  };

  /** Opens the last proof (finished or not) of this model. */
  $scope.openLastProof = function(modelId) {
    $http.get('models/users/' + sessionService.getUser() + "/model/" + modelId + "/proofs").then(function(response) {
      if (response.data.length > 0) {
        $location.path('proofs/' + response.data[response.data.length-1].id);
      }
    });
  };

  /** Creates a new proof from the model's tactic (if any). */
  $scope.proveFromTactic = function(modelId) {
    spinnerService.show('modelListProofLoadingSpinner');
    var uri     = 'models/users/' + sessionService.getUser() + '/model/' + modelId + '/createTacticProof'
    $http.post(uri, {}).success(function(data) {
      var proofId = data.id;
      $location.path('proofs/' + proofId);
    }).finally(function() { spinnerService.hide('modelListProofLoadingSpinner'); });
  }

  $scope.delayedProveFromTactic = function(modelId) {
    return function() { $scope.proveFromTactic(modelId); }
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
    $scope, $http, $location, $route, $uibModal, FileSaver, Blob, spinnerService, sessionService, Proofs, modelId) {
  $scope.modelId = modelId;
  $scope.userId = sessionService.getUser();

  $scope.intro.introOptions = {
    steps:[
    {
        element: '#proofsarchiving',
        intro: "Extract all proofs into .kyx archives.",
        position: 'bottom'
    },
    {
        element: '#proofsactions',
        intro: "Continue, inspect, export, or delete proofs here.",
        position: 'bottom'
    }
    ],
    showStepNumbers: false,
    exitOnOverlayClick: true,
    exitOnEsc:true,
    nextLabel: 'Next', // could use HTML in labels
    prevLabel: 'Previous',
    skipLabel: 'Exit',
    doneLabel: 'Done'
  }

  $scope.deleteProof = function(proof) {
    Proofs.deleteProof($scope.userId, proof);
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

  $scope.downloadTactic = function(proof) {
    Proofs.downloadTactic($scope.userId, proof);
  }
  $scope.downloadLemma = function(proof) {
    Proofs.downloadLemma($scope.userId, proof);
  }
  $scope.downloadPartialProof = function(proof) {
    Proofs.downloadProofArchive($scope.userId, proof)
  }

  $scope.openTactic = function (proofid) {
    var modalInstance = $uibModal.open({
      templateUrl: 'partials/prooftacticdialog.html',
      controller: 'ProofTacticDialogCtrl',
      size: 'fullscreen',
      resolve: {
        userid: function() { return $scope.userId; },
        proofid: function() { return proofid; },
        title: function() { return "Tactic"; },
        message: function() { return undefined; }
      }
    });
  };

  $scope.downloadModelProofs = function(modelId) {
    spinnerService.show('proofExportSpinner');
    Proofs.downloadModelProofs($scope.userId, modelId).finally(function() { spinnerService.hide('proofExportSpinner'); });
  }

  $scope.downloadAllProofs = function() {
    spinnerService.show('proofExportSpinner');
    Proofs.downloadAllProofs($scope.userId).finally(function() { spinnerService.hide('proofExportSpinner'); });
  }

  //Load the proof list and emit as a view.
  Proofs.loadProofList($scope.userId, $scope.modelId);
  $scope.proofs = Proofs.proofs;
  $scope.$emit('routeLoaded', {theview: 'proofs'});

});

angular.module('keymaerax.controllers').controller('ProofTacticDialogCtrl', function (
    $scope, $http, $uibModalInstance, userid, proofid, title, message) {
  $scope.title = title;
  $scope.message = message;
  $scope.tactic = {
    tacticBody: "",
    proofId: proofid
  };

  $http.get("proofs/user/" + userid + "/" + proofid + "/tactic").then(function(response) {
      $scope.tactic.tacticBody = response.data.tacticText;
  });

  $scope.ok = function() {
    $uibModalInstance.close();
  };

  $scope.aceLoaded = function(editor) {
    editor.setReadOnly(true);
  }
});
