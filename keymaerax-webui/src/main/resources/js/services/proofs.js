angular.module('keymaerax.services').factory('Proofs', ['$http', '$location', 'FileSaver', function($http, $location, FileSaver) {
  var proofServiceDef = {
    proofs: [],
    deleteProof: function(userId, proof) {
      return $http.post('user/' + userId + "/proof/" + proof.id + "/delete").success(function(data) {
         if (data.success) {
           var idx = proofServiceDef.proofs.indexOf(proof)
           if (idx > -1) proofServiceDef.proofs.splice(idx, 1);
         }
      });
    },
    createProof: function(userId, modelId, proofName, proofDescription) {
        var uri     = 'models/users/' + userId + '/model/' + modelId + '/createProof'
        var dataObj = {proofName: proofName, proofDescription: proofDescription}

        return $http.post(uri, dataObj).success(function(data) {
          var proofid = data.id
          // we may want to switch to ui.router
          $location.path('proofs/' + proofid);
        }).error(function(data, status, headers, config) {
          console.log('Error starting new proof for model ' + modelId)
        });
    },
    downloadTactic: function(userId, proof) {
      return $http.get("/proofs/user/" + userId + "/" + proof.id + "/extract").then(function(response) {
        var data = new Blob([response.data.tacticText], { type: 'text/plain;charset=utf-8' });
        FileSaver.saveAs(data, proof.name + '.kyt');
      });
    },
    downloadLemma: function(userId, proof) {
      return $http.get("/proofs/user/" + userId + "/" + proof.id + "/lemma").then(function(response) {
        var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
        FileSaver.saveAs(data, proof.name + '.kyp');
      });
    },
    downloadProofArchive: function(userId, proof) {
      return $http.get("/proofs/user/" + userId + "/" + proof.id + "/download").then(function(response) {
        var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
        FileSaver.saveAs(data, proof.name + '.kyx');
      });
    },
    downloadModelProofs: function(userId, modelId) {
      return $http.get("/models/user/" + userId + "/model/" + modelId + "/downloadProofs").then(function(response) {
        var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
        FileSaver.saveAs(data, modelId + '_' + proofServiceDef.currentDateString() + '.kyx');
      });
    },
    downloadAllProofs: function(userId) {
      return $http.get("/proofs/user/" + userId + "/downloadAllProofs").then(function(response) {
        var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
        FileSaver.saveAs(data, 'proofs_'+ proofServiceDef.currentDateString() +'.kyx');
      });
    },
    currentDateString: function() {
      var today = new Date();
      var dd = today.getDate();
      var mm = today.getMonth() + 1; //@note January is 0
      var yyyy = today.getFullYear();

      if(dd < 10) dd = '0' + dd
      if(mm < 10) mm='0'+mm
      return mm + dd + yyyy;
    },
    loadProofList: function(userId, modelId) {
      if (modelId !== undefined) {
        return $http.get('models/users/' + userId + "/model/" + modelId + "/proofs").success(function(data) {
          proofServiceDef.proofs.length = 0;
          proofServiceDef.proofs.push(...data);
        });
      } else {
        return $http.get('proofs/users/' + userId).success(function(data) {
          proofServiceDef.proofs.length = 0;
          proofServiceDef.proofs.push(...data);
        });
      }
    }
  }
  return proofServiceDef;
}])
