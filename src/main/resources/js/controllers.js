var keymaeraProofControllers = angular.module('keymaeraProofControllers', ['ngCookies', 'ngDialog']);

keymaeraProofControllers.controller('DashboardCtrl', ['$scope', '$rootScope', '$http', '$cookies', '$cookieStore', 'ngDialog',
  function ($scope, $rootScope, $http, $cookies, $cookieStore, ngDialog) {

    $rootScope.theme = 'ngdialog-theme-default';

    // Set the view for menu active class
    $scope.$on('routeLoaded', function (event, args) {
      $scope.theview = args.theview;
    });

    $scope.$emit('routeLoaded', {theview: 'dashboard'});
  }]);

keymaeraProofControllers.controller('ModelListCtrl', ['$scope', '$rootScope', '$http', '$cookies', '$cookieStore',
  function ($scope, $rootScope, $http, $cookies, $cookieStore) {
      //MODEL LIST
      $scope.models = [];

      //Populate the models list with data from the server.
      $http.get("models/users/" + $cookies.userId).success(function(data,status,headers,config) {
          for(var i=0;i<data.length;i++) {
              $scope.models.push(data[i])
          }
      });

      $scope.addModel = function() {
          var filename = $("#keyFile").val();
          var modelName = $("#modelName").val();
          var userId = $cookies.userId;

          $.ajax({
                url: "user/" + $cookies.userId + "/modeltextupload/" + modelName,
                type: "POST",
                data: window.UPLOADED_FILE_CONTENTS,
                async: true,
                dataType: 'json',
                contentType: 'application/json',
                success: function(data) {
                        //For now just completely repopulate...
                        while($scope.models.length != 0) { $scope.models.shift() }
                        $http.get("models/users/" + $cookies.userId).success(function(data,status,headers,config) {
                            for(var i=0;i<data.length;i++) {
                                $scope.models.push(data[i])
                            }
                            console.log("TODO-NRF -- now reset the form as well.")
                        });
                        },
                error: this.ajaxErrorHandler
              });
      }

    $scope.$emit('routeLoaded', {theview: 'models'});
  }]);

keymaeraProofControllers.controller('ModelProofCreateCtrl', ['$scope', '$http', '$cookies', '$routeParams',
  function ($scope, $http, $cookies, $routeParams) {
    $scope.createProof = function() {
        var proofName        = $scope.proofName ? $scope.proofName : ""
        var proofDescription = $scope.proofDescription ? $scope.proofDescription : ""
        var uri              = 'models/users/' + $cookies.userId + '/model/' + $routeParams.modelId + '/createProof'
        var dataObj          = {proofName : proofName, proofDescription : proofDescription}

        $http.post(uri, dataObj).
            success(function(data, status, headers, config) {
                alert("new proof id: " + data + "\n\t...off to the proof view with this proof id!")
            }).
            error(function(data, status, headers, config) {
                alert('TODO handle errors properly.')
            });
    }
  }]);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The proof list
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

keymaeraProofControllers.controller('ModelProofsCtrl', ['$scope', '$http', '$cookies', '$routeParams',
  function ($scope, $http, $cookies, $routeParams) {
    //Load the proof list and emit as a view.
    $http.get('models/users/' + $cookies.userId + "/model/" + $routeParams.modelId + "/proofs").success(function(data) {
      $scope.proofs = data;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  }]);

//keymaeraProofControllers.controller('ProofDetailCtrl', ['$scope', '$http', '$routeParams',
//  function($scope, $http, $routeParams) {
//    $http.get('user/0/proofs/' + $routeParams.proofId).success(function(data) {
//        $scope.proofId = data.proofid;
//        $scope.proofTree = data.proofTree;
//    });
//    $scope.$emit('routeLoaded', {theview: 'proofs'});
//  }]);



