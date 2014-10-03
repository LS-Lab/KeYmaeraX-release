var keymaeraProofControllers = angular.module('keymaeraProofControllers', ['ngCookies']);

keymaeraProofControllers.controller('DashboardCtrl', ['$scope', '$http', '$cookies', '$cookieStore',
  function ($scope, $http, $cookies, $cookieStore) {
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



//        while(window.UPLOADED_FILE_CONTENTS === null) {} //whatever. this all needs rewriting.

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

    // Set the view for menu active class
    $scope.$on('routeLoaded', function (event, args) {
      $scope.theview = args.theview;
    });

    $scope.$emit('routeLoaded', {theview: 'dashboard'});
  }]);

keymaeraProofControllers.controller('ModelListCtrl', ['$scope', '$http',
  function ($scope, $http) {
//    $http.get('models/').success(function(data) {
//      $scope.models = data;
//    });
    $scope.$emit('routeLoaded', {theview: 'models'});
  }]);

keymaeraProofControllers.controller('ModelProofCreateCtrl', ['$scope', '$http',
  function ($scope, $http) {
    // HACK: just to load some file
    jQuery.get('examples/ETCS-safety.key', function(fileContent) {
        $http.post("proofs/0", fileContent).success(function(data) {
            $scope.proofId = data.proofid;
            $http.get('user/0/proofs/' + data.proofid).success(function(data) {
                $scope.proofTree = [ data.proofTree.model ];
                globalProofTree = [ data.proofTree.model ];
            });
        });
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  }]);

keymaeraProofControllers.controller('ProofListCtrl', ['$scope', '$http',
  function ($scope, $http) {
    $http.get('proofs/').success(function(data) {
      $scope.proofs = data;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  }]);

keymaeraProofControllers.controller('ProofDetailCtrl', ['$scope', '$http', '$routeParams',
  function($scope, $http, $routeParams) {
    $http.get('user/0/proofs/' + $routeParams.proofId).success(function(data) {
        $scope.proofId = data.proofid;
        $scope.proofTree = data.proofTree;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  }]);