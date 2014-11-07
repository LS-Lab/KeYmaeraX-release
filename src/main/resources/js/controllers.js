var keymaeraProofControllers = angular.module('keymaeraProofControllers', ['ngCookies', 'ngDialog', 'angularTreeview']);

keymaeraProofControllers.factory('Models', function () {

    var models = [];

    return {
        getModels: function() {
            return models;
        },
        setModels: function(m) {
            models = m;
        },
        addModel: function(model) {
            models.push(model);
        },
        addModels: function(m) {
            for (var i = 0; i < m.length; i++) {
                models.push(m[i]);
            }
        }
    };
});

keymaeraProofControllers.controller('DashboardCtrl',
  function ($scope, $http, $rootScope) {
    $rootScope.theme = 'ngdialog-theme-default';
    // Set the view for menu active class
    $scope.$on('routeLoaded', function (event, args) {
      $scope.theview = args.theview;
    });

    $scope.$emit('routeLoaded', {theview: 'dashboard'});
  });

keymaeraProofControllers.controller('ModelUploadCtrl',
  function ($scope, $http, $cookies, $cookieStore, Models) {

     $scope.addModel = function() {
         $.ajax({
               url: "user/" + $cookies.userId + "/modeltextupload/" + $scope.modelName,
               type: "POST",
               data: window.UPLOADED_FILE_CONTENTS,
               async: true,
               dataType: 'json',
               contentType: 'application/json',
               success: function(data) {
                   while (Models.getModels().length != 0) { Models.getModels().shift() }
                   $http.get("models/users/" + $cookies.userId).success(function(data) {
                       Models.addModels(data);
                       $scope.modelName = '';
                       // TODO reset file chooser
                   });
               },
               error: this.ajaxErrorHandler
         });
     };

     $scope.$watch(
        function () { return Models.getModels(); }
     );

     $scope.$emit('routeLoaded', {theview: 'models'});
  });

keymaeraProofControllers.controller('ModelListCtrl',
  function ($scope, $http, $cookies, Models) {
    $scope.models = [];
    $http.get("models/users/" + $cookies.userId).success(function(data) {
        $scope.models = data
    });
    $scope.$watch('models',
        function (newModels) {
            if (newModels) Models.setModels(newModels);
        }
    );
    $scope.$emit('routeLoaded', {theview: 'models'});
  });

keymaeraProofControllers.controller('ModelCtrl',
  function ($scope, $http, $cookies, Models) {
    // TODO I don't like this way of structuring URIs: should be models/ID/... and user handled via session
    $scope.loadModel = function(modelid) {
        $http.get("users/" + $cookies.userId + "/model/" + modelid).success(function(data) {
            $scope.model = data
        });
    };
    $scope.$watch(
        function () { return Models.getModels(); }
    );

    $scope.$emit('routeLoaded', {theview: 'models'});
  });

keymaeraProofControllers.controller('ModelProofCreateCtrl',
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
  });

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The proof list
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

keymaeraProofControllers.controller('ModelProofsCtrl',
  function ($scope, $http, $cookies, $routeParams) {
    //Load the proof list and emit as a view.
    $http.get('models/users/' + $cookies.userId + "/model/" + $routeParams.modelId + "/proofs").success(function(data) {
      $scope.proofs = data;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  });


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proofs
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
keymaeraProofControllers.controller('ProofDetailCtrl',
  function($scope, $http, $routeParams) {
    $http.get('user/0/proofs/' + $routeParams.proofId).success(function(data) {
    $scope.proofId = data.proofid;
    $scope.proofTree = data.proofTree;
  });
  $scope.$emit('routeLoaded', {theview: 'proofs'});
});

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Testing...
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

keymaeraProofControllers.controller('TestCtrl',
  function ($scope, $http, $cookies, $routeParams) {
    $scope.treedata =
    [
        {
            "label" : "User",
            "id" : "role1",
            "children" : [
                { "label" : "subUser1", "id" : "role11", "children" : [] },
                { "label" : "subUser2", "id" : "role12", "children" : [
                    { "label" : "subUser2-1", "id" : "role121", "children" : [
                        { "label" : "subUser2-1-1", "id" : "role1211", "children" : [] },
                        { "label" : "subUser2-1-2", "id" : "role1212", "children" : [] }
                    ]}
            ]}
            ]
        },
        { "label" : "Admin", "id" : "role2", "children" : [] },
        { "label" : "Guest", "id" : "role3", "children" : [] }
    ];
  });
