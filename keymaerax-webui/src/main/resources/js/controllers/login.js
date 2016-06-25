angular.module('keymaerax.controllers').controller('LoginCtrl',
  function ($scope, $cookies, $uibModal, $http, sessionService) {
    $scope.defaultLogin = function() { login("guest", "guest") }

    $scope.username = ""
    $scope.password = ""

    $scope.processLogin = function() { login($scope.username, $scope.password) }

    $scope.processRegistration = function() {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/license_dialog.html',
        controller: 'LicenseDialogCtrl',
        backdrop: "static",
        size: 'lg'
      });
      modalInstance.result.then(function() {
        $http.post("/user/" + $scope.username + "/" + $scope.password)
          .then(function(response) {
            if (response.data.success === true) { $scope.processLogin(); }
            else { showMessage($uibModal, "Registration failed", "Sorry, user name is already taken. Please choose a different name."); }
          });
      });
    }

    login = function(username, password) {
      if (username === "guest") {
        // guests have to accept the license every time
        var modalInstance = $uibModal.open({
          templateUrl: 'partials/license_dialog.html',
          controller: 'LicenseDialogCtrl',
          backdrop: "static",
          size: 'lg'
        });
        modalInstance.result.then(function() {
          $http.get("/user/" + username + "/" + password).then(function(response) {
            if(response.data.type == "LoginResponse") {
              if(response.data.success) {
                sessionService.setToken(response.data.sessionToken);
                sessionService.setUser(response.data.value);
                document.location.href = "/dashboard.html"
              } else {
                showMessage($uibModal, "Login failed", "Please check user name and/or password");
              }
            }
          });
        });
      } else {
        $http.get("/user/" + username + "/" + password)
        .then(function(response) {
          if(response.data.type == "LoginResponse") {
            if(response.data.success) {
              sessionService.setToken(response.data.sessionToken);
              sessionService.setUser(response.data.value);
              document.location.href = "/dashboard.html"
            } else {
              showMessage($uibModal, "Login failed", "Please check user name and/or password");
            }
          }
        });
      }
    }
  });
