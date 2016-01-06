angular.module('keymaerax.controllers').controller('LoginCtrl',
  function ($scope, $cookies, $cookieStore, $uibModal) {
    $scope.defaultLogin = function() { login("guest", "guest") }

    $scope.username = ""
    $scope.password = ""

    $scope.processLogin = function() {
      if ($scope.username === undefined || $scope.password === undefined) {
          showErrorMessage($uibModal, "Please provide e-mail address and password for login");
      } else {
        login($scope.username, $scope.password)
      }
    }

    $scope.processRegistration = function() {
      if ($scope.username === undefined || $scope.password === undefined) {
          showErrorMessage($uibModal, "Please provide your e-mail address and choose a password for registration");
      } else {
        $.ajax({
              type: "POST",
              dataType: "json",
              contentType: "application/json",
              async: false,
              url: "/user/" + $scope.username + "/" + $scope.password,
              success: function(result) {
                 if(result.success === true) { $scope.processLogin(); }
                 else { showErrorMessage($uibModal, "Sorry, user name is already taken. Please choose a different name."); }
               },
              error: this.ajaxErrorHandler
            });
      }
    }

    ajaxErrorHandler = function(request, textStatus, errorThrown) {
      console.log("Error: " + textStatus + ". Error trace following...")
      console.log(errorThrown)
      showErrorMessage($uibModal, errorThrown);
    }

    login = function(username, password) {
      $.ajax({
        type: "GET",
        dataType: "json",
        contentType: "application/json",
        async: false,
        url: "/user/" + username + "/" + password,
        success: eventHandler,
        error: this.ajaxErrorHandler
      });
    }

    eventHandler = function(obj) {
      if(obj.type === null) {
        showErrorMessage($uibModal, "Trying to process a non-response in the event handler.")
      }

      if(obj.type == "LoginResponse") {
        if(obj.success) {
          //@todo $cookieStore; also: AuthenticationService
          document.cookie = obj.key + " = " + obj.value + "; path=/";
          document.location.href = "/dashboard.html"
        } else {
          showErrorMessage($uibModal, "Login failed!");
        }
      }
    }
  });