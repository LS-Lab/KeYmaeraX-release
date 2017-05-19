angular.module('keymaerax.controllers').controller('ProofAppCtrl', ['$scope', '$http', '$cookies', function ($scope, $http, $cookies) {

  $scope.theme = {css: 'app', name: 'KeYmaera X (Small)'};

  $scope.themes = [
    {css: 'app', name: 'KeYmaera X (Small)'},
    {css: 'app-medium', name: 'KeYmaera X (Medium)'},
    {css: 'app-large', name: 'KeYmaera X (Large)'},
    {css: 'presentation_small', name: 'High Contrast (Small)'},
    {css: 'presentation', name: 'High Contrast (Medium)'},
    {css: 'presentation_large', name: 'High Contrast (Large)'}
  ];

  $http.get('/users/' + $cookies.get('userId') + '/theme').then(function(response) {
    var savedTheme = $.grep($scope.themes, function(theme) { return theme.css === response.data.theme; });
    if (savedTheme.length > 0) $scope.theme = savedTheme[0];
  });

  $scope.selectTheme = function(theme) {
    $http.post('/users/' + $cookies.get('userId') + '/theme', theme.css).then(function(response) {
      var savedTheme = $.grep($scope.themes, function(t) { return t.css === theme.css; });
      $scope.theme = savedTheme[0];
    });
  }

}])