angular.module('keymaerax.controllers').controller('ProofAppCtrl', ['$scope', '$http', '$cookies', function ($scope, $http, $cookies) {

  $scope.theme = {css: 'app', name: 'KeYmaera X'};

  $scope.themes = [
    {css: 'app', name: 'KeYmaera X'},
    {css: 'presentation_small', name: 'Presentation (Small)'},
    {css: 'presentation', name: 'Presentation (Medium)'},
    {css: 'presentation_large', name: 'Presentation (Large)'}
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