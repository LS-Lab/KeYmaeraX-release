angular.module('keymaerax.controllers').controller('ProofAppCtrl', ['$scope', '$http', 'sessionService', function ($scope, $http, sessionService) {

  $scope.theme = {css: 'app', name: 'KeYmaera X', fontSize: 14};

  $scope.themes = [
    {css: 'app', name: 'KeYmaera X', fontSize: 14},
    {css: 'presentation', name: 'High Contrast', fontSize: 18}
  ];

  setTheme = function(newTheme) {
    var savedTheme = $.grep($scope.themes, function(theme) { return theme.css === newTheme.themeCss; });
    if (savedTheme.length > 0) {
      $scope.theme = savedTheme[0];
      $scope.theme.fontSize = newTheme.themeFontSize;
      $(document.documentElement).get(0).style.setProperty('--lsfontsize',newTheme.themeFontSize + 'px');
    }
  }

  $http.get('/users/' + sessionService.getUser() + '/theme').then(function(response) {
    setTheme(response.data);
  });

  $scope.selectTheme = function(theme) {
    if (theme.css && theme.fontSize) {
      $http.post('/users/' + sessionService.getUser() + '/theme', {css: theme.css, fontSize: theme.fontSize}).then(function(response) {
        setTheme(response.data);
      });
    }
  }

}])