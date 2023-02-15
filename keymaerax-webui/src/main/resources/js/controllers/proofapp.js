angular.module('keymaerax.controllers').controller('ProofAppCtrl', ['$scope', '$http', '$routeParams', 'sessionService', 'sequentProofData', function ($scope, $http, $routeParams, sessionService, sequentProofData) {

  $scope.theme = {css: 'app', name: 'KeYmaera X', fontSize: 14};

  $scope.themes = [
    {css: 'app', name: 'KeYmaera X', fontSize: 14, renderMargins: [40,80]},
    {css: 'presentation', name: 'High Contrast', fontSize: 18, renderMargins: [30,60]}
  ];

  setTheme = function(newTheme) {
    var savedTheme = $.grep($scope.themes, function(theme) { return theme.css === newTheme.themeCss; });
    if (savedTheme.length > 0) {
      $scope.theme = savedTheme[0];
      $scope.theme.fontSize = newTheme.themeFontSize;
      $scope.theme.renderMargins = newTheme.renderMargins;
      $(document.documentElement).get(0).style.setProperty('--lsfontsize',newTheme.themeFontSize + 'px');
    }
  }

  $http.get('/users/' + sessionService.getUser() + '/theme').then(function(response) {
    setTheme(response.data);
  });

  $scope.selectTheme = function(theme) {
    if (theme.css && theme.fontSize && theme.renderMargins && theme.renderMargins[0] && theme.renderMargins[1]) {
      $http.post('/users/' + sessionService.getUser() + '/theme', {css: theme.css, fontSize: theme.fontSize, renderMargins: theme.renderMargins}).then(function(response) {
        setTheme(response.data);
        if ($routeParams.proofId) {
          // refresh the proof view
          sequentProofData.fetchAgenda(sessionService.getUser(), $routeParams.proofId, function(agenda) {
            agenda.selectByIndex(0);
          });
        }
      });
    }
  }

  $scope.showCharacterMeasure = function(doShow) {
    sequentProofData.characterMeasure.show = doShow;
  }

}])