angular.module('keymaerax.controllers').controller('ProofAppCtrl', ['$scope', function ($scope) {

  $scope.theme = {css: 'app', name: 'KeYmaera X'};

  $scope.themes = [
    {css: 'app', name: 'KeYmaera X'},
    {css: 'presentation_small', name: 'Presentation (Small)'},
    {css: 'presentation', name: 'Presentation (Default)'},
    {css: 'presentation_large', name: 'Presentation (Large)'}
  ];

  $scope.selectTheme = function(theme) {
    $scope.theme.css = theme.css;
    $scope.theme.name = theme.name;
  }

}])