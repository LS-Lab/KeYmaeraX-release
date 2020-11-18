angular.module('keymaerax.ui.directives')
  .directive('k4TacticMenuEntry', ['derivationInfos', function(derivationInfos) {
    return {
      restrict: 'E',
      replace: true,
      scope: {
        userId: '@',
        proofId: '@',
        name: '@',
        codeName: '@',
        helpName: '@',
        hideLongHelp: '@',
        hideShortHelp: '@',
        exec: '&exec'
      },
      templateUrl: 'templates/tacticmenuentry.html',
      link: function(scope, element, attrs) {
        if (!scope.helpName) scope.helpName = scope.codeName;
        scope.rulehelp = {
          codeName: undefined,
          derivationInfo: undefined
        }
        scope.fetchHelp = function(codeName, kind) {
          if (scope.rulehelp.codeName !== codeName) {
            scope.rulehelp.codeName = codeName;
            derivationInfos.byName(scope.userId, scope.proofId, undefined, codeName).then(function(response) {
              if (response.data.length > 0) {
                scope.rulehelp.derivationInfo = response.data[0].standardDerivation;
              } else {
                scope.rulehelp.derivationInfo = undefined;
              }
            });
          }
        }
        scope.run = function() {
          scope.exec({codeName: scope.codeName})
        }
      }
    }
  }]);
