angular.module('keymaerax.ui.binding', ['ngSanitize']).directive('contenteditable', ['$sce', function($sce) {
  return {
    restrict: 'A',
    require: '?ngModel', // get NgModelController
    link: function(scope, element, attrs, ngModel) {
      if (!ngModel) return;

      ngModel.$render = function() {
        element.html($sce.getTrustedHtml(ngModel.$viewValue || ''));
      };

      element.on('blur keyup change', function() {
        scope.$evalAsync(read);
      });

      read();

      function read() {
        var html = element.html();
        // clearing the content leaves a <br> behind, which optionally is removed
        if (attrs.stripBr && html === '<br>') {
          html = '';
        }
        ngModel.$setViewValue(html);
      }
    }
  };
}]);