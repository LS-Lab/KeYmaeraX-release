angular.module('keymaerax.ui.binding', ['ngSanitize']).directive('contenteditable', ['$sce', function($sce) {
  return {
    restrict: 'A',
    require: '?ngModel', // get NgModelController
    link: function(scope, element, attrs, ngModel) {
      if (!ngModel) return;

//      rangy.init();
//      var savedSel = {};

      ngModel.$render = function() {
        element.html($sce.getTrustedHtml(ngModel.$viewValue || ''));
        //@note set cursor
//        if (savedSel.element !== undefined && savedSel.range !== undefined) {
//          rangy.getSelection().restoreCharacterRanges(savedSel.element, savedSel.range);
//        }
        read(); // initialize
      };

      element.on('blur keyup change', function(event) {
        // save range to reset cursor
//        savedSel.element = event.target;
//        savedSel.range = rangy.getSelection().saveCharacterRanges(event.target);
//        //@note set attributes for auto-completion
//        if (savedSel.element !== undefined && savedSel.range !== undefined) {
//          event.target.selectionDirection = 'none';
//          event.target.selectionStart = savedSel.range[0].characterRange.start;
//          event.target.selectionEnd = savedSel.range[0].characterRange.end;
//          event.target.value = element.text();
//        }
        scope.$evalAsync(read);
      });

      function read() {
        //var html = element.html();
        var text = element.text();
        //ngModel.$setViewValue(html);
        ngModel.$setViewValue(text);
      }
    }
  };
}]);