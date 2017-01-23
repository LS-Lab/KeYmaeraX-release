angular.module('keymaerax.ui.directives').directive('replaceInclude', function () {
    return {
        require: 'ngInclude',
        restrict: 'A',
        link: function (scope, elem, attr) {
            //@todo may need compile when ng-repeat is in template
            elem.replaceWith(elem.children());
        }
    };
});