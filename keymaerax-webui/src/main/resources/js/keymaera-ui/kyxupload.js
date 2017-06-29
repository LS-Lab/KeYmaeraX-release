angular.module('keymaerax.ui.directives').directive('k4FileUpload', function () {
  return {
    restrict: 'E',
    scope: {
      onFileConfirmed: '&',
    },
    templateUrl: 'templates/kyxupload.html',
    link: function(scope, element, attrs) {

      element.on("change.bs.fileinput", function(e) {
        scope.fileExt = (keyFile && keyFile.files && keyFile.files.length > 0
          ? keyFile.files[0].name.substr(keyFile.files[0].name.lastIndexOf('.'), 4)
          : '');
        scope.$apply();
      });

      scope.readFile = function() {
        var file = keyFile.files[0];
        var fr = new FileReader();
        fr.onerror = function(e) { alert("Error opening file: " + e.getMessage()); };
        fr.onload = function(e) {
          var fileContent = e.target.result;
          scope.onFileConfirmed({fileName: file.name, fileContent: fileContent});
        };

        fr.readAsText(file);
      }
    }
  }
})