angular.module('keymaerax.ui.directives').directive('k4FileUpload', function () {
  return {
    restrict: 'E',
    scope: {
      onFileChanged: '&'
    },
    templateUrl: 'templates/kyxupload.html',
    link: function(scope, element, attrs) {

      getFileExt = function(fileName) {
        var txtIdx = fileName.lastIndexOf('.txt'); //@note some browsers download our files as .kyx.txt
        var fn = txtIdx >= 0 ? fileName.substr(0, txtIdx) : fileName;
        return fn.substr(fn.lastIndexOf('.'), 4);
      }

      element.on("change.bs.fileinput", function(e) {
        if (keyFile && keyFile.files && keyFile.files.length > 0) {
          var file = keyFile.files[0];
          scope.fileExt = getFileExt(file.name);
          var fr = new FileReader();
          fr.onerror = function(e) { alert("Error opening file: " + e.getMessage()); };
          fr.onload = function(e) {
            var fileContent = e.target.result;
            scope.onFileChanged({ fileName: file.name, fileContent: fileContent });
          };

          fr.readAsText(file);
        } else {
          scope.fileExt = '';
          scope.onFileChanged({ fileName: '.kyx', fileContent: undefined });
        }
        scope.$apply();
      });

      element.on("clear.bs.fileinput", function(e) {
        scope.onFileChanged({ fileName: '.kyx', fileContent: undefined });
      });
    }
  }
})