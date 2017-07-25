angular.module('keymaerax.ui.directives').directive('k4FileUpload', function () {
  return {
    restrict: 'E',
    scope: {
      onFileConfirmed: '&'
    },
    templateUrl: 'templates/kyxupload.html',
    link: function(scope, element, attrs) {

      getFileExt = function(fileName) {
        var txtIdx = fileName.lastIndexOf('.txt'); //@note some browsers download our files as .kyx.txt
        var fn = txtIdx >= 0 ? fileName.substr(0, txtIdx) : fileName;
        return fn.substr(fn.lastIndexOf('.'), 4);
      }

      element.on("change.bs.fileinput", function(e) {
        scope.fileExt = (keyFile && keyFile.files && keyFile.files.length > 0
          ? getFileExt(keyFile.files[0].name)
          : '');
        scope.$apply();
      });

      scope.readFile = function(startProof) {
        var file = keyFile.files[0];
        var fr = new FileReader();
        var modelName = scope.fileExt == '.kyx' ? modelNameInput.value : undefined;
        fr.onerror = function(e) { alert("Error opening file: " + e.getMessage()); };
        fr.onload = function(e) {
          var fileContent = e.target.result;
          scope.onFileConfirmed({ fileName: file.name, fileContent: fileContent, modelName: modelName, startProof: startProof });
        };

        fr.readAsText(file);
      }
    }
  }
})