angular.module('keymaerax.controllers').controller('ControlledStabilityTemplateDialogCtrl',
  function($scope, $controller, $uibModal, $uibModalInstance, $window, $http,
    $route, $location, Models, sessionService, spinnerService, userId, template) {
  //@note inherit from ModelUploadCtrl, forward all parameters
  $controller('ModelUploadCtrl', {
    $scope: $scope,
    $http: $http,
    $route: $route,
    $uibModalInstance: $uibModalInstance,
    $uibModal: $uibModal,
    $location: $location,
    Models: Models,
    sessionService: sessionService,
    spinnerService: spinnerService,
    template: template
  });

  var mermaid = $window.mermaid;
  $scope.code = 'subgraph A\nMode1(x\'=1 & x<=5)\nMode2(x\'=-1 & x>=-5)\n\nMode1 -->|"?x>=5;x:=0;"| Mode2\nMode2 -->|"?x<=-5;x:=0;"| Mode1\nend\n\nInit("x:=0;") --> A';
  $scope.specKind = 'stability'

  function decode(encodedString) {
    var textArea = document.createElement('textarea');
    textArea.innerHTML = encodedString;
    return textArea.value;
  }

  $scope.getSpec = function(code, specKind) {
    var augmentedCode = 'flowchart TD\n' + code
    var ast = mermaid.parse(augmentedCode).parser.yy;
    var v = $.map(ast.getVertices(), function(e, k) { return { id: e.id, text: decode(e.text) }; });
    var e = $.map(ast.getEdges(), function(e, i) { return { start: e.start, end: e.end, text: decode(e.text) }; });
    var data = {
      code: code,
      vertices: v,
      edges: e
    };
    $http.post("models/users/" + userId + "/templates/controlledstability/create/" + specKind, data).then(function(response) {
      $scope.model.content = response.data.text;
    }).catch(function(err) {

    });
  }

  $scope.setSpecKind = function(specKind) {
    $scope.specKind = specKind;
    $scope.getSpec($scope.code, specKind);
  }

  $scope.onHAChange = function(code, svg) {
    $scope.getSpec(code, $scope.specKind);
  }
});

angular.module('keymaerax.controllers').controller('ModelUploadCtrl',
  function ($scope, $http, $route, $uibModalInstance, $uibModal, $location, Models, sessionService, spinnerService,
            template) {
     $scope.template = template;
     $scope.userId = sessionService.getUser();
     $scope.model = {
       modelName: undefined,
       modelId: undefined,
       content: $scope.template.text,
       savedContent: undefined,
       savedContentErrorText: ''
     };

     $scope.updateModelContentFromFile = function(fileName, fileContent) {
       $scope.model.content = fileContent;
       if (!fileContent || fileContent == '') $scope.model.content = $scope.template.text;
       if ($scope.numKyxEntries(fileContent) <= 0) {
         $scope.model.modelName = fileName.substring(0, fileName.indexOf('.'));
       }
       $scope.$digest();
     };

     /* Number of archive entries contained in `content`. */
     $scope.numKyxEntries = function(content) {
        // archives contain lemmas, theorems etc., e.g., search for matches: Theorem "...".
        var entryRegex = /(Theorem|Lemma|ArchiveEntry|Exercise)(\s*)\"[^\"]*\"/g;
        return (content && content.match(entryRegex) || []).length;
     };

     /* Number of tactic entries contained in `content`. */
     $scope.numKyxTactics = function(content) {
       var tacticRegex = /Tactic(\s*)\"[^\"]*\"/g;
       return (content && content.match(tacticRegex) || []).length;
     }

     $scope.saveContent = function(startProof) {
       var doStartProof = startProof && $scope.numKyxEntries($scope.model.content) <= 1 && $scope.numKyxTactics($scope.model.content) <= 0;
       if ($scope.model.modelId) {
         // update model at modelId
         $scope.updateContent($scope.userId, $scope.model.modelId, $scope.model.content, doStartProof);
       } else {
         // first-time save
         var url =  "user/" + sessionService.getUser() + "/modelupload/" + encodeURIComponent($scope.model.modelName);
         upload(url, $scope.model.content, doStartProof);
       }
     }

     $scope.updateContent = function(userid, modelid, content, startProof) {
       var data = {
         name: '',
         title: '',
         description: '',
         content: content
       };
       $http.post("user/" + userid + "/model/" + modelid + "/update", data).then(
         function(response) {
           $scope.model.savedContent = content;
           $scope.model.savedContentErrorText = response.data.errorText;
           if (startProof) $scope.startProof('');
         },
         function(error) {
           $scope.model.savedContent = content;
           $scope.model.savedContentErrorText = error.data.textStatus;
         }
       )
     }

     $scope.uploadContent = function(startProof) {
       if (startProof) {
         if ($scope.model.savedContent !== $scope.model.content) {
           var modalInstance = $uibModal.open({
             templateUrl: 'templates/modalMessageTemplate.html',
             controller: 'ModalMessageCtrl',
             size: 'md',
             resolve: {
               title: function() { return "Want to save changes?"; },
               message: function() { return "Do you want to save before starting the proof, or don't save and start the proof on the old model content?"; },
               mode: function() { return "yesnocancel"; },
               oktext: function() { return "Save"; },
               notext: function() { return "Don't save"; }
             }
           });
           modalInstance.result.then(
             function(result) {
               if (result == "ok") $scope.saveContent(startProof);
               else $scope.startProof($scope.model.savedContentErrorText);
             },
             function() {
               // cancel -> nothing to do, stay on dialog
             }
           );
         } else $scope.startProof($scope.model.savedContentErrorText);
       } else $scope.saveContent(startProof);
     }

     $scope.refreshModelList = function() {
       //Update the models list -- this should result in the view being updated?
       $http.get("models/users/" + sessionService.getUser() + "/").success(function(data) {
         Models.setModels(data);
       });
     }

     $scope.close = function() {
       if ($scope.model.savedContent !== $scope.model.content) {
         var modalInstance = $uibModal.open({
           templateUrl: 'templates/modalMessageTemplate.html',
           controller: 'ModalMessageCtrl',
           size: 'md',
           resolve: {
             title: function() { return "Want to save your changes?"; },
             message: function() { return "The editor has unsaved changes, do you want to save?"; },
             mode: function() { return "yesnocancel"; },
             oktext: function() { return "Save"; },
             notext: function() { return "Don't save"; }
           }
         });
         modalInstance.result.then(
           function(result) {
             if (result == "ok") $scope.uploadContent(false);
             $scope.refreshModelList();
             $uibModalInstance.close();
           },
           function() {
             // cancel -> nothing to do, stay on dialog
           }
         );
       } else {
         $scope.refreshModelList();
         $uibModalInstance.close();
       }
     };

     $scope.aceLoaded = function(editor) {
       editor.focus();
     }

     $scope.aceChanged = function(e) {
       var content = e[0];
       var editor = e[1];
       if (content.id == 1 && $scope.template.selectRange) {
         // first edit (id==1) inserts the initial template text; move cursor to beginning of comment and select
         editor.moveCursorTo($scope.template.selectRange.start.row, $scope.template.selectRange.start.column);
         editor.getSelection().setSelectionRange(new ace.Range(
          $scope.template.selectRange.start.row, $scope.template.selectRange.start.column,
          $scope.template.selectRange.end.row, $scope.template.selectRange.end.column), true);
       }
     }

     $scope.startProof = function(errorText) {
       if (errorText == '') {
         $scope.close();
         var uri = 'models/users/' + sessionService.getUser() + '/model/' + $scope.model.modelId + '/createProof'
         $http.post(uri, {proofName: '', proofDescription: ''}).
           success(function(data) { $location.path('proofs/' + data.id); }).
           error(function(data, status, headers, config) {
             console.log('Error starting new proof for model ' + modelId)
           });
       } else {
         var modalInstance = $uibModal.open({
           templateUrl: 'templates/modalMessageTemplate.html',
           controller: 'ModalMessageCtrl',
           size: 'md',
           resolve: {
             title: function() { return "Syntax error"; },
             message: function() { return "The model has syntax errors, please fix before starting a proof."; },
             mode: function() { return "ok"; }
           }
         });
       }
     }

     var upload = function(url, content, startProof) {
       spinnerService.show('caseStudyImportSpinner');
       $http.post(url, content)
         .then(function(response) {
           if (!response.data.success) {
             if (response.data.errorText) {
               showMessage($uibModal, "Error Uploading Model", response.data.errorText, "md")
             } else {
               showMessage($uibModal, "Unknown Error Uploading Model", "An unknown error that did not raise an uncaught exception occurred while trying to insert a model into the database. Perhaps see the server console output for more information.", "md")
             }
           } else { //Successfully uploaded model!
             $scope.model.modelId = response.data.modelId;
             $scope.model.savedContent = $scope.model.content;
             $scope.model.savedContentErrorText = response.data.errorText;
             if (startProof) $scope.startProof($scope.model.savedContentErrorText);
           }
         })
         .catch(function(err) {
           $uibModal.open({
             templateUrl: 'templates/parseError.html',
             controller: 'ParseErrorCtrl',
             size: 'fullscreen',
             resolve: {
               model: function () { return content; },
               error: function () { return err.data; }
           }});
         })
         .finally(function() { spinnerService.hide('caseStudyImportSpinner'); });
     }

     $scope.$watch('models',
        function () { return Models.getModels(); }
     );

     $scope.$emit('routeLoaded', {theview: 'models'});
});

angular.module('keymaerax.controllers').controller('ModelListCtrl', function ($scope, $http, $uibModal, $route,
    $location, FileSaver, Blob, Models, spinnerService, sessionService, firstTime) {
  $scope.models = Models.getModels();
  $scope.userId = sessionService.getUser();
  $scope.intro.firstTime = firstTime;
  $scope.workingDir = [];

  $scope.intro.introOptions = {
    steps: [
    {
        element: '#modelarchiving',
        intro: "Extract all models (with or without) their proofs into a .kyx archive file.",
        position: 'bottom'
    },
    {
        element: '#modelupload',
        intro: "Upload .kyx model files or .kyx archive files.",
        position: 'bottom'
    },
    {
        element: '#modeltutorialimport',
        intro: "Click 'Import' to add tutorials to your models overview.",
        position: 'bottom'
    },
    {
        element: '#modelopen',
        intro: "Inspect model definitions.",
        position: 'bottom'
    },
    {
        element: '#modelactions',
        intro: "Start new proofs, generate monitor conditions, and synthesize test cases here.",
        position: 'bottom'
    }
    ],
    showStepNumbers: false,
    exitOnOverlayClick: true,
    exitOnEsc: true,
    nextLabel: 'Next', // could use HTML in labels
    prevLabel: 'Previous',
    skipLabel: 'Exit',
    doneLabel: 'Done'
  }

  $scope.examples = [];
  $http.get("examples/user/" + $scope.userId + "/all").then(function(response) {
      $scope.examples = response.data;
  });

  $scope.templates = [];
  $http.get("templates/user/" + $scope.userId + "/all").then(function(response) {
      $scope.templates = response.data;
  });

  $scope.readModelList = function(folder) {
    if (folder.length > 0) {
      $http.get("models/users/" + $scope.userId + "/" + encodeURIComponent(folder.join("/"))).then(function(response) {
        Models.setModels(response.data);
      });
    } else {
      $http.get("models/users/" + $scope.userId + "/").then(function(response) {
        Models.setModels(response.data);
      });
    }
  }

  $scope.readModelList($scope.workingDir);

  $scope.setWorkingDir = function(folderIdx) {
    if (folderIdx == undefined) $scope.workingDir = [];
    else $scope.workingDir = $scope.workingDir.slice(0, folderIdx);
    $scope.readModelList($scope.workingDir);
  }

  $scope.open = function (modelId) {
    var modalInstance = $uibModal.open({
      templateUrl: 'partials/modeldialog.html',
      controller: 'ModelDialogCtrl',
      size: 'fullscreen',
      backdrop: 'static',
      keyboard: false,
      resolve: {
        userid: function() { return $scope.userId; },
        modelid: function() { return modelId; },
        proofid: function() { return undefined; },
        mode: function() { return Models.getModel(modelId).isExercise ? 'exercise' : 'edit'; }
      }
    });
  };

  $scope.openFolder = function(folder) {
    $scope.workingDir.push(folder);
    $scope.readModelList($scope.workingDir);
  }

  $scope.openNewModelDialog = function(template) {
    $uibModal.open({
      templateUrl: 'templates/modeluploaddialog.html',
      controller: 'ModelUploadCtrl',
      size: 'fullscreen',
      backdrop: 'static',
      keyboard: false,
      resolve: {
        template: function() { return template; }
      }
    });
  };

  $scope.openControlledStabilityModelTemplateDialog = function() {
    var modal = $uibModal.open({
      templateUrl: 'templates/hatemplatedialog.html',
      controller: 'ControlledStabilityTemplateDialogCtrl',
      size: 'fullscreen',
      backdrop: 'static',
      keyboard: false,
      resolve: {
        userId: function() { return $scope.userId; },
        template: function() { return { 'title': 'Controlled Stability Automaton' }; }
      }
    });
  };

  $scope.importRepo = function(repoUrl) {
    spinnerService.show('caseStudyImportSpinner');
    var userId = sessionService.getUser();
    $http.post("models/users/" + userId + "/importRepo", repoUrl).success(function(data) {
      $http.get("models/users/" + userId + "/").success(function(data) {
        Models.addModels(data);
        if($location.path() == "/models") {
          $route.reload();
        } else {
          $location.path( "/models" );
        }
      }).finally(function() { spinnerService.hide('caseStudyImportSpinner'); });
    }).error(function(err) {
       $uibModal.open({
         templateUrl: 'templates/modalMessageTemplate.html',
         controller: 'ModalMessageCtrl',
         size: 'lg',
         resolve: {
           title: function() { return "Error importing examples"; },
           message: function() { return err.textStatus; },
           mode: function() { return "ok"; }
         }
       });
    }).finally(function() { spinnerService.hide('caseStudyImportSpinner'); });
  };

  $scope.deleteModel = function(modelId) {
    $http.post("/user/" + sessionService.getUser() + "/model/" + modelId + "/delete").success(function(data) {
      if(data.errorThrown) {
        showCaughtErrorMessage($uibModal, data, "Model Deleter")
      } else {
        console.log("Model " + modelId + " was deleted. Getting a new model list and reloading the route.")
        $scope.readModelList($scope.workingDir);
      }
    })
  };

  $scope.downloadModel = function(modelid) {
    $http.get("user/" + $scope.userId + "/model/" + modelid).then(function(response) {
      var modelName = response.data.name;
      var fileContent = new Blob([response.data.keyFile], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(fileContent, modelName + '.kyx');
    });
  }

  currentDateString = function() {
    var today = new Date();
    var dd = today.getDate();
    var mm = today.getMonth() + 1; //@note January is 0
    var yyyy = today.getFullYear();

    if(dd < 10) dd = '0' + dd
    if(mm < 10) mm='0'+mm
    return mm + dd + yyyy;
  }

  $scope.downloadAllModels = function() {
    spinnerService.show('modelProofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/downloadAllModels/noProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, 'models_' + currentDateString() + '.kyx');
    })
    .finally(function() { spinnerService.hide('modelProofExportSpinner'); });
  }

  $scope.downloadModels = function() {
    spinnerService.show('modelProofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/downloadAllModels/noProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, 'models_' + currentDateString() + '.kyx');
    })
    .finally(function() { spinnerService.hide('modelProofExportSpinner'); });
  }

  //@note almost duplicate of proofs.js downloadAllProofs
  $scope.downloadAllProofs = function() {
    spinnerService.show('modelProofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/downloadAllModels/withProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, 'proofs_'+ currentDateString() +'.kyx');
    })
    .finally(function() { spinnerService.hide('modelProofExportSpinner'); });
  }

  //@note duplicate of proofs.js downloadModelProofs
  $scope.downloadModelProofs = function(modelId) {
    spinnerService.show('modelProofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/model/" + modelId + "/downloadProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, modelId + '_' + currentDateString() + '.kyx');
    })
    .finally(function() { spinnerService.hide('modelProofExportSpinner'); });
  }

  $scope.deleteAll = function() {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/deleteallmodelsdialog.html',
        controller: 'DeleteAllModelsDialogCtrl',
        size: 'sm'
      });

      modalInstance.result.then(function () {
        // modal ok
        spinnerService.show('modelDeleteAllSpinner');
        $http.get("/models/user/" + $scope.userId + "/delete/all").then(function(response) {
           Models.setModels([]);
        })
        .finally(function() { spinnerService.hide('modelDeleteAllSpinner'); });
      }, function () {
        // modal dismissed
      });
    }

  $scope.openTactic = function (modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/modeltacticdialog.html',
        controller: 'ModelTacticDialogCtrl',
        size: 'fullscreen',
        resolve: {
          userid: function() { return $scope.userId; },
          modelid: function () { return modelid; }
        }
      });
  };

  $scope.runTactic = function (modelid) {
    $http.post("user/" + $scope.userId + "/model/" + modelid + "/tactic/run").then(function(response) {
        if (respnse.data.errorThrown) showCaughtErrorMessage($uibModal, response.data, "Error While Running Tactic");
        else console.log("Done running tactic");
    });
  }

  $scope.testsynthesis = function(modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'templates/testsynthesis.html',
        controller: 'TestSynthCtrl',
        size: 'lg',
        resolve: {
          userid: function() { return $scope.userId; },
          modelid: function() { return modelid; }
        }
      })
    }

  $scope.$watch('models',
      function (newModels) { if (newModels) Models.setModels(newModels); }
  );
  $scope.$emit('routeLoaded', {theview: 'models'});
});

angular.module('keymaerax.controllers').filter("unique", function() {
  return function(items, property) {
    var result = [];
    var propVals = [];
    angular.forEach(items, function(item) {
      var propVal = item[property];
      if (propVals.indexOf(propVal) === -1) {
        propVals.push(propVal);
        result.push(item);
      }
    });
    return result;
  };
});

angular.module('keymaerax.controllers').controller('ModelDialogCtrl',
    function ($scope, $route, $http, $uibModal, $uibModalInstance, $location, Models, userid, modelid, proofid, mode) {
  $scope.mode = mode;
  $scope.proofId = proofid;
  $scope.model = undefined;         // model with edits
  $scope.origModel = undefined;     // original model from database
  $scope.save = {
    cmd: undefined,                 // save command: set on submit buttons
    editable: (mode === 'exercise' || mode === 'proofedit'),
    editor: undefined
  }

  $http.get("user/" + userid + "/model/" + modelid).then(function(response) {
    $scope.model = response.data;
    $scope.model.showModelIllustrations = true;
    $scope.origModel = JSON.parse(JSON.stringify(response.data)); // deep copy
  });

  $scope.aceLoaded = function(editor) {
    editor.setReadOnly(!$scope.save.editable);
    $scope.save.editor = editor;
  }

  $scope.enableEditing = function() {
    $scope.modelDataForm.$show();
    $scope.save.editor.setReadOnly(false);
  }

  /** Deletes all proofs of the model */
  $scope.deleteModelProofSteps = function(onSuccess) {
    $http.post('user/' + userid + "/model/" + modelid + "/deleteProofSteps").success(function(data) {
      if (data.success) {
        $scope.model.numAllProofSteps = 0;
        onSuccess();
      }
    });
  }

  $scope.checkModelData = function() {
    if ($scope.origModel.name !== $scope.model.name || $scope.origModel.title !== $scope.model.title
     || $scope.origModel.description !== $scope.model.description
     || $scope.origModel.keyFile !== $scope.model.keyFile) {
      if ($scope.save.cmd == $scope.cancel) {
        var modalInstance = $uibModal.open({
          templateUrl: 'templates/modalMessageTemplate.html',
          controller: 'ModalMessageCtrl',
          size: 'md',
          resolve: {
            title: function() { return "Want to save your changes?"; },
            message: function() { return "Saving tries to rerun existing proofs, which may need adaptation afterwards"; },
            mode: function() { return "yesnocancel"; },
            oktext: function() { return "Save"; },
            notext: function() { return "Don't save"; }
          }
        });
        modalInstance.result.then(
          function(result) {
            if (result == "ok") {
              $scope.save.cmd = $scope.redoProofAndClose;
              $scope.deleteModelProofSteps($scope.uploadModel);
            } else if ($scope.save.cmd) $scope.save.cmd();
          },
          function() {
            // cancel -> nothing to do, stay on dialog
          }
        );
      } else if ($scope.save.cmd == $scope.refreshModels || $scope.save.cmd == $scope.redoProof) {
        $scope.deleteModelProofSteps($scope.uploadModel);
      }
      return false;           // form will not close automatically -> $scope.save.cmd() on successful parsing
    } else {
      if ($scope.save.cmd) $scope.save.cmd();
      return true;
    }
  }

  $scope.uploadModel = function() {
    var data = {
      name: $scope.model.name,
      title: $scope.model.title,
      description: $scope.model.description,
      content: $scope.model.keyFile
    };
    $http.post("user/" + userid + "/model/" + modelid + "/update", data).then(function(response) {
      var model = Models.getModel(modelid);
      if (model) {
        // model === undefined on proof page reload
        model.name = response.data.name;
        model.title = response.data.title;
        model.description = response.data.description;
        model.keyFile = response.data.content;
      }
      $scope.origModel = JSON.parse(JSON.stringify($scope.model)); // deep copy
      $scope.save.cmd();
    })
    .catch(function(err) {
      $scope.modelDataForm.$setError("", err.data.textStatus);
      $uibModal.open({
        templateUrl: 'templates/parseError.html',
        controller: 'ParseErrorCtrl',
        size: 'fullscreen',
        resolve: {
          model: function () { return $scope.model.keyFile; },
          error: function () { return err.data; }
      }});
    });
  }

  $scope.startProof = function() {
    var uri = 'models/users/' + userid + '/model/' + $scope.model.id + '/createProof'
    $http.post(uri, {proofName: '', proofDescription: ''}).
      success(function(data) {
        $uibModalInstance.close();
        $location.path('proofs/' + data.id);
      }).
      error(function(data, status, headers, config) {
        $scope.modelDataForm.$setError("", data.textStatus);
        $uibModal.open({
          templateUrl: 'templates/modalMessageTemplate.html',
          controller: 'ModalMessageCtrl',
          size: 'md',
          resolve: {
            title: function() { return "Syntax error"; },
            message: function() { return "The model has syntax errors, please fix before starting a proof."; },
            mode: function() { return "ok"; }
          }
        });
      });
  }

  $scope.redoProof = function() {
    $route.reload();
  }

  $scope.redoProofAndClose = function() {
      $route.reload();
      $uibModalInstance.close();
    }

  $scope.modelIsComplete = function() { return $scope.model && $scope.model.keyFile.indexOf('__________') < 0; }

  $scope.checkName = function(name) {
    var nameIsUnique = $.grep(Models.getModels(), function(m) { return m.name === name && m.id !== modelid; }).length == 0;
    if (name === undefined || name === "") return "Name is mandatory. Please enter a name.";
    else if (!nameIsUnique) return "Model with name " + name + " already exists. Please choose a different name."
    else return true;
  }

  $scope.cancel = function() {
    $scope.model.keyFile = $scope.origModel.keyFile;
    $uibModalInstance.close();
  };

  $scope.refreshModels = function() {
    // Update the models list
    $http.get("models/users/" + userid + "/").success(function(data) {
      Models.setModels(data);
    });
  };

  $scope.showModelIllustrations = function(show) {
    $scope.model.showModelIllustrations = show;
    $scope.$apply(); // required since called from standard JavaScript onerror
  }
});

angular.module('keymaerax.controllers').controller('ModelTacticDialogCtrl', function ($scope, $http, $uibModalInstance, userid, modelid) {
  $http.get("user/" + userid + "/model/" + modelid + "/tactic").then(function(response) {
      $scope.modelId = modelid;
      $scope.tactic = response.data;
  });

  $scope.ok = function () { $uibModalInstance.close(); };
});

angular.module('keymaerax.controllers').controller('DeleteAllModelsDialogCtrl', function ($scope, $uibModalInstance) {
  $scope.ok = function () { $uibModalInstance.close(); };
  $scope.cancel = function () { $uibModalInstance.dismiss('cancel'); };
});
