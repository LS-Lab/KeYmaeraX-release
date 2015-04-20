function loadFile(userid, file) {
    alert(file)
    var fr = new FileReader();
    fr.onerror = function(e) { alert("Could not even open your file: " + e.getMessage()); }

    fr.onload = function(e) {
      ApiClient.createNewProof(userid, e.target.result,
      function(resp) {
        alert("yes!!!")
//		  ClientState.proofid = resp.proofid;
//		  update(root = resp.proofTree.model);
		});
    }

    fr.readAsText(file);
  }

// hardcoded for testing
function loadFakeFile() {
    jQuery.get('examples/ETCS-safety.key', function(data) {
        ApiClient.createNewUser(0);
        ApiClient.createNewProof(0, data,
            function(resp) {
                // TODO implement the corresponding GET request; also: no longer transmit proof tree
                window.location.href = "proof.html?proofid=" + resp.proofid;
            }
        );
    });
}