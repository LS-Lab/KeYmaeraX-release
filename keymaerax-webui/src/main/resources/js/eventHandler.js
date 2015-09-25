function eventHandler(obj) {
  if(obj.type === null) {
    alert("Trying to process a non-response in the event handler.")
  }
  
  if(obj.type == "LoginResponse") {
    if(obj.success) {
      document.cookie = obj.key + " = " + obj.value + "; path=/";
      document.location.href = "/dashboard.html"
    }
    else {
      alert("Login failed!");
    }
  }
}
