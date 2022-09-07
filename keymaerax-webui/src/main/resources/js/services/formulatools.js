angular.module('keymaerax.services').factory('formulaTools', [function() {

  return {
    formatSpecialNotation: function(html) {
      return html.replace(/(\w+)(?:(\(\))|(\(\|\|\))|({\|\^@\|}))/g,
        function (match, name, fnParens, fnctlParens, sysParens, offset, string) {
          if (name.startsWith('A__')) return name.replace(/A__(\d+)/g,
              function (match, i, offset, string) {
                return '<span class="k4-assumptions-cart fa fa-shopping-cart small text-muted"><sub>' + i + '</sub></span>';
              })
          else if (fnParens) return '<span class="k4-nullary-fn">' + name + '</span>';
          else if (fnctlParens) return '<span class="k4-functional">' + name + '</span>';
          else if (sysParens) return '<span class="k4-system-const">' + name + '</span>';
          else return html;
        });
    },
    formatPlainSpecialNotation: function(text) {
      return text.replace(/(\w+)(?:(\(\))|({\|\^@\|}))/g, function(match, name, fnParens, sysParens, offset, string) {
        return name;
      });
    },
    formatSubscriptIndex: function(html) {
      return html;
      //@note disabled for now for proper copy-paste behavior
//              return html.replace(/_(\d+)/g, function(match, idx, parens, offset, string) {
//                return '<sub>' + idx + '</sub>';
//              });
    }
  }
}])