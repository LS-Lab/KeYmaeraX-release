angular.module('progressMeter', [])
  .directive('k4ProgressMeter', function() {
    function link(scope, element, attrs) {
      var progress = attrs.progress,
          total = attrs.total,
          width = (attrs.width == undefined ? 40 : attrs.width),
          height = (attrs.height == undefined ? 40 : attrs.height),
          startAngle = (attrs.startAngle == undefined ? 0 : attrs.startAngle),
          radiusRatio = (attrs.radiusRatio == undefined ? .75 : attrs.radiusRatio),
          outerRadius = d3.min([width,height])/2,
          innerRadius = outerRadius * radiusRatio,
          format = (attrs.format == undefined ? 'progress-of-total' : attrs.format),
          formatPercent = d3.format(".0%");

      var arc = d3.svg.arc()
         .startAngle(startAngle)
         .innerRadius(innerRadius)
         .outerRadius(outerRadius);

      var svg = d3.select(element[0]).append("svg")
         .attr("width", width)
         .attr("height", height)
       .append("g")
         .attr("transform", "translate(" + width / 2 + "," + height / 2 + ")");

      var meter = svg.append("g")
         .attr("class", "progress-meter");

      meter.append("path")
         .attr("class", "background")
         .attr("d", arc.endAngle(2 * Math.PI));

      var foreground = meter.append("path")
         .attr("class", "foreground");

      var text = meter.append("text")
         .attr("text-anchor", "middle")
         .attr("dy", ".35em");

      foreground.attr("d", arc.endAngle(2 * Math.PI * progress / total));
      if (format == 'percentage') {
         text.text(formatPercent(progress/total));
      } else {
         text.text(progress + "/" + total);
      }
    }

    return {
      restrict: 'AE',
      link: link
    };
  });