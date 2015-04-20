angular.module('proofProgressChart', [])
  .directive('k4ProofProgressChart', function() {
    function link(scope, element, attrs) {
        var stack = d3.layout.stack();

        // TODO attrs
        var margin = {top: 40, right: 10, bottom: 20, left: 10},
            width = 230 - margin.left - margin.right,
            height = (150 - margin.top - margin.bottom)/2;

        var x = d3.scale.ordinal()
            .rangeRoundBands([0, width], .08);

        var xAxis = d3.svg.axis()
            .scale(x)
            .tickSize(0)
            .tickPadding(6)
            .orient("bottom");

        var parent = d3.select(element[0]);

        var svg = parent.append("svg")
            .attr("width", width + margin.left + margin.right)
            .attr("height", height + margin.top + margin.bottom)
            .append("g")
            .attr("transform", "translate(" + margin.left + "," + margin.top + ")");

        var svgclosed = parent.append("svg")
            .attr("width", width + margin.left + margin.right)
            .attr("height", height + margin.top + margin.bottom)
            .append("g")
            .attr("transform", "translate(" + margin.left + ",0)");

        // open steps
        d3.json("examples/proofprogress.json", function(error, layersdata) {
            var layers = stack(layersdata.slice(1));
            var yStackMax = d3.max(layers, function(layer) { return d3.max(layer, function(d) { return d.y0 + d.y; }); });
            var yStackMin = d3.min(layersdata.slice(0,1), function(layer) { return d3.min(layer, function(d) { return d.y; }); });

            var yMax = d3.max([yStackMax, -yStackMin]);

            var color = d3.scale.linear()
                .domain([0, yMax - 1])
                .range(["#aad", "#556"]);

            var xTickLabels = d3.scale.ordinal()
                .domain(layersdata.slice(0,1)[0].map(function(d) { return d.group; }))
                .range(layersdata.slice(0,1)[0].map(function(d) { return d.rule; }));

            x.domain(layersdata.slice(0,1)[0].map(function(d) { return d.group; }));
            xAxis.tickFormat(function(d) { return xTickLabels(d); })

            var y = d3.scale.linear()
                .domain([0, yMax])
                .range([height, 0]);

            var layer = svg.selectAll(".layer")
                .data(layers)
              .enter().append("g")
                .attr("class", "layer")
                .style("fill", function(d, i) { return color(i); });

            var rect = layer.selectAll("rect")
                .data(function(d) { return d; })
              .enter().append("rect")
                .attr("x", function(d) { return x(d.group); })
                .attr("y", height )
                .attr("width", x.rangeBand())
                .attr("height", 0 )
                // TODO correct event is raised, event handler is executed, but popover in event handler not working yet
                //.on("click", function(d) { return scope.onSeqClick.call(this, { event: { d:d } }); });
                .on("click", function(d) { togglePopover.call(this,d); });
                //.on("mouseover", function (d) { showPopover.call(this, d); })
                //.on("mouseout",  function (d) { removePopovers(); })

            rect.transition()
                .delay(function(d, i) { return i * 10; })
                .attr("y", function(d) { return y(d.y0 + d.y); })
                .attr("height", function(d) { return y(d.y0) - y(d.y0 + d.y); });

            svg.append("g")
                .attr("class", "x axis")
                .attr("transform", "translate(0," + height + ")")
                .call(xAxis);
        });

        // closed steps
        d3.json("examples/proofprogress.json", function(error, layersdata) {
            var layers = layersdata.slice(0,1);
            var yStackMax = d3.max(stack(layersdata.slice(1)), function(layer) { return d3.max(layer, function(d) { return d.y0 + d.y; }); });
            var yStackMin = d3.min(layers, function(layer) { return d3.min(layer, function(d) { return d.y; }); });

            var yMin = d3.min([-yStackMax, yStackMin]);

            x.domain(layers[0].map(function(d) { return d.group; }));

            var y = d3.scale.linear()
                .domain([yMin, 0])
                .range([height, 0]);

            var layer = svgclosed.selectAll(".layer")
                .data(layers)
                .enter().append("g")
                .attr("class", "layer");
                //.style("fill", function(d, i) { return color(i); });

            var rect = layer.selectAll("g")
                .data(function(d) { return d; })
              .enter().append("g");
                //.attr("transform", function(d, i) { return "translate(" + i * x.rangeBand() + ", 0)"; });

            rect.append("rect")
                .attr("class", "closedstep")
                .attr("x", function(d) { return x(d.group); })
                .attr("y", 0)
                .attr("width", x.rangeBand())
                .attr("height", function(d) { return Math.abs(y(d.y) - y(0)); });
    /*
            rect.append("foreignObject")
                .attr("x", function(d) { return x(d.group); })
                .attr("y", height)
                .attr("width", width)
                //.attr("height", height)
                .append("xhtml:body")
                .html('<div class="glyphicon glyphicon-ok"></div>');*/
        });
    }

    return {
      restrict: 'AE',
      link: link,
      scope: {
        onSeqClick: '&',
        onSeqMouseOver: '&',
        onSeqMouseOut: '&'
      }
      // controller: controller
    };
  });

function removePopovers () {
  $('.popover').each(function() {
    $(this).remove();
  });
}

function showPopover (d) {
  $(this).popover({
    title: "Prover Interaction",
    placement: 'auto top',
    container: 'body',
    trigger: 'manual',
    html : true,
    content: function() {
      return "Sequent: " + d.id +
             "<br/>Rule: " + d.rule; }
  });
  $(this).popover('show')
}

function togglePopover (d) {
  $(this).popover({
    title: "Background Progress",
    placement: 'auto top',
    container: 'body',
    trigger: 'manual',
    html : true,
    content: function() {
      return $('#popover_content_wrapper').html(); }
  });
  $(this).popover('toggle');
}
