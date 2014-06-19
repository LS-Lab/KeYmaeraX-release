function D3TreeView(tree, client, targetDiv) {
  this.tree = tree;
  this.client = client;

  // VIEW INITIALIZATION
  this.margin = {top: 30, right: 20, bottom: 30, left: 20};
  this.width = 960 - this.margin.left - this.margin.right;
  this.barHeight = 20,
  this.barWidth = this.width * .8;
  this.i = 0;
  this.duration = 400;
  this.root;

  this.d3tree = d3.layout.tree().size([0,100]);

  this.diagonal = d3.svg.diagonal()
      .projection(function(d) { return [d.y, d.x]; });

  this.svg = d3.select(targetDiv).append("svg")
        .attr("width", this.width + this.margin.left + this.margin.right)
        .append("g")
        .attr("transform", "translate(" + this.margin.left + "," + this.margin.top + ")");

  this.redrawIn = function(id) {
    if(id != targetDiv.getAttribute('id')) {
      console.error("Redrawing in non-target div!")
    }
    return this.redraw();
  }

  this.redraw = function() {
    alert("not yet ported to TreeView interface.");
    //this.update();
  }

  this.update = function() { //note: old "source" is not this.tree.
    // Compute the flattened node list. TODO use d3.layout.hierarchy.
    var nodes = this.d3tree.nodes(root);

    var height = Math.max(500, nodes.length * barHeight + margin.top + margin.bottom);

    d3.select("svg")
        .attr("height", height);

    d3.select(self.frameElement)
        .style("height", height + "px");

    // Compute the "layout".
    nodes.forEach(function(n, i) {
      n.x = i * barHeight;
    });

    // Update the nodes…
    var node = svg.selectAll("g.node")
        .data(nodes, function(d) { return d.id || (d.id = ++i); });

    var nodeEnter = node.enter().append("g")
        .attr("class", "node")
        .attr("transform", function(d) { return "translate(" + source.y0 + "," + source.x0 + ")"; })
        .style("opacity", 1e-6);

    // Enter any new nodes at the parent's previous position.
    nodeEnter.append("rect")
        .attr("y", -barHeight / 2)
        .attr("height", barHeight)
        .attr("width", barWidth)
        .style("fill", color)
        .on("click", click);

    nodeEnter.append("text")
        .attr("dy", 3.5)
        .attr("dx", 5.5)
        .text(function(d) { if(d.hasOwnProperty("sequent")) return d.sequent; else if(d.hasOwnProperty("rule")) return d.rule; else return d.name ; });

    // Transition nodes to their new position.
    nodeEnter.transition()
        .duration(duration)
        .attr("transform", function(d) { return "translate(" + d.y + "," + d.x + ")"; })
        .style("opacity", 1);

    node.transition()
        .duration(duration)
        .attr("transform", function(d) { return "translate(" + d.y + "," + d.x + ")"; })
        .style("opacity", 1)
      .select("rect")
        .style("fill", color);

    // Transition exiting nodes to the parent's new position.
    node.exit().transition()
        .duration(duration)
        .attr("transform", function(d) { return "translate(" + source.y + "," + source.x + ")"; })
        .style("opacity", 1e-6)
        .remove();

    // Update the links…
    var link = svg.selectAll("path.link")
        .data(tree.links(nodes), function(d) { return d.target.id; });

    // Enter any new links at the parent's previous position.
    link.enter().insert("path", "g")
        .attr("class", "link")
        .attr("d", function(d) {
          var o = {x: source.x0, y: source.y0};
          return diagonal({source: o, target: o});
        })
      .transition()
        .duration(duration)
        .attr("d", diagonal);

    // Transition links to their new position.
    link.transition()
        .duration(duration)
        .attr("d", diagonal);

    // Transition exiting nodes to the parent's new position.
    link.exit().transition()
        .duration(duration)
        .attr("d", function(d) {
          var o = {x: source.x, y: source.y};
          return diagonal({source: o, target: o});
        })
        .remove();

    // Stash the old positions for transition.
    nodes.forEach(function(d) {
      d.x0 = d.x;
      d.y0 = d.y;
    });
  }
  
  // Toggle children on click.
  this.click = function(d) {
    if (d.children) {
      d._children = d.children;
      d.children = null;
    } else {
      d.children = d._children;
      d._children = null;
    }
    update(d);
  }
  this.color = function(d) {
    return d.hasOwnProperty("sequent")?"#aaaaaa": d._children ? "#323232" : d.children ? "#8C8C8C" : "#3D7178";
  }     	

  //this.onAdd = function(parentId, tree) {alert("add")}
  //this.onDelete = function(nodeId) {}
}


/*
 * `
  function update(source) {


}
*/
