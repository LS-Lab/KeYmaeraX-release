#include <math.h>
#include <stdbool.h>

typedef struct parameters {
  long double A;
  long double B;
  long double V;
  long double dx;
  long double dxpost;
  long double dy;
  long double dypost;
  long double ep;
  long double tpost;
  long double v;
  long double vpost;
  long double x;
  long double xpost;
  long double y;
  long double ypost;
} parameters;

typedef struct state {
  long double a;
  long double dxo;
  long double dyo;
  long double r;
  long double w;
  long double xo;
  long double yo;
} state;

/* monitor */
bool monitor (state& curr, parameters& params) {
  static state pre = curr;
  int result = (((((curr.dxo)*(curr.dxo))) + (((curr.dyo)*(curr.dyo))))<=(((params.V)*(params.V))))&&((((((0))<=(params.ep))&&((params.v)>=((0))))&&((((((((((((((curr.xo)==(pre.xo))&&((curr.yo)==(pre.yo)))&&((curr.dxo)==(curr.dxo)))&&((curr.dyo)==(curr.dyo)))&&((params.xpost)==(params.x)))&&((params.ypost)==(params.y)))&&((params.dxpost)==(params.dx)))&&((params.dypost)==(params.dy)))&&((params.vpost)==(params.v)))&&((curr.w)==(pre.w)))&&((curr.a)==(-(params.B))))&&((curr.r)==(pre.r)))&&((params.tpost)==((0)))))||((((params.v)==((0)))&&(((((0))<=(params.ep))&&((params.v)>=((0))))&&((((((((((((((curr.xo)==(pre.xo))&&((curr.yo)==(pre.yo)))&&((curr.dxo)==(curr.dxo)))&&((curr.dyo)==(curr.dyo)))&&((params.xpost)==(params.x)))&&((params.ypost)==(params.y)))&&((params.dxpost)==(params.dx)))&&((params.dypost)==(params.dy)))&&((params.vpost)==(params.v)))&&((curr.w)==((0))))&&((curr.a)==((0))))&&((curr.r)==(pre.r)))&&((params.tpost)==((0))))))||((((-(params.B))<=(curr.a))&&((curr.a)<=(params.A)))&&(((curr.r)!=((0)))&&((((curr.w)*(curr.r))==(params.v))&&((((fabsl((params.x) - (curr.xo)))>((((((params.v)*(params.v)))/(((2))*(params.B))) + (((params.V)*(params.v))/(params.B))) + ((((params.A)/(params.B)) + ((1)))*((((params.A)/((2)))*(((params.ep)*(params.ep)))) + ((params.ep)*((params.v) + (params.V)))))))||((fabsl((params.y) - (curr.yo)))>((((((params.v)*(params.v)))/(((2))*(params.B))) + (((params.V)*(params.v))/(params.B))) + ((((params.A)/(params.B)) + ((1)))*((((params.A)/((2)))*(((params.ep)*(params.ep)))) + ((params.ep)*((params.v) + (params.V))))))))&&(((((0))<=(params.ep))&&((params.v)>=((0))))&&((((((((((((((curr.xo)==(curr.xo))&&((curr.yo)==(curr.yo)))&&((curr.dxo)==(curr.dxo)))&&((curr.dyo)==(curr.dyo)))&&((params.xpost)==(params.x)))&&((params.ypost)==(params.y)))&&((params.dxpost)==(params.dx)))&&((params.dypost)==(params.dy)))&&((params.vpost)==(params.v)))&&((curr.w)==(curr.w)))&&((curr.a)==(curr.a)))&&((curr.r)==(curr.r)))&&((params.tpost)==((0)))))))))));
  pre = curr;
  return result;
}
