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

typedef struct input input;

/* Computes distance to safety boundary on prior and current state (negative == safe, positive == unsafe) */
long double boundaryDist(state pre, state curr, const parameters* const params) {
  return (((((curr.dxo)*(curr.dxo))) + (((curr.dyo)*(curr.dyo))))<=(((params->V)*(params->V))))&&((((((0))<=(params->ep))&&((params->v)>=((0))))&&((((((((((((((curr.xo)==(pre.xo))&&((curr.yo)==(pre.yo)))&&((curr.dxo)==(curr.dxo)))&&((curr.dyo)==(curr.dyo)))&&((params->x)==(params->x)))&&((params->y)==(params->y)))&&((params->dx)==(params->dx)))&&((params->dy)==(params->dy)))&&((params->v)==(params->v)))&&((curr.w)==(pre.w)))&&((curr.a)==(-(params->B))))&&((curr.r)==(pre.r)))&&((params->t)==((0)))))||((((params->v)==((0)))&&(((((0))<=(params->ep))&&((params->v)>=((0))))&&((((((((((((((curr.xo)==(pre.xo))&&((curr.yo)==(pre.yo)))&&((curr.dxo)==(curr.dxo)))&&((curr.dyo)==(curr.dyo)))&&((params->x)==(params->x)))&&((params->y)==(params->y)))&&((params->dx)==(params->dx)))&&((params->dy)==(params->dy)))&&((params->v)==(params->v)))&&((curr.w)==((0))))&&((curr.a)==((0))))&&((curr.r)==(pre.r)))&&((params->t)==((0))))))||((((-(params->B))<=(curr.a))&&((curr.a)<=(params->A)))&&(((curr.r)!=((0)))&&((((curr.w)*(curr.r))==(params->v))&&((((fabsl((params->x) - (curr.xo)))>((((((params->v)*(params->v)))/(((2))*(params->B))) + (((params->V)*(params->v))/(params->B))) + ((((params->A)/(params->B)) + ((1)))*((((params->A)/((2)))*(((params->ep)*(params->ep)))) + ((params->ep)*((params->v) + (params->V)))))))||((fabsl((params->y) - (curr.yo)))>((((((params->v)*(params->v)))/(((2))*(params->B))) + (((params->V)*(params->v))/(params->B))) + ((((params->A)/(params->B)) + ((1)))*((((params->A)/((2)))*(((params->ep)*(params->ep)))) + ((params->ep)*((params->v) + (params->V))))))))&&(((((0))<=(params->ep))&&((params->v)>=((0))))&&((((((((((((((curr.xo)==(curr.xo))&&((curr.yo)==(curr.yo)))&&((curr.dxo)==(curr.dxo)))&&((curr.dyo)==(curr.dyo)))&&((params->x)==(params->x)))&&((params->y)==(params->y)))&&((params->dx)==(params->dx)))&&((params->dy)==(params->dy)))&&((params->v)==(params->v)))&&((curr.w)==(curr.w)))&&((curr.a)==(curr.a)))&&((curr.r)==(curr.r)))&&((params->t)==((0))))))))))) ? 0.0 : 1.0;
}

/* Evaluates monitor condition in prior and current state */
bool monitorSatisfied(state pre, state curr, const parameters* const params) {
  return boundaryDist(pre,curr,params) <= 0.0;
}

/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */
state monitoredCtrl(state curr, const parameters* const params, const input* const in,
                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const)) {
  state pre = curr;
  state post = (*ctrl)(pre,params,in);
  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);
  else return post;
}
