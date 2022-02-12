#include <math.h>
#include <stdbool.h>

/** Model parameters */
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

/** State (control choices, environment measurements etc.) */
typedef struct state {
  long double a;
  long double dxo;
  long double dyo;
  long double r;
  long double w;
  long double xo;
  long double yo;
} state;

/** Values for resolving non-deterministic assignments in control code */
typedef struct input input;

/** Monitor verdict: `id` identifies the violated monitor sub-condition, `val` the safety margin (<0 violated, >=0 satisfied). */
typedef struct verdict { int id; long double val; } verdict;


verdict checkInit(const state* const init, const parameters* const params) {
  bool initOk = 1.0L;
  verdict result = { .id=(initOk ? 1 : -1), .val=(initOk ? 1.0L : -1.0L) };
  return result;
}

/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */
verdict boundaryDist(state pre, state curr, const parameters* const params) {
  verdict result = { .id=((((curr.dxo_0)*(curr.dxo_0))+((curr.dyo_0)*(curr.dyo_0)) <= (params->V)*(params->V)) && ((((0.0L <= params->ep) && (params->v >= 0.0L)) && (((((((((((((curr.xo == pre.xo) && (curr.yo == pre.yo)) && (curr.dxo == curr.dxo_0)) && (curr.dyo == curr.dyo_0)) && (params->x == params->x)) && (params->y == params->y)) && (params->dx == params->dx)) && (params->dy == params->dy)) && (params->v == params->v)) && (curr.w == pre.w)) && (curr.a == -(params->B))) && (curr.r == pre.r)) && (params->t == 0.0L))) || (((params->v == 0.0L) && (((0.0L <= params->ep) && (params->v >= 0.0L)) && (((((((((((((curr.xo == pre.xo) && (curr.yo == pre.yo)) && (curr.dxo == curr.dxo_0)) && (curr.dyo == curr.dyo_0)) && (params->x == params->x)) && (params->y == params->y)) && (params->dx == params->dx)) && (params->dy == params->dy)) && (params->v == params->v)) && (curr.w == 0.0L)) && (curr.a == 0.0L)) && (curr.r == pre.r)) && (params->t == 0.0L)))) || (((-(params->B) <= curr.a_0) && (curr.a_0 <= params->A)) && ((curr.r_0 != 0.0L) && (((curr.w_0)*(curr.r_0) == params->v) && (((fabsl((params->x)-(curr.xo_0)) > ((((params->v)*(params->v))/((2.0L)*(params->B)))+(((params->V)*(params->v))/(params->B)))+((((params->A)/(params->B))+(1.0L))*((((params->A)/(2.0L))*((params->ep)*(params->ep)))+((params->ep)*((params->v)+(params->V)))))) || (fabsl((params->y)-(curr.yo_0)) > ((((params->v)*(params->v))/((2.0L)*(params->B)))+(((params->V)*(params->v))/(params->B)))+((((params->A)/(params->B))+(1.0L))*((((params->A)/(2.0L))*((params->ep)*(params->ep)))+((params->ep)*((params->v)+(params->V))))))) && (((0.0L <= params->ep) && (params->v >= 0.0L)) && (((((((((((((curr.xo == curr.xo_0) && (curr.yo == curr.yo_0)) && (curr.dxo == curr.dxo_0)) && (curr.dyo == curr.dyo_0)) && (params->x == params->x)) && (params->y == params->y)) && (params->dx == params->dx)) && (params->dy == params->dy)) && (params->v == params->v)) && (curr.w == curr.w_0)) && (curr.a == curr.a_0)) && (curr.r == curr.r_0)) && (params->t == 0.0L))))))))) ? 1 : -1), .val=((((curr.dxo_0)*(curr.dxo_0))+((curr.dyo_0)*(curr.dyo_0)) <= (params->V)*(params->V)) && ((((0.0L <= params->ep) && (params->v >= 0.0L)) && (((((((((((((curr.xo == pre.xo) && (curr.yo == pre.yo)) && (curr.dxo == curr.dxo_0)) && (curr.dyo == curr.dyo_0)) && (params->x == params->x)) && (params->y == params->y)) && (params->dx == params->dx)) && (params->dy == params->dy)) && (params->v == params->v)) && (curr.w == pre.w)) && (curr.a == -(params->B))) && (curr.r == pre.r)) && (params->t == 0.0L))) || (((params->v == 0.0L) && (((0.0L <= params->ep) && (params->v >= 0.0L)) && (((((((((((((curr.xo == pre.xo) && (curr.yo == pre.yo)) && (curr.dxo == curr.dxo_0)) && (curr.dyo == curr.dyo_0)) && (params->x == params->x)) && (params->y == params->y)) && (params->dx == params->dx)) && (params->dy == params->dy)) && (params->v == params->v)) && (curr.w == 0.0L)) && (curr.a == 0.0L)) && (curr.r == pre.r)) && (params->t == 0.0L)))) || (((-(params->B) <= curr.a_0) && (curr.a_0 <= params->A)) && ((curr.r_0 != 0.0L) && (((curr.w_0)*(curr.r_0) == params->v) && (((fabsl((params->x)-(curr.xo_0)) > ((((params->v)*(params->v))/((2.0L)*(params->B)))+(((params->V)*(params->v))/(params->B)))+((((params->A)/(params->B))+(1.0L))*((((params->A)/(2.0L))*((params->ep)*(params->ep)))+((params->ep)*((params->v)+(params->V)))))) || (fabsl((params->y)-(curr.yo_0)) > ((((params->v)*(params->v))/((2.0L)*(params->B)))+(((params->V)*(params->v))/(params->B)))+((((params->A)/(params->B))+(1.0L))*((((params->A)/(2.0L))*((params->ep)*(params->ep)))+((params->ep)*((params->v)+(params->V))))))) && (((0.0L <= params->ep) && (params->v >= 0.0L)) && (((((((((((((curr.xo == curr.xo_0) && (curr.yo == curr.yo_0)) && (curr.dxo == curr.dxo_0)) && (curr.dyo == curr.dyo_0)) && (params->x == params->x)) && (params->y == params->y)) && (params->dx == params->dx)) && (params->dy == params->dy)) && (params->v == params->v)) && (curr.w == curr.w_0)) && (curr.a == curr.a_0)) && (curr.r == curr.r_0)) && (params->t == 0.0L))))))))) ? 1.0L : -1.0L) }; return result;
}

/* Evaluates monitor condition in prior and current state */
bool monitorSatisfied(state pre, state curr, const parameters* const params) {
  return boundaryDist(pre,curr,params).val >= 0.0L;
}

/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */
state monitoredCtrl(state curr, const parameters* const params, const input* const in,
                    state (*ctrl)(state,const parameters* const,const input* const),
                    state (*fallback)(state,const parameters* const,const input* const)) {
  state pre = curr;
  state post = (*ctrl)(pre,params,in);
  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);
  else return post;
}