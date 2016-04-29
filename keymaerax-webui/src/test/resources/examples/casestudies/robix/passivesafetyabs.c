#include <math.h>
#include <stdbool.h>

/* function declaration */
long double A();
long double B();
long double V();
long double dx();
long double dxpost();
long double dy();
long double dypost();
long double ep();
long double tpost();
long double v();
long double vpost();
long double x();
long double xpost();
long double y();
long double ypost();

/* monitor */
bool monitor (long double w, long double r, long double xo, long double yo, long double apost, long double wpost, long double rpost, long double xopost, long double yopost, long double dxopost, long double dyopost) {
  /* Initial states for post variables */
  long double apost_0 = apost;
  long double wpost_0 = wpost;
  long double rpost_0 = rpost;
  long double xopost_0 = xopost;
  long double yopost_0 = yopost;
  long double dxopost_0 = dxopost;
  long double dyopost_0 = dyopost;

  return (((((dxopost_0)*(dxopost_0))) + (((dyopost_0)*(dyopost_0))))<=(((V())*(V()))))&&((((((0))<=(ep()))&&((v())>=((0))))&&((((((((((((((xopost)==(xo))&&((yopost)==(yo)))&&((dxopost)==(dxopost_0)))&&((dyopost)==(dyopost_0)))&&((xpost())==(x())))&&((ypost())==(y())))&&((dxpost())==(dx())))&&((dypost())==(dy())))&&((vpost())==(v())))&&((wpost)==(w)))&&((apost)==(-(B()))))&&((rpost)==(r)))&&((tpost())==((0)))))||((((v())==((0)))&&(((((0))<=(ep()))&&((v())>=((0))))&&((((((((((((((xopost)==(xo))&&((yopost)==(yo)))&&((dxopost)==(dxopost_0)))&&((dyopost)==(dyopost_0)))&&((xpost())==(x())))&&((ypost())==(y())))&&((dxpost())==(dx())))&&((dypost())==(dy())))&&((vpost())==(v())))&&((wpost)==((0))))&&((apost)==((0))))&&((rpost)==(r)))&&((tpost())==((0))))))||((((-(B()))<=(apost_0))&&((apost_0)<=(A())))&&(((rpost_0)!=((0)))&&((((wpost_0)*(rpost_0))==(v()))&&((((fabsl((x()) - (xopost_0)))>((((((v())*(v())))/(((2))*(B()))) + (((V())*(v()))/(B()))) + ((((A())/(B())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*((v()) + (V())))))))||((fabsl((y()) - (yopost_0)))>((((((v())*(v())))/(((2))*(B()))) + (((V())*(v()))/(B()))) + ((((A())/(B())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*((v()) + (V()))))))))&&(((((0))<=(ep()))&&((v())>=((0))))&&((((((((((((((xopost)==(xopost_0))&&((yopost)==(yopost_0)))&&((dxopost)==(dxopost_0)))&&((dyopost)==(dyopost_0)))&&((xpost())==(x())))&&((ypost())==(y())))&&((dxpost())==(dx())))&&((dypost())==(dy())))&&((vpost())==(v())))&&((wpost)==(wpost_0)))&&((apost)==(apost_0)))&&((rpost)==(rpost_0)))&&((tpost())==((0)))))))))));
}

