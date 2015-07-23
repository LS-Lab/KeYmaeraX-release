/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.codegen.{CodeGenerationException, CGenerator}

/**
 * Created by ran on 6/22/15.
 * @author Ran Ji
 */
class CCodeGeneratorTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  var cGen: CGenerator = null

  override def beforeEach() = {
    cGen = new CGenerator
  }

  override def afterEach() = {
    cGen = null
  }

  // terms

  "Numbers" should "compile floating point" in {
    cGen.apply("2+1.5>3.25".asFormula) should be  ("#include <math.h>\nint monitor () {\n  return ((2+1.5)>3.25);\n}")
  }

  it should "compile large number" in {
    cGen.apply("9223372036854775807>1".asFormula) should be  ("#include <math.h>\nint monitor () {\n  return (9223372036854775807>1);\n}")
  }

  it should "throw exception for too large number" in {
    a [CodeGenerationException] should be thrownBy cGen.apply("92233720368547758079>1".asFormula)
  }

  "variables" should "compile with index" in {
    cGen.apply("x*z-y_1>1".asFormula) should be  ("#include <math.h>\nint monitor (long double x, long double y_1, long double z) {\n  return (((x*z)-y_1)>1);\n}")
  }

  "power"  should "compile int exp" in {
    cGen.apply("x^3>1".asFormula) should be  ("#include <math.h>\nint monitor (long double x) {\n  return ((x*x*x)>1);\n}")
  }

  it should "compile neg int exp" in {
    cGen.apply("(x+y)^-3>1".asFormula) should be  ("#include <math.h>\nint monitor (long double x, long double y) {\n  return ((1/((x+y)*(x+y)*(x+y)))>1);\n}")
  }

  it should "compile any exp" in {
    cGen.apply("x()^y_0>1".asFormula) should be  ("#include <math.h>\nint monitor (long double x, long double y_0) {\n  return ((pow(x,y_0))>1);\n}")
  }

  // formulas

  // modelPlex generated expressions

  "Local lane control modelplex in place" should "generate C code" in {
    val input = ("-B<=al & al<=A & " +
      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
      "(-B<=af&af<=A&(xfPost()=xf&vfPost()=vf&afPost()=af&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0))) | " +
      "((vf=0&(xfPost()=xf&vfPost()=vf&afPost()=0&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0)) | " +
      "(-B<=af&af<=-b&(xfPost()=xf&vfPost()=vf&afPost()=af&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0))))").asFormula
    val outputC = "#include <math.h>\n" +
      "int monitor (long double A, long double B, long double af, long double afPost, long double al, long double alPost, long double b, long double ep, long double tPost, long double vf, long double vfPost, long double vl, long double vlPost, long double xf, long double xfPost, long double xl, long double xlPost) " +
      "{\n  return ((((-B)<=al)&&(al<=A))&&(((((xf+((vf*vf)/(2*b)))+(((A/b)+1)*(((A/2)*(ep*ep))+(ep*vf))))<(xl+((vl*vl)/(2*B))))&&" +
      "((((-B)<=af)&&(af<=A))&&(((((((xfPost==xf)&&(vfPost==vf))&&(afPost==af))&&(xlPost==xl))&&(vlPost==vl))&&(alPost==al))&&(tPost==0))))||" +
      "(((vf==0)&&(((((((xfPost==xf)&&(vfPost==vf))&&(afPost==0))&&(xlPost==xl))&&(vlPost==vl))&&(alPost==al))&&(tPost==0)))||" +
      "((((-B)<=af)&&(af<=(-b)))&&(((((((xfPost==xf)&&(vfPost==vf))&&(afPost==af))&&(xlPost==xl))&&(vlPost==vl))&&(alPost==al))&&(tPost==0))))));\n}"
    cGen.apply(input) should be (outputC)
  }

  "RSS passive safety modelplex in place" should "generate C code" in {
    val input = ("(xPost()=x&yPost()=y&vPost()=v&aPost()=-b&wPost()=w&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0) | " +
      "((v=0&(xPost()=x&yPost()=y&vPost()=v&aPost()=0&wPost()=0&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0)) | " +
      "(-b<=a&a<=A&(r>0&(w*r=v&((Abs(x-ox)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|Abs(y-oy)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&(xPost()=x&yPost()=y&vPost()=v&aPost()=a&wPost()=w&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0))))))").asFormula
    val outputC = "#include <math.h>\n" +
      "int monitor (long double A, long double a, long double aPost, long double b, long double dx, long double dxPost, long double dy, long double dyPost, long double ep, long double ox, long double oxPost, long double oy, long double oyPost, long double r, long double rPost, long double tPost, long double v, long double vPost, long double w, long double wPost, long double x, long double xPost, long double y, long double yPost) " +
      "{\n  return ((((((((((((xPost==x)&&(yPost==y))&&(vPost==v))&&(aPost==(-b)))&&(wPost==w))&&(dxPost==dx))&&(dyPost==dy))&&(rPost==r))&&(oxPost==ox))&&(oyPost==oy))&&(tPost==0))||" +
      "(((v==0)&&(((((((((((xPost==x)&&(yPost==y))&&(vPost==v))&&(aPost==0))&&(wPost==0))&&(dxPost==dx))&&(dyPost==dy))&&(rPost==r))&&(oxPost==ox))&&(oyPost==oy))&&(tPost==0)))||" +
      "((((-b)<=a)&&(a<=A))&&((r>0)&&(((w*r)==v)&&(((fabsl((x-ox))>(((v*v)/(2*b))+(((A/b)+1)*(((A/2)*(ep*ep))+(ep*v)))))||(fabsl((y-oy))>(((v*v)/(2*b))+(((A/b)+1)*(((A/2)*(ep*ep))+(ep*v))))))&&(((((((((((xPost==x)&&(yPost==y))&&(vPost==v))&&(aPost==a))&&(wPost==w))&&(dxPost==dx))&&(dyPost==dy))&&(rPost==r))&&(oxPost==ox))&&(oyPost==oy))&&(tPost==0))))))));\n}"
    cGen.apply(input) should be (outputC)
  }

  "VSL modelplex in place" should "generate C code" in {
    val input = ("(x1Post()=x1&v1Post()=v1&a1Post()=-B&tPost()=0&vslPost()=vsl&xslPost()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1Post()=x1&v1Post()=v1&a1Post()=-B&tPost()=0&vslPost()=vsl&xslPost()=xsl)) | " +
      "((xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1&a1<=A & " +
      "((x1Post()=x1&v1Post()=v1&a1Post()=a1&tPost()=0&vslPost()=vsl&xslPost()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1Post()=x1&v1Post()=v1&a1Post()=a1&tPost()=0&vslPost()=vsl&xslPost()=xsl))))) | " +
      "(x1>=xsl&(-B<=a1&a1<=A&a1<=(v1-vsl)/ep & " +
      "((x1Post()=x1&v1Post()=v1&a1Post()=a1&tPost()=0&vslPost()=vsl&xslPost()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1Post()=x1&v1Post()=v1&a1Post()=a1&tPost()=0&vslPost()=vsl&xslPost()=xsl))))))").asFormula
    val outputC = "#include <math.h>\n" +
      "int monitor (long double A, long double B, long double a1, long double a1Post, long double ep, long double tPost, long double v1, long double v1Post, long double vsl, long double vslPost, long double x1, long double x1Post, long double xsl, long double xslPost) " +
      "{\n  return ((((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==(-B)))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))||" +
      "(((vsl>=0)&&(xsl>=((x1+(((v1*v1)-(vsl*vsl))/(2*B)))+(((A/B)+1)*(((A/2)*(ep*ep))+(ep*v1))))))&&" +
      "((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==(-B)))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))))||" +
      "(((xsl>=((x1+(((v1*v1)-(vsl*vsl))/(2*B)))+(((A/B)+1)*(((A/2)*(ep*ep))+(ep*v1)))))&&((((-B)<=a1)&&(a1<=A))&&" +
      "(((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==a1))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))||" +
      "(((vsl>=0)&&(xsl>=((x1+(((v1*v1)-(vsl*vsl))/(2*B)))+(((A/B)+1)*(((A/2)*(ep*ep))+(ep*v1))))))&&" +
      "((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==a1))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))))))||" +
      "((x1>=xsl)&&(((((-B)<=a1)&&(a1<=A))&&(a1<=((v1-vsl)/ep)))&&" +
      "(((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==a1))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))||" +
      "(((vsl>=0)&&(xsl>=((x1+(((v1*v1)-(vsl*vsl))/(2*B)))+(((A/B)+1)*(((A/2)*(ep*ep))+(ep*v1))))))&&" +
      "((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==a1))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))))))));\n}"
    cGen.apply(input) should be (outputC)
  }
}
