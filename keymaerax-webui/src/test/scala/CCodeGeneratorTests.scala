import java.io.File

import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._
import edu.cmu.cs.ls.keymaerax.codegeneration.CCodeGenerator

/**
 * Created by ran on 6/22/15.
 * @author Ran Ji
 */
class CCodeGeneratorTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
  var cGen : CCodeGenerator = null

  override def beforeEach() = {
    cGen = new CCodeGenerator
  }

  override def afterEach() = {
    cGen = null
  }

  "Numbers" should "compile to C code" in {
    cGen.generateCCode("2+1>1".asFormula) should be  ("#include \"math.h\"\nint monitor () {\n  return ((2+1)>1);\n}")
  }

  "variables" should "compile to C code" in {
    cGen.generateCCode("x*y-z>1".asFormula) should be  ("#include \"math.h\"\nint monitor (long double x, long double y, long double z) {\n  return (((x*y)-z)>1);\n}")
  }

  it should "compile to C file" in {
    val cCode = cGen.generateCCode("x*y-z>1".asFormula)
    val fileName = "variables.c"
    cGen.generateCFileFromCCode(cCode, fileName) should be ("")
  }

  "power"  should "compile to C code" in {
    cGen.generateCCode("x^3>1".asFormula) should be  ("#include \"math.h\"\nint monitor (long double x) {\n  return ((x*x*x)>1);\n}")
  }

  it should "compile to C code 2" in {
    cGen.generateCCode("(x+y)^3>1".asFormula) should be  ("#include \"math.h\"\nint monitor (long double x, long double y) {\n  return (((x+y)*(x+y)*(x+y))>1);\n}")
  }

  it should "compile to C code 3" in {
    cGen.generateCCode("x()^3>1".asFormula) should be  ("#include \"math.h\"\nint monitor (long double x) {\n  return ((x*x*x)>1);\n}")
  }

  "Local lane control modelplex in place" should "generate C code" in {
    val input = ("-B<=al & al<=A & " +
      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
      "(-B<=af&af<=A&(xfPost()=xf&vfPost()=vf&afPost()=af&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0))) | " +
      "((vf=0&(xfPost()=xf&vfPost()=vf&afPost()=0&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0)) | " +
      "(-B<=af&af<=-b&(xfPost()=xf&vfPost()=vf&afPost()=af&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0))))").asFormula
    val outputC = "#include \"math.h\"\nint monitor (long double vf, long double xfPost, long double xlPost, long double al, long double b, long double xf, " +
      "long double tPost, long double xl, long double af, long double afPost, long double vl, long double A, long double ep, long double alPost, long double vfPost, long double B, long double vlPost) " +
      "{\n  return ((((-B)<=al)&&(al<=A))&&(((((xf+((vf*vf)/(2*b)))+(((A/b)+1)*(((A/2)*(ep*ep))+(ep*vf))))<(xl+((vl*vl)/(2*B))))&&((((-B)<=af)&&(af<=A))&&(((((((xfPost==xf)&&(vfPost==vf))&&(afPost==af))" +
      "&&(xlPost==xl))&&(vlPost==vl))&&(alPost==al))&&(tPost==0))))||(((vf==0)&&(((((((xfPost==xf)&&(vfPost==vf))&&(afPost==0))&&(xlPost==xl))&&(vlPost==vl))&&(alPost==al))&&(tPost==0)))" +
      "||((((-B)<=af)&&(af<=(-b)))&&(((((((xfPost==xf)&&(vfPost==vf))&&(afPost==af))&&(xlPost==xl))&&(vlPost==vl))&&(alPost==al))&&(tPost==0))))));\n}"
    cGen.generateCCode(input) should be (outputC)
  }

  it should "generate C file" in {
    val cCode = cGen.generateCCode(("-B<=al & al<=A & " +
      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
      "(-B<=af&af<=A&(xfPost()=xf&vfPost()=vf&afPost()=af&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0))) | " +
      "((vf=0&(xfPost()=xf&vfPost()=vf&afPost()=0&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0)) | " +
      "(-B<=af&af<=-b&(xfPost()=xf&vfPost()=vf&afPost()=af&xlPost()=xl&vlPost()=vl&alPost()=al&tPost()=0))))").asFormula)
    val fileName = "localLaneControl.c"
    cGen.generateCFileFromCCode(cCode, fileName) should be ("")
  }

  "RSS passive safety modelplex in place" should "generate C code" in {
    val input = ("(xPost()=x&yPost()=y&vPost()=v&aPost()=-b&wPost()=w&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0) | " +
      "((v=0&(xPost()=x&yPost()=y&vPost()=v&aPost()=0&wPost()=0&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0)) | " +
      "(-b<=a&a<=A&(r>0&(w*r=v&((Abs(x-ox)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|Abs(y-oy)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&(xPost()=x&yPost()=y&vPost()=v&aPost()=a&wPost()=w&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0))))))").asFormula
    val outputC = "#include \"math.h\"\nint monitor (long double vPost, long double yPost, long double dy, long double x, long double wPost, long double dxPost, long double a, long double dx, " +
      "long double ox, long double r, long double oy, long double b, long double tPost, long double dyPost, long double w, long double aPost, long double v, long double rPost, long double y, " +
      "long double Abs, long double A, long double ep, long double oyPost, long double xPost, long double oxPost) " +
      "{\n  return ((((((((((((xPost==x)&&(yPost==y))&&(vPost==v))&&(aPost==(-b)))&&(wPost==w))&&(dxPost==dx))&&(dyPost==dy))&&(rPost==r))&&(oxPost==ox))&&(oyPost==oy))&&(tPost==0))" +
      "||(((v==0)&&(((((((((((xPost==x)&&(yPost==y))&&(vPost==v))&&(aPost==0))&&(wPost==0))&&(dxPost==dx))&&(dyPost==dy))&&(rPost==r))&&(oxPost==ox))&&(oyPost==oy))&&(tPost==0)))" +
      "||((((-b)<=a)&&(a<=A))&&((r>0)&&(((w*r)==v)&&(((Abs>(((v*v)/(2*b))+(((A/b)+1)*(((A/2)*(ep*ep))+(ep*v)))))||(Abs>(((v*v)/(2*b))+(((A/b)+1)*(((A/2)*(ep*ep))+(ep*v))))))" +
      "&&(((((((((((xPost==x)&&(yPost==y))&&(vPost==v))&&(aPost==a))&&(wPost==w))&&(dxPost==dx))&&(dyPost==dy))&&(rPost==r))&&(oxPost==ox))&&(oyPost==oy))&&(tPost==0))))))));\n}"
    cGen.generateCCode(input) should be (outputC)
  }

  it should "generate C file" in {
    val cCode = cGen.generateCCode(("(xPost()=x&yPost()=y&vPost()=v&aPost()=-b&wPost()=w&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0) | " +
      "((v=0&(xPost()=x&yPost()=y&vPost()=v&aPost()=0&wPost()=0&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0)) | " +
      "(-b<=a&a<=A&(r>0&(w*r=v&((Abs(x-ox)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|Abs(y-oy)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&(xPost()=x&yPost()=y&vPost()=v&aPost()=a&wPost()=w&dxPost()=dx&dyPost()=dy&rPost()=r&oxPost()=ox&oyPost()=oy&tPost()=0))))))").asFormula)
    val fileName = "rss.c"
    cGen.generateCFileFromCCode(cCode, fileName) should be ("")
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
    val outputC = "#include \"math.h\"\nint monitor (long double vsl, long double xsl, long double xslPost, long double v1, long double v1Post, long double x1Post, long double a1, " +
      "long double tPost, long double a1Post, long double A, long double ep, long double vslPost, long double x1, long double B) " +
      "{\n  return ((((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==(-B)))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))||(((vsl>=0)&&(xsl>=((x1+(((v1*v1)-(vsl*vsl))/(2*B)))+(((A/B)+1)*(((A/2)*(ep*ep))+(ep*v1))))))" +
      "&&((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==(-B)))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))))||(((xsl>=((x1+(((v1*v1)-(vsl*vsl))/(2*B)))+(((A/B)+1)*(((A/2)*(ep*ep))+(ep*v1)))))" +
      "&&((((-B)<=a1)&&(a1<=A))&&(((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==a1))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))||(((vsl>=0)&&(xsl>=((x1+(((v1*v1)-(vsl*vsl))/(2*B)))+(((A/B)+1)*(((A/2)*(ep*ep))+(ep*v1))))))" +
      "&&((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==a1))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))))))||((x1>=xsl)&&(((((-B)<=a1)&&(a1<=A))&&(a1<=((v1-vsl)/ep)))&&(((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==a1))&&(tPost==0))" +
      "&&(vslPost==vsl))&&(xslPost==xsl))||(((vsl>=0)&&(xsl>=((x1+(((v1*v1)-(vsl*vsl))/(2*B)))+(((A/B)+1)*(((A/2)*(ep*ep))+(ep*v1))))))&&((((((x1Post==x1)&&(v1Post==v1))&&(a1Post==a1))&&(tPost==0))&&(vslPost==vsl))&&(xslPost==xsl))))))));\n}"
    cGen.generateCCode(input) should be (outputC)
  }

  it should "generate C file" in {
    val cCode = cGen.generateCCode(("(x1Post()=x1&v1Post()=v1&a1Post()=-B&tPost()=0&vslPost()=vsl&xslPost()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1Post()=x1&v1Post()=v1&a1Post()=-B&tPost()=0&vslPost()=vsl&xslPost()=xsl)) | " +
      "((xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1&a1<=A & " +
      "((x1Post()=x1&v1Post()=v1&a1Post()=a1&tPost()=0&vslPost()=vsl&xslPost()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1Post()=x1&v1Post()=v1&a1Post()=a1&tPost()=0&vslPost()=vsl&xslPost()=xsl))))) | " +
      "(x1>=xsl&(-B<=a1&a1<=A&a1<=(v1-vsl)/ep & " +
      "((x1Post()=x1&v1Post()=v1&a1Post()=a1&tPost()=0&vslPost()=vsl&xslPost()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1Post()=x1&v1Post()=v1&a1Post()=a1&tPost()=0&vslPost()=vsl&xslPost()=xsl))))))").asFormula)
    val fileName = "vsl.c"
    cGen.generateCFileFromCCode(cCode, fileName) should be ("")
  }
}
