package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.StaticAnnotation
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

class IdentAnnotation extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro IdentAnnotation.impl
}

object IdentAnnotation {
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] =  annottees(0)
}

class DerivedAxiomAnnotation(val display: String, val codeName: String = "", val linear: Boolean = false) extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro DerivedAxiomAnnotation.impl
}


object DerivedAxiomAnnotation {
  // @TODO: Is this signature correct
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    val display: String = c.prefix.tree match {
      case q"new $annotation($display)" => c.eval[String](c.Expr(display))
      case q"new $annotation($display, $codeName)" => c.eval[String](c.Expr(display))
      case q"new $annotation($display, $codeName, $linear)" => c.eval[String](c.Expr(display))
    }
    val codeNameParam: String = c.prefix.tree match {
      case q"new $annotation($display)" => ""
      case q"new $annotation($display, $codeName)" => c.eval[String](c.Expr(codeName))
      case q"new $annotation($display, $codeName, $linear)" => c.eval[String](c.Expr(codeName))
    }
    //val display: Expr[String] = reify {c.prefix.splice.asInstanceOf[DerivedAxiomAnnotation].display }
    def correctName(t: Tree): Boolean = {
      t match {
        case id: Ident => {
          if (id.name.decodedName.toString == "derivedAxiom") true
          else c.abort(c.enclosingPosition, "function named derivedAxiom string, got: " + t + " of type " + t.getClass() + " and length " + id.name.decodedName.toString.length)
        }
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected derivedAxiom string, got: " + t + " of type " + t.getClass())
      }
    }
    def extractValParts(valDecl: ValDef, codeNameParam: String): (Modifiers, TermName, TermName, String, Tree) = {
      valDecl match {
        case q"$mods val $declName: $tpt = $functionName( ..$params )"if correctName(functionName) && params.length == 3 =>
          (declName,  params(0)) match {
            case (declName: TermName, Literal(Constant(canonName: String))) =>
              val codeName: TermName = if(codeNameParam.nonEmpty) TermName(codeNameParam) else declName
              (mods, declName, codeName, canonName, valDecl.rhs)
            case (t1, t2) => c.abort(c.enclosingPosition, "Invalid annottee: val name = derivedAxiom(arg1, arg2, arg3), got: (" + t1 + " , " + t2 + ") of type " + t1.getClass() + " * " + t2.getClass())
          }
        case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected derivedAxiom with 3 parameters, got:" + params.length)
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val name = derivedAxioms(x1, x2, x3), got: " + t + " of type " + t.getClass())
      }
    }
    annottees map (_.tree) toList match {
      case (valDecl: ValDef) :: Nil =>
        val (mods, declName, codeName, canonName,  rhs) = extractValParts(valDecl, codeNameParam)
        val codeString = Literal(Constant(codeName.decodedName.toString))
        val canonString = Literal(Constant(canonName))
        val displayString = Literal(Constant(display))
        val displayInfo = q"""new edu.cmu.cs.ls.keymaerax.macros.SimpleDisplayInfo($displayString, $displayString)"""
        val expr = q"""({case () => edu.cmu.cs.ls.keymaerax.btactics.HilbertCalculus.useAt($canonString)})""" // : (Unit => Any)
        val info = q"""DerivedAxiomInfo(canonicalName = $canonString, display = $displayInfo, codeName = $codeString, linear = false, theExpr = $expr)"""
        val printInfo = q"""{println("Registering info: " + $info); $info}"""
        val application = q"edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.register($rhs, $printInfo)"
        val lemmaType = tq"edu.cmu.cs.ls.keymaerax.lemma.Lemma"
        c.Expr[Nothing](q"""$mods val $declName: $lemmaType = $application""")
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}

//val disp = (new edu.cmu.cs.ls.keymaerax.macros.DerivedAxiomAnnotation(display = "[:=]=y", linear = false)).display
//c.abort(c.enclosingPosition, show(display.tree))
//val displayString = display.tree  // Constant("[:=]=y")
//val displayString = q"""(new edu.cmu.cs.ls.keymaerax.macros.DerivedAxiomAnnotation(display = "[:=]=y", linear = false)).display"""
/*case q"val $cName = $functionName( ..$params )"if correctName(functionName) && params.length == 3 =>
  (cName,  params(0)) match {
    case (codeName: TermName, Literal(Constant(canonName: String))) =>
      (codeName, canonName, valDecl.rhs)
    case (t1, t2) => c.abort(c.enclosingPosition, "Invalid annottee: val name = derivedAxiom(arg1, arg2, arg3), got: (" + t1 + " , " + t2 + ") of type " + t1.getClass() + " * " + t2.getClass())
  }*/
/*case q"val $cName = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected derivedAxiom with 3 parameters, got:" + params.length)*/
/*match {
  case Literal(Constant(display: String)) => display
  case t => c.abort(c.enclosingPosition, "Bug in DerivedAxiomAnnotation: Failed to pass display name argument from annotation, got: " + t)
}*/
// Expr[String](new DerivedAxiomAnnotation("[:=]=y").asInstanceOf[DerivedAxiomAnnotation].display)
// (codeName, canonName, formula, proof, rhs)
// @TODO
//val codeName = "testName"
//val lemmaType = tq"edu.cmu.cs.ls.keymaerax.lemma.Lemma"
//val lemmaType = rhs.tpe
/*val q"$_; f[..$ts](..$args)" = toolbox.typecheck(q"""
 def f[T](xs: T*): List[T] = xs.toList
 f(1, 2, 3)
""")*/
// scala> reflect.runtime.universe.showRaw(tt.head)
/* val mirror = scala.reflect.runtime.universe.runtimeMirror(this.getClass.getClassLoader) // at runtime
// val mirror = c.mirror // at compile time
symbolOf: Type -> TypeSymbol
mirror.staticClass("mypackage.MyClass").typeSignature.decl(TermName("myfunc"))
*/
// val canonicalName: String
// val expr: Unit => DependentPositionTactic  =  HilbertCalculus.useAt(DerivedAxioms.assignbEquality_y)
/*
//valDecl.mods.flags. valDecl.mods,
classDecl match {
case q"val $valName =  extends ..$parents { ..$body }" =>
  (className, fields, parents, body)

lazy val allDual_time = derivedAxiom("all dual time",
  "(!\\exists t_ !p(||)) <-> \\forall t_ p(||)".asFormula,
  ProvableSig.axioms("all dual")(URename("x_".asVariable,"t_".asVariable,semantic=true))
)
  def extractAnnotationParameters(tree: Tree): List[Tree] = tree match {
    case q"new $name( ..$params )" => params.toList
    case _ => throw new Exception("ToStringObfuscate annotation must be have at least one parameter.")
  }
  def replaceCaseClassSensitiveValues(tree: Tree) = tree match {
    case Literal(Constant(field: String)) =>
      q"""
      ${TermName(field)} = com.fortysevendeg.macros.ToStringObfuscateImpl.obfuscateValue(this.${TermName(field)})
    """
    case _ => c.abort(c.enclosingPosition, s"[obfuscateValue] Match error with $tree")
  }
  //val sensitiveFields = extractAnnotationParameters(c.prefix.tree)
  //val fieldReplacements = sensitiveFields map (replaceCaseClassSensitiveValues(_))
*/
/*
        def extractNewToString(sensitiveFields: List[Tree]) = q"""
     lazy val
     override def toString: ${typeOf[String]} = {
      scala.runtime.ScalaRunTime._toString(this.copy(..$fieldReplacements))
     }"""
        //val newToString = extractNewToString(sensitiveFields)
        //val params = fields.asInstanceOf[List[ValDef]] map { p => p.duplicate}
object DerivedAxiomAnnotation {
  /** Locally embed single string names into SimpleDisplayInfo. */
  implicit def displayInfo(name: String): SimpleDisplayInfo = {SimpleDisplayInfo(name, name)}
  /** Locally embed pair string names into SimpleDisplayInfo distinguishing UI name from plain ASCII name. */
  implicit def displayInfo(pair: (String, String)): SimpleDisplayInfo = SimpleDisplayInfo(pair._1, pair._2)
  /** Locally embed pair of list of strings into SequentDisplayInfo. */
  implicit def sequentDisplay(succAcc:(List[String], List[String])): SequentDisplay = {
    SequentDisplay(succAcc._1, succAcc._2)
  }
  /** Locally embed pair of list of strings with boolean into SequentDisplayInfo with info on whether closing. */
  implicit def sequentDisplay(succAccClosed:(List[String], List[String], Boolean)): SequentDisplay = {
    SequentDisplay(succAccClosed._1, succAccClosed._2, succAccClosed._3)
  }
}*/


/*
  def modifiedDeclaration(classDecl: u.ClassDef) = {
//modifiedDeclaration(classDecl)
    //val (className, fields, parents, body) = extractCaseClassesParts(classDecl)
    //val newToString = extractNewToString(sensitiveFields)
    //val params = fields.asInstanceOf[List[ValDef]] map { p => p.duplicate}

    /*  q"""
    case class $className ( ..$params ) extends ..$parents {
      $newToString
      ..$body
    }
  """*/ */
/*  val lemmaType = u.typeOf[Lemma]
  val lemmaSymbol = lemmaType.typeSymbol.asClass
*/

/*val myAnnotatedClass: ClassSymbol = u.runtimeMirror(Thread.currentThread().getContextClassLoader).staticClass("MyAnnotatedClass")
val annotation: Option[Annotation] = myAnnotatedClass.annotations.find(_.tree.tpe =:= u.typeOf[MyAnnotationClass])
val result = annotation.flatMap { a =>
  a.tree.children.tail.collect({ case Literal(Constant(id: String)) => DoSomething(id) }).headOption
}*/
//platypusSymbol.annotations
//platypusSymbol: reflect.runtime.universe.ClassSymbol = class Platypus
//List[reflect.runtime.universe.Annotation] = List(animals.reflection.Mammal("North America"))*/
//lemmaType: reflect.runtime.universe.Type = edu.cmu.cs.ls.keymaerax.lemma.Lemma



// Example:
/*
package animals
// Create Annotation `Mammal`
class Mammal(indigenous:String) extends scala.annotation.StaticAnnotation

// Annotate class Platypus as a `Mammal`
@Mammal(indigenous = "North America")
class Platypus{}
Annotations can then be interrogated using the reflection API.

import edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.btactics.{DisplayInfo, SequentDisplay, SimpleDisplayInfo}
import scala.reflect.macros.whitebox
import scala.reflect.macros.Context
import scala.reflect.api.Universe
import scala.reflect.api._
import scala.reflect.runtime.{universe ⇒ u}
//import u._
// annotation.tree.children.tail.

*/