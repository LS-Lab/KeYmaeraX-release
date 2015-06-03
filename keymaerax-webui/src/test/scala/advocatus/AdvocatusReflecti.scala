import java.lang.reflect.ReflectPermission
import java.security.{AccessControlException, Permission}

import scala.collection.immutable

import edu.cmu.cs.ls.keymaera.core._

import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * "helpful" ways of proving false by weird Java reflection mechanisms.
* @author aplatzer
 * @todo write a similar test that recursively crawls all declared fields starting from Provable in search for something mutable and screams when found.
*/
class AdvocatusReflecti extends FlatSpec with Matchers {
  val verum = new Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(True))
  val falsum = new Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(False))


  "advocatus diavoli mutandis" should "not allow immutable Provable conclusion to be written to" in {
    var proof = Provable.startProof(verum)(CloseTrue(SuccPos(0)), 0)
    println("Provable " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
    println(classOf[Provable].getDeclaredFields.map(c => c.getName + " of type " + c.getType).mkString("\n"))
    val fld = classOf[Provable].getField("conclusion")
    a [IllegalAccessException] should be thrownBy fld.set(proof, falsum)
    println("Suddenly " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
  }

  it should "not allow immutable Provable conclusion to be written to via index" in {
    var proof = Provable.startProof(verum)(CloseTrue(SuccPos(0)), 0)
    println("Provable " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
    println(classOf[Provable].getDeclaredFields.map(c => c.getName + " of type " + c.getType).mkString("\n"))
    val fld = classOf[Provable].getDeclaredFields.apply(0)
    a [IllegalAccessException] should be thrownBy fld.set(proof, falsum)
    println("Suddenly " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
  }

  it should "not allow immutable Provable conclusion to be written to after accessible via index" in {
    var proof = Provable.startProof(verum)(CloseTrue(SuccPos(0)), 0)
    println("Provable " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
    println(classOf[Provable].getDeclaredFields.map(c => c.getName + " of type " + c.getType).mkString("\n"))
    val fld = classOf[Provable].getDeclaredFields.apply(0)
    a [SecurityException] should be thrownBy fld.setAccessible(true)
    a [IllegalAccessException] should be thrownBy fld.set(proof, falsum)
    println("Suddenly " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
  }

  it should "not allow immutable Provable conclusion to be written to after accessible with security manager via index" in {
    var proof = Provable.startProof(verum)(CloseTrue(SuccPos(0)), 0)
    println("Provable " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
    println(classOf[Provable].getDeclaredFields.map(c => c.getName + " of type " + c.getType).mkString("\n"))
    System.setSecurityManager(new SecurityManager() {
      override def checkPermission(perm: Permission) = {
        !(perm.isInstanceOf[ReflectPermission] && "suppressAccessChecks".equals(perm.getName()))
      }
    })
    val fld = classOf[Provable].getDeclaredFields.apply(0)
    a [SecurityException] should be thrownBy fld.setAccessible(true)
    a [IllegalAccessException] should be thrownBy fld.set(proof, falsum)
    println("Suddenly " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
  }

  it should "not allow immutable Provable conclusion to be written to after accessible with security manager reset via index" in {
    var proof = Provable.startProof(verum)(CloseTrue(SuccPos(0)), 0)
    println("Provable " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
    println(classOf[Provable].getDeclaredFields.map(c => c.getName + " of type " + c.getType).mkString("\n"))
    System.setSecurityManager(new SecurityManager() {
      override def checkPermission(perm: Permission) = {
        !(perm.isInstanceOf[RuntimePermission] && "setSecurityManager".equals(perm.getName)) &&
          !(perm.isInstanceOf[ReflectPermission] && "suppressAccessChecks".equals(perm.getName()))
      }
    })
    a [SecurityException] should be thrownBy System.setSecurityManager(new SecurityManager())
    val fld = classOf[Provable].getDeclaredFields.apply(0)
    a [SecurityException] should be thrownBy fld.setAccessible(true)
    a [IllegalAccessException] should be thrownBy fld.set(proof, falsum)
    println("Suddenly " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
  }

  //@todo also test against wrapping SecurityManager replacement inside a PrivilegedAction


  //@TODO turn the following into indexedSeq overwriting. Not sure why they don't yell nor effect.

  it should "not allow immutable Provable to be written to" in {
    var proof = Provable.startProof(verum)(CloseTrue(SuccPos(0)), 0)
    println("Provable " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
    val clazz = classOf[Sequent]
    println(clazz.getDeclaredFields.map(c => c.getName + " of type " + c.getType).mkString("\n"))
    val fld = clazz.getField("succ")
    a [IllegalAccessException] should be thrownBy fld.set(proof.conclusion, False)
    println("Suddenly " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
  }

  it should "not allow immutable Provable to be written to via index" in {
    var proof = Provable.startProof(verum)(CloseTrue(SuccPos(0)), 0)
    println("Provable " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
    val clazz = classOf[Sequent]
    println(clazz.getDeclaredFields.map(c => c.getName + " of type " + c.getType).mkString("\n"))
    val fld = clazz.getDeclaredFields.apply(2)
    a [IllegalAccessException] should be thrownBy fld.set(proof.conclusion, False)
    println("Suddenly " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
  }

  it should "not allow immutable Provable to be written to via index despite accessible" in {
    var proof = Provable.startProof(verum)(CloseTrue(SuccPos(0)), 0)
    println("Provable " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
    val clazz = classOf[Sequent]
    println(clazz.getDeclaredFields.map(c => c.getName + " of type " + c.getType).mkString("\n"))
    val fld = clazz.getDeclaredFields.apply(2)
    a [SecurityException] should be thrownBy fld.setAccessible(true)
    a [IllegalAccessException] should be thrownBy fld.set(proof.conclusion, False)
    println("Suddenly " + proof + " " + (if (proof.isProved) "proved" else "not proved"))
  }

  "advocatus diavoli reflecti" should "not allow new Provable via reflection" in {
    val clazz = Class.forName(Provable.getClass.getName)
    println("Got class " + clazz)
    a [IllegalAccessException] should be thrownBy clazz.newInstance()
  }

  it should "not allow new Provable via reflection classOf style" in {
    val clazz = classOf[Provable]
    println("Got class " + clazz)
    a [InstantiationException] should be thrownBy clazz.newInstance()
  }

  it should "not allow new Provable via constructor reflection" in {
    println(Class.forName(Provable.getClass.getName).getConstructors.map(c => c.getName + " with parameters " + c.getParameterTypes.map(t => t.toString).mkString(", ")))
    val cnstr = Class.forName(Provable.getClass.getName).getConstructor(classOf[Sequent], classOf[immutable.IndexedSeq[Sequent]])
    println("Got constructor " + cnstr)
    a [IllegalAccessException] should be thrownBy cnstr.newInstance(falsum, immutable.IndexedSeq())
  }

  it should "not allow new Provable via constructor reflection classOf style" in {
    println(classOf[Provable].getConstructors.map(c => c.getName + " with parameters " + c.getParameterTypes.map(t => t.toString).mkString(", ")))
    val cnstr = classOf[Provable].getConstructor(classOf[Sequent], classOf[immutable.IndexedSeq[Sequent]])
    println("Got constructor " + cnstr)
    val wrong = a [IllegalAccessException] should be thrownBy cnstr.newInstance(falsum, immutable.IndexedSeq())
  }

  it should "not allow new Provable via constructor reflection after making accessible" in {
    val cnstr = classOf[Provable].getConstructor(classOf[Sequent], classOf[immutable.IndexedSeq[Sequent]])
    println("Got constructor " + cnstr)
    a [SecurityException] should be thrownBy cnstr.setAccessible(true)
    a [IllegalAccessException] should be thrownBy cnstr.newInstance(falsum, immutable.IndexedSeq())
  }

  it should "not allow new Provable via constructor reflection after making accessible with Security Manager" in {
    val cnstr = classOf[Provable].getConstructor(classOf[Sequent], classOf[immutable.IndexedSeq[Sequent]])
    println("Got constructor " + cnstr)
    System.setSecurityManager(new SecurityManager() {
      override def checkPermission(perm: Permission) = {
        !(perm.isInstanceOf[ReflectPermission] && "suppressAccessChecks".equals(perm.getName()))
      }
    })
    a [SecurityException] should be thrownBy cnstr.setAccessible(true)
    a [IllegalAccessException] should be thrownBy cnstr.newInstance(falsum, immutable.IndexedSeq())
  }

  it should "not allow new Provable via constructor reflection after making accessible with Security Manager that has been overwritten" in {
    val cnstr = classOf[Provable].getConstructor(classOf[Sequent], classOf[immutable.IndexedSeq[Sequent]])
    println("Got constructor " + cnstr)
    System.setSecurityManager(new SecurityManager() {
      override def checkPermission(perm: Permission) = {
        !(perm.isInstanceOf[ReflectPermission] && "suppressAccessChecks".equals(perm.getName()))
      }
    })
    a [SecurityException] should be thrownBy System.setSecurityManager(new SecurityManager())
    a [SecurityException] should be thrownBy cnstr.setAccessible(true)
    a [IllegalAccessException] should be thrownBy cnstr.newInstance(falsum, immutable.IndexedSeq())
  }

  it should "for a decent SecurityManager not allow new Provable via constructor reflection after making accessible with Security Manager that has been overwritten" in {
    val cnstr = classOf[Provable].getConstructor(classOf[Sequent], classOf[immutable.IndexedSeq[Sequent]])
    println("Got constructor " + cnstr)
    System.setSecurityManager(new SecurityManager() {
      override def checkPermission(perm: Permission) = {
        !(perm.isInstanceOf[RuntimePermission] && "setSecurityManager".equals(perm.getName)) &&
        !(perm.isInstanceOf[ReflectPermission] && "suppressAccessChecks".equals(perm.getName()))
      }
    })
    a [AccessControlException] should be thrownBy System.setSecurityManager(new SecurityManager())
    a [SecurityException] should be thrownBy cnstr.setAccessible(true)
    a [IllegalAccessException] should be thrownBy cnstr.newInstance(falsum, immutable.IndexedSeq())
  }
}
