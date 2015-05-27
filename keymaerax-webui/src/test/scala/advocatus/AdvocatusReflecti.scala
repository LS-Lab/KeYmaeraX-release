import java.lang.reflect.ReflectPermission
import java.security.{AccessControlException, Permission}

import scala.collection.immutable

import edu.cmu.cs.ls.keymaera.core._

import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * "helpful" ways of proving false by weird Java reflection mechanisms.
* @author aplatzer
*/
class AdvocatusReflecti extends FlatSpec with Matchers {
  val falsum = new Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(False))

  "advocatus diavoli" should "not allow new Provable via reflection" in {
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
