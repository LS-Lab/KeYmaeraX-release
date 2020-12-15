package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import java.io.File

import com.sun.jna._

import scala.io.Source

/*
extern "C" void ffiget_const (int32_t *c, long clen, int32_t *a, long alen);
extern "C" void ffiget_sensor(int32_t *c, long clen, int32_t *a, long alen);
extern "C" void ffiget_ctrl (int32_t *c, long clen, int32_t *a, long alen);
extern "C" void ffiactuate(char *c, long clen, int32_t *a, long alen);
extern "C" void ffihas_next(int32_t *c, long clen, int8_t *a, long alen);
extern "C" void ffiviolation(char *c, long clen, int32_t *a, long alen);
 */

trait VeriPhySenselessFFIs extends Library {
  def ffiget_const(c: Array[Int], clen: Long, a: Array[Int], alen: Long): Unit
  def ffiget_ctrl(c: Array[Int], clen: Long, a: Array[Int], alen: Long): Unit
  def ffiactuate(c: Array[Char], clen: Long, a: Array[Int], alen: Long): Unit
  def ffihas_next(c: Array[Int], clen: Long, a: Array[Char], alen: Long): Unit
  def ffiviolation(c: Array[Char], clen: Long, a: Array[Int], alen: Long): Unit
}

trait VeriPhyFFIs extends VeriPhySenselessFFIs with Library {
  def ffiget_sensor(c: Array[Int], clen: Long, a: Array[Int], alen: Long): Unit
}


case class FFILoader(libName: String) {
  def Instance: VeriPhyFFIs = Native.load(
    libName,
    classOf[VeriPhyFFIs])//.asInstanceOf[VeriPhyFFIs]
}

/*object HelloWorld {
  def main(args: Array[String]) {
    /*for ((arg, i) <- args.zipWithIndex) {
      CLibrary.Instance.puts(
        "Argument %d: %s".format(i.asInstanceOf[AnyRef], arg))
    }*/
  }
}*/



object BotMain {
  def main(args: Array[String]): Unit = {
    val libName = args(0)
    if (args.length > 1) {
      val dirName = args(1)

      //NativeLibrary.addSearchPath(libName, dirName)
      val path = System.getProperty("jna.library.path")
      val fullPath = if(path == null) dirName else dirName + File.pathSeparator + path
      System.setProperty("jna.library.path", fullPath)
      val what = System.getProperty("jna.library.path")
      println("help:" + what)
    }

    val lib: VeriPhyFFIs = FFILoader(libName).Instance   //.Instance.puts("Hello, World");
    println("loaded!")
    println("Program runs")
  }
}