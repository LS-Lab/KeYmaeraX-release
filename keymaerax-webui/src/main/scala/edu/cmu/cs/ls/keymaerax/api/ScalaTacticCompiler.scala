package edu.cmu.cs.ls.keymaerax.api

import scala.reflect.internal.util.{AbstractFileClassLoader, BatchSourceFile}
import scala.tools.nsc.{Global, Settings}
import scala.tools.nsc.io.VirtualDirectory
import scala.tools.nsc.reporters.StoreReporter

/**
 * Compiles tactic files written in Scala.
 * @see [[https://github.com/Rogach/miltamm/blob/master/src/main/scala/BuildCompiler.scala#L8]]
 */
class ScalaTacticCompiler {
  def compile(source: String): Iterable[Class[_]] = {
    val sources = List(new BatchSourceFile("<source>", source))

    /* Take the classpath from the currently running scala environment */
    val settings = new Settings
    settings.usejavacp.value = true

    /* Save compiled classes into memory */
    val directory = new VirtualDirectory("(memory)", None)
    settings.outputDirs.setSingleOutput(directory)

    val reporter = new StoreReporter()
    val compiler = new Global(settings, reporter)
    new compiler.Run().compileSources(sources)

    if (reporter.hasErrors) {
      throw new CompilationFailedException(source,
        reporter.infos.map(info => CompileError(info.pos.line, info.pos.column, info.pos.lineContent, info.msg)).toList.sortBy(_.line))
    }

    // Loading new compiled classes
    val classLoader =  new AbstractFileClassLoader(directory, this.getClass.getClassLoader)

    /*! When classes are loading inner classes are being skipped. */
    for (classFile <- directory; if !classFile.name.contains('$')) yield {

      /*! Each file name is being constructed from a path in the virtual directory. */
      val path = classFile.path
      val fullQualifiedName = path.substring(path.indexOf('/')+1,path.lastIndexOf('.')).replace("/",".")

      /*! Loaded classes are collecting into a returning collection with `yield`. */
      classLoader.loadClass(fullQualifiedName)
    }
  }
}

/** Compilation exception with error positions with messages of what went wrong during compilation.
 */
class CompilationFailedException(val programme: String,
                                 val messages: Iterable[CompileError])
  extends Exception("\n" + messages.map(m => "line %d: %s \n    %s\n    %s" format (m.line - 3, m.message, m.lineContent, " " * (m.column - 1) + "^")).mkString("\n"))

/**
 * Single compile error.
 * @param line Line number, at which error took place.
 * @param column offset from line start.
 * @param lineContent Contents of source line.
 * @param message Error message.
 */
case class CompileError(line: Int, column: Int, lineContent: String, message: String)
