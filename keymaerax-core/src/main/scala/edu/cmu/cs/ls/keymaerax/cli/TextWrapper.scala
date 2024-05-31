/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

object TextWrapper {
  private class State(val maxWidth: Int) {
    private var finishedLines: Seq[String] = Seq()
    private var currentLine: Seq[String] = Seq()
    private var currentWordWidths: Long = 0

    def flushLine(): Unit = if (currentLine.nonEmpty) {
      finishedLines :+= currentLine.mkString(" ")
      currentLine = Seq()
      currentWordWidths = 0
    }

    def addWord(word: String): Unit = {
      val newWidth = currentWordWidths + word.length + currentLine.length
      if (newWidth > maxWidth) flushLine()
      currentLine :+= word
      currentWordWidths += word.length
    }

    def build(): String = {
      flushLine()
      finishedLines.mkString("\n")
    }
  }

  /**
   * Wrap words separated by whitespace to a specified maximum width. Collapses all inter-word whitespace down to either
   * a single space or newline. Removes leading and trailing whitespace.
   *
   * Assumes the width of a word is equal to its length. This breaks down with weirder unicode, but works for simple
   * text that's close to ASCII.
   */
  def wrap(text: String, maxWidth: Int): String = {
    val wrapper = new State(maxWidth)
    text.split("\\s+").filter(_.nonEmpty).foreach(wrapper.addWord)
    wrapper.build()
  }
}
