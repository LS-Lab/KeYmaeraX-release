package pdl.main
import pdl.core.Parser
import javax.swing.JFileChooser
import javax.swing.JOptionPane
import java.io.File

object EchoProgram {
  def main(args:Array[String]):Unit = {
    val fc = new JFileChooser(new File("/home/nfulton/dev/research/pdl_rewrite_old/pdl_programs/"))
    
    fc.showDialog(null, "Echo File");
    val f = scala.io.Source.fromFile(fc.getSelectedFile()).mkString
    val programOut = Parser.parseProgram(f).prettyString.replace(";", ";\n")
    JOptionPane.showMessageDialog(null, programOut)
  }
}