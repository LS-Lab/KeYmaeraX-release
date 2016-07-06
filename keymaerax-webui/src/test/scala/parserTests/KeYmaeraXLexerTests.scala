/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser._
import org.scalatest.{FlatSpec, Matchers}

/**
 * These are white space processing tests and location munging tests. All tests that don't care
 * about white space or location munging and that produce a parsable stream should be added
 * to PrelexedParserTests instead.
 * Created by nfulton on 6/10/15.
 */
class KeYmaeraXLexerTests extends FlatSpec with Matchers {
  "Lexer" should "Handle spaces correctly" in {
    val input = "   ("
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(LPAREN, Region(1, 4, 1, 4))
  }

  it should "Handle no spaces correctly" in {
    val input = ")"
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(RPAREN, Region(1, 1, 1, 1))
  }

  it should "Handle empty string correctly" in {
    val input = ""
    KeYmaeraXLexer(input).head shouldBe Token(EOF, SuffixRegion(1, 1))
  }

  //@todo Nathan
  //@todo do more location tests with newlines. And also with comments!
  it should "Handle newlines correctly" in {
    val input =
      """
        |   (""".stripMargin
    KeYmaeraXLexer(input).head.loc shouldBe Region(2, 4, 2, 4)
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(LPAREN, Region(2, 4, 2, 4))
  }

  it should "parse forall" in {
    val input = "\\forall"
    KeYmaeraXLexer(input).length shouldBe 2 //forall and EOS.
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(FORALL, Region(1,1,1,7))
  }

  it should "parse forall 2 times" in {
    val input = """\forall \forall"""
    KeYmaeraXLexer(input).length shouldBe 3 //forall and EOS.
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(FORALL, Region(1,1,1,7))
    KeYmaeraXLexer(input).tail.head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(FORALL, Region(1,9,1,15))
  }

  //@todo Nathan
  it should "parse an identifier" in {
    val input = "input"
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(IDENT("input"), Region(1,1,1,5))
  }

  it should "parse an identifier -- checking length is ok" in {
    val input = "thisisalongvariablename"
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(IDENT("thisisalongvariablename"), Region(1,1,1,input.length))
  }


  it should "parse an integer" in {
    val n = "99"
    KeYmaeraXLexer(n).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(NUMBER(n), Region(1,1,1,n.length))
  }

  it should "parse an number" in {
    val n = "99.999"
    KeYmaeraXLexer(n).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(NUMBER(n), Region(1,1,1,n.length))
  }

  it should "parse a single comment" in {
    val n = "/*an identifier*/x"
    KeYmaeraXLexer(n).head.tok shouldBe(IDENT("x"))
  }

  it should "parse a multi-line comment" in {
    val n =
      """
        |/*
        | * This is a comment.
        | */
        | x
      """.stripMargin
    KeYmaeraXLexer(n).head.tok shouldBe(IDENT("x"))
  }

  it should "eat loooong input at least with big stacks" in {
    val n = "(\\forall z3 (<{{{{{{z1':=z4';++{{?true;++?true;}++?true;++?true;}*}++?true;}++{{z1:=z1;}*++{z7:=0;}*}*{z3'=0&\\exists z5 \\exists z4 true}{{?true;?true;}?true;++{?true;++?true;}z6:=z6;}}++{{{{?true;?true;}*}*}*++{z7'=0,z6'=0&true}}{z7:=gg()-z3';}*{z5:=z5;++?<?true;++?true;>0>0;}}*{z6:=z6;z1:=z7;}*++z4:=z4;{?true;{{{?true;}*}*++?true;?true;++?true;++?true;}++{{z5'=65&<?true;>true}++z3':=0*0;}*}*?true;++z2:=z2;++?true;++?true;}*++{{?true;{{?true;}*}*z3':=z2';{{{?true;?true;++?true;?true;}z6:=z6;}*++z1:=z1;{?true;}*}}?true;++{{z4:=*;{{{?true;}*++{z6'=0&true}}++?true;?true;++?true;}{z7:=*;++z1:=0;}*++{?true;}*?true;++{{?true;}*++z2:=*;}*++{{?true;++?true;}*}*}++{{z1'=0&\\forall z3 \\exists z1 [{z5'=0&true}]0!=0}}*}*{{z5:=*;{{?true;?true;}*}*{{?true;++?true;}*}*}{{z3:=-4;++?true;?true;++z6:=z6;}++z7:=*;}*++{{z7'=0&[{?true;}*++{?true;}*]true}++{{z7'=0,z3'=0&true}}*z5:=z5;++{?true;?true;}*}*}*}*}*{{{z5'=ff(22),z2'=0&<{z7:=z7;}*++{{?true;{?true;?true;++z1:=z1;}}*{?\\forall z2 true;++?true;}{?true;}*}*>true->qq()}++{?true;}*}{z4'=(z7*gg()-0)*(ff(74)/(0/0))+(gg()+(0*0*(z2-61/61)+gg()^1-gg())/0)&[{z6'=-40+20&37!=gg()}]<z3:=z5;><{{{{z3:=*;}*{{?true;++?true;}++{?true;}*}++{{?true;}*++{?true;}*}++{?true;?true;}*}{{{{z4'=0&true}}*++{?true;++?true;}{?true;++?true;}}++?PP{[?true;]true};}}?true;}*>(true)'}}{{z6:=z6;}*++?[?\\forall z5 (z7*(0-0)>0^4*(0-0)->0/0>=0-0|\\exists z4 0<=0);++{{?true;++?true;}*?true;}*{{?true;{{?true;}*}*}*}*][{{z4'=z6-0&true}}*++{{z5':=96;{z2'=70&[?true;]true}}{z7:=z7;}*}*]true;++{z6'=75&0 < (z5+-34)'/0/(z3'*(16*z7'*(gg())'+ff(z6-z7)))}}{{?true;}*{{z7'=0,z4'=gg()/44+69--33*(0+z1)&\\exists z1 -46>z4&\\forall z2 \\exists z5 <{?true;}*?true;>([?true;]true-><?true;>true)}{z2':=gg();++{?true;{{?true;++?true;}*}*{z3'=0,z1'=0&(\\forall z4 true)'}}?true;}}z7:=z7;{{{?true;?true;++?true;?true;}*{{?true;?true;}z2:=0;}*}*{{z4:=0/0;{?true;?true;++{z5'=0,z1'=0&true}}}{z1:=z1;++z7:=0;++{?true;}*}}{?true;{?true;}*{?true;}*}*}{?true;++{?true;}*}}*><?true;>[{z7'=0,z1'=0&!<?([?[{{?true;++?true;}++?true;}{?true;++?true;}*][z3:=*;{?true;}*][{?true;}*]0 < 0;][{{{{?true;}*}*}*}*][{z5:=*;}*]<{?true;++?true;}++?true;>[{?true;}*][?true;]true)';++z3':=z4^0/z5';>\\exists z1 (<{{{{?true;?true;}*{?true;?true;}z1:=*;}{?true;}*}*}*>-49=(gg())'->[?true;{z2:=ff(0/0)-0/0*(0)';++z4:=z4;}]\\exists z5 true)}][?true;{{?true;}*++?true;{{z5'=0,z2'=0&\\exists z7 [{z7'=0,z2'=0&\\forall z7 true}][?true;?true;][?true;]true}++{?[?true;?true;]0>0;++z2:=0;z1:=0;++{?true;++?true;}{?true;++?true;}}{{{?true;++?true;}{?true;++?true;}}*}*}*}++z1':=((z3/60)^5-gg()/62)';++{?([{{?true;}*?true;}*]z7!=ff(21))'<-><?true;++?true;++z5:=*;><z6:=z6;{?true;?true;}?true;>[?true;]true;}*++?0!=z6';][{{?([z2:=0/0-z2;]<{{?true;}*}*>\\forall z4 \\exists z4 true)';{{z7'=0&ff(ff(0-0))=64-((0)'-gg())}++{{?true;}*}*}}*++{z1'=0&PP{55*(z7-z2)+(0/0-0*0+z4')*z7'<=(z6+-29)/z5-(z6'/0+(0*0-0-(z4+0/0)))}}}++z4:=*;][{{{{{{z2:=*;?true;?true;}?[?true;]true;}?qq();}{?true;++{?true;?true;}*}*}?true;++z2:=z6;++{{z1'=0&true->true}z5:=z5;++?\\forall z6 false;}++?true;}{{z7:=(0-0)';z7':=0;}*++{{{?true;?true;}{z7'=0,z2'=0&true}++{z5'=0&true}?true;?true;}++{?true;}*{{?true;}*++?true;++?true;}}*}*}{{z2:=*;}*{{{{?true;?true;}*{{?true;++?true;}++{?true;}*}}*}*}*}?true;][z3':=96--65+ff(z3');]\\forall z4 <{z3'=62&(false)'}++{{?true;++?true;++?true;}++z1:=0;}{z2:=*;{?true;}*}{{z1'=0&true}++z6:=z6;}++{{z6:=0;}*}*{?true;++{?true;++?true;}{?true;}*}><z2:=*;>[{?true;{{?true;}*}*}{z1'=0&<?true;>0>0}]z7=0|[{{{{?true;}*{{{z5:=-58;++{{{{z4'=0&true}}*}*}*}*}*++{?true;?true;?true;++{z5:=*;{{?true;++?true;}++{?true;}*}}{{?true;?true;}?true;}*++{z6'=0,z5'=0&<?true;>true->0!=0}{?true;{?true;++?true;}++{?true;++?true;}++?true;}}*}}*++?true;z6:=gg();}++{?true;}*}*++{z1:=z4;++{{z4:=z4;}*++{{{{{z7'=0&\\forall z2 true}++?\\exists z3 true;}++{z7'=0&<?true;>(!true)}}{z3':=gg();?true;?true;?true;++{?true;++?true;}*++{{?true;}*}*}}*{{{z6'=0,z2'=0&true}}*{?\\exists z2 true;++?true;{z7'=0,z3'=0&true}}++{{?true;++?true;++?true;}++{?true;?true;}*}{?true;?true;++?true;?true;}{z4'=0-0&true->true}}{{z5:=*;}*}*++{{{?true;?true;}?true;}{{z7:=z7;++z6':=0;}++{?true;}*++?true;?true;}z6:=z6;}*{z7'=0,z1'=0&(z3)'=(37^0+z7)'}}++{{z7'=0,z6'=0&[{?true;++{{?true;}*}*}++?true;][z7:=*;++{?true;++?true;}++?true;++?true;]<{?true;}*z3:=0;>true}z2':=ff(z1'-ff(0+0)-gg()*z5);}*}{z5:=(0^0+94)*0;}*}{{z1:=(0)';++z5:=-25;{{{z5':=(70)'-(gg()*(0+0)-(-64+z7));}*}*++z7:=z1;{?true;++{?true;}*++z5:=z5;}}}*++{{{z6'=0,z3'=0&<z1:=z1;>-83 < z5}++{z1':=(2--68)^2*0;++z5':=(-1)';++{{{?true;}*{?true;++?true;}++{?true;}*++{?true;}*}*}*}++?true;}*}*}]<?true;++{{z3:=z1;++{?true;}*?\\forall z5 [?pp(41)<->true;][{{z3'=0*0*(0*0)&<?true;>true}}*](<?true;++?true;>([?true;]true|true)<->\\exists z5 \\forall z5 <?true;>true);}++{z6':=z6;}*}*>(![?true;]<{z7'=0,z3'=0,z1'=0&\\exists z3 <{{{z7'=0,z3'=0,z1'=0&(0)'*z5>=(-81)'}?true;}*}*>(0-(43)'+z2'+z1'=0-z7|z1' < 0)}>([{{{?<?true;>0^2>=0;++?<{z7'=0,z5'=0,z2'=0&<?true;>true}>0^4 < 0^5;}?\\forall z7 (!\\forall z1 true)';}{{{?true;}*}*++{z4:=-30;++?true;++{{?true;}*}*}*}}{{?true;?true;{z5:=0;++?true;++?true;}{{?true;}*++{?true;}*}}*}*]65*z7'>=0&[?-58>0+z3';]true)))&<{z7'=0,z6'=0&0>z2'}>\\exists z6 \\forall z7 (0)'*0-z7' < 0-><{{{{{?0+z3'*(31)'*((z5'+ff(0-0))*(-61+0*5)') < (31)';}*}*}*{{{{{z4'=0&\\forall z3 \\exists z5 <?[{?true;}*]<?true;>true;{{z2:=0;}*++{?true;?true;}?true;?true;}++{{z7'=0,z4'=0,z2'=0&0=0}++?0 < 0;}?[?true;?true;][?true;]true;>(z2*z6+95)'=z2+-33}}*++z3:=z3;}++{{?true;{{z4:=gg();++z2:=(0+0)'-0-(ff(0*0)-56*(0*0));}*++?<{z3'=0+78&[{?true;}*][?true;]true|ff(0)!=-25}>gg()<=z2;++{z2':=ff(gg())+(0-0+0);++{z3'=-50&true}}?true;?qq();?true;{?true;?true;}{?true;}*}}*}*}++{{{z5:=*;}*{{{z7:=*;++{z6'=0/65&ff(0)-(0-0) < ff(-36)}{{z7'=0,z6'=0,z2'=0-0&true}}*}{{z7'=0&<{?true;?true;}?true;?true;>0+0!=(0)'}{{?true;?true;}*++?true;}*++z2:=z2;}}z7:=z7;}*}{{?[{?\\exists z7 [?true;]0>=0;}*++?[?true;]\\forall z5 <?true;>0=0;]<{?true;}*{z2:=z6;++z1':=84;}>pp((0)');++?<{{{?true;++?true;}z3:=0;++?!true;}{z1'=0&0*0!=gg()}}{z2':=(0)'/-12;++{?true;?true;++?true;++?true;}*}><{{{?true;?true;}?true;}*}*><z1:=(0)';?true;><?true;++?true;?true;>true;{{{?true;++{{z7'=0,z5'=0,z3'=0&true|true}{?true;?true;}*}*}++{z4:=z4;}*z4:=*;++{{z7'=0,z3'=0&0-0<=z2}}*}++?true;}}++{{{?true;{{?true;?true;++?true;?true;}*}*}*++{?[z2:=*;](<?true;>true->[?true;]true)';}*}z6:=(59)';z7:=*;}*}}{?true;++{{z6'=gg()*z3,z4'=0&((\\forall z7 (0*0)'^3=gg()-z2<->true)|(z3'+z2+(0+0-(0+0)))/z1'-(-58-(ff(0)+-27)^4)=gg()/z3')&[?true;]z6*gg()<=0}}*}}++?true;}*}*>[?true;][{?true;}*]0<=0)|<{{{{{z4'=0&true}{z7'=0&true}++{z1:=gg();++{{z1'=0&<{{{z4':=30;}*z1:=gg()*(0*0);++{z6:=0;{?true;++?true;}++{z4:=0;}*}{?true;++?true;}*}++?[?true;++?true;]0 < 0;{z6'=0,z3'=0,z2'=0&[?true;]true}{?true;++?true;?true;}++z6:=z6;{?true;}*?true;?true;++{?true;}*++{z7'=0&<?true;>true}}{{{?true;}*?true;?true;++{z4'=0,z2'=0&true}z5:=z5;}*}*{?true;}*>\\forall z4 \\exists z1 (!true)->true&<z3:=(z5'+z1)^1-(gg()+ff(0^1-0));>false}}*}++{z6:=*;}*}{{z7'=0&<{{{{?true;}*}*}*++{z2':=ff((z1+z6-97)/-96)+0;}*}++z7':=56;++z4:=z4;>((z1*0*(83*63))' < z5'-z7->\\forall z3 0-(gg()+-53) < z3'+z4)}++{{?true;{?true;}*++?true;{{z3:=z7';++{{{?true;?true;}?true;?true;++?<?true;>true;}++?true;{{?true;}*++{?true;}*}}*}++{z2:=(0-0)*0+(46)';++?true;++z3:=z3;}{z5'=0&<?true;>true}}*}{{{{{?true;++z4:=0-gg();}{{?true;}*?true;?true;}*z2:=0;}*}*}*{?true;z3:=z7;}*}*++?true;}++?true;{z2'=0&((z6-(0-z3'^4))*z7')^1*(-71-(z2+-81)*(ff(0^3)-gg())+gg())>=gg()+34}++z4:=z4;++?true;{{z7'=0,z1'=0&[?<{{z7'=0,z4'=0&true}}*>[?true;++?true;]<?true;>true;]<{z7'=0&true}>[{?true;}*++z7':=0;][{?true;}*]<?true;>true|\\exists z7 (PP{\\exists z4 0 < 0}->0^3+0>ff(0)--96)}}*++{z6:=z6;}*++{{{{z2'=0&0/0-(0+0)>=(54)'}{?true;}*}?true;}*}*}}{{z3':=z5*((0+gg())'^0+z5');z7:=(0)'*((z2)'+-28);}{{z2:=z6';}*++z7:=*;}++{{z7:=z6;{{?<{{{?true;}*++{?true;}*}*}*>\\exists z5 [{?true;}*]\\forall z2 [?true;]true&true;++{z5'=z1+31&\\exists z4 z1'!=z2'}}++z4:=*;}}{?[{z2'=0-53&[{z7'=0,z1'=0&<?true;>0/0 < z7}][?true;++{?true;}*z4:=0;]\\exists z1 <?true;?true;>(!true)}][?\\forall z3 true->\\forall z4 true;{z6'=0^5,z1'=0&<{?true;}*>\\exists z6 true}++{?true;++{z4'=0,z2'=0&<?true;>true}}++{?true;?true;++z1:=z1;}*](([z1:=z1;]<{?true;}*>[?true;]true<-><{?true;?true;}*>[z3:=*;](true->true))|true);?true;}{{{z1'=0&true}}*}*++{?\\forall z2 [?![{{{z6'=0/0&[?true;]true}}*}*]z2'!=z6';]<{{{z5':=gg();}*}*}*>[{?true;}*]\\forall z7 z5!=ff(0);}*}*}*}{{{{{{{?true;}*}*{z7'=0&true}{{{{?true;}*}*++{{{?true;++?true;}{?true;?true;++{?true;}*}}*++z3':=0;}++?0+0+(0)'>=z6'*(0)';++{z6:=z6;{{?true;}*}*}*}{z6'=86,z1'=0&\\forall z1 [{?true;++?true;?true;}{{z1'=0&true}++?true;++?true;}]0 < z7|0 < z5*z4'*(0*(0+0-0*0))}}*}{{{{z7:=*;++z4:=-58;{{z7'=0,z2'=0&\\exists z6 0 < 0}}*}++{z6'=0,z5'=0,z4'=0&z7'=z4'}}z4:=*;{{?true;}*}*{z1:=*;}*++{z2:=0;}*}*}*}*++{?true;++{{{{{{?true;++z2':=0-0;}{z5:=*;++?true;}++{{?true;++?true;?true;}{?true;}*{?true;}*}{z7:=0;?true;++z7:=*;}}{{z2'=76&ff(0)-0*0>22}++z1:=*;}}?true;}*++?[{z1:=z1;}*][?true;]<{?true;?true;}*{?true;}*?true;?true;>\\exists z4 z5 < 0-0;?true;}++{{{{{z3:=(0)'-58;}*}*}*++z5:=z5;}++?true;}*}{z7:=z7;++{?true;}*}*{{{{{?true;{?true;}*}{z2:=z2;++?true;}++?true;}++{{{z6'=0&true}}*++{{?true;}*}*}++{?true;?true;}*++?true;}*++{{z7'=0,z2'=gg()&<?true;++?true;>\\exists z7 true}}*{{{?true;}*}*}*++{z1'=0&<z5:=(0+0)^4;>(<?true;>true<-><z1:=z1;>0 < 0)}}{{{{z5'=61&pp(ff(0))}++?true;++?true;?false;}++{{{?true;?true;}{?true;}*}z4:=0+0;}*}++z4:=z7;{{?true;++?true;}*{?true;?true;++z3:=*;}}*}{{{{{?true;}*}*++{?true;?true;}{z6'=0&true}}++{{?true;++?true;}++?true;++?true;}z6:=z6;}{?true;{{?true;++?true;}++{?true;}*}}*}{{{{?true;++?true;}++?true;?true;}++{{?true;}*}*}++z5:=0-0*0;}*++{{{z7'=0,z5'=0,z1'=0&\\exists z2 true}{?true;++?true;?true;}}*{?true;z4:=*;}*++z2:=(1)';{?true;}*}*z1:=z1;}}++{{{z5:=*;++?true;}{z6'=-41&\\exists z7 true}++z5':=-49;z3:=z5+((z2)'-(0)');}{z7'=0&(z3!=ff(z4))'}}{{{?true;}*}*}*}++{z7:=z5';{z5:=z2;}*}?[z1':=0;++?true;]\\exists z4 \\exists z4 <{z4:=z4;?true;++z7:=z1'/(0-0*0-72*(0)')+(20+(z1+z1'))^3;}++?<?z4>=z3'*(0)'+0;>z2'=z1'+(10)'+z6;>true;}++{{z1'=0&[{z5:=*;}*][{{{{{{z4'=0,z1'=0&true|true}}*++{z1'=0&[{?true;}*]true}}*}*}*++z2:=z2-0;{z4':=0;{?0 < 0;?true|true;++z3:=z3;++{?true;}*}++{{z4:=0;++{z1'=0&true}}++{{?true;}*}*}*{?true;++{?true;}*++z2:=0;}*}}*++{z4'=0,z3'=0&<z4':=ff(0);>0!=(10)'}{?true;}*][?true;]<{z1'=0&(-23+0^0)*z5'!=gg()-(66)'}>(\\exists z7 [{z5:=0;?true;?true;}*{{?true;}*z2':=0;}{?true;}*{?true;}*++z2':=38;]<{z5:=z5;}*>\\exists z2 true->\\forall z7 (true)'|\\forall z6 [{?true;++{?true;}*}*]z2-(0)'>=z2+0)}}*++?[{{{?\\exists z6 <z2:=*;{?true;}*><{?true;}*><{{?true;++?true;}++?true;?true;}*>z6>z5;}*}*}*{{{z2':=ff(z6')+((0+0)/(0+0))';++{z5'=ff(0)&<z3:=*;><?true;>([?true;]true<->true|true)}}*}*{z5'=gg()&<{?true;}*{{?<?true;>true;}*++z4:=z1;++{?true;?true;}{?true;}*}++{{{?true;?true;}z7:=z7;}{?true;?true;}*++{?true;++?true;++?true;}++?true;++?true;}z4:=*;>([{{?true;}*++{?true;}*}*++{{?true;}*}*{?true;++?true;}?true;][?true;++?true;][?true;]\\forall z4 <?true;>true<->\\forall z2 \\exists z7 [{z6'=0,z3'=0,z2'=0&\\forall z6 true}]\\exists z5 0 < 0)}++?true;}{{z2'=0+-56&z2*(z7*z4/(((0+0)/0)^2*(0*0*(0+0))'))=z5}}*{?true;?true;}{{z1:=z1;z5:=0;++{z7'=0,z5'=39,z2'=z7&<?true;++?true;>0 < 0&\\exists z3 [?true;]true}{?true<-><?true;>true;}*}{{z5:=z2;z6:=z6;}{z1':=0;{?true;++?true;}}*++?true;}*}z6:=z7'+(26-(z7*(0)'+0*0*(0)'));z7:=*;](0-z1)/85>z3;}}{?true;{z3'=95-(0^0-ff(64*97+62))/40&\\exists z4 qq()}++{z1:=z1;}*{?<{{{{{?true;++{?true;}*}*{?true;++?true;}*{{?true;}*++?true;++?true;}}?[{?true;}*++?true;?true;](!\\exists z6 true);++z6':=z5-z2-(z5'-(gg()-0));}z5:=0+z5;++{?true;z2:=z2;++z4:=gg();}*}{{{z4':=0*0;?true;}*?true;z1:=ff((0)');++z3:=0^4*(40*0--37);}{z4'=gg()&z3'^0>(3)'}?true;}{{{?\\forall z4 (true&true);++?true;}{z1:=z1;{z4:=z4;}*}*++?true;}++{z4'=0&true}}}*++z4:=z4;><{{{{{?true;}*{{z2:=0;}*}*}{{?true;++?true;}++?true;?true;++z6:=0;}*}{z7:=(0+0)*z7+0;}*}*z3:=(80)'+z5;++{z6':=0+ff(0/0)-(77-0/0/(0*0))-((0*35)^2)';++{{?true;++{?true;}*}*++{{?true;++?true;}++?true;?true;}?true;}?\\exists z4 \\exists z2 \\exists z4 true;++{?true;}*++{z2:=23;{{?true;++?true;}++?true;?true;}}{z1'=0&true}}*}*>\\forall z7 [{?\\exists z4 [{?true;?true;}*{?true;++?true;}{?true;++?true;}]ff(0)-(0)'>=(0)'^2|gg()^3+2 < (gg()+0)/z2';}*]z5'-0*ff(z5)>=gg();{{{{{{{?true;{z6'=26&[?true;]true|(true<->true)}}z7:=-26;}{{z6:=*;z5:=z3';++{?true;}*{?true;++?true;}++{z7'=0,z3'=0&<?true;>true}}++z3:=z3;?true;}}{{{{?true;++?true;}z1:=z1;++?true;++?true;?true;}z5:=0;}{z4'=54--17*(0+0)&\\exists z4 (true)'}}?true;++z5:=z5;++{{{?true;}*++{{?true;++?true;}{?true;}*}{z5'=0,z2'=0&0 < 0}}++z1:=z1;}*}{{{z5'=96&true}}*++{?qq();}*}}*{{{{z7'=0&[{z2:=*;}*]<{?true;?true;++{?true;}*}z1:=z1;{?true;}*>\\forall z5 (\\forall z1 true->\\forall z4 true)}z2:=35;++?[{?true;++z1:=z1;}{{{?true;}*}*++?true;}{{?true;?true;}?true;}?true;]true;}++{{{{{?true;}*}*{z1:=0*0;}*{{z6'=0&true}{?true;}*}{{?true;++?true;}++{?true;}*}}{{{{?true;++?true;}++?true;++?true;}++?true;?true;++?true;}{?true;++{?true;}*}{?true;?true;}*}{?true->true;{?true;?true;}*}{{?true;}*{?true;}*++?true;}}*}*}++{?((ff(0))'+(0-0)^5)/z3' < (gg()+11)';}*{{z6':=z6'-z5/43;++{?\\exists z7 (true&true);++{?true;?true;++?true;?true;}*}{z2':=z4';{?true;?true;++?true;?true;}}?true;{{?true;++?true;}++?true;++?true;}}++{{{?true;?true;++{?true;}*++?true;}++z3:=z3;++{?true;++?true;}?true;?true;}++{?true;?true;++{?true;}*}*?<z5:=0;>\\forall z5 true;}++z3:=*;}++{{{{?true;?true;++?true;++?true;}*}*{z1:=z1;}*?true;}{?true;++{?true;{z5'=0&true}}*{{z7:=0;}*}*}++{z5'=0,z4'=0,z1'=0&\\exists z3 [{z1:=0;++{?true;}*}++z3':=0;++{?true;}*]<?true;><?true;++?true;><?true;>true}}++{?true;}*}}{{?true;++z5:=z7';{z5:=gg()*((0+0)*44)';{?true;}*}*}*}*++?!(<{{{z5':=0-0;++{?true;}*}++{{{?true;}*}*}*}?false;}*>\\exists z1 [{{?true;}*++?true;}{{{?true;}*}*++{?true;}*}]true&<{{z1:=z1;}*z3:=z6;}*>(z6<=gg()<->\\exists z1 (\\forall z7 false)')->\\forall z2 ((gg()^2)^4)^4=z4*(z7'+(ff(0)-0/0)')^0);++{z2:=41*(0-(z5'+-96)/(22*(0-z7')))^2;?0+z2^3!=0;++{z7:=z7;}*{{z4:=z4;}*++{{?PP{true&true};{{?true;}*++z5:=z3;}}?true;++{z5:=z5;{z6':=0+0;}*}*}{{{z6'=0-0,z1'=0&\\exists z1 \\exists z6 true}++?<?true;++?true;>\\forall z2 true;}{z7:=z7;}*}*}}{z1:=z1;}*}}{{{z3'=0&(54--54)*0!=-33}}*++?true;}}>z4' < 0+0"
    KeYmaeraXLexer(n).head.tok shouldBe(LPAREN)
  }
}
