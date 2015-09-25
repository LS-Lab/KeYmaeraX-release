KeYmaera parser and pretty printer


The KeYmaera parsers typically look something like this:

object SpecificParser {
  type TargetTy = ...
  val precedence : List[PackratParser[TargetTy]] = p1 :: p2 :: ... :: Nil
  lazy val specificParser = precedence.reduce(_ | _)

  lazy val p1 : PackratParser[TargetTy]
  lazy val p1 : PackratParser[TargetTy]
}

The TargetTy is the type of the target of the parser. The precedence list
is a list of all subparsers, arranged by precedence. For instance, if + binds
tighter then ; then the precedence list might look like:

  sequenceP :: plusP :: Nil

ADDING A NEW SUBPARSER
----------------------
When adding a new subparser, ensure that it's a lazy val, and add it to the 
correct place in the precedence list. Everything else should take care of 
itself.
  
