# KeYmaera X Coding Conventions

Especially for the soundness-critical core, we adopt the following coding conventions:

1) Code should be optimized for correctness by a strict "correctness-first" principle.

2) Code should further be optimized for readability and simplicity, making it obvious what it does so that it is easier
   to check whether it is correct.

3) Use pure functional code without mutable data structures and without side effects. Algebraic data types via case
   classes are encouraged along with value pattern matching such as: val Imply(p,q) = f. One downside is that
   incomprehensible MatchErrors are thrown if f is not of this shape, which may require additional error messages.

4) Requires preconditions are strictly enforced. Ample use of asserts, assumes, and ensures postconditions are
   encouraged. Their string arguments should state the expected *positive* outcome, unlike thrown exceptions, whose
   strings talk negatively about what failed. No hidden aspects that are crucial to the understanding of the correctness
   of the local code is acceptable without documentation or local checking via asserts even if that causes redundant
   assertion checking.

   `assert`, `assume`, `require`, `ensures`

   If there is a way of running your core code to obtain an incorrect answer or incorrect behavior without a `requires`
   contract failing, then your code is wrong. If you detect invalid input by a `requires` contracts, then it's the fault
   of the program calling yours. If your assert or ensures contracts fails, then at least it prevented incorrect output
   from happening.

5) The code should follow the principle of least astonishment, not using surprising or unconventional Scala features in
   the prover core. Preferably do not make the correctness of code depend on the order that match cases are placed in,
   without an explicit comment indicating that. Matches may be reordered to have common cases checked first.

6) Let's not be dogmatic about the writing part of code. Simplicity and elegance are always preferred over lexical
   style. Lines that are longer than 120 characters are discouraged, though, for readability reasons.

7) Brief scaladoc compatible one-line comments `/** like this */` are encouraged for documentation purposes except when
   more lines are needed, in which case the style is
   ```scala
   /**
     * Comment styles should
     * be like this instead.
     * @param x specify some interesting position argument.
     * @return whatever we give back
     */
   ```
   The use of `// one line comments` is reserved for internal comments such as in the middle of a function.

8) Type delimiters go short right after the name and return types should be declared for public functions, so
   ```scala
   def someMemorableFunction(x: Int, p: Function): Boolean
   ```
   instead of
   ```scala
   def someMemorableFunction(x : Int, p :Function) : Boolean
   ```

   If/while expect a space around their condition. Braces are encouraged when the range is otherwise unclear or when
   else is used, so
   ```scala
   if (x>0) {
     beHappy()
   } else {
     doSomethingElse()
   }
   ```

   Use lowercase camelCase naming conventions for functions/values and uppercase CamelCase for types. Stay clear of
   meaningless or vague names like tmpzz or doNext or checkSome.

9) For reasons of modularity, abstraction, and documentation, LIMIT accessibility of functions and types to a
   need-to-know basis. Use the `private[this]` or private modifier if nobody needs to know/use it. Use `protected`
   and/or`private[packagename]` if `private` is too restrictive. ONLY use public access for parts that are conceptually
   important interfaces to the rest of the system and that you personally commit to support long-term. For the purpose
   of writing test cases, remember that test cases declared in the same package get to see`private[packagename]` and
   protected functions. `PrivateMethodTester` can be used to test private functions (albeit with unfortunate notational
   overhead).

10) Document your source code and its intended use cases well. Seriously! Including `package.scala` overviews and
    argument explanations. If something is important enough to be publicly accessible, it should be important enough for
    you to explain what it does, or else others are free to delete undocumented public functions arbitrarily to improve
    code quality, which loses code features.

11) Global variables cause incredible pain later, but variables or initialized values in objects are just global
    variables with a name prefix. Stay away from using objects, because you may cause incredibly subtle static
    initializer order bugs elsewhere later on.

    "Making something variable is easy. Controlling duration of constancy is the trick."
    -- Alan J. Perlis 66

12) Don't make other developers suffer endlessly by using `println` or tactic debug steps all over the map.
    Use `with Logging` or use `private val logger = Logger(getClass)` to get `logger.debug("Information")` to make it
    possible to more selectively control the messages you are interested in.
