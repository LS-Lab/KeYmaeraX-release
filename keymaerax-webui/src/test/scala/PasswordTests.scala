import edu.cmu.cs.ls.keymaerax.hydra.Password
import org.scalatest.{FlatSpec, Matchers}

/**
  * For debugging cross-platform password hashing inconsistencies.
  * Created by bbohrer on 1/12/16.
  */
class PasswordTests extends FlatSpec with Matchers {
  "Password hashing" should "have the same result on all platforms" in {
    val password = "guest".toCharArray
    val iterations = 10000
    val salt = "q6+NJQ23N9YcPo3JdOr3rhuSmuwnaIBxjIcuC7DFwhb2fUequYqh0E8fhDmtzX79NUeGt/sMcbc/ygMXOTn+gfVbR3X4wMogx28M/yMf6HP2fEv6kc+Uiu1dQnqDHd+Y7aaE7kf/VR1QJ6LlyEQxcrEpuhKmqzgCMwc/ajG34cd3qPnBVuiqeECx6SZsfqAcKFMiC/jtTHJH8JyS+4jDstmvZ4mgT7KBo36n2ODoQGd+gzHuuY7NkLxjdpKCe4wkLWGEneHf3TiQzf1EvVXVO26XRoT/86cTv2nBZatrgeslsta1+CHP6lB1aIuzdq9VfEwAYYRhrWdSAeSc0gQhYtw11Xx2HNX3K/KX9kqYML/IOEJ9EOB92SgSk6H0UWvSB4EbHuzyc+HinEYVgSHUkd44VCU/nXcTFobFh8e3NI4H65lIXzQ8k8CROuBoyOLn70roNWszOASzRUaiwFtS4GimmOv3iIgIJbpXKirowDsXGLJSKr+quXRfMRxp8u5RYPbZChGfKCE/H6JGnp9gWHvOZBnzlh3mCvv8r/RJqdFD70LJvBkcCz+l5c/fXuQXpAMYG6a8PUxP7qQ26cvza7YeDVnXs5LnRMyJD8cXdHFc333QOQRA2raocH5N/EUDL/QlU3yJf+RxmRGobAaz1J+66kiErbjl7Iu+QbOY5Mo="
      .getBytes("UTF-8")
    val hash = "CdAe+W5p0gUlfcWIPYcqKtwbiJs="
    Password.hash(password, salt, iterations) shouldBe hash
  }
}
