import com.mongodb.casbah.Imports._
import edu.cmu.cs.ls.keymaera.hydra.MongoDB

val m = MongoDB
m.createUser("username", "password")

val u = MongoDBObject("username" -> "nfulton")
m.mongoClient("keymaera")("users").insert(u)