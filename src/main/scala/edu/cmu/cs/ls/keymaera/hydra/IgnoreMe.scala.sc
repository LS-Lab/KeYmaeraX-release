import com.mongodb.casbah.Imports._
import edu.cmu.cs.ls.keymaera.hydra.MongoDB

val m = MongoDB


m.getModelList("a").map(x => print(x.toString()))