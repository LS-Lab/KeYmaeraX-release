package 
// AUTO-GENERATED Slick data model
/** Stand-alone Slick data model for immediate use */
object Tables extends {
  val profile = scala.slick.driver.SQLiteDriver
} with Tables

/** Slick data model trait for extension, choice of backend or usage in the cake pattern. (Make sure to initialize this late.) */
trait Tables {
  val profile: scala.slick.driver.JdbcProfile
  import profile.simple._
  import scala.slick.model.ForeignKeyAction
  // NOTE: GetResult mappers for plain SQL are only generated for tables where Slick knows how to map the types of all columns.
  import scala.slick.jdbc.{GetResult => GR}
  
  /** DDL for all tables. Call .create to execute. */
  lazy val ddl = Clterms.ddl ++ Completedtasks.ddl ++ Config.ddl ++ Models.ddl ++ Proofs.ddl ++ Prooftacticinput.ddl ++ Tacticonproof.ddl ++ Tactics.ddl ++ Users.ddl
  
  /** Entity class storing rows of table Clterms
   *  @param termid Database column termId DBType(TEXT), PrimaryKey
   *  @param clterm Database column clTerm DBType(TEXT)
   *  @param proofid Database column proofId DBType(TEXT)
   *  @param nodeid Database column nodeId DBType(TEXT)
   *  @param status Database column status DBType(TEXT) */
  case class CltermsRow(termid: Option[String], clterm: Option[String], proofid: Option[String], nodeid: Option[String], status: Option[String])
  /** GetResult implicit for fetching CltermsRow objects using plain SQL queries */
  implicit def GetResultCltermsRow(implicit e0: GR[Option[String]]): GR[CltermsRow] = GR{
    prs => import prs._
    CltermsRow.tupled((<<?[String], <<?[String], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table CLTerms. Objects of this class serve as prototypes for rows in queries. */
  class Clterms(_tableTag: Tag) extends Table[CltermsRow](_tableTag, "CLTerms") {
    def * = (termid, clterm, proofid, nodeid, status) <> (CltermsRow.tupled, CltermsRow.unapply)
    
    /** Database column termId DBType(TEXT), PrimaryKey */
    val termid: Column[Option[String]] = column[Option[String]]("termId", O.PrimaryKey)
    /** Database column clTerm DBType(TEXT) */
    val clterm: Column[Option[String]] = column[Option[String]]("clTerm")
    /** Database column proofId DBType(TEXT) */
    val proofid: Column[Option[String]] = column[Option[String]]("proofId")
    /** Database column nodeId DBType(TEXT) */
    val nodeid: Column[Option[String]] = column[Option[String]]("nodeId")
    /** Database column status DBType(TEXT) */
    val status: Column[Option[String]] = column[Option[String]]("status")
    
    /** Foreign key referencing Proofs (database name proofs_FK_1) */
    lazy val proofsFk = foreignKey("proofs_FK_1", proofid, Proofs)(r => r.proofid, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Clterms */
  lazy val Clterms = new TableQuery(tag => new Clterms(tag))
  
  /** Entity class storing rows of table Completedtasks
   *  @param stepid Database column stepId DBType(TEXT), PrimaryKey
   *  @param proofid Database column proofId DBType(TEXT)
   *  @param idx Database column idx DBType(INTEGER)
   *  @param termid Database column termId DBType(TEXT)
   *  @param prooftacticid Database column proofTacticId DBType(TEXT) */
  case class CompletedtasksRow(stepid: String, proofid: Option[String], idx: Int, termid: Option[String], prooftacticid: Option[String])
  /** GetResult implicit for fetching CompletedtasksRow objects using plain SQL queries */
  implicit def GetResultCompletedtasksRow(implicit e0: GR[String], e1: GR[Option[String]], e2: GR[Int]): GR[CompletedtasksRow] = GR{
    prs => import prs._
    CompletedtasksRow.tupled((<<[String], <<?[String], <<[Int], <<?[String], <<?[String]))
  }
  /** Table description of table completedTasks. Objects of this class serve as prototypes for rows in queries. */
  class Completedtasks(_tableTag: Tag) extends Table[CompletedtasksRow](_tableTag, "completedTasks") {
    def * = (stepid, proofid, idx, termid, prooftacticid) <> (CompletedtasksRow.tupled, CompletedtasksRow.unapply)
    /** Maps whole row to an option. Useful for outer joins. */
    def ? = (stepid.?, proofid, idx.?, termid, prooftacticid).shaped.<>({r=>import r._; _1.map(_=> CompletedtasksRow.tupled((_1.get, _2, _3.get, _4, _5)))}, (_:Any) =>  throw new Exception("Inserting into ? projection not supported."))
    
    /** Database column stepId DBType(TEXT), PrimaryKey */
    val stepid: Column[String] = column[String]("stepId", O.PrimaryKey)
    /** Database column proofId DBType(TEXT) */
    val proofid: Column[Option[String]] = column[Option[String]]("proofId")
    /** Database column idx DBType(INTEGER) */
    val idx: Column[Int] = column[Int]("idx")
    /** Database column termId DBType(TEXT) */
    val termid: Column[Option[String]] = column[Option[String]]("termId")
    /** Database column proofTacticId DBType(TEXT) */
    val prooftacticid: Column[Option[String]] = column[Option[String]]("proofTacticId")
    
    /** Foreign key referencing Clterms (database name CLTerms_FK_1) */
    lazy val cltermsFk = foreignKey("CLTerms_FK_1", termid, Clterms)(r => r.termid, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
    /** Foreign key referencing Proofs (database name proofs_FK_2) */
    lazy val proofsFk = foreignKey("proofs_FK_2", proofid, Proofs)(r => r.proofid, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
    /** Foreign key referencing Tacticonproof (database name tacticOnProof_FK_3) */
    lazy val tacticonproofFk = foreignKey("tacticOnProof_FK_3", prooftacticid, Tacticonproof)(r => r.prooftacticid, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Completedtasks */
  lazy val Completedtasks = new TableQuery(tag => new Completedtasks(tag))
  
  /** Entity class storing rows of table Config
   *  @param configid Database column configId DBType(TEXT), PrimaryKey
   *  @param configname Database column configName DBType(TEXT)
   *  @param key Database column key DBType(TEXT)
   *  @param value Database column value DBType(TEXT) */
  case class ConfigRow(configid: Option[String], configname: Option[String], key: Option[String], value: Option[String])
  /** GetResult implicit for fetching ConfigRow objects using plain SQL queries */
  implicit def GetResultConfigRow(implicit e0: GR[Option[String]]): GR[ConfigRow] = GR{
    prs => import prs._
    ConfigRow.tupled((<<?[String], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table config. Objects of this class serve as prototypes for rows in queries. */
  class Config(_tableTag: Tag) extends Table[ConfigRow](_tableTag, "config") {
    def * = (configid, configname, key, value) <> (ConfigRow.tupled, ConfigRow.unapply)
    
    /** Database column configId DBType(TEXT), PrimaryKey */
    val configid: Column[Option[String]] = column[Option[String]]("configId", O.PrimaryKey)
    /** Database column configName DBType(TEXT) */
    val configname: Column[Option[String]] = column[Option[String]]("configName")
    /** Database column key DBType(TEXT) */
    val key: Column[Option[String]] = column[Option[String]]("key")
    /** Database column value DBType(TEXT) */
    val value: Column[Option[String]] = column[Option[String]]("value")
  }
  /** Collection-like TableQuery object for table Config */
  lazy val Config = new TableQuery(tag => new Config(tag))
  
  /** Entity class storing rows of table Models
   *  @param modelid Database column modelId DBType(TEXT), PrimaryKey
   *  @param userid Database column userId DBType(TEXT)
   *  @param name Database column name DBType(TEXT)
   *  @param date Database column date DBType(TEXT)
   *  @param description Database column description DBType(TEXT)
   *  @param filecontents Database column fileContents DBType(TEXT)
   *  @param publink Database column publink DBType(TEXT)
   *  @param title Database column title DBType(TEXT) */
  case class ModelsRow(modelid: Option[String], userid: Option[String], name: Option[String], date: Option[String], description: Option[String], filecontents: Option[String], publink: Option[String], title: Option[String])
  /** GetResult implicit for fetching ModelsRow objects using plain SQL queries */
  implicit def GetResultModelsRow(implicit e0: GR[Option[String]]): GR[ModelsRow] = GR{
    prs => import prs._
    ModelsRow.tupled((<<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table models. Objects of this class serve as prototypes for rows in queries. */
  class Models(_tableTag: Tag) extends Table[ModelsRow](_tableTag, "models") {
    def * = (modelid, userid, name, date, description, filecontents, publink, title) <> (ModelsRow.tupled, ModelsRow.unapply)
    
    /** Database column modelId DBType(TEXT), PrimaryKey */
    val modelid: Column[Option[String]] = column[Option[String]]("modelId", O.PrimaryKey)
    /** Database column userId DBType(TEXT) */
    val userid: Column[Option[String]] = column[Option[String]]("userId")
    /** Database column name DBType(TEXT) */
    val name: Column[Option[String]] = column[Option[String]]("name")
    /** Database column date DBType(TEXT) */
    val date: Column[Option[String]] = column[Option[String]]("date")
    /** Database column description DBType(TEXT) */
    val description: Column[Option[String]] = column[Option[String]]("description")
    /** Database column fileContents DBType(TEXT) */
    val filecontents: Column[Option[String]] = column[Option[String]]("fileContents")
    /** Database column publink DBType(TEXT) */
    val publink: Column[Option[String]] = column[Option[String]]("publink")
    /** Database column title DBType(TEXT) */
    val title: Column[Option[String]] = column[Option[String]]("title")
    
    /** Foreign key referencing Users (database name users_FK_1) */
    lazy val usersFk = foreignKey("users_FK_1", userid, Users)(r => r.email, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Models */
  lazy val Models = new TableQuery(tag => new Models(tag))
  
  /** Entity class storing rows of table Proofs
   *  @param proofid Database column proofId DBType(TEXT), PrimaryKey
   *  @param modelid Database column modelId DBType(TEXT)
   *  @param name Database column name DBType(TEXT)
   *  @param description Database column description DBType(TEXT)
   *  @param date Database column date DBType(TEXT)
   *  @param closed Database column closed DBType(INTEGER) */
  case class ProofsRow(proofid: Option[String], modelid: Option[String], name: Option[String], description: Option[String], date: Option[String], closed: Option[Int])
  /** GetResult implicit for fetching ProofsRow objects using plain SQL queries */
  implicit def GetResultProofsRow(implicit e0: GR[Option[String]], e1: GR[Option[Int]]): GR[ProofsRow] = GR{
    prs => import prs._
    ProofsRow.tupled((<<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[Int]))
  }
  /** Table description of table proofs. Objects of this class serve as prototypes for rows in queries. */
  class Proofs(_tableTag: Tag) extends Table[ProofsRow](_tableTag, "proofs") {
    def * = (proofid, modelid, name, description, date, closed) <> (ProofsRow.tupled, ProofsRow.unapply)
    
    /** Database column proofId DBType(TEXT), PrimaryKey */
    val proofid: Column[Option[String]] = column[Option[String]]("proofId", O.PrimaryKey)
    /** Database column modelId DBType(TEXT) */
    val modelid: Column[Option[String]] = column[Option[String]]("modelId")
    /** Database column name DBType(TEXT) */
    val name: Column[Option[String]] = column[Option[String]]("name")
    /** Database column description DBType(TEXT) */
    val description: Column[Option[String]] = column[Option[String]]("description")
    /** Database column date DBType(TEXT) */
    val date: Column[Option[String]] = column[Option[String]]("date")
    /** Database column closed DBType(INTEGER) */
    val closed: Column[Option[Int]] = column[Option[Int]]("closed")
    
    /** Foreign key referencing Models (database name models_FK_1) */
    lazy val modelsFk = foreignKey("models_FK_1", modelid, Models)(r => r.modelid, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Proofs */
  lazy val Proofs = new TableQuery(tag => new Proofs(tag))
  
  /** Entity class storing rows of table Prooftacticinput
   *  @param prooftacticid Database column proofTacticId DBType(TEXT), PrimaryKey
   *  @param inputorder Database column inputOrder DBType(INTEGER)
   *  @param input Database column input DBType(TEXT) */
  case class ProoftacticinputRow(prooftacticid: Option[String], inputorder: Option[Int], input: Option[String])
  /** GetResult implicit for fetching ProoftacticinputRow objects using plain SQL queries */
  implicit def GetResultProoftacticinputRow(implicit e0: GR[Option[String]], e1: GR[Option[Int]]): GR[ProoftacticinputRow] = GR{
    prs => import prs._
    ProoftacticinputRow.tupled((<<?[String], <<?[Int], <<?[String]))
  }
  /** Table description of table proofTacticInput. Objects of this class serve as prototypes for rows in queries. */
  class Prooftacticinput(_tableTag: Tag) extends Table[ProoftacticinputRow](_tableTag, "proofTacticInput") {
    def * = (prooftacticid, inputorder, input) <> (ProoftacticinputRow.tupled, ProoftacticinputRow.unapply)
    
    /** Database column proofTacticId DBType(TEXT), PrimaryKey */
    val prooftacticid: Column[Option[String]] = column[Option[String]]("proofTacticId", O.PrimaryKey)
    /** Database column inputOrder DBType(INTEGER) */
    val inputorder: Column[Option[Int]] = column[Option[Int]]("inputOrder")
    /** Database column input DBType(TEXT) */
    val input: Column[Option[String]] = column[Option[String]]("input")
  }
  /** Collection-like TableQuery object for table Prooftacticinput */
  lazy val Prooftacticinput = new TableQuery(tag => new Prooftacticinput(tag))
  
  /** Entity class storing rows of table Tacticonproof
   *  @param prooftacticid Database column proofTacticId DBType(TEXT), PrimaryKey
   *  @param proofid Database column proofId DBType(TEXT)
   *  @param tacticsid Database column tacticsId DBType(TEXT)
   *  @param nodeid Database column nodeId DBType(TEXT)
   *  @param formulaid Database column formulaId DBType(TEXT)
   *  @param auto Database column auto DBType(TEXT)
   *  @param status Database column status DBType(TEXT) */
  case class TacticonproofRow(prooftacticid: Option[String], proofid: Option[String], tacticsid: Option[String], nodeid: Option[String], formulaid: Option[String], auto: Option[String], status: Option[String])
  /** GetResult implicit for fetching TacticonproofRow objects using plain SQL queries */
  implicit def GetResultTacticonproofRow(implicit e0: GR[Option[String]]): GR[TacticonproofRow] = GR{
    prs => import prs._
    TacticonproofRow.tupled((<<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table tacticOnProof. Objects of this class serve as prototypes for rows in queries. */
  class Tacticonproof(_tableTag: Tag) extends Table[TacticonproofRow](_tableTag, "tacticOnProof") {
    def * = (prooftacticid, proofid, tacticsid, nodeid, formulaid, auto, status) <> (TacticonproofRow.tupled, TacticonproofRow.unapply)
    
    /** Database column proofTacticId DBType(TEXT), PrimaryKey */
    val prooftacticid: Column[Option[String]] = column[Option[String]]("proofTacticId", O.PrimaryKey)
    /** Database column proofId DBType(TEXT) */
    val proofid: Column[Option[String]] = column[Option[String]]("proofId")
    /** Database column tacticsId DBType(TEXT) */
    val tacticsid: Column[Option[String]] = column[Option[String]]("tacticsId")
    /** Database column nodeId DBType(TEXT) */
    val nodeid: Column[Option[String]] = column[Option[String]]("nodeId")
    /** Database column formulaId DBType(TEXT) */
    val formulaid: Column[Option[String]] = column[Option[String]]("formulaId")
    /** Database column auto DBType(TEXT) */
    val auto: Column[Option[String]] = column[Option[String]]("auto")
    /** Database column status DBType(TEXT) */
    val status: Column[Option[String]] = column[Option[String]]("status")
    
    /** Foreign key referencing Proofs (database name proofs_FK_1) */
    lazy val proofsFk = foreignKey("proofs_FK_1", proofid, Proofs)(r => r.proofid, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
    /** Foreign key referencing Tactics (database name tactics_FK_2) */
    lazy val tacticsFk = foreignKey("tactics_FK_2", tacticsid, Tactics)(r => r.tacticid, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Tacticonproof */
  lazy val Tacticonproof = new TableQuery(tag => new Tacticonproof(tag))
  
  /** Entity class storing rows of table Tactics
   *  @param tacticid Database column tacticId DBType(TEXT), PrimaryKey
   *  @param name Database column name DBType(TEXT)
   *  @param clazz Database column clazz DBType(TEXT)
   *  @param kind Database column kind DBType(TEXT) */
  case class TacticsRow(tacticid: Option[String], name: Option[String], clazz: Option[String], kind: Option[String])
  /** GetResult implicit for fetching TacticsRow objects using plain SQL queries */
  implicit def GetResultTacticsRow(implicit e0: GR[Option[String]]): GR[TacticsRow] = GR{
    prs => import prs._
    TacticsRow.tupled((<<?[String], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table tactics. Objects of this class serve as prototypes for rows in queries. */
  class Tactics(_tableTag: Tag) extends Table[TacticsRow](_tableTag, "tactics") {
    def * = (tacticid, name, clazz, kind) <> (TacticsRow.tupled, TacticsRow.unapply)
    
    /** Database column tacticId DBType(TEXT), PrimaryKey */
    val tacticid: Column[Option[String]] = column[Option[String]]("tacticId", O.PrimaryKey)
    /** Database column name DBType(TEXT) */
    val name: Column[Option[String]] = column[Option[String]]("name")
    /** Database column clazz DBType(TEXT) */
    val clazz: Column[Option[String]] = column[Option[String]]("clazz")
    /** Database column kind DBType(TEXT) */
    val kind: Column[Option[String]] = column[Option[String]]("kind")
  }
  /** Collection-like TableQuery object for table Tactics */
  lazy val Tactics = new TableQuery(tag => new Tactics(tag))
  
  /** Entity class storing rows of table Users
   *  @param email Database column email DBType(TEXT), PrimaryKey
   *  @param password Database column password DBType(TEXT) */
  case class UsersRow(email: Option[String], password: Option[String])
  /** GetResult implicit for fetching UsersRow objects using plain SQL queries */
  implicit def GetResultUsersRow(implicit e0: GR[Option[String]]): GR[UsersRow] = GR{
    prs => import prs._
    UsersRow.tupled((<<?[String], <<?[String]))
  }
  /** Table description of table users. Objects of this class serve as prototypes for rows in queries. */
  class Users(_tableTag: Tag) extends Table[UsersRow](_tableTag, "users") {
    def * = (email, password) <> (UsersRow.tupled, UsersRow.unapply)
    
    /** Database column email DBType(TEXT), PrimaryKey */
    val email: Column[Option[String]] = column[Option[String]]("email", O.PrimaryKey)
    /** Database column password DBType(TEXT) */
    val password: Column[Option[String]] = column[Option[String]]("password")
  }
  /** Collection-like TableQuery object for table Users */
  lazy val Users = new TableQuery(tag => new Users(tag))
}