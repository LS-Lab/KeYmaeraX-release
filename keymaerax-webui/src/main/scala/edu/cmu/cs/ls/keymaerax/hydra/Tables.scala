package edu.cmu.cs.ls.keymaerax.hydra
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
  lazy val ddl = Config.ddl ++ Executableparameter.ddl ++ Executables.ddl ++ Executionsteps.ddl ++ Lemmas.ddl ++ Models.ddl ++ Patterns.ddl ++ Proofs.ddl ++ Provables.ddl ++ Scalatactics.ddl ++ Sequentformulas.ddl ++ Sequents.ddl ++ Tacticexecutions.ddl ++ Users.ddl
  
  /** Entity class storing rows of table Config
   *  @param configid Database column configId DBType(INTEGER), PrimaryKey
   *  @param configname Database column configName DBType(TEXT)
   *  @param key Database column key DBType(TEXT)
   *  @param value Database column value DBType(TEXT) */
  case class ConfigRow(configid: Option[Int], configname: Option[String], key: Option[String], value: Option[String])
  /** GetResult implicit for fetching ConfigRow objects using plain SQL queries */
  implicit def GetResultConfigRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ConfigRow] = GR{
    prs => import prs._
    ConfigRow.tupled((<<?[Int], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table config. Objects of this class serve as prototypes for rows in queries. */
  class Config(_tableTag: Tag) extends Table[ConfigRow](_tableTag, "config") {
    def * = (configid, configname, key, value) <> (ConfigRow.tupled, ConfigRow.unapply)
    
    /** Database column configId DBType(INTEGER), PrimaryKey */
    val configid: Column[Option[Int]] = column[Option[Int]]("configId", O.PrimaryKey)
    /** Database column configName DBType(TEXT) */
    val configname: Column[Option[String]] = column[Option[String]]("configName")
    /** Database column key DBType(TEXT) */
    val key: Column[Option[String]] = column[Option[String]]("key")
    /** Database column value DBType(TEXT) */
    val value: Column[Option[String]] = column[Option[String]]("value")
  }
  /** Collection-like TableQuery object for table Config */
  lazy val Config = new TableQuery(tag => new Config(tag))
  
  /** Entity class storing rows of table Executableparameter
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param executableid Database column executableId DBType(INTEGER)
   *  @param idx Database column idx DBType(INT)
   *  @param valuetype Database column valueType DBType(TEXT)
   *  @param value Database column value DBType(TEXT) */
  case class ExecutableparameterRow(_Id: Option[Int], executableid: Option[Int], idx: Option[Int], valuetype: Option[String], value: Option[String])
  /** GetResult implicit for fetching ExecutableparameterRow objects using plain SQL queries */
  implicit def GetResultExecutableparameterRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ExecutableparameterRow] = GR{
    prs => import prs._
    ExecutableparameterRow.tupled((<<?[Int], <<?[Int], <<?[Int], <<?[String], <<?[String]))
  }
  /** Table description of table executableParameter. Objects of this class serve as prototypes for rows in queries. */
  class Executableparameter(_tableTag: Tag) extends Table[ExecutableparameterRow](_tableTag, "executableParameter") {
    def * = (_Id, executableid, idx, valuetype, value) <> (ExecutableparameterRow.tupled, ExecutableparameterRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column executableId DBType(INTEGER) */
    val executableid: Column[Option[Int]] = column[Option[Int]]("executableId")
    /** Database column idx DBType(INT) */
    val idx: Column[Option[Int]] = column[Option[Int]]("idx")
    /** Database column valueType DBType(TEXT) */
    val valuetype: Column[Option[String]] = column[Option[String]]("valueType")
    /** Database column value DBType(TEXT) */
    val value: Column[Option[String]] = column[Option[String]]("value")
    
    /** Foreign key referencing Executables (database name executables_FK_1) */
    lazy val executablesFk = foreignKey("executables_FK_1", executableid, Executables)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Executableparameter */
  lazy val Executableparameter = new TableQuery(tag => new Executableparameter(tag))
  
  /** Entity class storing rows of table Executables
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param scalatacticid Database column scalaTacticId DBType(INTEGER)
   *  @param belleexpr Database column belleExpr DBType(TEXT) */
  case class ExecutablesRow(_Id: Option[Int], scalatacticid: Option[Int], belleexpr: Option[String])
  /** GetResult implicit for fetching ExecutablesRow objects using plain SQL queries */
  implicit def GetResultExecutablesRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ExecutablesRow] = GR{
    prs => import prs._
    ExecutablesRow.tupled((<<?[Int], <<?[Int], <<?[String]))
  }
  /** Table description of table executables. Objects of this class serve as prototypes for rows in queries. */
  class Executables(_tableTag: Tag) extends Table[ExecutablesRow](_tableTag, "executables") {
    def * = (_Id, scalatacticid, belleexpr) <> (ExecutablesRow.tupled, ExecutablesRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column scalaTacticId DBType(INTEGER) */
    val scalatacticid: Column[Option[Int]] = column[Option[Int]]("scalaTacticId")
    /** Database column belleExpr DBType(TEXT) */
    val belleexpr: Column[Option[String]] = column[Option[String]]("belleExpr")
    
    /** Foreign key referencing Scalatactics (database name scalaTactics_FK_1) */
    lazy val scalatacticsFk = foreignKey("scalaTactics_FK_1", scalatacticid, Scalatactics)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Executables */
  lazy val Executables = new TableQuery(tag => new Executables(tag))
  
  /** Entity class storing rows of table Executionsteps
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param executionid Database column executionId DBType(INTEGER)
   *  @param previousstep Database column previousStep DBType(INTEGER)
   *  @param parentstep Database column parentStep DBType(INTEGER)
   *  @param branchorder Database column branchOrder DBType(INT)
   *  @param branchlabel Database column branchLabel DBType(TEXT)
   *  @param alternativeorder Database column alternativeOrder DBType(INT)
   *  @param status Database column status DBType(TEXT)
   *  @param executableid Database column executableId DBType(INTEGER)
   *  @param inputprovableid Database column inputProvableId DBType(INTEGER)
   *  @param resultprovableid Database column resultProvableId DBType(INTEGER)
   *  @param userexecuted Database column userExecuted DBType(BOOLEAN)
   *  @param childrenrecorded Database column childrenRecorded DBType(BOOLEAN) */
  case class ExecutionstepsRow(_Id: Option[Int], executionid: Option[Int], previousstep: Option[Int], parentstep: Option[Int], branchorder: Option[Int], branchlabel: Option[String], alternativeorder: Option[Int], status: Option[String], executableid: Option[Int], inputprovableid: Option[Int], resultprovableid: Option[Int], userexecuted: Option[String], childrenrecorded: Option[String])
  /** GetResult implicit for fetching ExecutionstepsRow objects using plain SQL queries */
  implicit def GetResultExecutionstepsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ExecutionstepsRow] = GR{
    prs => import prs._
    ExecutionstepsRow.tupled((<<?[Int], <<?[Int], <<?[Int], <<?[Int], <<?[Int], <<?[String], <<?[Int], <<?[String], <<?[Int], <<?[Int], <<?[Int], <<?[String], <<?[String]))
  }
  /** Table description of table executionSteps. Objects of this class serve as prototypes for rows in queries. */
  class Executionsteps(_tableTag: Tag) extends Table[ExecutionstepsRow](_tableTag, "executionSteps") {
    def * = (_Id, executionid, previousstep, parentstep, branchorder, branchlabel, alternativeorder, status, executableid, inputprovableid, resultprovableid, userexecuted, childrenrecorded) <> (ExecutionstepsRow.tupled, ExecutionstepsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column executionId DBType(INTEGER) */
    val executionid: Column[Option[Int]] = column[Option[Int]]("executionId")
    /** Database column previousStep DBType(INTEGER) */
    val previousstep: Column[Option[Int]] = column[Option[Int]]("previousStep")
    /** Database column parentStep DBType(INTEGER) */
    val parentstep: Column[Option[Int]] = column[Option[Int]]("parentStep")
    /** Database column branchOrder DBType(INT) */
    val branchorder: Column[Option[Int]] = column[Option[Int]]("branchOrder")
    /** Database column branchLabel DBType(TEXT) */
    val branchlabel: Column[Option[String]] = column[Option[String]]("branchLabel")
    /** Database column alternativeOrder DBType(INT) */
    val alternativeorder: Column[Option[Int]] = column[Option[Int]]("alternativeOrder")
    /** Database column status DBType(TEXT) */
    val status: Column[Option[String]] = column[Option[String]]("status")
    /** Database column executableId DBType(INTEGER) */
    val executableid: Column[Option[Int]] = column[Option[Int]]("executableId")
    /** Database column inputProvableId DBType(INTEGER) */
    val inputprovableid: Column[Option[Int]] = column[Option[Int]]("inputProvableId")
    /** Database column resultProvableId DBType(INTEGER) */
    val resultprovableid: Column[Option[Int]] = column[Option[Int]]("resultProvableId")
    /** Database column userExecuted DBType(BOOLEAN) */
    val userexecuted: Column[Option[String]] = column[Option[String]]("userExecuted")
    /** Database column childrenRecorded DBType(BOOLEAN) */
    val childrenrecorded: Column[Option[String]] = column[Option[String]]("childrenRecorded")
    
    /** Foreign key referencing Executables (database name executables_FK_1) */
    lazy val executablesFk = foreignKey("executables_FK_1", executableid, Executables)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
    /** Foreign key referencing Executionsteps (database name executionSteps_FK_2) */
    lazy val executionstepsFk = foreignKey("executionSteps_FK_2", (parentstep, previousstep), Executionsteps)(r => (r._Id, r._Id), onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
    /** Foreign key referencing Provables (database name provables_FK_3) */
    lazy val provablesFk = foreignKey("provables_FK_3", (resultprovableid, inputprovableid), Provables)(r => (r._Id, r._Id), onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
    /** Foreign key referencing Tacticexecutions (database name tacticExecutions_FK_4) */
    lazy val tacticexecutionsFk = foreignKey("tacticExecutions_FK_4", executionid, Tacticexecutions)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Executionsteps */
  lazy val Executionsteps = new TableQuery(tag => new Executionsteps(tag))
  
  /** Entity class storing rows of table Lemmas
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param lemma Database column lemma DBType(TEXT) */
  case class LemmasRow(_Id: Option[Int], lemma: Option[String])
  /** GetResult implicit for fetching LemmasRow objects using plain SQL queries */
  implicit def GetResultLemmasRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[LemmasRow] = GR{
    prs => import prs._
    LemmasRow.tupled((<<?[Int], <<?[String]))
  }
  /** Table description of table lemmas. Objects of this class serve as prototypes for rows in queries. */
  class Lemmas(_tableTag: Tag) extends Table[LemmasRow](_tableTag, "lemmas") {
    def * = (_Id, lemma) <> (LemmasRow.tupled, LemmasRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column lemma DBType(TEXT) */
    val lemma: Column[Option[String]] = column[Option[String]]("lemma")
  }
  /** Collection-like TableQuery object for table Lemmas */
  lazy val Lemmas = new TableQuery(tag => new Lemmas(tag))
  
  /** Entity class storing rows of table Models
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param userid Database column userId DBType(TEXT)
   *  @param name Database column name DBType(TEXT)
   *  @param date Database column date DBType(TEXT)
   *  @param description Database column description DBType(TEXT)
   *  @param filecontents Database column fileContents DBType(TEXT)
   *  @param publink Database column publink DBType(TEXT)
   *  @param title Database column title DBType(TEXT)
   *  @param tactic Database column tactic DBType(TEXT) */
  case class ModelsRow(_Id: Option[Int], userid: Option[String], name: Option[String], date: Option[String], description: Option[String], filecontents: Option[String], publink: Option[String], title: Option[String], tactic: Option[String])
  /** GetResult implicit for fetching ModelsRow objects using plain SQL queries */
  implicit def GetResultModelsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ModelsRow] = GR{
    prs => import prs._
    ModelsRow.tupled((<<?[Int], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String], <<?[String]))
  }
  /** Table description of table models. Objects of this class serve as prototypes for rows in queries. */
  class Models(_tableTag: Tag) extends Table[ModelsRow](_tableTag, "models") {
    def * = (_Id, userid, name, date, description, filecontents, publink, title, tactic) <> (ModelsRow.tupled, ModelsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
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
    /** Database column tactic DBType(TEXT) */
    val tactic: Column[Option[String]] = column[Option[String]]("tactic")
    
    /** Foreign key referencing Users (database name users_FK_1) */
    lazy val usersFk = foreignKey("users_FK_1", userid, Users)(r => r.email, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Models */
  lazy val Models = new TableQuery(tag => new Models(tag))
  
  /** Entity class storing rows of table Patterns
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param executableid Database column executableId DBType(INTEGER)
   *  @param idx Database column idx DBType(INT)
   *  @param patternformula Database column patternFormula DBType(TEXT)
   *  @param resultingexecutable Database column resultingExecutable DBType(INTEGER) */
  case class PatternsRow(_Id: Option[Int], executableid: Option[Int], idx: Option[Int], patternformula: Option[String], resultingexecutable: Option[Int])
  /** GetResult implicit for fetching PatternsRow objects using plain SQL queries */
  implicit def GetResultPatternsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[PatternsRow] = GR{
    prs => import prs._
    PatternsRow.tupled((<<?[Int], <<?[Int], <<?[Int], <<?[String], <<?[Int]))
  }
  /** Table description of table patterns. Objects of this class serve as prototypes for rows in queries. */
  class Patterns(_tableTag: Tag) extends Table[PatternsRow](_tableTag, "patterns") {
    def * = (_Id, executableid, idx, patternformula, resultingexecutable) <> (PatternsRow.tupled, PatternsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column executableId DBType(INTEGER) */
    val executableid: Column[Option[Int]] = column[Option[Int]]("executableId")
    /** Database column idx DBType(INT) */
    val idx: Column[Option[Int]] = column[Option[Int]]("idx")
    /** Database column patternFormula DBType(TEXT) */
    val patternformula: Column[Option[String]] = column[Option[String]]("patternFormula")
    /** Database column resultingExecutable DBType(INTEGER) */
    val resultingexecutable: Column[Option[Int]] = column[Option[Int]]("resultingExecutable")
    
    /** Foreign key referencing Executables (database name executables_FK_1) */
    lazy val executablesFk = foreignKey("executables_FK_1", (resultingexecutable, executableid), Executables)(r => (r._Id, r._Id), onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Patterns */
  lazy val Patterns = new TableQuery(tag => new Patterns(tag))
  
  /** Entity class storing rows of table Proofs
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param modelid Database column modelId DBType(INTEGER)
   *  @param name Database column name DBType(TEXT)
   *  @param description Database column description DBType(TEXT)
   *  @param date Database column date DBType(TEXT)
   *  @param closed Database column closed DBType(INTEGER) */
  case class ProofsRow(_Id: Option[Int], modelid: Option[Int], name: Option[String], description: Option[String], date: Option[String], closed: Option[Int])
  /** GetResult implicit for fetching ProofsRow objects using plain SQL queries */
  implicit def GetResultProofsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ProofsRow] = GR{
    prs => import prs._
    ProofsRow.tupled((<<?[Int], <<?[Int], <<?[String], <<?[String], <<?[String], <<?[Int]))
  }
  /** Table description of table proofs. Objects of this class serve as prototypes for rows in queries. */
  class Proofs(_tableTag: Tag) extends Table[ProofsRow](_tableTag, "proofs") {
    def * = (_Id, modelid, name, description, date, closed) <> (ProofsRow.tupled, ProofsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column modelId DBType(INTEGER) */
    val modelid: Column[Option[Int]] = column[Option[Int]]("modelId")
    /** Database column name DBType(TEXT) */
    val name: Column[Option[String]] = column[Option[String]]("name")
    /** Database column description DBType(TEXT) */
    val description: Column[Option[String]] = column[Option[String]]("description")
    /** Database column date DBType(TEXT) */
    val date: Column[Option[String]] = column[Option[String]]("date")
    /** Database column closed DBType(INTEGER) */
    val closed: Column[Option[Int]] = column[Option[Int]]("closed")
    
    /** Foreign key referencing Models (database name models_FK_1) */
    lazy val modelsFk = foreignKey("models_FK_1", modelid, Models)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Proofs */
  lazy val Proofs = new TableQuery(tag => new Proofs(tag))
  
  /** Entity class storing rows of table Provables
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param insertstatementwassyntacticallyvalid Database column insertStatementWasSyntacticallyValid DBType(INTEGER) */
  case class ProvablesRow(_Id: Option[Int], insertstatementwassyntacticallyvalid: Option[Int])
  /** GetResult implicit for fetching ProvablesRow objects using plain SQL queries */
  implicit def GetResultProvablesRow(implicit e0: GR[Option[Int]]): GR[ProvablesRow] = GR{
    prs => import prs._
    ProvablesRow.tupled((<<?[Int], <<?[Int]))
  }
  /** Table description of table provables. Objects of this class serve as prototypes for rows in queries. */
  class Provables(_tableTag: Tag) extends Table[ProvablesRow](_tableTag, "provables") {
    def * = (_Id, insertstatementwassyntacticallyvalid) <> (ProvablesRow.tupled, ProvablesRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column insertStatementWasSyntacticallyValid DBType(INTEGER) */
    val insertstatementwassyntacticallyvalid: Column[Option[Int]] = column[Option[Int]]("insertStatementWasSyntacticallyValid")
  }
  /** Collection-like TableQuery object for table Provables */
  lazy val Provables = new TableQuery(tag => new Provables(tag))
  
  /** Entity class storing rows of table Scalatactics
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param location Database column location DBType(TEXT)
   *  @param name Database column name DBType(TEXT) */
  case class ScalatacticsRow(_Id: Option[Int], location: Option[String], name: Option[String])
  /** GetResult implicit for fetching ScalatacticsRow objects using plain SQL queries */
  implicit def GetResultScalatacticsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ScalatacticsRow] = GR{
    prs => import prs._
    ScalatacticsRow.tupled((<<?[Int], <<?[String], <<?[String]))
  }
  /** Table description of table scalaTactics. Objects of this class serve as prototypes for rows in queries. */
  class Scalatactics(_tableTag: Tag) extends Table[ScalatacticsRow](_tableTag, "scalaTactics") {
    def * = (_Id, location, name) <> (ScalatacticsRow.tupled, ScalatacticsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column location DBType(TEXT) */
    val location: Column[Option[String]] = column[Option[String]]("location")
    /** Database column name DBType(TEXT) */
    val name: Column[Option[String]] = column[Option[String]]("name")
  }
  /** Collection-like TableQuery object for table Scalatactics */
  lazy val Scalatactics = new TableQuery(tag => new Scalatactics(tag))
  
  /** Entity class storing rows of table Sequentformulas
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param sequentid Database column sequentId DBType(INTEGER)
   *  @param isante Database column isAnte DBType(BOOLEAN)
   *  @param idx Database column idx DBType(INTEGER)
   *  @param formula Database column formula DBType(TEXT) */
  case class SequentformulasRow(_Id: Option[Int], sequentid: Option[Int], isante: Option[String], idx: Option[Int], formula: Option[String])
  /** GetResult implicit for fetching SequentformulasRow objects using plain SQL queries */
  implicit def GetResultSequentformulasRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[SequentformulasRow] = GR{
    prs => import prs._
    SequentformulasRow.tupled((<<?[Int], <<?[Int], <<?[String], <<?[Int], <<?[String]))
  }
  /** Table description of table sequentFormulas. Objects of this class serve as prototypes for rows in queries. */
  class Sequentformulas(_tableTag: Tag) extends Table[SequentformulasRow](_tableTag, "sequentFormulas") {
    def * = (_Id, sequentid, isante, idx, formula) <> (SequentformulasRow.tupled, SequentformulasRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column sequentId DBType(INTEGER) */
    val sequentid: Column[Option[Int]] = column[Option[Int]]("sequentId")
    /** Database column isAnte DBType(BOOLEAN) */
    val isante: Column[Option[String]] = column[Option[String]]("isAnte")
    /** Database column idx DBType(INTEGER) */
    val idx: Column[Option[Int]] = column[Option[Int]]("idx")
    /** Database column formula DBType(TEXT) */
    val formula: Column[Option[String]] = column[Option[String]]("formula")
    
    /** Foreign key referencing Sequents (database name sequents_FK_1) */
    lazy val sequentsFk = foreignKey("sequents_FK_1", sequentid, Sequents)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Sequentformulas */
  lazy val Sequentformulas = new TableQuery(tag => new Sequentformulas(tag))
  
  /** Entity class storing rows of table Sequents
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param provableid Database column provableId DBType(INTEGER)
   *  @param idx Database column idx DBType(INTEGER) */
  case class SequentsRow(_Id: Option[Int], provableid: Option[Int], idx: Option[Int])
  /** GetResult implicit for fetching SequentsRow objects using plain SQL queries */
  implicit def GetResultSequentsRow(implicit e0: GR[Option[Int]]): GR[SequentsRow] = GR{
    prs => import prs._
    SequentsRow.tupled((<<?[Int], <<?[Int], <<?[Int]))
  }
  /** Table description of table sequents. Objects of this class serve as prototypes for rows in queries. */
  class Sequents(_tableTag: Tag) extends Table[SequentsRow](_tableTag, "sequents") {
    def * = (_Id, provableid, idx) <> (SequentsRow.tupled, SequentsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column provableId DBType(INTEGER) */
    val provableid: Column[Option[Int]] = column[Option[Int]]("provableId")
    /** Database column idx DBType(INTEGER) */
    val idx: Column[Option[Int]] = column[Option[Int]]("idx")
    
    /** Foreign key referencing Provables (database name provables_FK_1) */
    lazy val provablesFk = foreignKey("provables_FK_1", provableid, Provables)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Sequents */
  lazy val Sequents = new TableQuery(tag => new Sequents(tag))
  
  /** Entity class storing rows of table Tacticexecutions
   *  @param _Id Database column _id DBType(INTEGER), PrimaryKey
   *  @param proofid Database column proofId DBType(INTEGER) */
  case class TacticexecutionsRow(_Id: Option[Int], proofid: Option[Int])
  /** GetResult implicit for fetching TacticexecutionsRow objects using plain SQL queries */
  implicit def GetResultTacticexecutionsRow(implicit e0: GR[Option[Int]]): GR[TacticexecutionsRow] = GR{
    prs => import prs._
    TacticexecutionsRow.tupled((<<?[Int], <<?[Int]))
  }
  /** Table description of table tacticExecutions. Objects of this class serve as prototypes for rows in queries. */
  class Tacticexecutions(_tableTag: Tag) extends Table[TacticexecutionsRow](_tableTag, "tacticExecutions") {
    def * = (_Id, proofid) <> (TacticexecutionsRow.tupled, TacticexecutionsRow.unapply)
    
    /** Database column _id DBType(INTEGER), PrimaryKey */
    val _Id: Column[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)
    /** Database column proofId DBType(INTEGER) */
    val proofid: Column[Option[Int]] = column[Option[Int]]("proofId")
    
    /** Foreign key referencing Proofs (database name proofs_FK_1) */
    lazy val proofsFk = foreignKey("proofs_FK_1", proofid, Proofs)(r => r._Id, onUpdate=ForeignKeyAction.NoAction, onDelete=ForeignKeyAction.NoAction)
  }
  /** Collection-like TableQuery object for table Tacticexecutions */
  lazy val Tacticexecutions = new TableQuery(tag => new Tacticexecutions(tag))
  
  /** Entity class storing rows of table Users
   *  @param email Database column email DBType(TEXT), PrimaryKey
   *  @param hash Database column hash DBType(TEXT)
   *  @param salt Database column salt DBType(TEXT)
   *  @param iterations Database column iterations DBType(INTEGER) */
  case class UsersRow(email: Option[String], hash: Option[String], salt: Option[String], iterations: Option[Int])
  /** GetResult implicit for fetching UsersRow objects using plain SQL queries */
  implicit def GetResultUsersRow(implicit e0: GR[Option[String]], e1: GR[Option[Int]]): GR[UsersRow] = GR{
    prs => import prs._
    UsersRow.tupled((<<?[String], <<?[String], <<?[String], <<?[Int]))
  }
  /** Table description of table users. Objects of this class serve as prototypes for rows in queries. */
  class Users(_tableTag: Tag) extends Table[UsersRow](_tableTag, "users") {
    def * = (email, hash, salt, iterations) <> (UsersRow.tupled, UsersRow.unapply)
    
    /** Database column email DBType(TEXT), PrimaryKey */
    val email: Column[Option[String]] = column[Option[String]]("email", O.PrimaryKey)
    /** Database column hash DBType(TEXT) */
    val hash: Column[Option[String]] = column[Option[String]]("hash")
    /** Database column salt DBType(TEXT) */
    val salt: Column[Option[String]] = column[Option[String]]("salt")
    /** Database column iterations DBType(INTEGER) */
    val iterations: Column[Option[Int]] = column[Option[Int]]("iterations")
  }
  /** Collection-like TableQuery object for table Users */
  lazy val Users = new TableQuery(tag => new Users(tag))
}