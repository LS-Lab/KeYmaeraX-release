/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra
// AUTO-GENERATED Slick data model
/** Stand-alone Slick data model for immediate use */
object Tables extends Tables {
  val profile: slick.jdbc.JdbcProfile = slick.jdbc.SQLiteProfile
}

/**
 * Slick data model trait for extension, choice of backend or usage in the cake pattern. (Make sure to initialize this
 * late.)
 */
trait Tables {
  val profile: slick.jdbc.JdbcProfile
  import profile.api._
  import slick.model.ForeignKeyAction
  // NOTE: GetResult mappers for plain SQL are only generated for
  // tables where Slick knows how to map the types of all columns.
  import slick.jdbc.{GetResult => GR}

  /** DDL for all tables. Call .create to execute. */
  lazy val schema: profile.SchemaDescription = Array(
    Agendaitems.schema,
    Config.schema,
    Executables.schema,
    Executionsteps.schema,
    Lemmas.schema,
    Models.schema,
    Proofs.schema,
    Users.schema,
  ).reduceLeft(_ ++ _)

  /**
   * Entity class storing rows of table Agendaitems
   * @param _Id
   *   Database column _id SqlType(INTEGER), PrimaryKey
   * @param proofid
   *   Database column proofId SqlType(INTEGER)
   * @param stepid
   *   Database column stepId SqlType(INTEGER)
   * @param subgoalid
   *   Database column subgoalId SqlType(INTEGER)
   * @param displayname
   *   Database column displayName SqlType(STRING)
   */
  case class AgendaitemsRow(
      _Id: Option[Int],
      proofid: Option[Int],
      stepid: Option[Int],
      subgoalid: Option[Int],
      displayname: Option[String],
  )

  /** GetResult implicit for fetching AgendaitemsRow objects using plain SQL queries */
  implicit def GetResultAgendaitemsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[AgendaitemsRow] =
    GR { prs =>
      import prs._
      (AgendaitemsRow.apply _).tupled((<<?[Int], <<?[Int], <<?[Int], <<?[Int], <<?[String]))
    }

  /** Table description of table agendaItems. Objects of this class serve as prototypes for rows in queries. */
  class Agendaitems(_tableTag: Tag) extends profile.api.Table[AgendaitemsRow](_tableTag, "agendaItems") {
    def * = ((_Id, proofid, stepid, subgoalid, displayname)).mapTo[AgendaitemsRow]

    /** Database column _id SqlType(INTEGER), PrimaryKey */
    val _Id: Rep[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)

    /** Database column proofId SqlType(INTEGER) */
    val proofid: Rep[Option[Int]] = column[Option[Int]]("proofId")

    /** Database column stepId SqlType(INTEGER) */
    val stepid: Rep[Option[Int]] = column[Option[Int]]("stepId")

    /** Database column subgoalId SqlType(INTEGER) */
    val subgoalid: Rep[Option[Int]] = column[Option[Int]]("subgoalId")

    /** Database column displayName SqlType(STRING) */
    val displayname: Rep[Option[String]] = column[Option[String]]("displayName")

    /** Foreign key referencing Executionsteps (database name executionSteps_FK_1) */
    lazy val executionstepsFk = foreignKey("executionSteps_FK_1", stepid, Executionsteps)(
      r => r._Id,
      onUpdate = ForeignKeyAction.NoAction,
      onDelete = ForeignKeyAction.Cascade,
    )

    /** Foreign key referencing Proofs (database name proofs_FK_2) */
    lazy val proofsFk = foreignKey("proofs_FK_2", proofid, Proofs)(
      r => r._Id,
      onUpdate = ForeignKeyAction.NoAction,
      onDelete = ForeignKeyAction.Cascade,
    )
  }

  /** Collection-like TableQuery object for table Agendaitems */
  lazy val Agendaitems = new TableQuery(tag => new Agendaitems(tag))

  /**
   * Entity class storing rows of table Config
   * @param configid
   *   Database column configId SqlType(INTEGER), PrimaryKey
   * @param configname
   *   Database column configName SqlType(TEXT)
   * @param key
   *   Database column key SqlType(TEXT)
   * @param value
   *   Database column value SqlType(TEXT)
   */
  case class ConfigRow(configid: Option[Int], configname: Option[String], key: Option[String], value: Option[String])

  /** GetResult implicit for fetching ConfigRow objects using plain SQL queries */
  implicit def GetResultConfigRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ConfigRow] = GR { prs =>
    import prs._
    (ConfigRow.apply _).tupled((<<?[Int], <<?[String], <<?[String], <<?[String]))
  }

  /** Table description of table config. Objects of this class serve as prototypes for rows in queries. */
  class Config(_tableTag: Tag) extends profile.api.Table[ConfigRow](_tableTag, "config") {
    def * = ((configid, configname, key, value)).mapTo[ConfigRow]

    /** Database column configId SqlType(INTEGER), PrimaryKey */
    val configid: Rep[Option[Int]] = column[Option[Int]]("configId", O.PrimaryKey)

    /** Database column configName SqlType(TEXT) */
    val configname: Rep[Option[String]] = column[Option[String]]("configName")

    /** Database column key SqlType(TEXT) */
    val key: Rep[Option[String]] = column[Option[String]]("key")

    /** Database column value SqlType(TEXT) */
    val value: Rep[Option[String]] = column[Option[String]]("value")
  }

  /** Collection-like TableQuery object for table Config */
  lazy val Config = new TableQuery(tag => new Config(tag))

  /**
   * Entity class storing rows of table Executables
   * @param _Id
   *   Database column _id SqlType(INTEGER), PrimaryKey
   * @param belleexpr
   *   Database column belleExpr SqlType(TEXT)
   */
  case class ExecutablesRow(_Id: Option[Int], belleexpr: Option[String])

  /** GetResult implicit for fetching ExecutablesRow objects using plain SQL queries */
  implicit def GetResultExecutablesRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ExecutablesRow] =
    GR { prs =>
      import prs._
      (ExecutablesRow.apply _).tupled((<<?[Int], <<?[String]))
    }

  /** Table description of table executables. Objects of this class serve as prototypes for rows in queries. */
  class Executables(_tableTag: Tag) extends profile.api.Table[ExecutablesRow](_tableTag, "executables") {
    def * = ((_Id, belleexpr)).mapTo[ExecutablesRow]

    /** Database column _id SqlType(INTEGER), PrimaryKey */
    val _Id: Rep[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)

    /** Database column belleExpr SqlType(TEXT) */
    val belleexpr: Rep[Option[String]] = column[Option[String]]("belleExpr")
  }

  /** Collection-like TableQuery object for table Executables */
  lazy val Executables = new TableQuery(tag => new Executables(tag))

  /**
   * Entity class storing rows of table Executionsteps
   * @param _Id
   *   Database column _id SqlType(INTEGER), PrimaryKey
   * @param proofid
   *   Database column proofId SqlType(INTEGER)
   * @param previousstep
   *   Database column previousStep SqlType(INTEGER)
   * @param branchorder
   *   Database column branchOrder SqlType(INT)
   * @param status
   *   Database column status SqlType(TEXT)
   * @param executableid
   *   Database column executableId SqlType(INTEGER)
   * @param inputprovableid
   *   Database column inputProvableId SqlType(INTEGER)
   * @param resultprovableid
   *   Database column resultProvableId SqlType(INTEGER)
   * @param localprovableid
   *   Database column localProvableId SqlType(INTEGER)
   * @param userexecuted
   *   Database column userExecuted SqlType(BOOLEAN)
   * @param childrenrecorded
   *   Database column childrenRecorded SqlType(BOOLEAN)
   * @param rulename
   *   Database column ruleName SqlType(STRING)
   * @param numsubgoals
   *   Database column numSubGoals SqlType(INTEGER), Default(-1)
   * @param numopensubgoals
   *   Database column numOpenSubGoals SqlType(INTEGER), Default(-1)
   */
  case class ExecutionstepsRow(
      _Id: Option[Int],
      proofid: Option[Int],
      previousstep: Option[Int],
      branchorder: Int,
      status: Option[String],
      executableid: Option[Int],
      inputprovableid: Option[Int],
      resultprovableid: Option[Int],
      localprovableid: Option[Int],
      userexecuted: Option[String],
      childrenrecorded: Option[String],
      rulename: Option[String],
      numsubgoals: Int = -1,
      numopensubgoals: Int = -1,
  )

  /** GetResult implicit for fetching ExecutionstepsRow objects using plain SQL queries */
  implicit def GetResultExecutionstepsRow(implicit
      e0: GR[Option[Int]],
      e1: GR[Int],
      e2: GR[Option[String]],
  ): GR[ExecutionstepsRow] = GR { prs =>
    import prs._
    (ExecutionstepsRow.apply _).tupled((
      <<?[Int],
      <<?[Int],
      <<?[Int],
      <<[Int],
      <<?[String],
      <<?[Int],
      <<?[Int],
      <<?[Int],
      <<?[Int],
      <<?[String],
      <<?[String],
      <<?[String],
      <<[Int],
      <<[Int],
    ))
  }

  /** Table description of table executionSteps. Objects of this class serve as prototypes for rows in queries. */
  class Executionsteps(_tableTag: Tag) extends profile.api.Table[ExecutionstepsRow](_tableTag, "executionSteps") {
    def * = (
      (
        _Id,
        proofid,
        previousstep,
        branchorder,
        status,
        executableid,
        inputprovableid,
        resultprovableid,
        localprovableid,
        userexecuted,
        childrenrecorded,
        rulename,
        numsubgoals,
        numopensubgoals,
      ),
    ).mapTo[ExecutionstepsRow]

    /** Maps whole row to an option. Useful for outer joins. */
    def ? = (
      (
        _Id,
        proofid,
        previousstep,
        Rep.Some(branchorder),
        status,
        executableid,
        inputprovableid,
        resultprovableid,
        localprovableid,
        userexecuted,
        childrenrecorded,
        rulename,
        Rep.Some(numsubgoals),
        Rep.Some(numopensubgoals),
      ),
    ).shaped
      .<>(
        { r =>
          import r._;
          _4.map(_ =>
            (ExecutionstepsRow.apply _)
              .tupled((_1, _2, _3, _4.get, _5, _6, _7, _8, _9, _10, _11, _12, _13.get, _14.get))
          )
        },
        (_: Any) => throw new Exception("Inserting into ? projection not supported."),
      )

    /** Database column _id SqlType(INTEGER), PrimaryKey */
    val _Id: Rep[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)

    /** Database column proofId SqlType(INTEGER) */
    val proofid: Rep[Option[Int]] = column[Option[Int]]("proofId")

    /** Database column previousStep SqlType(INTEGER) */
    val previousstep: Rep[Option[Int]] = column[Option[Int]]("previousStep")

    /** Database column branchOrder SqlType(INT) */
    val branchorder: Rep[Int] = column[Int]("branchOrder")

    /** Database column status SqlType(TEXT) */
    val status: Rep[Option[String]] = column[Option[String]]("status")

    /** Database column executableId SqlType(INTEGER) */
    val executableid: Rep[Option[Int]] = column[Option[Int]]("executableId")

    /** Database column inputProvableId SqlType(INTEGER) */
    val inputprovableid: Rep[Option[Int]] = column[Option[Int]]("inputProvableId")

    /** Database column resultProvableId SqlType(INTEGER) */
    val resultprovableid: Rep[Option[Int]] = column[Option[Int]]("resultProvableId")

    /** Database column localProvableId SqlType(INTEGER) */
    val localprovableid: Rep[Option[Int]] = column[Option[Int]]("localProvableId")

    /** Database column userExecuted SqlType(BOOLEAN) */
    val userexecuted: Rep[Option[String]] = column[Option[String]]("userExecuted")

    /** Database column childrenRecorded SqlType(BOOLEAN) */
    val childrenrecorded: Rep[Option[String]] = column[Option[String]]("childrenRecorded")

    /** Database column ruleName SqlType(STRING) */
    val rulename: Rep[Option[String]] = column[Option[String]]("ruleName")

    /** Database column numSubGoals SqlType(INTEGER), Default(-1) */
    val numsubgoals: Rep[Int] = column[Int]("numSubGoals", O.Default(-1))

    /** Database column numOpenSubGoals SqlType(INTEGER), Default(-1) */
    val numopensubgoals: Rep[Int] = column[Int]("numOpenSubGoals", O.Default(-1))

    /** Foreign key referencing Executables (database name executables_FK_1) */
    lazy val executablesFk = foreignKey("executables_FK_1", executableid, Executables)(
      r => r._Id,
      onUpdate = ForeignKeyAction.NoAction,
      onDelete = ForeignKeyAction.NoAction,
    )

    /** Foreign key referencing Executionsteps (database name executionSteps_FK_2) */
    lazy val executionstepsFk = foreignKey("executionSteps_FK_2", previousstep, Executionsteps)(
      r => r._Id,
      onUpdate = ForeignKeyAction.NoAction,
      onDelete = ForeignKeyAction.Cascade,
    )

    /** Foreign key referencing Lemmas (database name lemmas_FK_3) */
    lazy val lemmasFk = foreignKey("lemmas_FK_3", (localprovableid, resultprovableid, inputprovableid), Lemmas)(
      r => (r._Id, r._Id, r._Id),
      onUpdate = ForeignKeyAction.NoAction,
      onDelete = ForeignKeyAction.Cascade,
    )

    /** Foreign key referencing Proofs (database name proofs_FK_4) */
    lazy val proofsFk = foreignKey("proofs_FK_4", proofid, Proofs)(
      r => r._Id,
      onUpdate = ForeignKeyAction.NoAction,
      onDelete = ForeignKeyAction.Cascade,
    )

    /** Index over (proofid,status,numopensubgoals) (database name finishedOpenSteps) */
    val index1 = index("finishedOpenSteps", (proofid, status, numopensubgoals))

    /** Index over (proofid,previousstep,status) (database name finishedProofStepParent) */
    val index2 = index("finishedProofStepParent", (proofid, previousstep, status))

    /** Index over (proofid,status) (database name finishedProofSteps) */
    val index3 = index("finishedProofSteps", (proofid, status))
  }

  /** Collection-like TableQuery object for table Executionsteps */
  lazy val Executionsteps = new TableQuery(tag => new Executionsteps(tag))

  /**
   * Entity class storing rows of table Lemmas
   * @param _Id
   *   Database column _id SqlType(INTEGER), PrimaryKey
   * @param lemma
   *   Database column lemma SqlType(TEXT)
   */
  case class LemmasRow(_Id: Option[Int], lemma: Option[String])

  /** GetResult implicit for fetching LemmasRow objects using plain SQL queries */
  implicit def GetResultLemmasRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[LemmasRow] = GR { prs =>
    import prs._
    (LemmasRow.apply _).tupled((<<?[Int], <<?[String]))
  }

  /** Table description of table lemmas. Objects of this class serve as prototypes for rows in queries. */
  class Lemmas(_tableTag: Tag) extends profile.api.Table[LemmasRow](_tableTag, "lemmas") {
    def * = ((_Id, lemma)).mapTo[LemmasRow]

    /** Database column _id SqlType(INTEGER), PrimaryKey */
    val _Id: Rep[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)

    /** Database column lemma SqlType(TEXT) */
    val lemma: Rep[Option[String]] = column[Option[String]]("lemma")
  }

  /** Collection-like TableQuery object for table Lemmas */
  lazy val Lemmas = new TableQuery(tag => new Lemmas(tag))

  /**
   * Entity class storing rows of table Models
   * @param _Id
   *   Database column _id SqlType(INTEGER), PrimaryKey
   * @param userid
   *   Database column userId SqlType(TEXT)
   * @param name
   *   Database column name SqlType(TEXT)
   * @param date
   *   Database column date SqlType(TEXT)
   * @param description
   *   Database column description SqlType(TEXT)
   * @param filecontents
   *   Database column fileContents SqlType(TEXT)
   * @param publink
   *   Database column publink SqlType(TEXT)
   * @param title
   *   Database column title SqlType(TEXT)
   * @param tactic
   *   Database column tactic SqlType(TEXT)
   * @param istemporary
   *   Database column isTemporary SqlType(INTEGER), Default(Some(0))
   */
  case class ModelsRow(
      _Id: Option[Int],
      userid: Option[String],
      name: Option[String],
      date: Option[String],
      description: Option[String],
      filecontents: Option[String],
      publink: Option[String],
      title: Option[String],
      tactic: Option[String],
      istemporary: Option[Int] = Some(0),
  )

  /** GetResult implicit for fetching ModelsRow objects using plain SQL queries */
  implicit def GetResultModelsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ModelsRow] = GR { prs =>
    import prs._
    (ModelsRow.apply _).tupled((
      <<?[Int],
      <<?[String],
      <<?[String],
      <<?[String],
      <<?[String],
      <<?[String],
      <<?[String],
      <<?[String],
      <<?[String],
      <<?[Int],
    ))
  }

  /** Table description of table models. Objects of this class serve as prototypes for rows in queries. */
  class Models(_tableTag: Tag) extends profile.api.Table[ModelsRow](_tableTag, "models") {
    def * = ((_Id, userid, name, date, description, filecontents, publink, title, tactic, istemporary)).mapTo[ModelsRow]

    /** Database column _id SqlType(INTEGER), PrimaryKey */
    val _Id: Rep[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)

    /** Database column userId SqlType(TEXT) */
    val userid: Rep[Option[String]] = column[Option[String]]("userId")

    /** Database column name SqlType(TEXT) */
    val name: Rep[Option[String]] = column[Option[String]]("name")

    /** Database column date SqlType(TEXT) */
    val date: Rep[Option[String]] = column[Option[String]]("date")

    /** Database column description SqlType(TEXT) */
    val description: Rep[Option[String]] = column[Option[String]]("description")

    /** Database column fileContents SqlType(TEXT) */
    val filecontents: Rep[Option[String]] = column[Option[String]]("fileContents")

    /** Database column publink SqlType(TEXT) */
    val publink: Rep[Option[String]] = column[Option[String]]("publink")

    /** Database column title SqlType(TEXT) */
    val title: Rep[Option[String]] = column[Option[String]]("title")

    /** Database column tactic SqlType(TEXT) */
    val tactic: Rep[Option[String]] = column[Option[String]]("tactic")

    /** Database column isTemporary SqlType(INTEGER), Default(Some(0)) */
    val istemporary: Rep[Option[Int]] = column[Option[Int]]("isTemporary", O.Default(Some(0)))

    /** Foreign key referencing Users (database name users_FK_1) */
    lazy val usersFk = foreignKey("users_FK_1", userid, Users)(
      r => r.email,
      onUpdate = ForeignKeyAction.NoAction,
      onDelete = ForeignKeyAction.NoAction,
    )
  }

  /** Collection-like TableQuery object for table Models */
  lazy val Models = new TableQuery(tag => new Models(tag))

  /**
   * Entity class storing rows of table Proofs
   * @param _Id
   *   Database column _id SqlType(INTEGER), PrimaryKey
   * @param modelid
   *   Database column modelId SqlType(INTEGER)
   * @param name
   *   Database column name SqlType(TEXT)
   * @param description
   *   Database column description SqlType(TEXT)
   * @param date
   *   Database column date SqlType(TEXT)
   * @param closed
   *   Database column closed SqlType(INTEGER)
   * @param lemmaid
   *   Database column lemmaId SqlType(INTEGER)
   * @param istemporary
   *   Database column isTemporary SqlType(INTEGER), Default(Some(0))
   * @param tactic
   *   Database column tactic SqlType(TEXT)
   */
  case class ProofsRow(
      _Id: Option[Int],
      modelid: Option[Int],
      name: Option[String],
      description: Option[String],
      date: Option[String],
      closed: Option[Int],
      lemmaid: Option[Int],
      istemporary: Option[Int] = Some(0),
      tactic: Option[String],
  )

  /** GetResult implicit for fetching ProofsRow objects using plain SQL queries */
  implicit def GetResultProofsRow(implicit e0: GR[Option[Int]], e1: GR[Option[String]]): GR[ProofsRow] = GR { prs =>
    import prs._
    (ProofsRow.apply _)
      .tupled((<<?[Int], <<?[Int], <<?[String], <<?[String], <<?[String], <<?[Int], <<?[Int], <<?[Int], <<?[String]))
  }

  /** Table description of table proofs. Objects of this class serve as prototypes for rows in queries. */
  class Proofs(_tableTag: Tag) extends profile.api.Table[ProofsRow](_tableTag, "proofs") {
    def * = ((_Id, modelid, name, description, date, closed, lemmaid, istemporary, tactic)).mapTo[ProofsRow]

    /** Database column _id SqlType(INTEGER), PrimaryKey */
    val _Id: Rep[Option[Int]] = column[Option[Int]]("_id", O.PrimaryKey, O.AutoInc)

    /** Database column modelId SqlType(INTEGER) */
    val modelid: Rep[Option[Int]] = column[Option[Int]]("modelId")

    /** Database column name SqlType(TEXT) */
    val name: Rep[Option[String]] = column[Option[String]]("name")

    /** Database column description SqlType(TEXT) */
    val description: Rep[Option[String]] = column[Option[String]]("description")

    /** Database column date SqlType(TEXT) */
    val date: Rep[Option[String]] = column[Option[String]]("date")

    /** Database column closed SqlType(INTEGER) */
    val closed: Rep[Option[Int]] = column[Option[Int]]("closed")

    /** Database column lemmaId SqlType(INTEGER) */
    val lemmaid: Rep[Option[Int]] = column[Option[Int]]("lemmaId")

    /** Database column isTemporary SqlType(INTEGER), Default(Some(0)) */
    val istemporary: Rep[Option[Int]] = column[Option[Int]]("isTemporary", O.Default(Some(0)))

    /** Database column tactic SqlType(TEXT) */
    val tactic: Rep[Option[String]] = column[Option[String]]("tactic")

    /** Foreign key referencing Models (database name models_FK_1) */
    lazy val modelsFk = foreignKey("models_FK_1", modelid, Models)(
      r => r._Id,
      onUpdate = ForeignKeyAction.NoAction,
      onDelete = ForeignKeyAction.Cascade,
    )
  }

  /** Collection-like TableQuery object for table Proofs */
  lazy val Proofs = new TableQuery(tag => new Proofs(tag))

  /**
   * Entity class storing rows of table Users
   * @param email
   *   Database column email SqlType(TEXT), PrimaryKey
   * @param hash
   *   Database column hash SqlType(TEXT)
   * @param salt
   *   Database column salt SqlType(TEXT)
   * @param iterations
   *   Database column iterations SqlType(INTEGER)
   * @param level
   *   Database column level SqlType(INTEGER), Default(Some(0))
   */
  case class UsersRow(
      email: Option[String],
      hash: Option[String],
      salt: Option[String],
      iterations: Option[Int],
      level: Option[Int] = Some(0),
  )

  /** GetResult implicit for fetching UsersRow objects using plain SQL queries */
  implicit def GetResultUsersRow(implicit e0: GR[Option[String]], e1: GR[Option[Int]]): GR[UsersRow] = GR { prs =>
    import prs._
    (UsersRow.apply _).tupled((<<?[String], <<?[String], <<?[String], <<?[Int], <<?[Int]))
  }

  /** Table description of table users. Objects of this class serve as prototypes for rows in queries. */
  class Users(_tableTag: Tag) extends profile.api.Table[UsersRow](_tableTag, "users") {
    def * = ((email, hash, salt, iterations, level)).mapTo[UsersRow]

    /** Database column email SqlType(TEXT), PrimaryKey */
    val email: Rep[Option[String]] = column[Option[String]]("email", O.PrimaryKey)

    /** Database column hash SqlType(TEXT) */
    val hash: Rep[Option[String]] = column[Option[String]]("hash")

    /** Database column salt SqlType(TEXT) */
    val salt: Rep[Option[String]] = column[Option[String]]("salt")

    /** Database column iterations SqlType(INTEGER) */
    val iterations: Rep[Option[Int]] = column[Option[Int]]("iterations")

    /** Database column level SqlType(INTEGER), Default(Some(0)) */
    val level: Rep[Option[Int]] = column[Option[Int]]("level", O.Default(Some(0)))
  }

  /** Collection-like TableQuery object for table Users */
  lazy val Users = new TableQuery(tag => new Users(tag))
}
