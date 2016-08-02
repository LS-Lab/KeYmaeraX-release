CREATE TABLE IF NOT EXISTS `config`  (
  `configId` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `configName` TEXT,
  `key` TEXT,
  `value` TEXT
);

CREATE TABLE IF NOT EXISTS `users` (
  `email` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `hash` TEXT,
  `salt` TEXT,
  `iterations` INTEGER
);

CREATE TABLE IF NOT EXISTS `models` (
  -- _id is the SQLite keyword for the auto-generated unique row ID
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `userId` TEXT REFERENCES `users` (`email`),
  `name` TEXT,
  `date` TEXT,
  `description` TEXT,
  `fileContents` TEXT,
  `publink` TEXT,
  `title` TEXT,
  `tactic` TEXT
);

CREATE TABLE IF NOT EXISTS `proofs` (
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `modelId` INTEGER REFERENCES `models` (`_id`),
  `name` TEXT,
  `description` TEXT,
  `date` TEXT,
  `closed` BOOLEAN
);

CREATE TABLE IF NOT EXISTS `agendaItems`(
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `proofId` INTEGER REFERENCES `proofs` (`_id`),
  `initialProofNode` INTEGER,
  `displayName` STRING

);

----------------------------------------------------------------------------------------------------
-- Serialization of Provables
----------------------------------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS `lemmas` (
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `lemma` TEXT -- A string that can be parsed by the Lemma parser
);


----------------------------------------------------------------------------------------------------
-- Record of tactic execution
-- These tables record only the *structure* of a tactic execution.
-- The actual contents of each step of the execution are stored in the tables in the next section.
----------------------------------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS `tacticExecutions` (
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `proofId` INTEGER REFERENCES `proofs` (`_id`)
);

CREATE TABLE IF NOT EXISTS `executionSteps` (
  `_id`              INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `executionId`      INTEGER REFERENCES `tacticExecutions` (`_id`),

  -- Rows that identify where in the proof this execution step occurs.
  `previousStep`     INTEGER REFERENCES `executionSteps` (`_id`),
  `parentStep`       INTEGER REFERENCES `executionSteps` (`_id`),
  `branchOrder`      INT,
  `branchLabel`      TEXT
    CHECK (`branchOrder` ISNULL OR `branchLabel` ISNULL), -- mixing branching styles is a bad idea.
  `alternativeOrder` INT,

  -- Rows that identify whether this is a tactic execution, or some other form of user interaction (e.g., interruption)
  `status`           TEXT,
    CHECK (`status` IN ('Prepared', 'Running', 'Finished', 'Aborted', 'Error', 'DependsOnChildren'))
  `executableId`     INTEGER REFERENCES `executables` (`_id`),

  -- Rows that identify input and output of the tactic
  `inputProvableId`  INTEGER REFERENCES `provables` (`_id`),
  `resultProvableId` INTEGER REFERENCES `provables` (`_id`),
  `localProvableId`  INTEGER REFERENCES `provables` (`_id`),

  -- Indicates whether this tactic was *directly* executed by the user.
  `userExecuted`     BOOLEAN,
  -- Indicates whether all children of this execution step are present in the database yet. By default children are not
  -- saved in the database because they take a lot of space
  `childrenRecorded` BOOLEAN,
  --
  -- In theory this can be recovered from the belleExpr, but life is easier this way
  `ruleName` STRING
);

----------------------------------------------------------------------------------------------------
-- Serialization of tactics
-- These tables record enough information to reconstruct executed tactics.
----------------------------------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS `executables` (
  `_id`  INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `belleExpr`     TEXT
);
