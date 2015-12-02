CREATE TABLE IF NOT EXISTS `config`  (
  `configId` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `configName` TEXT,
  `key` TEXT,
  `value` TEXT
);

CREATE TABLE IF NOT EXISTS `users` (
  `email` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `password` TEXT
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
  `closed` INTEGER -- ?
);

----------------------------------------------------------------------------------------------------
-- Serialization of Provables
----------------------------------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS `provables` (
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL
);

CREATE TABLE IF NOT EXISTS `sequents` (
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `provableId` INTEGER REFERENCES `provables` (`_id`),
  `idx` INTEGER, -- index of the sequent within the provable. If null then this is the conclusion of the provable.
  `conclusionId` INTEGER REFERENCES `sequents` (`_id`)
);

CREATE TABLE IF NOT EXISTS `sequentFormulas` (
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `sequentId` INTEGER REFERENCES `sequents` (`_id`),
  `isAnte` BOOLEAN,
  `idx` INTEGER,
  `formula` TEXT
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
  `executableId`     INTEGER REFERENCES `executables` (`_id`),

  -- Rows that identify input and output of the tactic
  `inputProvableId`  INTEGER REFERENCES `provables` (`_id`),
  `resultProvableId` INTEGER REFERENCES `provables` (`_id`),

  -- Indicates whether this tactic was *directly* executed by the user.
  `userExecuted`     BOOLEAN
);

----------------------------------------------------------------------------------------------------
-- Serialization of tactics
-- These tables record enough information to reconstruct executed tactics.
----------------------------------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS `executables` (
  `_id`  INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `scalaTacticId` INTEGER REFERENCES `scalaTactics` (`_id`),
  `belleExpr`     TEXT
    CHECK (`scalaTacticId` ISNULL OR
           `belleExpr` ISNULL) -- each executable is either a bellerophon expression (a.k.a. custom tactic) or a built-in scala tactic.
);

CREATE TABLE IF NOT EXISTS `scalaTactics` (
  `_id` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `location`      TEXT,
  `name`          TEXT
);

CREATE TABLE `executableParameter` (
  `_id`  INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `executableId` INTEGER REFERENCES `executables` (`_id`),
  `idx`          INT,
  `valueType`  TEXT,
  `value`        TEXT
);

-- Specific table for serializing USubstPatternTactics.
CREATE TABLE `patterns` (
  `_id`           INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `executableId`        INTEGER REFERENCES `executables` (`_id`),
  `idx`                 INT,
  `patternFormula`      TEXT,
  `resultingExecutable` INTEGER REFERENCES `executables` (`_id`)
);
