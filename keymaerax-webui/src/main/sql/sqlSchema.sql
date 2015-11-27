CREATE TABLE IF NOT EXISTS `config`  (
  `configId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `configName` TEXT,
  `key` TEXT,
  `value` TEXT
);

CREATE TABLE IF NOT EXISTS `users` (
  `email` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `password` TEXT
);

CREATE TABLE IF NOT EXISTS `models` (
  `modelId` TEXT PRIMARY KEY ON CONFLICT FAIL,
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
  `proofId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `modelId` TEXT REFERENCES `models` (`modelId`),
  `name` TEXT,
  `description` TEXT,
  `date` TEXT,
  `closed` INTEGER -- ?
);

----------------------------------------------------------------------------------------------------
-- Serialization of Provables
----------------------------------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS `provables` (
  `provableId` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `conclusionId` INTEGER REFERENCES `sequents` (`sequentId`)
);

CREATE TABLE IF NOT EXISTS `sequents` (
  `sequentId` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `provableId` INTEGER REFERENCES `provables` (`provableId`)
);

CREATE TABLE IF NOT EXISTS `sequentFormulas` (
  `sequentFormulaId` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `sequentId` INTEGER REFERENCES `sequents` (`sequentId`),
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
  `executionId` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `proofId` TEXT REFERENCES `proofs` (`proofId`)
);

CREATE TABLE IF NOT EXISTS `executionSteps` (
  `stepId`           INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `executionId`      INTEGER REFERENCES `tacticExecutions` (`executionId`),

  -- Rows that identify where in the proof this execution step occurs.
  `previousStep`     INTEGER REFERENCES `executionSteps` (`stepId`),
  `parentStep`       INTEGER REFERENCES `executionSteps` (`stepId`),
  `branchOrder`      INT,
  `branchLabel`      TEXT
    CHECK (`branchOrder` ISNULL OR `branchLabel` ISNULL), -- mixing branching styles is a bad idea.
  `alternativeOrder` INT,

  -- Rows that identify whether this is a tactic execution, or some other form of user interaction (e.g., interruption)
  `status`           TEXT,
  `executableId`     INTEGER REFERENCES `executables` (`executableId`),

  -- Rows that identify input and output of the tactic
  `inputProvableId`  INTEGER REFERENCES `provables` (`provableId`),
  `resultProvableId` INTEGER REFERENCES `provables` (`provableId`),

  -- Indicates whether this tactic was *directly* executed by the user.
  `userExecuted`     BOOLEAN
);

----------------------------------------------------------------------------------------------------
-- Serialization of tactics
-- These tables record enough information to reconstruct executed tactics.
----------------------------------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS `executables` (
  `executableId`  INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `scalaTacticId` INTEGER REFERENCES `scalaTactics` (`scalaTacticId`),
  `belleExpr`     TEXT
    CHECK (`scalaTacticId` ISNULL OR
           `belleExpr` ISNULL) -- each executable is either a bellerophon expression (a.k.a. custom tactic) or a built-in scala tactic.
);

CREATE TABLE IF NOT EXISTS `scalaTactics` (
  `scalaTacticId` INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `location`      TEXT,
  `name`          TEXT
);

CREATE TABLE `executableParameter` (
  `parameterId`  INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `executableId` INTEGER REFERENCES `executables` (`executableId`),
  `idx`          INT,
  `valueType`  TEXT,
  `value`        TEXT
);

-- Specific table for serializing USubstPatternTactics.
CREATE TABLE `patterns` (
  `patternId`           INTEGER PRIMARY KEY ON CONFLICT FAIL,
  `executableId`        INTEGER REFERENCES `executables` (`executableId`),
  `idx`                 INT,
  `patternFormula`      TEXT,
  `resultingExecutable` INTEGER REFERENCES `executables` (`executableId`)
);
