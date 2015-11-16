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
  `provableId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `conclusionId` TEXT REFERENCES `sequents`
);

CREATE TABLE IF NOT EXISTS `sequents` (
  `sequentId` TEXT,
  `provableId` TEXT REFERENCES `provables` (`provableId`)
);

CREATE TABLE IF NOT EXISTS `sequentFormulas` (
  `sequentFormulaId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `sequentId` TEXT REFERENCES `sequents` (`sequentId`),
  `isAnte` BOOLEAN,
  `idx` INTEGER,
  `formula` TEXT
);

----------------------------------------------------------------------------------------------------
-- Record of tactic exeuction
-- These tables record only the *structure* of a tactic execution.
-- The actual contents of each step of the execution are stored in the tables in the next section.
----------------------------------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS `tacticExecutions` (
  `executionId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `proofId` TEXT REFERENCES `proofs` (`proofId`)
);

CREATE TABLE IF NOT EXISTS `executionSteps` (
  `stepId`           TEXT PRIMARY KEY ON CONFLICT FAIL,
  `exeuctionId`      TEXT REFERENCES `tacticExecutions` (`executionId`),

  -- Rows that identify where in the proof this execution step occurs.
  `previousStep`     TEXT REFERENCES `executionSteps` (`stepId`),
  `parentStep`       TEXT REFERENCES `executionSteps` (`stepId`),
  `branchOrder`      TEXT,
  `branchLabel`      INT
    CHECK (`branchOrder` ISNULL OR `branchLabel` ISNULL), -- mixing branching styles is a bad idea.
  `alternativeOrder` INT,

  -- Rows that identify whether this is a tactic execution, or some other form of user interaction (e.g., interruption)
  `status`           TEXT,
  `executableId`     TEXT REFERENCES `executables` (`executableId`),

  -- Rows that identify input and output of the tactic
  `inputProvableId`  TEXT REFERENCES `provables` (`provableId`),
  `resultProvableId` TEXT REFERENCES `provables` (`provableId`),

  -- Indicates whether this tactic was *directly* executed by the user.
  `userExecuted`     BOOLEAN
);

----------------------------------------------------------------------------------------------------
-- Serialization of tactics
-- These tables record enough information to reconstruct executed tactics.
----------------------------------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS `executables` (
  `executableId`  TEXT PRIMARY KEY ON CONFLICT FAIL,
  `scalaTacticId` TEXT,
  `belleExpr`     TEXT
    CHECK (`scalaTacticId` ISNULL OR
           `belleExpr` ISNULL) -- each executable is either a bellerophon expression (a.k.a. custom tactic) or a built-in scala tactic.
);

CREATE TABLE IF NOT EXISTS `scalaTactics` (
  `scalaTacticId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `location`      TEXT
);

CREATE TABLE `executableParameter` (
  `parameterId`  TEXT PRIMARY KEY ON CONFLICT FAIL,
  `executableId` TEXT REFERENCES `executables` (`executableId`),
  `idx`          INT,
  `valueTypeId`  TEXT REFERENCES `argumentTypes` (`typeId`),
  `value`        TEXT
);

CREATE TABLE `valueTypes` (
  `valueTypeId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `type` TEXT
);
INSERT INTO valueTypes VALUES('0', 'String');
INSERT INTO valueTypes VALUES('1', 'Position');
INSERT INTO valueTypes VALUES('2', 'Formula');
INSERT INTO valueTypes VALUES('3', 'Provable'); -- If `executableParameter`.`valueTypeId` = 3, then `executableParameter`.`value` is an FK to provables.

-- Specific table for serializing USubstPatternTactics.
CREATE TABLE `patterns` (
  `patternId`           TEXT PRIMARY KEY ON CONFLICT FAIL,
  `executableId`        TEXT REFERENCES `executables` (`executableId`),
  `idx`                 INT,
  `patternFormula`      TEXT,
  `resultingExecutable` TEXT REFERENCES `executables` (`executableId`)
);