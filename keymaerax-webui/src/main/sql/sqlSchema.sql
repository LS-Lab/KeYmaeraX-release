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

  -- Considering the proof as a sequence of steps, the previous step.
  -- The input provable of this step must match with the output of the previous step,
  -- and the localProvable must make sense when applied to previousStep.subgoals(branchOrder)
  `previousStep`     INTEGER REFERENCES `executionSteps` (`_id`),
  -- Enables recording a tactic execution at multiple levels of detail. If set, indicates that this step
  -- is a sub-step of parentStep (e.g. parentStep involves doing many things, one of which is this step)
  `parentStep`       INTEGER REFERENCES `executionSteps` (`_id`),
  -- Indicates which subgoal of previousStep the step affects. If previousStep is NULL, this is the first step,
  -- so there is only one subgoal and branchOrder will always be 0.
  `branchOrder`      INT,
  -- (UNUSED) Indicates which subgoal of previousStep the step affects, using a textual label. It should be easier
  -- to translate the label to an index before storing the step.
  `branchLabel`      TEXT
    CHECK (`branchOrder` ISNULL OR `branchLabel` ISNULL), -- mixing branching styles is a bad idea.
  -- Which alternate history of the universe this step inhabits. The ExecutionSteps table stores a complete history
  -- of the execution. If a user undoes a proof step, this is implemented as going back to the undo-point and adding
  -- a new execution step as part of a "more recent" (higher alternativeOrder) version of the universe.
  `alternativeOrder` INT,

  -- Progress or final outcome of tactic execution.
  --   Prepared: We know what tactic we will run, but have not started running it yet.
  --   Finished: Tactic succeeded
  --   Aborted: User cancelled the tactic (e.g. because it is taking too long)
  --   Error: Tactic encountered an error all on its own (e.g. not applicable, or Mathemetica broke)
  --   DependsOnChildren: Cannot determine status without inspecting status of children. Should not be visible to user
  --     but necessary to compute status correctly in concurrent situations.
  `status`           TEXT,
    CHECK (`status` IN ('Prepared', 'Running', 'Finished', 'Aborted', 'Error', 'DependsOnChildren'))
  `executableId`     INTEGER REFERENCES `executables` (`_id`),

  -- Global provable at beginning of step
  `inputProvableId`  INTEGER REFERENCES `provables` (`_id`),
  -- Global provable at end of step
  `resultProvableId` INTEGER REFERENCES `provables` (`_id`),
  -- Local provable that proves inputProvable(branchOrder) from 0 or more subgoals */
  `localProvableId`  INTEGER REFERENCES `provables` (`_id`),

  -- Indicates whether this tactic was *directly* executed by the user.
  -- Example scenario where this is false: KeYmaeraX needed to issue tactics to implement some other feature, such as undo.
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
