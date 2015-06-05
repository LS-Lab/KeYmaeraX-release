CREATE TABLE IF NOT EXISTS `config`  (
  `configId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `configName` TEXT,
  `key` TEXT,
  `value` TEXT
);

CREATE TABLE IF NOT EXISTS `tactics` (
  `tacticId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `name` TEXT,
  `clazz` TEXT,
  `kind` TEXT
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

--proofs
--  proofId
--  modelId
--  name
--  description
--  date
--  closed
CREATE TABLE IF NOT EXISTS `proofs` (
  `proofId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `modelId` TEXT REFERENCES `models` (`modelId`),
  `name` TEXT,
  `description` TEXT,
  `date` TEXT,
  `closed` INTEGER -- ?
);

CREATE TABLE IF NOT EXISTS `tacticOnProof` (
  `proofTacticId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `proofId` TEXT REFERENCES `proofs` (`proofId`),
  `tacticsId` TEXT REFERENCES `tactics` (`tacticId`),
  `nodeId` TEXT,
  `formulaId` TEXT,
  `auto` TEXT,
  `status` TEXT
);

CREATE TABLE IF NOT EXISTS `proofTacticInput` (
  `proofTacticId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `inputOrder` INTEGER,
  `input` TEXT
);

CREATE TABLE IF NOT EXISTS `CLTerms` (
  `termId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `clTerm` TEXT,
  `proofId` TEXT REFERENCES `proofs` (`proofId`),
  `nodeId` TEXT,
  `status` TEXT
);

CREATE TABLE IF NOT EXISTS `completedTasks` (
  `stepId` TEXT PRIMARY KEY NOT NULL ON CONFLICT FAIL,
  `proofId` TEXT REFERENCES `proofs` (`proofId`),
  `idx` INTEGER NOT NULL,
  `termId` TEXT REFERENCES `CLTerms` (`termId`),
  `proofTacticId` TEXT REFERENCES `tacticOnProof` (`proofTacticId`)
);
