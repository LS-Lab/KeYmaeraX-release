DELETE FROM executionSteps;
DELETE FROM executables;
DELETE FROM lemmas;
UPDATE proofs SET lemmaId = NULL;
UPDATE config SET value="4.8.0" WHERE configName="version" AND key="version";