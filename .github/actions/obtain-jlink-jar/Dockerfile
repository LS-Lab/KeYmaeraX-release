# Uses a digest instead of a version number to be as exact as possible.
# This ensures CI doesn't unexpectedly break as a result of a new release.
# However, the version should be manually bumped from time to time.
#
# See also:
# https://www.wolfram.com/engine/
# https://hub.docker.com/r/wolframresearch/wolframengine
# https://docs.docker.com/engine/reference/builder/#from
#
# Digest from version 13.3.0
FROM wolframresearch/wolframengine@sha256:3ff9460b7c53a66f4eb5528e066a40293f3ad935c85f12353ad3dc9fe121c127

# The Wolfram Engine docker image appears to switch to a different user.
# However, we need to be root to write to /github/workspace/.
# https://github.com/orgs/community/discussions/25892
USER root

COPY entrypoint.sh /entrypoint.sh

ENTRYPOINT ["/entrypoint.sh"]
