HYRDA WEB SERVER
================

HyDRA (Hybrid Distributed Reasoning Architecture) is the "middle man" between
the Javascript user interface and KeYmaera instances. Hydra exposes a REST API
using the Spray framework.  KeYmaera instances as well as Javascript clients
interact with this API.


#API DEFINITION#

##State Update Messages (sent by KeYmaera)##

    The KeYmaera client is in edu.cmu.cs.ls.keymaera.hydra.client

    Return Format: application/json
    Return value: { success: true|false; }

    nodeClosed/<list[sequent]>
    nodePruned/<list[sequent]>
    limitExceeded/<list[sequent]>
    startingStrategy/<?>/<strategy name>

##State Query Messages (sent by GUI)##

    The JS client is in jsgui/api_client.js

    Prototypes for Event and Sequent are defined in jsgui/api_types.js

    State Request Messages:
      /startSession/
        Returns: { sessionName: <string>; }
      /getUpdates/<sessionName>
        Returns: [ Event, Event, ... ]
      /getNode/<?>
        Returns: [ Sequent, Sequent, ... ]

##Requests (sent by GUI)##

    /applyTactic/<position>/<tactic name>

##To add a new request/response

 * Add a Request class
 * Add a Update class
 * Add a path in RestApi (be sure to append to the list of routes).
 * Add a case in the HydraEventHandler javascript function.



DESIGN DISCUSSION
=================

- REST API should have multiple categories: proof, lemma, tactic
- Within proof there should be local lemmas and tactics
- Business Logic generates identifiers for proof nodes using base 36 encoding of numbers of the form 1/1/2/1/3/4 interpreted as 112134 base 5 and then translated to base 36 (digits + lowercase letters). We can do this conversion since the out-degree of proof rules is known.
- Alternatives should then be marked with specific prefix and be encoded by integers. Thus, we will have /proof/A32B/alt:3/B21 to switch to the third alternative from a specific node and then proceed along the default alternative there. This will only get big if we spawn lots and lots of alternatives in each alternative.
- If the URL ever gets too long: Introduce unique node identifiers to shorten the path
- Store all mappings in a data base on the web server side
- Give out JSON to the client such that it does not have to compute any identifiers itself
- Work on JSON instead of named objects on the client side
- Tactic applications should be of the form /proof/<nodeid>/apply?name="tacticxyz"&inv="x^2 > 5"&form="Ante,2,92B36X"

