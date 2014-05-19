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

