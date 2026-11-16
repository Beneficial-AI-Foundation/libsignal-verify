import LibsignalVerifyBlueprint.VCVio
import LibsignalVerifyBlueprint.PQXDH
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
open Verso.Genre Verso.Genre.Manual Informal
#doc (Manual) "Libsignal protocol verification" =>

{include 0 LibsignalVerifyBlueprint.VCVio}

{include 0 LibsignalVerifyBlueprint.PQXDH}

{blueprint_graph (direction := LR)}
{blueprint_summary}
