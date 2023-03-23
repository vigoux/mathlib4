import Mathlib.Tactic.ChatGPT.Curl
import Mathlib.Tactic.ChatGPT.JSON

open Lean

namespace Mathlib.Tactic.ChatGPT

def sendMessages (messages : List Message) (attempts : Nat := 3) : IO Response :=
  aux none none (toString <| toJson <| ({ messages := messages } : Request)) attempts
where
  aux (error lastJSON : Option String) (jsonMessage : String) : Nat → IO Response
  | 0 => throw <| IO.userError <| s!"Failed after {attempts} attempts.\n" ++ error.getD "" ++ "\n" ++ lastJSON.getD ""
  | i+1 => do
    let jsonResponse ← curl <| jsonMessage
    match parseResponse jsonResponse with
    | .error e =>
        if e.startsWith "server_error: " then
          aux e jsonResponse jsonMessage i
        else
          throw <| IO.userError <| e ++ "\n" ++ jsonResponse
    | .ok r => pure r

def send (request : String) : IO String := do
  let r ← sendMessages [⟨.user, request⟩]
  match r.content with
  | none => throw <| IO.userError "ChatGPT response did not contain content."
  | some r => pure r
