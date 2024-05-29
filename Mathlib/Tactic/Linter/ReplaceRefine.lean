/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.List.Basic
import Mathlib.Tactic.Lemma

/-!
# A linter to replace `refine'` with `refine`
-/

namespace Mathlib.Linter

/--
The linter helps with the conversion `refine'` to `refine`, by printing the positions of
missing `?`.
-/
register_option linter.refine'ToRefine : Bool := {
  defValue := true
  descr := "flag `refine'` that can be converted to `refine`s"
}

namespace Refine'

open Lean Elab

/-- converts
* `theorem x ...`  to `example ...`,
* `lemma x ...`    to `example ...`,
* `instance x ...` to `example ...`,
*  everything else goes to itself.

This avoids producing two declarations with the same name in the environment.
-/
def toExample {m : Type → Type} [Monad m] [MonadQuotation m] : Syntax → m Syntax
  | `($_dm:declModifiers theorem $_did:declId $ds* : $t $dv:declVal) =>
    `(example $ds* : $t $dv:declVal)
  | `($_dm:declModifiers lemma $_did:declId $ds* : $t $dv:declVal) =>
    `(example $ds* : $t $dv:declVal)
  | `($_dm:declModifiers instance $_did:declId $ds* : $t $dv:declVal) =>
    `(example $ds* : $t $dv:declVal)
  | s => return s

/-- extracts the `Array` of subsyntax of the input `Syntax` that satisfies the given predicate
`Syntax → Bool`.
-/
partial
def _root_.Lean.Syntax.findAll : Syntax → (Syntax → Bool) → Array Syntax
  | stx@(.node _ _ args), f =>
    let rest := (args.map (·.findAll f)).flatten
    if f stx then rest.push stx else rest
  | s, f => if f s then #[s] else #[]

/-- extracts "holes" `_`, taking care of not extracting them when they appear in a "synthetic hole"
`?_`, nor in a "by assumption" `‹_›`. -/
partial
def getHoles : Syntax → Array Syntax
  | .node _ ``Lean.Parser.Term.syntheticHole _ => #[]
  | .node _ ``«term‹_›» _ => #[]
  | hole@(.node _ kind args) =>
    let args := (args.map getHoles).flatten
    if kind == ``Lean.Parser.Term.hole then args.push hole else args
  | _ => #[]

/-- extracts "synthetic holes" `?_` from the input syntax.
After converting `refine'` to `refine`, these are the locations of the nodes that have been
successfully replaced with `?_`.
-/
def getSynthHoles (stx : Syntax) : Array Syntax :=
  stx.findAll (·.isOfKind ``Lean.Parser.Term.syntheticHole)

/-- converts an "anonymous hole" `_` to a "synthetic hole" `?_` with comparable
`SourceInfo`.
Leaves unchanged inputs that are not "anonymous holes".
-/
def holeToSyntHole : Syntax → Syntax
  | hole@(.node si ``Lean.Parser.Term.hole _) =>
    .node si ``Lean.Parser.Term.syntheticHole #[mkAtomFrom hole "?", hole]
  | s => s

/-- extracts `refine'` from the input syntax. -/
def getRefine's (stx : Syntax) : Array Syntax :=
  stx.findAll (·.isOfKind ``Lean.Parser.Tactic.refine')

/-- `candidateRefines stx` returns the array `#[stx₁, ..., stxₙ]`, where each `stxᵢ` is obtained
from `stx` by replacing a subset of the `_` with `?_`.

The intended application is when `stx` is a syntax node representing `refine' ...`. -/
def candidateRefines (stx : Syntax) : Array (Syntax × List Syntax) := Id.run do
  let mut cands := #[]
  let holes := getHoles stx
  for sub in holes.toList.sublistsFast do
    let mut newCmd := stx
    for s in sub do
      newCmd ← newCmd.replaceM (fun t =>
        if t == s && t.getPos? == s.getPos? then some (holeToSyntHole s) else none)
    cands := cands.push (newCmd, sub)
  return cands

/-- converts each `refine'` with a `refine` in `stx`. -/
def ToRefine (stx : Syntax) : Syntax := Id.run do
  stx.replaceM (fun s => match s with
    | .node si ``Lean.Parser.Tactic.refine' args =>
      let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine"
      return some (.node si ``Lean.Parser.Tactic.refine args)
    | _ => return none)

/-- replaces each `refine'` by `refine` in succession in `cmd`, trying to replace every subset of
`?_` with `_`.

Eventually, it returns an array of pairs `(1/0, position)`, where
* `1` means that the `position` is the beginning of `refine'` and
* `0` means that the `position` is a missing `?`,
for each successful replacement.
-/
def getQuestions (cmd : Syntax) : Command.CommandElabM (Array (Syntax × List Syntax)) := do
  let exm ← toExample cmd
  let st ← get
  let refine's := getRefine's cmd
  let mut suma := #[]
  for refine' in refine's do
    let refine := ToRefine refine'
    let cands := candidateRefines refine
    for (cand, holes) in cands do
      let repl ← exm.replaceM fun s => if s == refine' then return some cand else return none
      Command.elabCommand repl
      if !(← get).messages.hasErrors then
        suma := suma.push ((Syntax.getHead? refine').getD default, holes)
        logInfoAt ((Syntax.getHead? refine').getD default) m!"{refine}"
        logInfoAt ((Syntax.getHead? refine').getD default) m!"{cand}"
        --let sr := (refine'.getRange?).getD default
        --logInfoAt ((Syntax.getHead? refine').getD default) m!"{(sr.start, sr.stop)}"
        break
      set st
  return suma

/-- Gets the value of the `linter.refine'ToRefine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.refine'ToRefine o

/-- Reports the positions of missing `?`. -/
def ToRefineLinter : Linter where run stx := do
  --let fm ← getFileMap
  if getLinterHash (← getOptions) then
    let _pos ← getQuestions stx
    --for (r, hls) in pos do
    --  let rPos := r.getPos?.getD default
    --  let lc := fm.toPosition rPos
    --  logInfoAt r m!"(1, {lc.1}, {lc.2})"
    --  let _ ← hls.mapM fun hl =>
    --    let hlPos := hl.getPos?.getD default
    --    let hlc := fm.toPosition hlPos
    --    (logInfoAt hl m!"(0, {hlc.1}, {hlc.2})")

initialize addLinter ToRefineLinter
