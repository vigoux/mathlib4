/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean.Elab.Command
import Lean.Linter.Util

namespace Mathlib.Prelude.Rename

open Lean
open System (FilePath)
open Lean (HashMap)

/-- This structure keeps track of alignments from lean 3 names to lean 4 names and vice versa. -/
structure RenameMap where
  /-- This maps `n3 ↦ (dubious, n4)` where `n3` is the lean 3 name and `n4` is the corresponding
  lean 4 name. `dubious` is either empty, or a warning message to be displayed when `n3` is
  translated, which indicates that the translation from `n3` to `n4` is approximate and may cause
  downstream errors. -/
  toLean4 : NameMap (String × Name) := {}
  /-- This maps `n4 ↦ (n3, clashes)` where `n4` is the lean 4 name and `n3::clashes` is the list of
  all (non-`synthetic`) declarations that map to `n4`. (That is, we do not assume the mapping
  from lean 3 to lean 4 name is injective.) -/
  toLean3 : NameMap (Name × List Name) := {}
  deriving Inhabited

/-- An `olean` entry for the rename extension. -/
structure NameEntry where
  /-- The lean 3 name. -/
  n3 : Name
  /-- The lean 4 name, or `.anonymous` for a `#noalign`. -/
  n4 : Name
  /-- If true, this lean 3 -> lean 4 mapping will not be entered into the converse map.
  This is used for "internal" definitions that should never be referred to in the source syntax. -/
  synthetic := false
  /-- A dubious translation is one where there is a type mismatch
  from the translated lean 3 definition to a pre-existing lean 4 definition.
  Type errors are likely in downstream theorems.
  The string stored here is printed in the event that `n3` is encountered by synport. -/
  dubious := ""

/-- Insert a name entry into the `RenameMap`. -/
def RenameMap.insert (m : RenameMap) (e : NameEntry) : RenameMap :=
  let ⟨to4, to3⟩ := m
  let to4 := to4.insert e.n3 (e.dubious, e.n4)
  let to3 := if e.synthetic || e.n4.isAnonymous then to3 else
    match to3.find? e.n4 with
    | none => to3.insert e.n4 (e.n3, [])
    | some (a, l) => if (a::l).contains e.n3 then to3 else to3.insert e.n4 (a, e.n3 :: l)
  ⟨to4, to3⟩

/-- Look up a lean 4 name from the lean 3 name. Also return the `dubious` error message. -/
def RenameMap.find? (m : RenameMap) : Name → Option (String × Name) := m.toLean4.find?

set_option autoImplicit true in
-- TODO: upstream into core/std
instance [Inhabited α] : Inhabited (Thunk α) where
  default := .pure default

/-- This extension stores the lookup data generated from `#align` commands. -/
-- wrap state in `Thunk` as downstream projects rarely actually query it; it only
-- gets queried when new `#align`s are added.
initialize renameExtension : SimplePersistentEnvExtension NameEntry (Thunk RenameMap) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun t e => t.map (·.insert e)
    addImportedFn := fun es => ⟨fun _ => mkStateFromImportedEntries (·.insert) {} es⟩
  }

/-- Insert a new name alignment into the rename extension. -/
def addNameAlignment (n3 : Name) (n4 : Name) (synthetic := false) (dubious := "") : CoreM Unit := do
  modifyEnv fun env => renameExtension.addEntry env { n3, n4, synthetic, dubious }

/-- The `@[binport]` attribute should not be added manually, it is added automatically by mathport
to definitions that it created based on a lean 3 definition (as opposed to pre-existing
definitions). -/
initialize binportTag : TagAttribute ←
  registerTagAttribute `binport "this definition was autogenerated by mathport"

/--
Removes all occurrences of `ₓ` from the name.
This is the same processing used by mathport to generate name references,
and declarations with `ₓ` are used to align declarations that do not defeq match the originals.
-/
def removeX : Name → Name
  | .anonymous => .anonymous
  | .str p s =>
    let s := if s.contains 'ₓ' then
      s.foldl (fun acc c => if c = 'ₓ' then acc else acc.push c) ""
    else s
    .str (removeX p) s
  | .num p n => .num (removeX p) n

open Lean.Elab Lean.Elab.Command

/-- Because lean 3 uses a lowercase snake case convention, it is expected that all lean 3
declaration names should use lowercase, with a few rare exceptions for categories and the set union
operator. This linter warns if you use uppercase in the lean 3 part of an `#align` statement,
because this is most likely a typo. But if the declaration actually uses capitals it is not unusual
to disable this lint locally or at file scope. -/
register_option linter.uppercaseLean3 : Bool := {
  defValue := true
  descr := "enable the lean 3 casing lint"
}

/-- Check that the referenced lean 4 definition exists in an `#align` directive. -/
register_option align.precheck : Bool := {
  defValue := true
  descr := "Check that the referenced lean 4 definition exists in an `#align` directive."
}

/--
`#align lean_3.def_name Lean4.defName` will record an "alignment" from the lean 3 name
to the corresponding lean 4 name. This information is used by the
[mathport](https://github.com/leanprover-community/mathport) utility to translate later uses of
the definition.

If there is no alignment for a given definition, mathport will attempt to convert
from the lean 3 `snake_case` style to `UpperCamelCase` for namespaces and types and
`lowerCamelCase` for definitions, and `snake_case` for theorems. But for various reasons,
it may fail either to determine whether it is a type, definition, or theorem, or to determine
that a specific definition is in fact being called. Or a specific definition may need a different
name altogether because the existing name is already taken in lean 4 for something else. For
these reasons, you should use `#align` on any theorem that needs to be renamed from the default.
-/
syntax (name := align) "#align " ident ppSpace ident : command

/-- Checks that `id` has not already been `#align`ed or `#noalign`ed. -/
def ensureUnused {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (id : Name) : m Unit := do
  if let some (_, n) := (renameExtension.getState (← getEnv)).get.toLean4.find? id then
    if n.isAnonymous then
      throwError "{id} has already been no-aligned"
    else
      throwError "{id} has already been aligned (to {n})"

/--
Purported Lean 3 names containing capital letters are suspicious.
However, we disregard capital letters occurring in a few common names.
-/
def suspiciousLean3Name (s : String) : Bool := Id.run do
  let allowed : List String :=
    ["Prop", "Type", "Pi", "Exists", "End",
     "Inf", "Sup", "Union", "Inter",
     "Hausdorff", "is_R_or_C",
     "Ioo", "Ico", "Iio", "Icc", "Iic", "Ioc", "Ici", "Ioi", "Ixx"]
  let mut s := s
  for a in allowed do
    s := s.replace a ""
  return s.any (·.isUpper)

/-- Elaborate an `#align` command. -/
@[command_elab align] def elabAlign : CommandElab
  | `(#align $id3:ident $id4:ident) => do
    if (← getInfoState).enabled then
      addCompletionInfo <| CompletionInfo.id id4 id4.getId (danglingDot := false) {} none
      let c := removeX id4.getId
      if (← getEnv).contains c then
        addConstInfo id4 c none
      else if align.precheck.get (← getOptions) then
        let note := "(add `set_option align.precheck false` to suppress this message)"
        let inner := match ←
          try some <$> (liftCoreM <| realizeGlobalConstWithInfos id4)
          catch _ => pure none with
        | none => m!""
        | some cs => m!" Did you mean:\n\n\
              {("\n":MessageData).joinSep (cs.map fun c' => m!"  #align {id3} {c'}")}\n\n\
            #align inputs have to be fully qualified. \
            (Double check the lean 3 name too, we can't check that!)"
        throwErrorAt id4 "Declaration {c} not found.{inner}\n{note}"
      if Linter.getLinterValue linter.uppercaseLean3 (← getOptions) then
        if id3.getId.anyS suspiciousLean3Name then
          Linter.logLint linter.uppercaseLean3 id3
            "Lean 3 names are usually lowercase. This might be a typo.\n\
             If the Lean 3 name is correct, then above this line, add:\n\
             set_option linter.uppercaseLean3 false in\n"
    withRef id3 <| ensureUnused id3.getId
    liftCoreM <| addNameAlignment id3.getId id4.getId
  | _ => throwUnsupportedSyntax

/--
`#noalign lean_3.def_name` will record that `lean_3.def_name` has been marked for non-porting.
This information is used by the [mathport](https://github.com/leanprover-community/mathport)
utility, which will remove the declaration from the corresponding mathport file, and later
uses of the definition will be replaced by `sorry`.
-/
syntax (name := noalign) "#noalign " ident : command

/-- Elaborate a `#noalign` command. -/
@[command_elab noalign] def elabNoAlign : CommandElab
  | `(#noalign $id3:ident) => do
    withRef id3 <| ensureUnused id3.getId
    liftCoreM <| addNameAlignment id3.getId .anonymous
  | _ => throwUnsupportedSyntax

/-- Show information about the alignment status of a lean 3 definition. -/
syntax (name := lookup3) "#lookup3 " ident : command

/-- Elaborate a `#lookup3` command. -/
@[command_elab lookup3] def elabLookup3 : CommandElab
  | `(#lookup3%$tk $id3:ident) => do
    let n3 := id3.getId
    let m := renameExtension.getState (← getEnv) |>.get
    match m.find? n3 with
    | none    => logInfoAt tk s!"name `{n3} not found"
    | some (dubious, n4) => do
      if n4.isAnonymous then
        logInfoAt tk m!"{n3} has been no-aligned"
      else
        let mut msg := m!"{n4}"
        if !dubious.isEmpty then
          msg := msg ++ s!" (dubious: {dubious})"
        logInfoAt tk <|
          match m.toLean3.find? n4 with
          | none | some (_, []) => msg
          | some (n, l) => m!"{msg} (aliases {n :: l})"
  | _ => throwUnsupportedSyntax

open Lean Lean.Parser Lean.PrettyPrinter

/-- An entry in the `#align_import` extension, containing all the data in the command. -/
structure ImportEntry where
  /-- The lean 3 name of the module. -/
  mod3 : Name
  /-- The original repository from which this module was derived. -/
  origin : Option (String × String)

/-- The data for `#align_import` that is stored in memory while processing a lean file. -/
structure ImportState where
  /-- This is the same as `(← getEnv).header.mainModule`,
  but we need access to it in `exportEntriesFn` where the environment is not available. -/
  mod4 : Name := .anonymous
  /-- The original list of import entries from imported files. We do not process these because
  only mathport actually uses it. -/
  extern : Array (Array (Name × ImportEntry)) := #[]
  /-- The import entries from the current file. -/
  entries : List ImportEntry := []
  deriving Inhabited

/-- This extension stores the lookup data generated from `#align_import` commands. -/
initialize renameImportExtension :
    PersistentEnvExtension (Name × ImportEntry) (Name × ImportEntry) ImportState ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addEntryFn := fun s (mod4, e) => { s with mod4, entries := e :: s.entries }
    addImportedFn := fun extern => return { mod4 := (← read).env.header.mainModule, extern }
    exportEntriesFn := fun s => s.entries.reverse.foldl (fun a b => a.push (s.mod4, b)) #[]
  }

/-- Declare the corresponding mathlib3 module for the current mathlib4 module. -/
syntax (name := alignImport) "#align_import " ident (" from " str "@" str)? : command

/-- Elaborate a `#align_import` command. -/
@[command_elab alignImport] def elabAlignImport : CommandElab
  | `(#align_import $mod3 $[from $repo @ $sha]?) => do
    let origin ← repo.mapM fun repo => do
      let sha := sha.get!
      let shaStr := sha.getString
      if !shaStr.all ("abcdef0123456789".contains) then
        throwErrorAt sha "not a valid hex sha, bad digits"
      else if shaStr.length ≠ 40 then
        throwErrorAt sha "must be a full sha"
      else
        pure (repo.getString, shaStr)
    modifyEnv fun env =>
      renameImportExtension.addEntry env (env.header.mainModule, { mod3 := mod3.getId, origin })
  | _ => throwUnsupportedSyntax
