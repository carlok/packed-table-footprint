/- Where exactly does each axiom enter? Breadth-first search over the constants a
   declaration uses, in its type and value, printing a shortest chain to each axiom.
   Diagnostic only; nothing here is part of any certificate. -/
import Lean
import JudgeFinOp.MemoFinOp

open Lean
open Lean.Elab
open Lean.Elab.Command

def uses(env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | none => #[]
  | some ci =>
    let fromType := ci.type.getUsedConstants
    let fromValue := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    fromType ++ fromValue

/-- Shortest chain from `start` to each constant, by parent pointers. -/
partial def bfs (env : Environment) (start : Name) : Std.HashMap Name Name := Id.run do
  let mut parent : Std.HashMap Name Name := {}
  parent := parent.insert start start
  let mut frontier := #[start]
  while !frontier.isEmpty do
    let mut next := #[]
    for c in frontier do
      for d in uses env c do
        unless parent.contains d do
          parent := parent.insert d c
          next := next.push d
    frontier := next
  return parent

def chain (parent : Std.HashMap Name Name) (target : Name) : List Name := Id.run do
  let mut out := [target]
  let mut cur := target
  for _ in [0:10000] do
    match parent[cur]? with
    | some p =>
      if p == cur then break
      out := p :: out
      cur := p
    | none => break
  return out

elab "#axiom_paths " id:ident : command => do
  let env ← getEnv
  let c ← Lean.Elab.Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← Lean.Elab.Command.liftCoreM <| Lean.collectAxioms c
  logInfo m!"{c}: axioms {axs.toList}"
  let parent := bfs env c
  for a in axs do
    logInfo m!"  {a} via {chain parent a}"

#axiom_paths MemoFinOp.finOpTable
#axiom_paths String.toList
#axiom_paths List.filterMap
#axiom_paths Char.isDigit
#axiom_paths Char.toNat
#axiom_paths List.getD
#axiom_paths Option.getD
#axiom_paths List.getElem?_cons
#axiom_paths Nat.mod_lt
#axiom_paths Nat.decidableForallFin
#axiom_paths instDecidableEqFin
#axiom_paths magmaFin
