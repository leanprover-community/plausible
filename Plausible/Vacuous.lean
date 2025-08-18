import Lean
import Plausible
import Plausible.MetaTestable
/-!
## Vacuous Implication

The `vacuous` tactic is used to prove vacuous implications. We use the plausible search for counterexamples (actually at the `MetaTestable` level) to find a counterexample to the hypothesis. If a counterexample is found, we can prove the vacuous implication by showing that the hypothesis is never satisfied.
-/

open Lean Meta Elab Tactic Plausible

partial def proveVacuous? (p: Expr) (cfg : Configuration := {})  : MetaM <| Option Expr := do
  match p with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      let b := b.instantiate1 x
      let contra? ← try
        disproveM? cfg d -- proof of ¬d
      catch _ =>
        pure none
      match contra? with
      | some contra =>
        logInfo m!"Vacuous Implication. Hypothesis {← ppExpr d} is never satisfied"
        let pfFalse ← mkAppM' contra #[x]
        let pfBody ← mkAppOptM ``False.elim #[b, pfFalse]
        mkLambdaFVars #[x] pfBody
      | none =>
        let inner ← proveVacuous? b cfg
        inner.mapM fun pf => mkLambdaFVars #[x] pf
  | _ =>
    return none

open Lean.Parser.Tactic

syntax (name := vacuousSyntax) "vacuous" (config)? : tactic
elab_rules : tactic | `(tactic| vacuous $[$cfg]?) => withMainContext do
  let cfg ← elabConfig (mkOptionalNode cfg)  let (_, g) ← (← getMainGoal).revert ((← getLocalHyps).map (Expr.fvarId!))
  let cfg := { cfg with
    traceDiscarded := cfg.traceDiscarded || (← isTracingEnabledFor `plausible.discarded),
    traceSuccesses := cfg.traceSuccesses || (← isTracingEnabledFor `plausible.success),
    traceShrink := cfg.traceShrink || (← isTracingEnabledFor `plausible.shrink.steps),
    traceShrinkCandidates := cfg.traceShrinkCandidates
      || (← isTracingEnabledFor `plausible.shrink.candidates) }
  g.withContext do
  let tgt ← g.getType
  match ← proveVacuous? tgt cfg with
  | some pf =>
    g.assign pf
  | none =>
    throwError "no vacuous proof found"
