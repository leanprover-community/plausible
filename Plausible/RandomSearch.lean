import Plausible.MetaTestable
/-!
## Random Search

The `random_search` tactic tries to prove a result by searching for a counter-example to its negation using `MetaTestable`. If a counter-example is found, we can prove the result by showing that the negation is false.
-/

open Lean Meta Elab Term

namespace Plausible

open Classical in
theorem not_not (p: Prop) : ¬ ¬ p → p :=
  fun h' => if h : p then h else absurd h h'

open Classical in
theorem not_and {p q : Prop} : ¬ (p ∧ q) →  ¬ p ∨ ¬ q :=
  fun h => if hp : p then Or.inr fun hq => h ⟨hp, hq⟩ else Or.inl hp

theorem induced_or {p₁ q₁ p₂ q₂ : Prop} (h₁ : p₁ → q₁) (h₂ : p₂ → q₂) : p₁ ∨ p₂ → q₁ ∨ q₂
  | Or.inl h => Or.inl (h₁ h)
  | Or.inr h => Or.inr (h₂ h)

theorem induced_and {p₁ q₁ p₂ q₂ : Prop} (h₁ : p₁ → q₁) (h₂ : p₂ → q₂) : p₁ ∧ p₂ → q₁ ∧ q₂
  | ⟨h1, h2⟩ => ⟨h₁ h1, h₂ h2⟩

theorem induced_exists {p q : α → Prop}(f : ∀x : α, p x → q x) : (∃ x, p x) → ∃ x, q x
  | ⟨x, h⟩ => ⟨x, f x h⟩

theorem not_or_mp {p q : Prop} (h : ¬ (p ∨ q)) : ¬ p ∧ ¬ q :=
  ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩

theorem not_forall {p : α → Prop} : ¬ (∀ x, p x) →  ∃ x, ¬ p x := by
  intro h
  apply not_not
  intro contra
  have l : ∀ (x : α), p x := by
    intro x
    by_cases h' : p x
    · exact h'
    · exfalso
      exact contra ⟨x, h'⟩
  contradiction


partial def negate (e: Expr) : MetaM <| Expr × Expr := do
  match ← notProp? e with
  | some e' =>
    let negProof ← mkAppOptM ``id #[e]
    return (e', negProof)
  | _ =>
  match ← andProp? e with
  | (some e₁, some e₂) =>
    let (negProp₁, negProof₁) ← negate e₁
    let (negProp₂, negProof₂) ← negate e₂
    let negProp ← mkAppM ``Or #[negProp₁, negProp₂]
    let negPf ← withLocalDeclD `h (← mkAppM ``Not #[negProp]) fun h => do
      let h' ← mkAppM ``not_or_mp #[h]
      let negProof ← mkAppM ``induced_and #[negProof₁, negProof₂, h']
      mkLambdaFVars #[h] negProof
    return (negProp, negPf)
  | _ =>
  match ← orProp? e with
  | (some e₁, some e₂) =>
    let (negProp₁, negProof₁) ← negate e₁
    let (negProp₂, negProof₂) ← negate e₂
    let negProp ← mkAppM ``And #[negProp₁, negProp₂]
    let negPf ← withLocalDeclD `h (← mkAppM ``Not #[negProp]) fun h => do
      let h' ← mkAppM ``not_and #[h]
      let negProof ← mkAppM ``induced_or #[negProof₁, negProof₂, h']
      mkLambdaFVars #[h] negProof
    return (negProp, negPf)
  | _ =>
  match ← existsProp? e with
  | (some p, some α) =>
    logInfo m!"Negating existential quantifier {← ppExpr e}, family: {← ppExpr p}, domain: {← ppExpr α}"
    let (negProp, negProofFamily) ← withLocalDeclD `x α fun x => do
      let y ← mkAppM' p #[x]
      let (y, _) ← dsimp y {}
      let (negProp, negProof) ← negate y
      pure (← mkForallFVars #[x] negProp, ← mkLambdaFVars #[x] negProof)
    logInfo m!"Negation of {← ppExpr e} is {← ppExpr negProp}"
    let negPf ← withLocalDeclD `h (← mkAppM ``Not #[negProp]) fun h => do
      let h' ← mkAppM ``not_forall #[h]
      let negProof ← mkAppM ``induced_exists #[negProofFamily, h']
      mkLambdaFVars #[h] negProof
    return (negProp, negPf)
  | _ =>
    let negProp ← mkAppM ``Not #[e]
    let negProof ← mkAppM ``not_not #[e]
    return (negProp, negProof)

open Elab Term
elab "neg_neg" t:term : term => do
  let e ← elabTerm t none
  let (negProp, negProof) ← negate e
  let pfType ← inferType negProof
  -- disproof of negation implies `e`
  let goal ← mkArrow (← mkAppM ``Not #[negProp]) e
  let check ← isDefEq pfType goal
  logInfo m!"Negation of {← ppExpr e} is {← ppExpr negProp}"
  logInfo m!"Proof of negation is {← ppExpr negProof} with type {← ppExpr <| ← inferType negProof}, should be {← ppExpr goal}"
  logInfo m!"check: {check}"
  return negProp

open Lean.Parser.Tactic Tactic
syntax (name := searchSyntax) "random_search" (config)? : tactic
elab_rules : tactic | `(tactic| random_search $[$cfg]?) => withMainContext do
  let cfg ← elabConfig (mkOptionalNode cfg)  let (_, g) ← (← getMainGoal).revert ((← getLocalHyps).map (Expr.fvarId!))
  let cfg := { cfg with
    traceDiscarded := cfg.traceDiscarded || (← isTracingEnabledFor `plausible.discarded),
    traceSuccesses := cfg.traceSuccesses || (← isTracingEnabledFor `plausible.success),
    traceShrink := cfg.traceShrink || (← isTracingEnabledFor `plausible.shrink.steps),
    traceShrinkCandidates := cfg.traceShrinkCandidates
      || (← isTracingEnabledFor `plausible.shrink.candidates) }
  g.withContext do
  let tgt ← g.getType
  let (negProp, negProof) ← negate tgt
  match ← disproveM? cfg negProp with
  | some pf =>
    let pf' ← mkAppM' negProof #[pf]
    logInfo m!"Found a proof by negated counter-example!"
    g.assign pf'
  | none =>
    throwError "could not find a proof by negated counter-example"

end Plausible
