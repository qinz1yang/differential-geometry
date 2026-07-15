import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFrameInvariant
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The orthonormal-frame reaction-form bridge for the `∇ᵏRm` tower

This file builds the **algebraic half** of the bridge connecting the *concrete,
derived, intrinsic* all-`k` heat equation `nablaKRm04NormHeatEquationOn_intrinsic`
(`Evolution/IteratedRmTowerHeatEq.lean`) to the *schematic* tower interface
`IteratedRmTowerOn` (`Evolution/IteratedNablaRmTower.lean`).

## The two reaction forms

The concrete heat equation produces the predicate
`NablaRm04NormHeatEquationOn u uLap nabla2 reaction` with `u = |∇ᵏRm|²` the
intrinsic fibre norm and the **derived** reaction

`reaction = nablaKRm04ReactionIntrinsic = ricReactionContract(gInv,ric,∇ᵏRm,∇ᵏRm)`
`         + 2·⟨(∂ₜ − Δ)∇ᵏRm, ∇ᵏRm⟩`

(`Evolution/IteratedRmTowerHeatEq.lean`), a *metric-contracted* scalar.

The tower interface `IteratedRmTowerOn` wants the reaction in the **schematic
plain-component** form

`towerReactionMulti (level·) (star·) k = Σⱼ 2·Σ_m (level k m)·(star k j m)`,

a plain (orthonormal-frame, no metric raising) component contraction, with the
star arrays controlled by `starBound`.

## What this file proves (the orthonormal collapse — the non-blocked half)

The mismatch between the two forms is purely the metric raising: `inner0S` and
`ricReactionContract` carry the inverse metric `gInv`, while
`nablaRmReactionMulti` is a plain component sum.  In a **`g`-orthonormal** frame
(`gInv = δ`) the two coincide, by the same orthonormal collapse the norm
frame-invariance bridge (`compNormSqMulti_orthoBasis_eq_normSq0S`,
`Evolution/NablaRiemannHeatFrameInvariant.lean`) uses for the norms:

* `inner0S_orthoBasis_eq_compContract` — in a `g`-orthonormal basis,
  `inner0S g x s A B = Σ_m (comp A m)·(comp B m)`, the plain component
  contraction (the polarization of `compNormSqMulti_orthoBasis_eq_normSq0S`,
  via `inner0S_eq_coord` + `coordInner0S_identity_eq_sum`);
* `ricReactionContract_delta_eq_compContract` — with the Kronecker-delta inverse
  metric, `ricReactionContract δ ric cA cB = 2·Σ_I0 (Σ_b ric (I0 b) ⋆ ...)·cA·cB`
  collapses to a plain component contraction of `cA` against the **Ricci-raised
  star array** `ricStarArray ric cB` (each entry a genuine `Ric ∗ cB` slot
  contraction);
* `nablaKRm04Reaction_orthoBasis_eq_compContract` — assembling the two, the
  concrete reaction in a `g`-orthonormal basis equals the **single** plain
  component contraction `2·Σ_m (∇ᵏRm m)·(combinedStar m)` with the genuine
  combined star `combinedStar = ricStarArray + residualComps`, where
  `residualComps` are the genuine frame components of `(∂ₜ − Δ)∇ᵏRm`.

This is exactly the CLAUDE.md crux's step *"set the tower's star arrays to these
factors so that `towerReactionMulti = 2⟨(∂ₜ − Δ)∇ᵏRm, ∇ᵏRm⟩ + ric` matches the
concrete reaction"* — at the algebraic (orthonormal-collapse) level, with **no**
vacuous discharge and **no** renamed identity: the reaction really is the plain
contraction of `∇ᵏRm` against the genuine combined residual+Ricci star.

## What remains (the genuinely-blocked half — the commuted-curvature decomposition)

The collapse above expresses the reaction as a *single* contraction
`2⟨combinedStar, ∇ᵏRm⟩`.  To populate `IteratedRmTowerOn` one further needs the
combined star *split over `j ∈ {0,…,k}`* into genuine `∇ʲRm ∗ ∇^{k−j}Rm` factors
each obeying the Cauchy–Schwarz `starBound` `|star j| ≤ card²·√(wⱼ)·√(w_{k−j})`.

The Ricci half (`ricStarArray`) is already a genuine `Rm ∗ ∇ᵏRm` factor
(`j = 0`/`j = k`).  The residual half `(∂ₜ − Δ)∇ᵏRm` is, mathematically, the
commuted-curvature sum `Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm`; proving that as a Lean identity
with each factor a genuine `∇^{..}Rm` is the standing frontier recorded in
`Evolution/IteratedNablaRmTower.md` (it needs both the unbuilt component time
derivative `∂ₜ∇ᵏRm` from a solution — the Lemma-6.1 assembly — and the all-`k`
spatial commutator `[Δ,∇ᵏ]Rm = Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm`, of which only the `k = 1`
two-term version is assembled).  See the file footer for the precise statement.

`#print axioms` for every public theorem is `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## The orthonormal collapse of the metric inner product

In a `g`-orthonormal basis the metric fibre inner product `inner0S` is the plain
component contraction `Σ_m (comp A m)·(comp B m)`.  This is the polarization of
`compNormSqMulti_orthoBasis_eq_normSq0S`; it removes the inverse metric `gInv`
that distinguishes `inner0S` from the tower's `nablaRmReactionMulti`. -/

section OrthonormalCollapse

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- **The orthonormal collapse of `inner0S`.**  For a `g`-orthonormal basis, the
metric fibre inner product equals the plain component contraction:

`inner0S g x s A B = Σ_m (A (basis ∘ m))·(B (basis ∘ m))`.

The inverse metric is the Kronecker delta (`metricInverseInBasis_identity_of_orthonormal`),
so `inner0S_eq_coord` + `coordInner0S_identity_eq_sum` collapse both index sums to
the diagonal.  This is the polarization of the norm identity
`compNormSqMulti_orthoBasis_eq_normSq0S`. -/
theorem inner0S_orthoBasis_eq_compContract
    (g : SmoothMetric_gen I M) {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A B =
      ∑ m : Fin s → Idx,
        tensor0SComponent (I := I) A (fun i => basis i) m *
          tensor0SComponent (I := I) B (fun i => basis i) m := by
  classical
  rw [inner0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx))
    (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth) A B]
  rw [coordInner0S_identity_eq_sum (I := I) (x := x) s A B basis]

end OrthonormalCollapse

/-! ## The orthonormal collapse of the Ricci reaction contraction

The Ricci reaction term `ricReactionContract gInv ric cA cB`
(`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean`) carries the inverse
metric `gInv` on the un-Ricci'd slots and a doubled Ricci-raised contraction on
the distinguished slot.  With the Kronecker-delta inverse metric `gInv = δ`,
every off-slot `δ` collapses the `J0`-sum to `I0` except on the distinguished
slot, and the inner `(p,q)`-deltas reduce the Ricci-raised contraction to a plain
`ric (I0 b) (J0 b)`.  The result is a plain component contraction of `cA` against
the **Ricci star array** `ricStarArray ric cB` — each entry the genuine `Ric ∗ cB`
slot contraction `Σ_b Σ_e ric (I0 b) e · cB (update I0 b e)`.  Pure finite-sum
algebra on real component arrays; no geometry. -/

section RicReactionCollapse

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- **Slot delta-collapse.**  A sum over tuples `J0 : Fin s → Idx` weighted by the
off-slot Kronecker-delta product `∏_{a≠b} δ(I0 a, J0 a)` collapses to a single
sum over the free slot-`b` value: the weight is `1` exactly when `J0` agrees with
`I0` off `b` (`J0 = update I0 b (J0 b)`), and `0` otherwise.  Hence

`Σ_{J0} (∏_{a≠b} δ(I0 a, J0 a)) · G J0 = Σ_e G (update I0 b e)`.

Pure finite-sum algebra; the engine of the `ricReactionContract` orthonormal
collapse. -/
theorem sum_delta_erase_slot_eq {s : ℕ}
    (I0 : Fin s → Idx) (b : Fin s) (G : (Fin s → Idx) → Real) :
    (∑ J0 : Fin s → Idx,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 a) (J0 a)) * G J0) =
      ∑ e : Idx, G (Function.update I0 b e) := by
  classical
  -- The forward map `e ↦ update I0 b e` is injective (evaluate at `b`).
  have hinj : Function.Injective (fun e : Idx => Function.update I0 b e) := by
    intro e e' he
    have := congrFun he b
    simpa [Function.update_self] using this
  -- RHS = sum of the weighted summand over the image (on the image the off-slot
  -- delta-product is `1`).
  have himg :
      (∑ e : Idx, G (Function.update I0 b e)) =
        ∑ J0 ∈ (Finset.univ : Finset Idx).image
            (fun e : Idx => Function.update I0 b e),
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) * G J0 := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    refine Finset.sum_congr rfl fun e _ => ?_
    -- On `J0 = update I0 b e`, the off-slot delta-product is `1`.
    have hprod :
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 a) (Function.update I0 b e a)) = 1 := by
      refine Finset.prod_eq_one fun a ha => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
      rw [identityInvMetric_apply_self]
    rw [hprod, one_mul]
  rw [himg]
  -- Extend the image sum to the full `univ`: the summand vanishes off the image.
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro J0 _ hJ0
  -- `J0` not in the image ⟹ `J0 ≠ update I0 b (J0 b)` ⟹ some off-slot disagrees.
  have hne : J0 ≠ Function.update I0 b (J0 b) := by
    intro h
    exact hJ0 (Finset.mem_image.mpr ⟨J0 b, Finset.mem_univ _, h.symm⟩)
  -- Some `a ≠ b` has `J0 a ≠ I0 a`, killing the product.
  have hsome : ∃ a : Fin s, a ≠ b ∧ I0 a ≠ J0 a := by
    by_contra hnone
    -- `¬∃ a, a ≠ b ∧ I0 a ≠ J0 a` ⟹ `∀ a ≠ b, I0 a = J0 a`, contradicting `hne`.
    apply hne
    funext a
    by_cases hab : a = b
    · subst hab; rw [Function.update_self]
    · rw [Function.update_of_ne hab]
      by_contra hcon
      exact hnone ⟨a, hab, fun h => hcon h.symm⟩
  obtain ⟨a, hab, hdis⟩ := hsome
  refine mul_eq_zero_of_left ?_ _
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩) ?_
  rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hdis]

/-- The **Ricci star array** of a rank-`s` component array `cB` against a Ricci
component matrix `ric`: the genuine `Ric ∗ cB` slot contraction

`ricStarArray ric cB I0 = Σ_b Σ_e ric (I0 b) e · cB (update I0 b e)`,

summing over each slot `b` the replacement of the `b`-th index by a Ricci-traced
index.  This is the `Ric ∗ ∇ᵏRm` factor (the `j = 0` term of the eq-7.4 reaction)
in plain component form. -/
def ricStarArray {s : ℕ}
    (ric : Idx → Idx → Real) (cB : (Fin s → Idx) → Real) :
    (Fin s → Idx) → Real :=
  fun I0 => ∑ b : Fin s, ∑ e : Idx, ric (I0 b) e * cB (Function.update I0 b e)

/-- **Cauchy–Schwarz bound on the Ricci star array** (the eq-7.4 `j = 0` star
factor).  Each entry of `ricStarArray ric cB` is the genuine `Ric ∗ cB` slot
contraction, bounded by `s·card · Rbnd · √(compNormSqMulti cB)` whenever every
Ricci entry obeys `|ric p q| ≤ Rbnd`:

`|ricStarArray ric cB I0| ≤ s · card · Rbnd · √(compNormSqMulti cB)`.

With `Rbnd = √(|Ric|²)` and `|Ric| ≤ C·|Rm|` this is the genuine
`|Ric ∗ ∇ᵏRm| ≤ C·|Rm|·|∇ᵏRm|` `starBound` shape — demonstrating the Ricci half of
the combined star is a genuine, controlled `Rm ∗ ∇ᵏRm` factor (not a vacuous
dump).  Mirror of `abs_curvatureAction0SAt_orthoBasis_le`. -/
theorem abs_ricStarArray_le {s : ℕ}
    (ric : Idx → Idx → Real) (cB : (Fin s → Idx) → Real)
    (Rbnd : Real) (hRbnd_nonneg : (0 : Real) ≤ Rbnd)
    (hRbnd : ∀ p q : Idx, |ric p q| ≤ Rbnd)
    (I0 : Fin s → Idx) :
    |ricStarArray ric cB I0| ≤
      (s : Real) * (Fintype.card Idx : Real) * Rbnd *
        Real.sqrt (compNormSqMulti cB) := by
  classical
  have hNB : (0 : Real) ≤ Real.sqrt (compNormSqMulti cB) := Real.sqrt_nonneg _
  unfold ricStarArray
  -- Triangle inequality over the `(b, e)` index pairs.
  have hstep :
      |∑ b : Fin s, ∑ e : Idx, ric (I0 b) e * cB (Function.update I0 b e)| ≤
        ∑ b : Fin s, ∑ e : Idx, Rbnd * Real.sqrt (compNormSqMulti cB) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun e _ => ?_
    rw [abs_mul]
    exact mul_le_mul (hRbnd (I0 b) e)
      (abs_le_sqrt_compNormSqMulti cB (Function.update I0 b e))
      (abs_nonneg _) hRbnd_nonneg
  refine le_trans hstep ?_
  -- Evaluate the constant double sum: `s·card` terms.
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  rw [show ((Fintype.card Idx : Real) * (Rbnd * Real.sqrt (compNormSqMulti cB))) =
    (Fintype.card Idx : Real) * Rbnd * Real.sqrt (compNormSqMulti cB) from by ring]
  -- `Σ_b (card · Rbnd · √..) = s · card · Rbnd · √..`.
  rw [show ((s : Real) *
        ((Fintype.card Idx : Real) * Rbnd * Real.sqrt (compNormSqMulti cB))) =
      (s : Real) * (Fintype.card Idx : Real) * Rbnd *
        Real.sqrt (compNormSqMulti cB) from by ring]

/-- **The orthonormal collapse of `ricReactionContract`.**  With the
Kronecker-delta inverse metric, the Ricci reaction term is the plain component
contraction of `cA` against twice the Ricci star array:

`ricReactionContract δ ric cA cB = 2·Σ_I0 cA I0 · ricStarArray ric cB I0`.

Pure finite-sum algebra: the off-slot `δ`s collapse the `J0`-sum, and the inner
`(p,q)`-deltas reduce the Ricci-raised contraction to `ric (I0 b) (J0 b)`. -/
theorem ricReactionContract_delta_eq_compContract {s : ℕ}
    (ric : Idx → Idx → Real) (cA cB : (Fin s → Idx) → Real) :
    ricReactionContract (identityInvMetric (Idx := Idx)) ric cA cB =
      2 * ∑ I0 : Fin s → Idx, cA I0 * ricStarArray ric cB I0 := by
  classical
  unfold ricReactionContract ricStarArray
  congr 1
  -- Work termwise in `I0`.
  refine Finset.sum_congr rfl fun I0 _ => ?_
  -- The inner `(p,q)` Ricci-raised contraction against the deltas reduces to
  -- `ric (I0 b) (J0 b)`.
  have hric : ∀ (J0 : Fin s → Idx) (b : Fin s),
      (∑ p : Idx, ∑ q : Idx,
          identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q) =
        ric (I0 b) (J0 b) := by
    intro J0 b
    rw [Finset.sum_eq_single (I0 b)]
    · rw [Finset.sum_eq_single (J0 b)]
      · rw [identityInvMetric_apply_self, identityInvMetric_apply_self]; ring
      · intro q _ hq
        rw [show identityInvMetric (Idx := Idx) (J0 b) q = 0 from
          diagonalInvMetric_eq_zero_of_ne (fun h => hq h.symm)]
        ring
      · intro h; exact absurd (Finset.mem_univ (J0 b)) h
    · intro p _ hp
      -- `δ(I0 b, p) = 0` since `p ≠ I0 b`, killing every `q`-summand.
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [show identityInvMetric (Idx := Idx) (I0 b) p = 0 from
        diagonalInvMetric_eq_zero_of_ne (fun h => hp h.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ (I0 b)) h
  -- Step 1: rewrite the inner `(p,q)` contraction to `ric (I0 b) (J0 b)`.
  have hstep1 :
      (∑ J0 : Fin s → Idx,
          (∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                  identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
                (∑ p : Idx, ∑ q : Idx,
                  identityInvMetric (Idx := Idx) (I0 b) p *
                    identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) *
            cA I0 * cB J0) =
        ∑ b : Fin s, ∑ J0 : Fin s → Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
            (ric (I0 b) (J0 b) * cB J0) * cA I0 := by
    -- First distribute `cA·cB` into the slot sum termwise, and apply `hric`.
    have hdist :
        (∑ J0 : Fin s → Idx,
            (∑ b : Fin s,
                (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                    identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
                  (∑ p : Idx, ∑ q : Idx,
                    identityInvMetric (Idx := Idx) (I0 b) p *
                      identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) *
              cA I0 * cB J0) =
          ∑ J0 : Fin s → Idx, ∑ b : Fin s,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
              (ric (I0 b) (J0 b) * cB J0) * cA I0 := by
      refine Finset.sum_congr rfl fun J0 _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hric J0 b]
      ring
    rw [hdist, Finset.sum_comm]
  rw [hstep1]
  -- Step 2: apply the slot delta-collapse to each slot-`b` `J0`-sum.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- Pull `cA I0` out, collapse the `J0`-sum, then pull `cA I0` back in.
  have hstep2 :
      (∑ J0 : Fin s → Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
            (ric (I0 b) (J0 b) * cB J0) * cA I0) =
        cA I0 *
          ∑ J0 : Fin s → Idx,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
              (ric (I0 b) (J0 b) * cB J0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun J0 _ => ?_
    ring
  rw [hstep2, sum_delta_erase_slot_eq (Idx := Idx) I0 b
    (fun J0 : Fin s → Idx => ric (I0 b) (J0 b) * cB J0)]
  -- `(update I0 b e) b = e`, so each term is `ric (I0 b) e · cB (update I0 b e)`.
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Function.update_self]

end RicReactionCollapse

/-! ## The assembled reaction-form bridge

Combining the two orthonormal collapses, the concrete intrinsic reaction
`nablaKRm04ReactionIntrinsic` of `Evolution/IteratedRmTowerHeatEq.lean` equals, in
a `g`-orthonormal basis, the **single plain component contraction** of `∇ᵏRm`
against the genuine **combined star array**

`combinedStarArray = ricStarArray ric (comp ∇ᵏRm) + (comp (∂ₜ − Δ)∇ᵏRm)`,

namely

`nablaKRm04ReactionIntrinsic = 2·Σ_m (comp ∇ᵏRm m)·(combinedStarArray m)`.

The Ricci half `ricStarArray ric (comp ∇ᵏRm)` is the genuine `Ric ∗ ∇ᵏRm`
(`j = 0`) factor; the residual half is the genuine frame components of the heat
residual `(∂ₜ − Δ)∇ᵏRm`.  No vacuous discharge, no renamed identity — this is the
orthonormal-frame metric collapse of the derived reaction. -/

section ReactionBridge

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The **combined star array** of the eq-7.4 reaction in a `g`-orthonormal basis:
the Ricci-raised star `ricStarArray ric (comp ∇ᵏRm)` (the `Ric ∗ ∇ᵏRm` factor) plus
the plain frame components of the heat residual `(∂ₜ − Δ)∇ᵏRm`.

Here `residualComp m` is the `m`-component of `(∂ₜ − Δ)∇ᵏRm = Tdot − roughLap`
(`Tdot` the bundled `∂ₜ∇ᵏRm`, `roughLap = metricTrace0S2 (∇^{k+2}Rm)`).  The
concrete reaction is `2·Σ_m (∇ᵏRm m)·(combinedStarArray …)`. -/
def combinedStarArray {s : ℕ}
    (ric : Idx → Idx → Real)
    (rmComp residualComp : (Fin s → Idx) → Real) :
    (Fin s → Idx) → Real :=
  fun m => ricStarArray ric rmComp m + residualComp m

/-- **The assembled reaction-form bridge.**  In a `g`-orthonormal basis (`gInv =
δ`), the concrete intrinsic reaction `nablaKRm04ReactionIntrinsic` equals the
single plain component contraction of `∇ᵏRm` against the genuine combined star
array:

`nablaKRm04ReactionIntrinsic S k basis gInv ric Tdot t x =`
`  2·Σ_m (comp ∇ᵏRm m)·(combinedStarArray (ric t x) (comp ∇ᵏRm) (comp residual) m)`,

with `comp residual` the frame components of `(∂ₜ − Δ)∇ᵏRm = Tdot − roughLap`.

This is the algebraic half of the bridge to `IteratedRmTowerOn.heatEq`: it removes
the inverse metric `gInv` (via `inner0S_orthoBasis_eq_compContract` and
`ricReactionContract_delta_eq_compContract`), turning the metric-contracted
reaction into the plain component form `nablaRmReactionMulti` consumes.  The
residual half `comp (Tdot − Δ∇ᵏRm)` is `comp T` with `T ∈ StarSum2 k`
(`StarSum/TimeRecursion.resStarLFU`), bounded by `StarSum/TowerHeat.resStarBoundLF`; so
`combinedStarArray` is bounded as a whole rather than split per-`j` (see the updated file footer). -/
theorem nablaKRm04Reaction_orthoBasis_eq_compContract
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (basis : (x : M) → Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real → M → Idx → Idx → Real)
    (ric : Real → M → Idx → Idx → Real)
    (Tdot : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (4 + k) x)
    (t : Real) (x : M)
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis x i) (basis x j) =
        if i = j then (1 : Real) else 0)
    (hgInv : gInv t x = identityInvMetric (Idx := Idx)) :
    nablaKRm04ReactionIntrinsic (I := I) S k basis gInv ric Tdot t x =
      2 * ∑ m : Fin (4 + k) → Idx,
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis x i) m *
          combinedStarArray (ric t x)
            (fun I0 : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
                (fun i => basis x i) I0)
            (fun m : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I)
                (Tdot t x -
                  metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
                    (nablaKRm04Field (I := I) S t (k + 2) x))
                (fun i => basis x i) m)
            m := by
  classical
  -- Unfold the concrete reaction first, then abbreviate the level-`k` components
  -- and the residual (folding both sides, so the only remaining bare `gInv t x`
  -- is the one in `ricReactionContract`).
  rw [nablaKRm04ReactionIntrinsic]
  set rmC : (Fin (4 + k) → Idx) → Real :=
    fun I0 => tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
      (fun i => basis x i) I0 with hrmC
  set resid : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + k) x :=
    Tdot t x -
      metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
        (nablaKRm04Field (I := I) S t (k + 2) x) with hresid
  set residC : (Fin (4 + k) → Idx) → Real :=
    fun m => tensor0SComponent (I := I) resid (fun i => basis x i) m with hresidC
  -- The Ricci half collapses (orthonormal `gInv = δ`); `hgInv` now only hits the
  -- `ricReactionContract` argument (the residual's `gInv t x` is folded in `resid`).
  rw [hgInv]
  rw [ricReactionContract_delta_eq_compContract (Idx := Idx) (ric t x) rmC rmC]
  -- The residual half collapses via `inner0S_orthoBasis_eq_compContract`.
  rw [inner0S_orthoBasis_eq_compContract (I := I) (S.base.metric t) (basis x) horth
    resid (nablaKRm04Field (I := I) S t k x)]
  -- Assemble: `2·(Σ rmC·ricStar) + 2·(Σ residC·rmC) = 2·(Σ rmC·(ricStar + residC))`.
  -- It suffices to show the bracketed sums agree: `Σ rmC·ricStar + Σ residC·rmC
  --   = Σ rmC·(ricStar + residC)`.
  have hcombine :
      (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
          (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        ∑ m : Fin (4 + k) → Idx,
          rmC m * combinedStarArray (ric t x) rmC residC m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold combinedStarArray
    ring
  -- Conclude `2·X + 2·Y = 2·(X + Y)`.
  rw [show
      2 * (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
          2 * (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        2 * ((∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
              (∑ m : Fin (4 + k) → Idx, residC m * rmC m)) from by ring]
  rw [hcombine]

/-- Pointwise orthonormal collapse of the intrinsic tower reaction. This is the
local-basis form consumed by the pointwise heat producer. -/
theorem nablaKReactionAt_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv ric : Idx → Idx → Real)
    (Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x)
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hgInv : gInv = identityInvMetric (Idx := Idx)) :
    nablaKReactionAt (I := I) S k t x basis gInv ric Tdot =
      2 * ∑ m : Fin (4 + k) → Idx,
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis i) m *
          combinedStarArray ric
            (fun I0 : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
                (fun i => basis i) I0)
            (fun m : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I)
                (Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
                    (nablaKRm04Field (I := I) S t (k + 2) x))
                (fun i => basis i) m)
            m := by
  classical
  rw [nablaKReactionAt]
  set rmC : (Fin (4 + k) → Idx) → Real :=
    fun I0 => tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
      (fun i => basis i) I0 with hrmC
  set resid : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x :=
    Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
      (nablaKRm04Field (I := I) S t (k + 2) x) with hresid
  set residC : (Fin (4 + k) → Idx) → Real :=
    fun m => tensor0SComponent (I := I) resid (fun i => basis i) m with hresidC
  rw [hgInv]
  rw [ricReactionContract_delta_eq_compContract (Idx := Idx) ric rmC rmC]
  rw [inner0S_orthoBasis_eq_compContract (I := I) (S.base.metric t) basis horth
    resid (nablaKRm04Field (I := I) S t k x)]
  have hcombine :
      (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
          (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        ∑ m : Fin (4 + k) → Idx,
          rmC m * combinedStarArray ric rmC residC m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold combinedStarArray
    ring
  rw [show
      2 * (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
          2 * (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        2 * ((∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
              (∑ m : Fin (4 + k) → Idx, residC m * rmC m)) from by ring]
  rw [hcombine]

end ReactionBridge

/-! ## The remaining frontier (the commuted-curvature star decomposition)

**UPDATE (2026-06-13): frontier #1 below is resolved by the StarSum2 route — do not build the
per-`j` split.**  `StarSum/TimeRecursion.resStarLFU` proves `(∂ₜ − Δ)∇ᵏRm = T` with
`T ∈ StarSum2 k` (all `k`, no `0<j<k` iterated-commutator assembly needed), and
`StarSum2.bound` / `StarSum/TowerHeat.resStarBoundLF` give the residual component bound
`|T y (frame·y)| ≤ C·Σⱼ √wⱼ·√w_{k−j}` directly.  The downstream consumer is
`BernsteinShiHigher.TowerHeatBoundOn`, whose reaction is the **summed** `towerReactionSum =
Σⱼ c·√wⱼ·√w_{k−j}·√w_k` — NOT the per-`j` `IteratedRmTowerOn.starBound` arrays.  So `combinedStarArray`
is bounded as a whole (Cauchy–Schwarz on `2⟨∇ᵏRm, combinedStar⟩`, then Minkowski split
`combinedStar = ricStar + residual`, with `abs_ricStarArray_le` for the `j=0` half and
`resStarBoundLF` (per-component → L²) for the residual half); the explicit `j`-bucket split below is
bypassed.  The genuine remaining work is the analytic estimate-plumbing of those norm bounds plus
discharging `Tdot = ∂ₜ∇ᵏRm` (the time-side inputs).  The original analysis is kept below for history.

This file closes the **algebraic (orthonormal-collapse) half** of the bridge from
the concrete derived heat equation `nablaKRm04NormHeatEquationOn_intrinsic` to the
schematic tower interface `IteratedRmTowerOn`:

* `inner0S_orthoBasis_eq_compContract` / `ricReactionContract_delta_eq_compContract`
  remove the inverse metric `gInv`, turning the metric-contracted reaction into a
  **plain component contraction** — the form `nablaRmReactionMulti` consumes;
* `nablaKRm04Reaction_orthoBasis_eq_compContract` assembles the concrete reaction,
  in a `g`-orthonormal basis, as the single plain contraction `2·Σ_m (∇ᵏRm m)·
  (combinedStarArray m)`, with `combinedStarArray = ricStarArray + residualComps`;
* `abs_ricStarArray_le` discharges the `starBound` for the genuine `Ric ∗ ∇ᵏRm`
  (`j = 0`) factor `ricStarArray`.

What this does **not** close — discharging the full `IteratedRmTowerOn` from a
`SolutionOn` — and the precise grep-confirmed walls (cross-checked against the 14
follow-ups in `Evolution/IteratedNablaRmTower.md`):

1. **The commuted-curvature star decomposition of the residual.**
   `combinedStarArray`'s residual half `residualComp = comp ((∂ₜ − Δ)∇ᵏRm)` must
   be split over `j ∈ {0,…,k}` into genuine `∇ʲRm ∗ ∇^{k−j}Rm` factors each obeying
   `|star j| ≤ card²·√(wⱼ)·√(w_{k−j})`, so that the *single* contraction
   `2⟨combinedStar, ∇ᵏRm⟩` becomes the *sum* `towerReactionMulti = Σⱼ 2·Σ_m (∇ᵏRm
   m)·(star j m)`.  Mathematically `(∂ₜ − Δ)∇ᵏRm = Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm` (Uhlenbeck
   `∂ₜRm = ΔRm + Rm∗Rm`, the connection evolution, and the iterated spatial
   commutator `[Δ,∇ᵏ]Rm = Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm`).  The genuinely-available pieces —
   the *single*-derivative spatial commutator `nablaKRm04_ricciIdentityAt`
   (`[∇,∇]∇ᵏRm = curvatureAction(rm13)(∇ᵏRm) = Rm ∗ ∇ᵏRm`, all-`k`,
   `Evolution/RmRealizationBridgeAllK.lean`), its rank-uniform Cauchy–Schwarz bound
   `abs_curvatureAction0SAt_orthoBasis_le` (all-`s`,
   `Evolution/NablaRiemannT2Bound.lean`), and the covariant Leibniz `inner0S_nabla`
   (`Tensor/RSTensor/FiberMetric/Tensor0SInnerLeibniz.lean`) — give only the
   `j = 0`/`j = k` boundary terms; the **iterated** spatial commutator
   `[Δ,∇ᵏ]Rm = Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm` (the `0 < j < k` cross terms) is *not* assembled
   beyond `k = 1` (only the `k = 1` two-term version exists, via the
   `T₁`/`T₂` machinery of `NablaRiemannReactionBound.lean`).

2. **The component time derivative `∂ₜ∇ᵏRm` (the `Tdot` input).**  The residual's
   temporal half needs `∂ₜ∇ᵏRm` from a solution.  `iteratedRmComp_hasDerivWithinAt`
   (`Evolution/IteratedRmTowerHeatEq.lean`) supplies it *from* the level-0 `∂ₜRm`,
   the Christoffel `∂ₜΓ`, and the spatial/time swap `hswap` — but `∂ₜrm04` itself is
   the unbuilt Lemma-6.1 assembly (`Evolution/IteratedNablaRmTower.md`, eleventh
   follow-up: banked `∂ₜRm13`
   `christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation` + realization +
   metric lowering; unblocked but unbuilt).

3. **Frame reconciliation (WALL 2).**  The orthonormal collapse here requires a
   `g(t)`-orthonormal basis (`gInv = δ`); the clean-`∂ₜ` time derivative
   `iteratedRmComp_hasDerivWithinAt` is in the *time-independent* `coordinateFrameAt`
   (actual `gInv`).  Reconciling them is the standing WALL 2 (the same gap the
   `k = 0` baseline leaves open for `∂ₜ|Rm|²`).

The deliverable here is the precise reduction of the `heatEq`-reaction-shape
mismatch to a single reusable orthonormal-collapse identity, isolating the
commuted-curvature decomposition (wall 1) as the genuine remaining content.  Per
the project honesty constraints: no vacuous discharge (the combined star is the
*genuine* `ricStarArray + residual`, the Ricci half is bounded by
`abs_ricStarArray_le`), and no renamed/axiomatized identity.

`#print axioms` for every public theorem is `[propext, Classical.choice, Quot.sound]`. -/

end DifferentialGeometry.PDE.RicciFlow
