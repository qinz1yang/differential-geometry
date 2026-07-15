import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Smooth
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The general-rank covariant inner-product Leibniz rule

This file proves the **rank-uniform** directional metric compatibility of the
induced inner product on covariant `(0,s)` tensor fibres:

`∇_X ⟨T, S⟩_g = ⟨∇_X T, S⟩_g + ⟨T, ∇_X S⟩_g`.

Only the `(0,2)` case (`inner0S_two_nabla`,
`inner0S_two_metricCompatible_extDerivFun`,
`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`) existed before; this file
generalises it to arbitrary rank `s` by mirroring the same coordinate proof at
the rank-uniform contraction level.

## Method

The squared/bilinear inner product equals the `gInv`-raised coordinate
contraction `coordContract gInv (comps T) (comps S)` (`inner0S_eq_coord`,
`coordContract_eq_coordInner0S`).  Differentiating the local coordinate
expression along `X`:

* the `∏ gInv` factors are `∇`-parallel — the inverse metric components satisfy
  `∇gInv = 0` (`gInvCovZeroAt`), turning the metric-derivative term into
  Christoffel-correction contractions;
* the `comps T`, `comps S` factors give the directional derivatives `DcT`, `DcS`;
* `nabla0SFun_eval_coordFrame_moving_raw` rewrites the component covariant
  derivative as `DcT − (Christoffel corrections)`, and the corrections coming
  from the metric term cancel exactly against those, leaving
  `coordContract gInv (comps ∇T) (comps S) + coordContract gInv (comps T) (comps ∇S)`.

The whole Christoffel-correction algebra is carried out at the assumption-free
level of real component arrays over `Fin s → Idx`, generalising the `(0,2)`
position-hardcoded lemmas of `Tensor0SRiemannian/Product.lean`.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Pure rank-uniform contraction algebra of component arrays

We work at the assumption-free level of real component arrays
`(Fin s → Idx) → Real`.  `coordContract gInv cA cB`
(`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean`) is the `gInv`-raised
contraction `Σ_{I0,J0} (∏_a gInv (I0 a)(J0 a)) · cA I0 · cB J0`.  The two facts
proved here are the rank-uniform generalisations of the `(0,2)`
`inner0S_two_metricCompatible_coord_algebra` / `deriv4sum` of
`Tensor0SRiemannian/Product.lean`. -/

section CoordAlgebra

variable {Idx : Type*} [Fintype Idx]

/-- Reorder a triple finite sum `Σ_{I0} Σ_{J0} Σ_b` over two tuple sums and an
inner `Fin s` sum into `Σ_b Σ_{I0} Σ_{J0}`. -/
private theorem sum_reorder_b_out {s : Nat} {α : Type*} [AddCommMonoid α]
    (F : (Fin s -> Idx) -> (Fin s -> Idx) -> Fin s -> α) :
    (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx, ∑ b : Fin s, F I0 J0 b) =
      ∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx, F I0 J0 b := by
  classical
  -- Inner swap `Σ_{J0} Σ_b → Σ_b Σ_{J0}` under each `I0`.
  rw [show
      (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx, ∑ b : Fin s, F I0 J0 b) =
        ∑ I0 : Fin s -> Idx, ∑ b : Fin s, ∑ J0 : Fin s -> Idx, F I0 J0 b from by
    refine Finset.sum_congr rfl fun I0 _ => ?_
    rw [Finset.sum_comm (f := fun J0 b : _ => F I0 J0 b)]]
  -- Outer swap `Σ_{I0} Σ_b → Σ_b Σ_{I0}`.
  rw [Finset.sum_comm
    (f := fun I0 b : _ => ∑ J0 : Fin s -> Idx, F I0 J0 b)]

/-- The **Christoffel correction array** of a rank-`s` component array `cA`
against a directional Christoffel matrix `Γ`:

`christoffelCorrComp Γ cA I0 = Σ_b Σ_a Γ (I0 b) a · cA (update I0 b a)`,

the sum over each slot `b` of the correction replacing the `b`-th index by a
contracted index.  This is the rank-uniform Christoffel correction appearing in
the coordinate-frame component covariant derivative
`(∇_X T)(I0) = D_X cT (I0) − christoffelCorrComp Γ cT I0`. -/
def christoffelCorrComp {s : Nat}
    (Γ : Idx -> Idx -> Real)
    (cA : (Fin s -> Idx) -> Real) :
    (Fin s -> Idx) -> Real :=
  fun I0 =>
    ∑ b : Fin s, ∑ a : Idx, Γ (I0 b) a * cA (Function.update I0 b a)

/-- `coordContract` is additive-subtractive in its first component array. -/
theorem coordContract_sub_left {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (cA cA' cB : (Fin s -> Idx) -> Real) :
    coordContract gInv (fun I0 => cA I0 - cA' I0) cB =
      coordContract gInv cA cB - coordContract gInv cA' cB := by
  classical
  unfold coordContract
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I0 _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun J0 _ => ?_
  ring

/-- `coordContract` is additive-subtractive in its second component array. -/
theorem coordContract_sub_right {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (cA cB cB' : (Fin s -> Idx) -> Real) :
    coordContract gInv cA (fun J0 => cB J0 - cB' J0) =
      coordContract gInv cA cB - coordContract gInv cA cB' := by
  classical
  unfold coordContract
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I0 _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun J0 _ => ?_
  ring

/-- The slot-`b` index swap on `(Fin s → Idx) × Idx`: exchange the value of the
tuple at slot `b` with the scalar component.  It is an involution. -/
def slotSwap {s : Nat} [DecidableEq (Fin s)] (b : Fin s) :
    ((Fin s -> Idx) × Idx) ≃ ((Fin s -> Idx) × Idx) where
  toFun p := (Function.update p.1 b p.2, p.1 b)
  invFun p := (Function.update p.1 b p.2, p.1 b)
  left_inv p := by
    obtain ⟨I0, c⟩ := p
    simp only [Function.update_idem, Function.update_self, Function.update_eq_self]
  right_inv p := by
    obtain ⟨I0, c⟩ := p
    simp only [Function.update_idem, Function.update_self, Function.update_eq_self]

/-- **First-part per-slot identity.**  Tracing the `gInv`-side Christoffel term of
`DU` over slot `b` rebuilds the slot-`b` part of the `cA`-side correction
contraction.  The proof is the slot-`b` index swap. -/
theorem coordContractDt_firstPart_slot {s : Nat}
    (gInv Γ : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real) (b : Fin s) :
    (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
          (∑ c : Idx, Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0) =
      ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
        (∏ a : Fin s, gInv (I0 a) (J0 a)) *
          (∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0 := by
  classical
  -- Sum over `J0` outside; for each `J0`, reindex the joint `(I0, c)` sum by the
  -- slot-`b` swap.
  rw [Finset.sum_comm
    (f := fun I0 J0 : Fin s -> Idx =>
      (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
        (∑ c : Idx, Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0)]
  rw [Finset.sum_comm
    (f := fun I0 J0 : Fin s -> Idx =>
      (∏ a : Fin s, gInv (I0 a) (J0 a)) *
        (∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0)]
  refine Finset.sum_congr rfl fun J0 _ => ?_
  -- Pull the `Σ_c` out of each side into a joint `(I0, c)` sum.
  have hL :
      (∑ I0 : Fin s -> Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0) =
        ∑ p : (Fin s -> Idx) × Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (p.1 a) (J0 a)) *
            (Γ p.2 (p.1 b) * gInv p.2 (J0 b)) * cA p.1 * cB J0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun I0 _ => ?_
    have hexp :
        ∀ c : Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            (Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0 =
          ((∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            cA I0 * cB J0) * (Γ c (I0 b) * gInv c (J0 b)) := fun c => by ring
    rw [show
        (∑ c : Idx,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
              (Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0) =
          ((∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            cA I0 * cB J0) *
            (∑ c : Idx, Γ c (I0 b) * gInv c (J0 b)) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => hexp c]
    ring
  have hR :
      (∑ I0 : Fin s -> Idx,
          (∏ a : Fin s, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0) =
        ∑ p : (Fin s -> Idx) × Idx,
          (∏ a : Fin s, gInv (p.1 a) (J0 a)) *
            (Γ (p.1 b) p.2 * cA (Function.update p.1 b p.2)) * cB J0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun I0 _ => ?_
    have hexp :
        ∀ c : Idx,
          (∏ a : Fin s, gInv (I0 a) (J0 a)) *
            (Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0 =
          ((∏ a : Fin s, gInv (I0 a) (J0 a)) * cB J0) *
            (Γ (I0 b) c * cA (Function.update I0 b c)) := fun c => by ring
    rw [show
        (∑ c : Idx,
            (∏ a : Fin s, gInv (I0 a) (J0 a)) *
              (Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0) =
          ((∏ a : Fin s, gInv (I0 a) (J0 a)) * cB J0) *
            (∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => hexp c]
    ring
  rw [hL, hR]
  -- Reindex the LHS joint sum by the slot-`b` swap and match termwise.
  rw [← Equiv.sum_comp (slotSwap (Idx := Idx) (s := s) b)
    (fun p : (Fin s -> Idx) × Idx =>
      (∏ a : Fin s, gInv (p.1 a) (J0 a)) *
        (Γ (p.1 b) p.2 * cA (Function.update p.1 b p.2)) * cB J0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨I0, c⟩ := p
  simp only [slotSwap, Equiv.coe_fn_mk]
  -- After the swap the slot-`b` value becomes `c`; rebuild the full `gInv` product.
  rw [Function.update_self, Function.update_idem]
  rw [Function.update_eq_self]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin s)) _ (Finset.mem_univ b)]
  rw [Function.update_self]
  have hprod :
      (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
          gInv (Function.update I0 b c a) (J0 a)) =
        ∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a) := by
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
  rw [hprod]
  ring

/-- **Second-part per-slot identity.**  Tracing the `gInv`-side Christoffel term
of `DU` over slot `b` rebuilds the slot-`b` part of the `cB`-side correction
contraction.  The proof is the slot-`b` index swap on the `J0` side. -/
theorem coordContractDt_secondPart_slot {s : Nat}
    (gInv Γ : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real) (b : Fin s) :
    (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
          (∑ c : Idx, Γ c (J0 b) * gInv (I0 b) c) * cA I0 * cB J0) =
      ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
        (∏ a : Fin s, gInv (I0 a) (J0 a)) *
          cA I0 * (∑ c : Idx, Γ (J0 b) c * cB (Function.update J0 b c)) := by
  classical
  -- `I0` stays outermost; for each `I0`, reindex the joint `(J0, c)` sum.
  refine Finset.sum_congr rfl fun I0 _ => ?_
  have hL :
      (∑ J0 : Fin s -> Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ c (J0 b) * gInv (I0 b) c) * cA I0 * cB J0) =
        ∑ p : (Fin s -> Idx) × Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (p.1 a)) *
            (Γ p.2 (p.1 b) * gInv (I0 b) p.2) * cA I0 * cB p.1 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun J0 _ => ?_
    rw [show
        (∑ c : Idx,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
              (Γ c (J0 b) * gInv (I0 b) c) * cA I0 * cB J0) =
          ((∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            cA I0 * cB J0) *
            (∑ c : Idx, Γ c (J0 b) * gInv (I0 b) c) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring]
    ring
  have hR :
      (∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, gInv (I0 a) (J0 a)) *
            cA I0 * (∑ c : Idx, Γ (J0 b) c * cB (Function.update J0 b c))) =
        ∑ p : (Fin s -> Idx) × Idx,
          (∏ a : Fin s, gInv (I0 a) (p.1 a)) *
            cA I0 * (Γ (p.1 b) p.2 * cB (Function.update p.1 b p.2)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun J0 _ => ?_
    rw [show
        (∑ c : Idx,
            (∏ a : Fin s, gInv (I0 a) (J0 a)) *
              cA I0 * (Γ (J0 b) c * cB (Function.update J0 b c))) =
          ((∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0) *
            (∑ c : Idx, Γ (J0 b) c * cB (Function.update J0 b c)) from by
        rw [Finset.mul_sum]]
  rw [hL, hR]
  rw [← Equiv.sum_comp (slotSwap (Idx := Idx) (s := s) b)
    (fun p : (Fin s -> Idx) × Idx =>
      (∏ a : Fin s, gInv (I0 a) (p.1 a)) *
        cA I0 * (Γ (p.1 b) p.2 * cB (Function.update p.1 b p.2)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨J0, c⟩ := p
  simp only [slotSwap, Equiv.coe_fn_mk]
  rw [Function.update_self, Function.update_idem]
  rw [Function.update_eq_self]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin s)) _ (Finset.mem_univ b)]
  rw [Function.update_self]
  have hprod :
      (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
          gInv (I0 a) (Function.update J0 b c a)) =
        ∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a) := by
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
  rw [hprod]
  ring

/-- **Key cancellation.**  The metric-derivative term `coordContractDt`, with the
metric-compatible value `DU(p,q) = −Σ_c (Γ(c,p) gInv(c,q) + Γ(c,q) gInv(p,c))`,
equals the negated sum of the two Christoffel-correction contractions:

`coordContractDt gInv DU cA cB
  = − coordContract gInv (christoffelCorrComp Γ cA) cB
    − coordContract gInv cA (christoffelCorrComp Γ cB)`.

This is the rank-uniform heart, generalising
`inner0S_two_metricCompatible_coord_DU_first/second`.  Pure finite-sum algebra. -/
theorem coordContractDt_eq_neg_christoffelCorr {s : Nat}
    (gInv Γ : Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ c : Idx, Γ c p * gInv c q) + (∑ c : Idx, Γ c q * gInv p c))) :
    coordContractDt gInv DU cA cB =
      - coordContract gInv (christoffelCorrComp Γ cA) cB
        - coordContract gInv cA (christoffelCorrComp Γ cB) := by
  classical
  -- Step 1: expand `coordContractDt`, substitute `hDU`, and split into the two
  -- slot-summed Christoffel groups.
  have hStep1 :
      coordContractDt gInv DU cA cB =
        - (∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
              (∑ c : Idx, Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0) -
          (∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
              (∑ c : Idx, Γ c (J0 b) * gInv (I0 b) c) * cA I0 * cB J0) := by
    unfold coordContractDt
    -- Rewrite each `(I0,J0)` summand by `hDU` as a `Σ_b` of the negated pair.
    rw [show
        (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∑ b : Fin s,
                (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                  DU (I0 b) (J0 b)) * cA I0 * cB J0) =
          ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx, ∑ b : Fin s,
            (- ((∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                  (∑ c : Idx, Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0) -
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                  (∑ c : Idx, Γ c (J0 b) * gInv (I0 b) c) * cA I0 * cB J0) from by
      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hDU (I0 b) (J0 b)]
      ring]
    -- Reorder `Σ_{I0} Σ_{J0} Σ_b → Σ_b Σ_{I0} Σ_{J0}` and split the difference.
    rw [sum_reorder_b_out (fun I0 J0 b =>
      (- ((∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0) -
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ c (J0 b) * gInv (I0 b) c) * cA I0 * cB J0))]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun I0 _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  rw [hStep1]
  -- Step 2: apply the per-slot identities inside the `Σ_b`.
  rw [show
      (∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ c (I0 b) * gInv c (J0 b)) * cA I0 * cB J0) =
        ∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0 from by
    refine Finset.sum_congr rfl fun b _ => ?_
    exact coordContractDt_firstPart_slot gInv Γ cA cB b]
  rw [show
      (∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ c (J0 b) * gInv (I0 b) c) * cA I0 * cB J0) =
        ∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, gInv (I0 a) (J0 a)) *
            cA I0 * (∑ c : Idx, Γ (J0 b) c * cB (Function.update J0 b c)) from by
    refine Finset.sum_congr rfl fun b _ => ?_
    exact coordContractDt_secondPart_slot gInv Γ cA cB b]
  -- Step 3: pull the `Σ_b` back inside as `christoffelCorrComp` and recognise the
  -- two coordinate contractions.
  have hContrA :
      coordContract gInv (christoffelCorrComp Γ cA) cB =
        ∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, gInv (I0 a) (J0 a)) *
            (∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0 := by
    unfold coordContract christoffelCorrComp
    -- Distribute the `Σ_b` factor and reorder it outermost.
    rw [show
        (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, gInv (I0 a) (J0 a)) *
              (∑ b : Fin s, ∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) *
                cB J0) =
          ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx, ∑ b : Fin s,
            (∏ a : Fin s, gInv (I0 a) (J0 a)) *
              (∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0 from by
      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]]
    rw [sum_reorder_b_out (fun I0 J0 b =>
      (∏ a : Fin s, gInv (I0 a) (J0 a)) *
        (∑ c : Idx, Γ (I0 b) c * cA (Function.update I0 b c)) * cB J0)]
  have hContrB :
      coordContract gInv cA (christoffelCorrComp Γ cB) =
        ∑ b : Fin s, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, gInv (I0 a) (J0 a)) *
            cA I0 * (∑ c : Idx, Γ (J0 b) c * cB (Function.update J0 b c)) := by
    unfold coordContract christoffelCorrComp
    rw [show
        (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 *
              (∑ b : Fin s, ∑ c : Idx, Γ (J0 b) c * cB (Function.update J0 b c))) =
          ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx, ∑ b : Fin s,
            (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 *
              (∑ c : Idx, Γ (J0 b) c * cB (Function.update J0 b c)) from by
      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
      rw [Finset.mul_sum]]
    rw [sum_reorder_b_out (fun I0 J0 b =>
      (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 *
        (∑ c : Idx, Γ (J0 b) c * cB (Function.update J0 b c)))]
  rw [hContrA, hContrB]

end CoordAlgebra

/-! ## The directional product rule of the coordinate contraction

The directional derivative `extDerivFun` along a tangent vector obeys the same
product rule as the `(0,2)` `deriv4sum`, but rank-uniform.  We first record an
`extDerivFun` Leibniz for a finite product, then assemble the contraction
derivative. -/

section DirectionalDeriv

variable {Idx : Type} [Fintype Idx]

open DifferentialGeometry.Tensor.Coordinates (extDerivFun_mul_real
  extDerivFun_finset_sum_real)

/-- **`extDerivFun` finite-product Leibniz.**  The directional derivative of a
finite product of `MDifferentiableAt` scalar fields is the sum, over each factor,
of the derivative of that factor times the product of the others. -/
theorem extDerivFun_finset_prod_real
    {ι : Type} [DecidableEq ι] (t : Finset ι) (f : ι -> M -> Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    extDerivFun (I := I) (fun y : M => ∏ i ∈ t, f i y) x v =
      ∑ i ∈ t, (∏ j ∈ t.erase i, f j x) * extDerivFun (I := I) (f i) x v := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [extDerivFun]
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x :=
        hf i (Finset.mem_insert_self i t)
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hprodt : MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => ∏ j ∈ t, f j y) x := by
        have h := MDifferentiableAt.prod (I := I) (𝕜 := Real)
          (F' := Real) (f := f) (t := t) (z := x) hft
        simpa [Finset.prod_fn] using h
      have hsplit :
          (fun y : M => ∏ j ∈ insert i t, f j y) =
            fun y : M => f i y * ∏ j ∈ t, f j y := by
        funext y; rw [Finset.prod_insert hit]
      rw [hsplit, extDerivFun_mul_real (I := I) v hfi hprodt, ih hft]
      rw [Finset.sum_insert hit]
      rw [Finset.erase_insert hit]
      -- The `i`-term: `(∏_{j∈t}) · D f i`.  The other terms get the extra factor `f i x`.
      have hother :
          (∑ j ∈ t, (∏ k ∈ (insert i t).erase j, f k x) *
              extDerivFun (I := I) (f j) x v) =
            f i x *
              ∑ j ∈ t, (∏ k ∈ t.erase j, f k x) * extDerivFun (I := I) (f j) x v := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hji : j ≠ i := fun h => hit (h ▸ hj)
        rw [Finset.erase_insert_of_ne hji.symm, Finset.prod_insert]
        · ring
        · exact fun h => hit (Finset.mem_of_mem_erase h)
      rw [hother]
      ring

/-- Directional product rule for a single coordinate-contraction summand
`(∏_a U(I0a,J0a)) · cA(I0) · cB(J0)`. -/
theorem extDerivFun_coordContract_summand {s : Nat}
    (U : M -> Idx -> Idx -> Real)
    (cA cB : M -> (Fin s -> Idx) -> Real)
    {x : M} (v : TangentSpace I x) (I0 J0 : Fin s -> Idx)
    (hU : ∀ i j : Idx, MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x)
    (hcA : MDifferentiableAt I 𝓘(Real, Real) (fun y : M => cA y I0) x)
    (hcB : MDifferentiableAt I 𝓘(Real, Real) (fun y : M => cB y J0) x) :
    extDerivFun (I := I)
        (fun y : M => (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) x v =
      (∑ b : Fin s,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, U x (I0 a) (J0 a)) *
            extDerivFun (I := I) (fun y => U y (I0 b) (J0 b)) x v) *
          cA x I0 * cB x J0 +
        ((∏ a : Fin s, U x (I0 a) (J0 a)) *
            extDerivFun (I := I) (fun y => cA y I0) x v * cB x J0 +
          (∏ a : Fin s, U x (I0 a) (J0 a)) * cA x I0 *
            extDerivFun (I := I) (fun y => cB y J0) x v) := by
  classical
  have hprodU : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => ∏ a : Fin s, U y (I0 a) (J0 a)) x := by
    have := MDifferentiableAt.prod (I := I) (𝕜 := Real)
      (f := fun a => fun y : M => U y (I0 a) (J0 a))
      (t := (Finset.univ : Finset (Fin s))) (z := x)
      (fun a _ => hU (I0 a) (J0 a))
    simpa [Finset.prod_fn] using this
  have hAB : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0) x := hprodU.mul hcA
  -- Outer product `((∏ U) · cA) · cB`.
  rw [extDerivFun_mul_real (I := I) v hAB hcB]
  -- Inner product `(∏ U) · cA`.
  rw [extDerivFun_mul_real (I := I) v hprodU hcA]
  -- Finite product `∏_a U`.
  rw [extDerivFun_finset_prod_real (Finset.univ : Finset (Fin s))
    (fun a y => U y (I0 a) (J0 a)) v (fun a _ => hU (I0 a) (J0 a))]
  ring

/-- **The directional product rule of `coordContract`.**  For component fields
`U y i j`, `cA y I0`, `cB y J0` differentiable at `x`, the directional derivative
of the coordinate contraction splits as the metric-derivative term plus the two
component-derivative contractions:

`∇_v coordContract (U ·) (cA ·) (cB ·)
  = coordContractDt (U x) DU (cA x) (cB x)
    + coordContract (U x) DcA (cB x) + coordContract (U x) (cA x) DcB`,

where `DU/DcA/DcB` are the directional derivatives of the components.  The
rank-uniform spatial analogue of `deriv4sum` / `hasDerivWithinAt_coordContract`. -/
theorem extDerivFun_coordContract {s : Nat}
    (U : M -> Idx -> Idx -> Real)
    (cA cB : M -> (Fin s -> Idx) -> Real)
    {x : M} (v : TangentSpace I x)
    (hU : ∀ i j : Idx, MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x)
    (hcA : ∀ I0 : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => cA y I0) x)
    (hcB : ∀ J0 : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => cB y J0) x) :
    extDerivFun (I := I)
        (fun y : M => coordContract (U y) (cA y) (cB y)) x v =
      coordContractDt (U x) (fun i j => extDerivFun (I := I) (fun y => U y i j) x v)
          (cA x) (cB x) +
        coordContract (U x)
          (fun I0 => extDerivFun (I := I) (fun y => cA y I0) x v) (cB x) +
        coordContract (U x) (cA x)
          (fun J0 => extDerivFun (I := I) (fun y => cB y J0) x v) := by
  classical
  have hprodU : ∀ (I0 J0 : Fin s -> Idx),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ∏ a : Fin s, U y (I0 a) (J0 a)) x := by
    intro I0 J0
    have := MDifferentiableAt.prod (I := I) (𝕜 := Real)
      (f := fun a => fun y : M => U y (I0 a) (J0 a))
      (t := (Finset.univ : Finset (Fin s))) (z := x)
      (fun a _ => hU (I0 a) (J0 a))
    simpa [Finset.prod_fn] using this
  have hGmdiff : ∀ I0 J0 : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) x :=
    fun I0 J0 => ((hprodU I0 J0).mul (hcA I0)).mul (hcB J0)
  have hG1mdiff : ∀ I0 : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) x := by
    intro I0
    have hsum := DifferentialGeometry.Tensor.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset (Fin s -> Idx)))
      (fun J0 => fun y : M => (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0)
      (fun J0 _ => hGmdiff I0 J0)
    have heqfun :
        (Finset.univ : Finset (Fin s -> Idx)).sum
            (fun J0 => fun y : M =>
              (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) =
          fun y : M => ∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0 := by
      funext y; rw [Finset.sum_apply]
    rwa [heqfun] at hsum
  -- Differentiate the outer `I0`-sum, then the inner `J0`-sum, then each summand.
  rw [show
      (fun y : M => coordContract (U y) (cA y) (cB y)) =
        fun y : M => ∑ I0 : Fin s -> Idx,
          (∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) from by
    funext y; rfl]
  rw [DifferentialGeometry.extDerivFun_finset_sum_at'
    (I := I) (Finset.univ : Finset (Fin s -> Idx))
    (fun I0 y => ∑ J0 : Fin s -> Idx,
      (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) v
    (fun I0 _ => hG1mdiff I0)]
  -- Now the goal is `Σ_{I0} extDerivFun (Σ_{J0} ...) = RHS`.  Expand each.
  rw [show
      (∑ I0 : Fin s -> Idx,
          extDerivFun (I := I)
            (fun y : M => ∑ J0 : Fin s -> Idx,
              (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) x v) =
        ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          ((∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, U x (I0 a) (J0 a)) *
                extDerivFun (I := I) (fun y => U y (I0 b) (J0 b)) x v) *
              cA x I0 * cB x J0 +
            ((∏ a : Fin s, U x (I0 a) (J0 a)) *
                extDerivFun (I := I) (fun y => cA y I0) x v * cB x J0 +
              (∏ a : Fin s, U x (I0 a) (J0 a)) * cA x I0 *
                extDerivFun (I := I) (fun y => cB y J0) x v)) from by
    refine Finset.sum_congr rfl fun I0 _ => ?_
    rw [DifferentialGeometry.extDerivFun_finset_sum_at'
      (I := I) (Finset.univ : Finset (Fin s -> Idx))
      (fun J0 y => (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) v
      (fun J0 _ => hGmdiff I0 J0)]
    refine Finset.sum_congr rfl fun J0 _ => ?_
    exact extDerivFun_coordContract_summand U cA cB v I0 J0 hU (hcA I0) (hcB J0)]
  -- Collect the three groups and recognise the three contractions.
  unfold coordContractDt coordContract
  simp only [Finset.sum_add_distrib]
  rw [← add_assoc]

end DirectionalDeriv

/-! ## The general-rank directional inner-product Leibniz -/

section Leibniz

open DifferentialGeometry.Tensor.Coordinates

/-- **The general-rank directional metric compatibility of the induced inner
product.**  For a metric-compatible connection `cov`, smooth `(0,s)` tensor fields
`A`, `B`, a smooth vector field `X`, and a point `x`,

`∇_X ⟨A, B⟩_g = ⟨∇_X A, B⟩_g + ⟨A, ∇_X B⟩_g`,

with `∇_X` the raw `nabla0SFun`.  This is the rank-uniform generalisation of
`inner0S_two_nabla`. -/
theorem inner0S_nabla {s : Nat}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y s (A y) (B y)) x (X x) =
      inner0S (I := I) g x s
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X A x) (B x) +
        inner0S (I := I) g x s (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X B x) := by
  classical
  set Idx : Type := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
    with hIdx
  set frame : Idx -> (y : M) -> TangentSpace I y :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x with hframe
  set U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x y) with hU
  set cA : M -> (Fin s -> Idx) -> Real :=
    fun y I0 => A y (fun a => frame (I0 a) y) with hcAdef
  set cB : M -> (Fin s -> Idx) -> Real :=
    fun y J0 => B y (fun a => frame (J0 a) y) with hcBdef
  have hx : x ∈ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  -- Differentiability of the component fields.
  have hUmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x := by
    intro i j
    simpa [U, Idx] using
      DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt (I := I) g x i j
  have hcAmdiff : ∀ I0 : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => cA y I0) x := by
    intro I0
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) A x I0
    exact h.mdifferentiableAt (by simp)
  have hcBmdiff : ∀ J0 : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => cB y J0) x := by
    intro J0
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) B x J0
    exact h.mdifferentiableAt (by simp)
  -- Directional Christoffel matrix.
  set Γ : Idx -> Idx -> Real :=
    fun p q =>
      DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
        x (X x) p q with hΓ
  -- The inverse-metric components are `∇`-parallel: the metric-derivative value.
  have hDU : ∀ p q : Idx,
      extDerivFun (I := I) (fun y => U y p q) x (X x) =
        - ((∑ c : Idx, Γ c p * U x c q) + (∑ c : Idx, Γ c q * U x p c)) := by
    intro p q
    have hzero := DifferentialGeometry.Tensor.Coordinates.gInvCovZeroAt
      (I := I) g cov X hmc x p q
    unfold DifferentialGeometry.Tensor.Coordinates.inverseMetricCovDerivForMetricCompAlongInFrame
      at hzero
    have hzero' :
        extDerivFun (I := I) (fun y => U y p q) x (X x) +
          (∑ c : Idx, Γ c p * U x c q) +
          (∑ c : Idx, Γ c q * U x p c) = 0 := by
      simpa [U, Γ, hframe, Idx] using hzero
    linarith
  -- Local agreement of the inner product with the coordinate contraction.
  have hlocal :
      (fun y : M => inner0S (I := I) g y s (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => coordContract (U y) (cA y) (cB y) := by
    filter_upwards
      [(DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    rw [inner0S_eq_coord (I := I) g y s
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hy)
      (U y) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)]
    rw [← coordContract_eq_coordInner0S (I := I) (U y) (A y) (B y)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hy)]
    refine congrArg₂ (fun f h => coordContract (U y) f h) ?_ ?_
    · funext I0
      simp only [tensor0SComponent, cA, frame]
      refine congrArg (fun w => A y w) ?_
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]
    · funext J0
      simp only [tensor0SComponent, cB, frame]
      refine congrArg (fun w => B y w) ?_
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]
  -- Differentiate the inner product through the contraction.
  rw [DifferentialGeometry.Tensor.Coordinates.deriv_congr_nhds (I := I) (x := x) (X x) hlocal]
  rw [extDerivFun_coordContract U cA cB (X x) hUmdiff hcAmdiff hcBmdiff]
  -- The metric-derivative term collapses by `∇gInv = 0`.
  rw [show
      coordContractDt (U x) (fun i j => extDerivFun (I := I) (fun y => U y i j) x (X x))
          (cA x) (cB x) =
        coordContractDt (U x) (fun i j =>
            - ((∑ c : Idx, Γ c i * U x c j) + (∑ c : Idx, Γ c j * U x i c)))
          (cA x) (cB x) from by
    refine congrArg (fun D => coordContractDt (U x) D (cA x) (cB x)) ?_
    funext i j; exact hDU i j]
  rw [coordContractDt_eq_neg_christoffelCorr (U x) Γ
    (fun i j => - ((∑ c : Idx, Γ c i * U x c j) + (∑ c : Idx, Γ c j * U x i c)))
    (cA x) (cB x) (fun p q => rfl)]
  -- Identify the two component covariant derivatives.
  have hcompA : ∀ I0 : Fin s -> Idx,
      extDerivFun (I := I) (fun y => cA y I0) x (X x) -
          christoffelCorrComp Γ (cA x) I0 =
        tensor0SComponent (I := I)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X A x)
          (fun i => frame i x) I0 := by
    intro I0
    have hnab := DifferentialGeometry.Tensor.Coordinates.nabla0S_coordFrame_slots_of_smooth
      (I := I) (𝕜 := Real) cov X A x I0
    have hDcA :
        extDerivFun (I := I) (fun y => cA y I0) x (X x) =
          DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
            (fun y => X y) x (fun y => A y) I0 := by
      rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv]
      rfl
    have hRHS :
        tensor0SComponent (I := I)
            (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X A x)
            (fun i => frame i x) I0 =
          DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt (I := I)
            (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X A x) I0 := by
      rw [DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_apply,
        tensor0SComponent]
      refine congrArg
        (fun w => (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X A x) w) ?_
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
    rw [hRHS, hnab, hDcA]
    congr 1
    simp only [christoffelCorrComp, hΓ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_apply]
    refine congrArg (fun w => (A x) w) ?_
    funext c
    rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
  have hcompB : ∀ J0 : Fin s -> Idx,
      extDerivFun (I := I) (fun y => cB y J0) x (X x) -
          christoffelCorrComp Γ (cB x) J0 =
        tensor0SComponent (I := I)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X B x)
          (fun i => frame i x) J0 := by
    intro J0
    have hnab := DifferentialGeometry.Tensor.Coordinates.nabla0S_coordFrame_slots_of_smooth
      (I := I) (𝕜 := Real) cov X B x J0
    have hDcB :
        extDerivFun (I := I) (fun y => cB y J0) x (X x) =
          DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
            (fun y => X y) x (fun y => B y) J0 := by
      rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv]
      rfl
    have hRHS :
        tensor0SComponent (I := I)
            (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X B x)
            (fun i => frame i x) J0 =
          DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt (I := I)
            (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X B x) J0 := by
      rw [DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_apply,
        tensor0SComponent]
      refine congrArg
        (fun w => (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X B x) w) ?_
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
    rw [hRHS, hnab, hDcB]
    congr 1
    simp only [christoffelCorrComp, hΓ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt_apply]
    refine congrArg (fun w => (B x) w) ?_
    funext c
    rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
  -- Recognise the two intrinsic inner products at `x`.
  have hbasis : ∀ (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
      (S : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x),
      coordContract (U x)
          (fun I0 => tensor0SComponent (I := I) T (fun i => frame i x) I0)
          (fun J0 => tensor0SComponent (I := I) S (fun i => frame i x) J0) =
        inner0S (I := I) g x s T S := by
    intro T S
    rw [show (fun i => frame i x) =
        ⇑(DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hx) from by
      funext i
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]]
    rw [coordContract_eq_coordInner0S (I := I) (U x) T S
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hx)]
    rw [← inner0S_eq_coord (I := I) g x s
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hx) T S]
  -- The two grouped contractions are the intrinsic inner products.
  have hgroupA :
      coordContract (U x)
            (fun I0 => extDerivFun (I := I) (fun y => cA y I0) x (X x)) (cB x) -
          coordContract (U x) (christoffelCorrComp Γ (cA x)) (cB x) =
        inner0S (I := I) g x s
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X A x) (B x) := by
    rw [← coordContract_sub_left]
    rw [show
        (fun I0 => extDerivFun (I := I) (fun y => cA y I0) x (X x) -
            christoffelCorrComp Γ (cA x) I0) =
          fun I0 => tensor0SComponent (I := I)
            (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X A x)
            (fun i => frame i x) I0 from funext hcompA]
    rw [show (cB x) =
        fun J0 => tensor0SComponent (I := I) (B x) (fun i => frame i x) J0 from rfl]
    exact hbasis (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X A x) (B x)
  have hgroupB :
      coordContract (U x) (cA x)
            (fun J0 => extDerivFun (I := I) (fun y => cB y J0) x (X x)) -
          coordContract (U x) (cA x) (christoffelCorrComp Γ (cB x)) =
        inner0S (I := I) g x s (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X B x) := by
    rw [← coordContract_sub_right]
    rw [show
        (fun J0 => extDerivFun (I := I) (fun y => cB y J0) x (X x) -
            christoffelCorrComp Γ (cB x) J0) =
          fun J0 => tensor0SComponent (I := I)
            (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X B x)
            (fun i => frame i x) J0 from funext hcompB]
    rw [show (cA x) =
        fun I0 => tensor0SComponent (I := I) (A x) (fun i => frame i x) I0 from rfl]
    exact hbasis (A x) (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X B x)
  linarith [hgroupA, hgroupB]

/-- Fibre inner-product symmetry on covariant tensors. -/
theorem inner0S_symm {s : Nat}
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A B = inner0S (I := I) g x s B A := by
  unfold inner0S MetricFiberData.inner
  exact (tensor0SMetricData (I := I) g x s).symm A B

/-- **The first-order directional derivative of a covariant-tensor norm square.**
For a metric-compatible connection, `∇_X ‖T‖² = 2 ⟨∇_X T, T⟩`.  This is the
rank-uniform generalisation of the `(0,2)` `du_norm02`, derived directly from the
general inner-product Leibniz `inner0S_nabla`. -/
theorem normSq0S_nabla {s : Nat}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M => normSq0S (I := I) g y s (T y)) x (X x) =
      2 * inner0S (I := I) g x s
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X T x) (T x) := by
  have hL := inner0S_nabla (I := I) cov g hmc T T X x
  have hnorm :
      (fun y : M => normSq0S (I := I) g y s (T y)) =
        fun y : M => inner0S (I := I) g y s (T y) (T y) := by
    funext y; rw [normSq0S_eq_inner]
  rw [hnorm, hL]
  rw [inner0S_symm (I := I) g x (T x)
    (nabla0SFun (E := E) (H := H) (I := I) (M := M) s cov X T x)]
  ring

end Leibniz

end

end Tensor0SBundle
