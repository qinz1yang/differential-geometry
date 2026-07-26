import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder1TameEnvelope

/-!
# Summed data-weighted jet-L2 bound for the connection-difference field (DIRECT route)

This file proves the **connection-difference** analogue of the arm summed bounds in
`ArmBaseCoeffJetL2Summed.lean`: a single `R`-independent-top data-weighted jet-L2 bound for the
`(3,4)` field `connDiffContrInsertionField g₀ g₁`.

The construction follows the DIRECT-summed recipe of `RemainderCoeffTopSeparated.md` (skipping the
field-level `∃ Hd` witness): the committed engine
`rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
(`CurvatureCoefficientDifferenceJetTower.lean`) splits the section jet into a top head and a
data-weighted remainder; the field↔section identity
`connDiffContrInsertionField_eq_reindex_slotExtend_two` transfers this to the field with a
`finrank²` factor; the remainder is reshaped to a `boundedFactorGridWindow` and integrated by
`boundedFactorGridWindow_integral_ballUniform_tameWindow`.  The **top-split coefficient `Ktop`** is
built only from `(g₀, hδ₀)`-level committed constants (engine head `10·S 0`, times `2·finrank²`),
hence `R`-independent; the lumped low constant `Kc` follows the accepted house `R`-pattern (it is
threaded through the ball-uniform tame-window converter, exactly as arm0's accepted generic).

The end shape (both windows land at order `a+2`):
```
∑_{i ≤ a} ‖∇^i (connDiffContrInsertionField g₀ (realizedFam …))‖²
  ≤ Ktop · (∑_{j < a+2} (‖∇^j T‖² + ‖∇^j T'‖²))
  +  Kc  · (1 + ∑_{j < a+2} (‖∇^j T‖² + ‖∇^j T'‖²))
```
This is constituent 3-of-5 of the data-weighted threeArm precursor (R1τ item (2)); see
`UNIF_EXISTENCE_PLAN.md` "Planner acceptance №4" and `RemainderCoeffTopSeparated.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet)

/-! ### Pure real / `Finset` / combinatorial helpers (no geometry). -/

/-- Copied verbatim (pure combinatorial, only `Combinatorics.*` deps) from the private
`tsResSum_le_boundedWindow` of `CurvatureCoefficientDifferenceJetTower.lean`.  Reshapes the engine
remainder sum into a `boundedFactorGridWindow`. -/
private lemma tsResSum_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
  calc ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ ∑ _k ∈ Finset.range j, Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
          (show k + 1 ≤ j from by omega)]
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGrid_le b hb
          (k + 1) (j - k) (by omega) (by omega)) ?_
        rw [show (k + 1) + (j - k) = j + 1 from by omega]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
    _ = (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Shifted-range domination for a nonnegative sequence (copied from `ArmBaseCoeffJetL2Summed`). -/
private lemma sum_shift_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (m c : ℕ) :
    ∑ i ∈ Finset.range m, g (i + c) ≤ ∑ j ∈ Finset.range (m + c), g j := by
  classical
  have hsub :
      (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩ ⊆
        Finset.range (m + c) := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    simp only [Function.Embedding.coeFn_mk]
    omega
  calc ∑ i ∈ Finset.range m, g (i + c)
      = ∑ j ∈ (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩, g j := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j ∈ Finset.range (m + c), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hg j)

/-- Summation of a per-order top-separated bound with **independent** top offset `p` and low-window
offset `q` (the connDiff field naturally has top point at order `i+1` but low window `i+2`, so the
single-offset `jetL2_sum_of_perOrder` of `ArmBaseCoeffJetL2Summed` does not apply directly). -/
private lemma jetL2_sum_lowShift
    (a p q : ℕ) (Ktop : ℝ) (hKtop : 0 ≤ Ktop) (Kc : ℕ → ℝ) (hKc : ∀ i, 0 ≤ Kc i)
    (f w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hper : ∀ i, i ≤ a →
        f i ≤ Ktop * w (i + p) + Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) :
    ∑ i ∈ Finset.range (a + 1), f i ≤
      Ktop * (∑ j ∈ Finset.range (a + 1 + p), w j) +
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
  refine le_trans (Finset.sum_le_sum (fun i hi =>
    hper i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) ?_
  rw [Finset.sum_add_distrib]
  have hB : (∑ i ∈ Finset.range (a + 1), Ktop * w (i + p)) ≤
      Ktop * ∑ j ∈ Finset.range (a + 1 + p), w j := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_shift_le w hw (a + 1) p) hKtop
  have hA : (∑ i ∈ Finset.range (a + 1), Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) ≤
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine mul_le_mul_of_nonneg_left ?_ (hKc i)
    have hsub : Finset.range (i + q) ⊆ Finset.range (a + q) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    have hss : ∑ j ∈ Finset.range (i + q), w j ≤ ∑ j ∈ Finset.range (a + q), w j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    linarith
  linarith [hA, hB]

/-! ### Geometry setting. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Real-scalar linearity of `iteratedCovGrad` (copied from the private helper of
`RemainderCoeffL2JetMoser.lean`; needed for the `convexPerturbation` jet expansion). -/
private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

/-! ### Generic per-order top-separated bound (DIRECT route). -/

set_option linter.unusedVariables false in
/-- DIRECT per-order top-separated jet-L2 bound for the connection-difference field, generic in
`(g₁, P, htie)`.  The **top-split coefficient** `2·finrank²·Kt0` (`Kt0` = engine head `10·S 0`) is
`R`-independent; the lumped low coefficient carries the ball-uniform tame-window constant `KI`
(house `R`-pattern). -/
theorem connDiffContrInsertionField_perOrder_l2_topSeparated_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 3 4 i
              (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨KI, hKI_nn, hKI⟩ :=
    boundedFactorGridWindow_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := by rw [hfr_def]; exact Nat.cast_nonneg _
  have hfr2_nn : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg fr
  have hKtop_nn : (0 : ℝ) ≤ 2 * fr ^ 2 * Kt0 :=
    mul_nonneg (mul_nonneg (by norm_num) hfr2_nn) hKt0_nn
  have hKc_nn : ∀ i, (0 : ℝ) ≤ 2 * fr ^ 2 * Kc0 i * (i : ℝ) * KI i := fun i =>
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hfr2_nn) (hKc0_nn i))
      (Nat.cast_nonneg i)) (hKI_nn i)
  refine ⟨2 * fr ^ 2 * Kt0, hKtop_nn,
    fun i => 2 * fr ^ 2 * Kc0 i * (i : ℝ) * KI i, hKc_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    -- `δ ≥ 0` is forced by the fibre-op bound at a nonzero vector (copied from the tameEnvelope
    -- producer `connDiffContrInsertionField_order0sup_perOrder_l2_tameEnvelope_generic`).
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr' : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr'
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbnd := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbnd]
    -- named integrand summands (top head + reshaped remainder window)
    set uFun : M → ℝ := fun x => 2 * fr ^ 2 * Kt0 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) with huFun_def
    set vFun : M → ℝ := fun x => 2 * fr ^ 2 * Kc0 i * (i : ℝ) *
        Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) with hvFun_def
    -- pointwise bound: field jet ≤ uFun + vFun
    have hpt : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 3 4 i
              (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
          uFun x + vFun x := by
      intro x
      -- field↔section transfer with a `finrank²` factor
      have htrans : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 3 4 i
            (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
          fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 3 4 i
              (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 3 4 i
                (slotExtend (I := I) (M := M) g₀ 2 3
                  (slotExtend (I := I) (M := M) g₀ 1 2
                    (connDiffSection (I := I) g₁ g₀)))).toSection x) := by
          rw [connDiffContrInsertionField_eq_reindex_slotExtend_two (I := I) (M := M) g₀ g₁]
          exact rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
            (slotExtend (I := I) (M := M) g₀ 2 3
              (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
            coreInPerm201 i x
        have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) i x
        have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I) g₁ g₀) i x
        rw [h0]
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 3 4 i
                  (slotExtend (I := I) (M := M) g₀ 2 3
                    (slotExtend (I := I) (M := M) g₀ 1 2
                      (connDiffSection (I := I) g₁ g₀)))).toSection x)
            ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 3 i
                  (slotExtend (I := I) (M := M) g₀ 1 2
                    (connDiffSection (I := I) g₁ g₀))).toSection x) := h1
          _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 2 i
                  (connDiffSection (I := I) g₁ g₀)).toSection x)) :=
              mul_le_mul_of_nonneg_left h2 hfr_nn
          _ = fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 2 i
                  (connDiffSection (I := I) g₁ g₀)).toSection x) := by ring
      -- engine split of the section jet at order `i`
      have heng := hbot g₁ P htie hδ_le hδ0 hδ i x
      -- fold the head into `Hd`
      set Hd : SmoothCcTensor g₀ 1 (2 + i) :=
        appCcRS (I := I) (M := M) g₀ 1 1 (2 + i)
          (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
      have hhead := heng.1
      have hrem := heng.2
      -- `∇^i sec = Hd + (∇^i sec - Hd)`
      have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x (Hd.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀) -
              Hd).toSection x) := by
        have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + i) x
          (Hd.toSection x)
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀) - Hd).toSection x)
        have key :
            (iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x =
              Hd.toSection x +
                (iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀) -
                  Hd).toSection x := by
          simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
          abel
        rw [key]
        exact hadd
      -- reshape the remainder into a bounded-factor grid window
      have hrem_reshaped : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀) - Hd).toSection x) ≤
          Kc0 i * ((i : ℝ) * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
        refine le_trans hrem ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKc0_nn i)
        refine le_trans (tsResSum_le_boundedWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x))
          (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _) i) ?_
        exact mul_le_mul_of_nonneg_left
          (Combinatorics.boundedFactorGridWindow_mono _
            (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _)
            (by omega) (by omega)) (Nat.cast_nonneg i)
      -- combine: section bound
      have hsec_bound : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) +
          2 * (Kc0 i * ((i : ℝ) * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))) := by
        linarith [hsplit, hhead, hrem_reshaped]
      -- assemble the pointwise bound
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 3 4 i
                (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x)
          ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) :=
            htrans
        _ ≤ fr ^ 2 * (2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) +
              2 * (Kc0 i * ((i : ℝ) * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)))) :=
            mul_le_mul_of_nonneg_left hsec_bound hfr2_nn
        _ = uFun x + vFun x := by simp only [huFun_def, hvFun_def]; ring
    -- integrate
    have hu_int : MeasureTheory.Integrable uFun
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      simp only [huFun_def]
      exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 1))
        (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P)).const_mul (2 * fr ^ 2 * Kt0)
    have hv_int : MeasureTheory.Integrable vFun
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      simp only [hvFun_def]
      exact ((hKI P hPball i hi).1).const_mul (2 * fr ^ 2 * Kc0 i * (i : ℝ))
    have hu_eval : (∫ x, uFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        2 * fr ^ 2 * Kt0 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 := by
      simp only [huFun_def]
      rw [MeasureTheory.integral_const_mul,
        SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P),
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
          (2 + (i + 1)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P)]
    have hv_eval : (∫ x, vFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        2 * fr ^ 2 * Kc0 i * (i : ℝ) * KI i *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      simp only [hvFun_def]
      rw [MeasureTheory.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (hKI P hPball i hi).2
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hfr2_nn) (hKc0_nn i))
          (Nat.cast_nonneg i))) (le_of_eq (by ring))
    refine le_trans (normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3
      (4 + i) (iteratedCovGrad (I := I) g₀ 3 4 i (connDiffContrInsertionField (I := I) g₀ g₁))
      (fun x => uFun x + vFun x) (hu_int.add hv_int) hpt) ?_
    rw [MeasureTheory.integral_add hu_int hv_int, hu_eval]
    linarith [hv_eval]
  · -- empty manifold: the jet L² seminorm is `0`
    haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    have hz : ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖)
      linarith
    calc ‖iteratedCovGrad (I := I) g₀ 3 4 i
            (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2
        = 0 := by rw [hz]; norm_num
      _ ≤ 2 * fr ^ 2 * Kt0 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 +
            2 * fr ^ 2 * Kc0 i * (i : ℝ) * KI i *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
          add_nonneg (mul_nonneg hKtop_nn (sq_nonneg _)) (mul_nonneg (hKc_nn i) hwin_nn)

/-! ### `realizedFam` per-order and summed bounds. -/

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
/-- `realizedFam` per-order top-separated bound: instantiate the generic producer at the convex
perturbation `g₁ = realizedFam g₀ T T' hδ hδ' s`, converting the perturbation data-weights to
`(T, T')` weights.  The top coefficient `Ktop` is unchanged (`R`-independent). -/
theorem connDiffContrInsertionField_realizedFam_jetL2_perOrder_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 3 4 i
              (connDiffContrInsertionField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hgen⟩ :=
    connDiffContrInsertionField_perOrder_l2_topSeparated_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨Ktop, hKtop_nn, Kc, hKc_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hwin : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤
        (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
    nlinarith [mul_le_mul hnorm_le hnorm_le (norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  have hmain := hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
  refine le_trans hmain (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left (hwin (i + 1)) hKtop_nn
  · refine mul_le_mul_of_nonneg_left ?_ (hKc_nn i)
    have hsum := Finset.sum_le_sum
      (fun j (_ : j ∈ Finset.range (i + 2)) => hwin j)
    linarith

set_option linter.unusedVariables false in
/-- **Summed** data-weighted jet-L2 bound for the connection-difference field (constituent
3-of-5 of the data-weighted threeArm precursor).  Summing the `realizedFam` per-order bound over
`i ≤ a` lands both data windows at order `a+2`, with `Ktop` `R`-independent (the engine head,
times `2·finrank²`) and `Kc = ∑_{i≤a} Kc_perOrder i` following the accepted house `R`-pattern. -/
theorem connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 4 i
                (connDiffContrInsertionField (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hper⟩ :=
    connDiffContrInsertionField_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨Ktop, hKtop_nn, ∑ i ∈ Finset.range (a + 1), Kc i,
    Finset.sum_nonneg (fun i _ => hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  exact jetL2_sum_lowShift a 1 2 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 3 4 i
      (connDiffContrInsertionField (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i hi => hper T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi)

end DifferentialGeometry.Integral.Connection
