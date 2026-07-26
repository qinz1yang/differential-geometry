import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder1TameEnvelope

/-!
# Top-separated jet-L2 head atom for `covGrad (connDiffSection)` — the DLa top factor

The DeTurck-Lie coefficient field splits `deTurckLieCoeffField = deTurckLieDLaCoeffField +
deTurckLieDLbCoeffField`, and the DLa half is a `g₁`-dependent bicontraction whose *top factor* is
`covGrad (connDiffSection g₁ g₀)` (one covariant derivative above the connection-difference field).
When the DLa reduction is top-separated (keeping the head cell separate through the bicontraction
Leibniz), the single summand that reaches the protected top window `∇^{i+2}T` is this factor.

This file proves that **head atom**: a data-weighted jet-L2 bound for
`covGrad (connDiffSection g₁ g₀)` whose top-split coefficient is `R`-independent.  It is *pure
`connDiffSection`* — no DLa-specific definition is used, so the committed-clean import cone matches
`ConnDiffJetL2Summed.lean`.

The route is the recon snapshot's two-liner:
* the commutation identity `rfns_iteratedCovGrad_covGrad_comm_rs` turns
  `rfns (∇^i (covGrad (connDiffSection))) = rfns (∇^{i+1} (connDiffSection))` — an equality, unlike
  the connDiff field's `slotExtend` transfer which loses a `finrank²` factor;
* the committed engine `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`, applied at order
  `j = i+1`, splits the section jet into a top head `10·S 0·rfns (∇^{i+2}T)` (`R`-independent) and a
  data-weighted remainder, which is reshaped to a `boundedFactorGridWindow` and integrated by
  `boundedFactorGridWindow_integral_ballUniform_tameWindow`.

End shape of the generic per-order bound (top point `i+2`, low window `i+2`, both one order above
the connDiff field, matching the deTurckLie top window `a+2`):
```
‖∇^i (covGrad (connDiffSection g₁ g₀))‖²
  ≤ Ktop · ‖∇^{i+2} P‖²  +  Kc i · (1 + ∑_{j < i+2} ‖∇^j P‖²)
```
with `Ktop = 2·(10·S 0)` `R`-independent and `Kc i` the accepted house `R`-pattern (threaded through
the ball-uniform tame-window converter).

This is sub-brick 1 (the head atom) of the DLa top-separation; see
`DeTurckLieJetL2Summed.md` and `UNIF_EXISTENCE_PLAN.md` "DLa sub-brick recon snapshot".
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
`tsResSum_le_boundedWindow` of `CurvatureCoefficientDifferenceJetTower.lean` (and identically in
`ConnDiffJetL2Summed.lean`).  Reshapes the engine remainder sum into a `boundedFactorGridWindow`. -/
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

/-- Shifted-range domination for a nonnegative sequence (copied from `ConnDiffJetL2Summed`). -/
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
offset `q` (copied from `ConnDiffJetL2Summed`).  The DLa head atom has top point at order `i+2` and
low window `i+2`, so `p = q = 2`. -/
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
`RemainderCoeffL2JetMoser.lean` / `ConnDiffJetL2Summed.lean`; needed for the `convexPerturbation`
jet expansion in the `realizedFam` wrapper). -/
private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

/-! ### Generic per-order top-separated bound for `covGrad (connDiffSection)` (the head atom). -/

set_option linter.unusedVariables false in
/-- **Head atom** — DIRECT per-order top-separated jet-L2 bound for `covGrad (connDiffSection g₁ g₀)`,
generic in `(g₁, P, htie)`.  The **top-split coefficient** `2·Kt0` (`Kt0` = engine head `10·S 0`) is
`R`-independent; the lumped low coefficient carries the ball-uniform tame-window constant `KI` (house
`R`-pattern).  Top point `i+2`, low window `i+2` — one order above the connection-difference field. -/
theorem covGradConnDiffSection_perOrder_l2_topSeparated_generic
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
          ‖iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
              (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨KI, hKI_nn, hKI⟩ :=
    boundedFactorGridWindow_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  have hKtop_nn : (0 : ℝ) ≤ 2 * Kt0 := mul_nonneg (by norm_num) hKt0_nn
  have hKc_nn : ∀ i, (0 : ℝ) ≤ 2 * Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) * KI i := fun i =>
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hKc0_nn (i + 1)))
      (Nat.cast_nonneg (i + 1))) (hKI_nn i)
  refine ⟨2 * Kt0, hKtop_nn,
    fun i => 2 * Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) * KI i, hKc_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    -- `δ ≥ 0` is forced by the fibre-op bound at a nonzero vector (copied from the connDiff
    -- producer `connDiffContrInsertionField_perOrder_l2_topSeparated_generic`).
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
    -- named integrand summands (top head at `∇^{i+2}P` + reshaped remainder window)
    set uFun : M → ℝ := fun x => 2 * Kt0 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) with huFun_def
    set vFun : M → ℝ := fun x => 2 * Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) *
        Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) with hvFun_def
    -- pointwise bound: covGrad-section jet ≤ uFun + vFun
    have hpt : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
              (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
          uFun x + vFun x := by
      intro x
      -- commutation identity: `rfns (∇^i (covGrad Φ)) = rfns (∇^{i+1} Φ)` (an equality)
      rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
        (connDiffSection (I := I) g₁ g₀) x]
      -- engine split of the section jet at order `i+1`
      have heng := hbot g₁ P htie hδ_le hδ0 hδ (i + 1) x
      -- fold the head into `Hd`
      set Hd : SmoothCcTensor g₀ 1 (2 + (i + 1)) :=
        appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
      -- re-ascribe the engine head bound to the clean `i+2` index form (defeq `(i+1)+1 = i+2`)
      have hhead : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x (Hd.toSection x) ≤
          Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := heng.1
      have hrem := heng.2
      -- `∇^{i+1} sec = Hd + (∇^{i+1} sec - Hd)`
      have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x (Hd.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
              Hd).toSection x) := by
        have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          (Hd.toSection x)
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
            Hd).toSection x)
        have key :
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀)).toSection x =
              Hd.toSection x +
                (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
                  Hd).toSection x := by
          simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
          abel
        rw [key]
        exact hadd
      -- reshape the remainder into a bounded-factor grid window (no widening needed at order `i+1`)
      have hrem_reshaped : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
            Hd).toSection x) ≤
          Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
        refine le_trans hrem ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKc0_nn (i + 1))
        exact tsResSum_le_boundedWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x))
          (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _) (i + 1)
      -- combine: section bound
      have hsec_bound : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
          2 * (Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))) := by
        linarith [hsplit, hhead, hrem_reshaped]
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
                (connDiffSection (I := I) g₁ g₀)).toSection x)
          ≤ 2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
            2 * (Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))) :=
            hsec_bound
        _ = uFun x + vFun x := by simp only [huFun_def, hvFun_def]; ring
    -- integrate
    have hu_int : MeasureTheory.Integrable uFun
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      simp only [huFun_def]
      exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
        (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)).const_mul (2 * Kt0)
    have hv_int : MeasureTheory.Integrable vFun
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      simp only [hvFun_def]
      exact ((hKI P hPball i hi).1).const_mul (2 * Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ))
    have hu_eval : (∫ x, uFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        2 * Kt0 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
      simp only [huFun_def]
      rw [MeasureTheory.integral_const_mul,
        SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
          (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]
    have hv_eval : (∫ x, vFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        2 * Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) * KI i *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      simp only [hvFun_def]
      rw [MeasureTheory.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (hKI P hPball i hi).2
        (mul_nonneg (mul_nonneg (by norm_num) (hKc0_nn (i + 1)))
          (Nat.cast_nonneg (i + 1)))) (le_of_eq (by ring))
    refine le_trans (normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1
      (2 + 1 + i) (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
      (fun x => uFun x + vFun x) (hu_int.add hv_int) hpt) ?_
    rw [MeasureTheory.integral_add hu_int hv_int, hu_eval]
    linarith [hv_eval]
  · -- empty manifold: the jet L² seminorm is `0`
    haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖)
      linarith
    calc ‖iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))‖ ^ 2
        = 0 := by rw [hz]; norm_num
      _ ≤ 2 * Kt0 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            2 * Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) * KI i *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
          add_nonneg (mul_nonneg hKtop_nn (sq_nonneg _)) (mul_nonneg (hKc_nn i) hwin_nn)

/-! ### `realizedFam` per-order and summed bounds. -/

set_option linter.unusedVariables false in
/-- `realizedFam` per-order top-separated bound for the DLa head atom: instantiate the generic
producer at the convex perturbation `g₁ = realizedFam g₀ T T' hδ hδ' s`, converting the perturbation
data-weights to `(T, T')` weights.  The top coefficient `Ktop` is unchanged (`R`-independent).  Top
point `i+2`. -/
theorem covGradConnDiffSection_realizedFam_jetL2_perOrder_topSeparated
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
          ‖iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
              (covGrad (I := I) (M := M) g₀ 1 2
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hgen⟩ :=
    covGradConnDiffSection_perOrder_l2_topSeparated_generic
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
  · exact mul_le_mul_of_nonneg_left (hwin (i + 2)) hKtop_nn
  · refine mul_le_mul_of_nonneg_left ?_ (hKc_nn i)
    have hsum := Finset.sum_le_sum
      (fun j (_ : j ∈ Finset.range (i + 2)) => hwin j)
    linarith

set_option linter.unusedVariables false in
/-- **Summed** data-weighted jet-L2 bound for the DLa head atom (`covGrad (connDiffSection)`).
Summing the `realizedFam` per-order bound over `i ≤ a` lands the top window at order `a+3`
(one order above the connDiff field, matching the deTurckLie top window `a+2`), with `Ktop`
`R`-independent and `Kc = ∑_{i≤a} Kc_perOrder i` following the accepted house `R`-pattern. -/
theorem covGradConnDiffSection_realizedFam_jetL2_summed_topSeparated
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
              ‖iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
                (covGrad (I := I) (M := M) g₀ 1 2
                  (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hper⟩ :=
    covGradConnDiffSection_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨Ktop, hKtop_nn, ∑ i ∈ Finset.range (a + 1), Kc i,
    Finset.sum_nonneg (fun i _ => hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  exact jetL2_sum_lowShift a 2 2 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
      (covGrad (I := I) (M := M) g₀ 1 2
        (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i hi => hper T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi)

-- Axiom audit (temporary; must be exactly [propext, Classical.choice, Quot.sound]).

end DifferentialGeometry.Integral.Connection
