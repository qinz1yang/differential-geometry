import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DLaCoefficientFieldTopSeparated
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

/-!
# Top-separated realized-family jet bounds for the DLa coefficient field

The pointwise DLa coefficient-field estimate is integrated along the realized metric family.  This
gives both per-order and summed jet-L2 bounds whose protected top coefficient is independent of the
lower-order ball radius.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet Icc_subset_realizedSmallSet)
open DifferentialGeometry.Analysis.Laplacian
  (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section DLaGridBrick

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
      intro y hy; rw [Finset.mem_range] at hy ⊢; omega
    have hss : ∑ j ∈ Finset.range (i + q), w j ≤ ∑ j ∈ Finset.range (a + q), w j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    linarith
  linarith [hA, hB]
-- The realized-family jet assembly requires additional elaboration budget.
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (Icc_subset_realizedSmallSet) in
/-- **`realizedFam` per-order top-separated jet-L2 bound** for the DLa coefficient field.  Fixes
the single top constant `Ktop = Ktop_field·(diagonalGridGrowthFactor a)²` (`R`-free) by
`diagonalGridGrowthFactor i ≤ diagonalGridGrowthFactor a`; the remainder uses the ball-uniform tame-window integrator. -/
theorem deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieConnDiffDerivCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Ktop_field, hKtop_field_nn, Kc_field, hKc_field_nn, hfield⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_deTurckLieConnDiffDerivCoeffField_topSeparated_le (I := I) (M := M) g₀ g_bg hδ₁_lt
  obtain ⟨K, hK_nn, hK⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Ktop_field * diagonalGridGrowthFactor (E := E) a * diagonalGridGrowthFactor (E := E) a,
      mul_nonneg (mul_nonneg hKtop_field_nn (appCcGdiag_nonneg (E := E) a))
        (appCcGdiag_nonneg (E := E) a),
    fun i => Kc_field i * ∑ k ∈ Finset.range (i + 3), K k,
    fun i => mul_nonneg (hKc_field_nn i) (Finset.sum_nonneg fun k _ => hK_nn k), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]; exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc) δP :=
    gFibreOpBound_mono_of_le (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def, show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_dla, iteratedCovGrad_smul_dla]
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
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def, show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_dla, iteratedCovGrad_smul_dla]
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤
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
        (iteratedCovGrad (I := I) g₀ 0 2 j Pc)) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  -- pointwise field top-sep bound (with the grid remainder in explicit `∑∑∑∏` form).
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc).toSection x)) +
          Kc_field i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x) := by
    intro x
    refine (hfield g₁ Pc htie hδP_le hδP_nn hδP_bound i x).trans_eq ?_
    have hgw : antidiagonalTupleGridPartialSum (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l Pc).toSection x)) (i + 3) =
        ∑ k ∈ Finset.range (i + 3), ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x) := by
      rw [antidiagonalTupleGridPartialSum]; rfl
    rw [hgw]
  have hint_k : ∀ k ∈ Finset.range (i + 3), MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k _ => (hK Pc hPball k).1
  have hutop_int : MeasureTheory.Integrable
      (fun x => Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
      (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc)).const_mul _
  have hvrem_int : MeasureTheory.Integrable
      (fun x => Kc_field i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 3)) hint_k).const_mul _
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => (Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc).toSection x)) +
      Kc_field i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
    (hutop_int.add hvrem_int) hpt
  refine le_trans hnorm ?_
  rw [MeasureTheory.integral_add hutop_int hvrem_int]
  -- top integral
  have htop_eval : (∫ x, Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i *
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc‖ ^ 2 := by
    rw [MeasureTheory.integral_const_mul,
      SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
        (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc)]
  rw [htop_eval]
  -- remainder integral
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum (Finset.range (i + 3)) hint_k]
  -- top: bound `diagonalGridGrowthFactor i·diagonalGridGrowthFactor i ≤ diagonalGridGrowthFactor a·diagonalGridGrowthFactor a` and `Pc → (T,T')`.
  have happ_mono : diagonalGridGrowthFactor (E := E) i ≤ diagonalGridGrowthFactor (E := E) a := by
    rw [diagonalGridGrowthFactor, diagonalGridGrowthFactor]
    exact pow_le_pow_right₀ (by
      have : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      linarith) hi
  have happ_nn : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
  have happa_nn : 0 ≤ diagonalGridGrowthFactor (E := E) a := appCcGdiag_nonneg (E := E) a
  have htop_le : Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i *
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc‖ ^ 2 ≤
      (Ktop_field * diagonalGridGrowthFactor (E := E) a * diagonalGridGrowthFactor (E := E) a) *
        (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by
    have hc_le : Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i ≤
        Ktop_field * diagonalGridGrowthFactor (E := E) a * diagonalGridGrowthFactor (E := E) a := by
      have h1 : Ktop_field * diagonalGridGrowthFactor (E := E) i ≤ Ktop_field * diagonalGridGrowthFactor (E := E) a :=
        mul_le_mul_of_nonneg_left happ_mono hKtop_field_nn
      have h2 : 0 ≤ Ktop_field * diagonalGridGrowthFactor (E := E) i :=
        mul_nonneg hKtop_field_nn happ_nn
      calc Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i
          ≤ Ktop_field * diagonalGridGrowthFactor (E := E) a * diagonalGridGrowthFactor (E := E) i :=
            mul_le_mul_of_nonneg_right h1 happ_nn
        _ ≤ Ktop_field * diagonalGridGrowthFactor (E := E) a * diagonalGridGrowthFactor (E := E) a :=
            mul_le_mul_of_nonneg_left happ_mono (mul_nonneg hKtop_field_nn happa_nn)
    have hc_nn : 0 ≤ Ktop_field * diagonalGridGrowthFactor (E := E) a * diagonalGridGrowthFactor (E := E) a :=
      mul_nonneg (mul_nonneg hKtop_field_nn happa_nn) happa_nn
    calc Ktop_field * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc‖ ^ 2
        ≤ (Ktop_field * diagonalGridGrowthFactor (E := E) a * diagonalGridGrowthFactor (E := E) a) *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hc_le (sq_nonneg _)
      _ ≤ (Ktop_field * diagonalGridGrowthFactor (E := E) a * diagonalGridGrowthFactor (E := E) a) *
            (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hwin (i + 2)) hc_nn
  -- remainder: bound each `∫ grid_k ≤ K k·(1+∑_{j<k+1}‖∇^jPc‖²)`, then Pc→(T,T').
  have hrem_le : Kc_field i * ∑ k ∈ Finset.range (i + 3),
        (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (Kc_field i * ∑ k ∈ Finset.range (i + 3), K k) *
        (1 + ∑ j ∈ Finset.range (i + 3),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
    have hstep : (∑ k ∈ Finset.range (i + 3),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))) ≤
        (∑ k ∈ Finset.range (i + 3), K k) *
          (1 + ∑ j ∈ Finset.range (i + 3),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_range] at hk
      refine le_trans (hK Pc hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hK_nn k)
      have hjwin : (∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2) ≤
          ∑ j ∈ Finset.range (i + 3),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) := by
        calc (∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2)
            ≤ ∑ j ∈ Finset.range (k + 1),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
              Finset.sum_le_sum fun j _ => hwin j
          _ ≤ ∑ j ∈ Finset.range (i + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (by intro y hy; rw [Finset.mem_range] at hy ⊢; omega)
                (fun j _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      linarith
    calc Kc_field i * ∑ k ∈ Finset.range (i + 3), (∫ x, _ ∂_)
        ≤ Kc_field i * ((∑ k ∈ Finset.range (i + 3), K k) *
            (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hstep (hKc_field_nn i)
      _ = (Kc_field i * ∑ k ∈ Finset.range (i + 3), K k) *
            (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by ring
  linarith [htop_le, hrem_le]

/-- **Summed** `realizedFam` top-separated jet-L2 bound for the DLa coefficient field.  Top window
`a+3` (matching the deTurckLie window), `Ktop` `R`-free, `Kc = ∑_{i≤a} Kc_perOrder i`. -/
theorem deTurckLieDLaCoeffField_realizedFam_jetL2_summed_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (deTurckLieConnDiffDerivCoeffField (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hper⟩ :=
    deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Ktop, hKtop_nn, ∑ i ∈ Finset.range (a + 1), Kc i,
    Finset.sum_nonneg (fun i _ => hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  exact jetL2_sum_lowShift a 2 3 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (deTurckLieConnDiffDerivCoeffField (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i hi => hper T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi)

end DLaGridBrick

end DifferentialGeometry.Analysis.Sobolev

end
