import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundCoeffFieldOrderZeroPointwise
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffCovDerivBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnDiffCovDeriv connDiff_pairing_mdiffAt connDiffCovDerivOp dLaCovKernel_apply_extend
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem deTurckLieDLaCoeffField_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((deTurckLieConnDiffDerivCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  have hcoeff : 0 < 1 - δ₁ := by linarith
  set κ : ℝ := Real.sqrt (1 / (1 - δ₁)) with hκ_def
  have hκ_nn : 0 ≤ κ := Real.sqrt_nonneg _
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.Analysis.Parabolic.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  set B : ℝ := Csob * R with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hCsob_nn hR
  obtain ⟨Cq, hCq_nn, hCq⟩ :=
    exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope (I := I) (M := M) g₀
      (δ₀ := δ₁) hδ₁_lt B hB_nn
  obtain ⟨Cbg, hCbg_nn, hCbg⟩ :=
    exists_fixed_covDerivConnDiff_sqrt_bound (I := I) (M := M) g₀ g_bg
  obtain ⟨Cc, hCc_nn, hCc⟩ := exists_fixed_connDiff_sqrt_bound (I := I) (M := M) g₀ g_bg
  obtain ⟨Ca0, hCa0_nn, hCa0⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₁_nn hδ₁_lt
  set CaB : ℝ := Ca0 * B with hCaB_def
  have hCaB_nn : 0 ≤ CaB := mul_nonneg hCa0_nn hB_nn
  set CK : ℝ := (Cq + Cbg + 3 * (CaB * (CaB + Cc))) * (κ * κ) with hCK_def
  have hCK_nn : 0 ≤ CK := by
    rw [hCK_def]
    refine mul_nonneg ?_ (mul_nonneg hκ_nn hκ_nn)
    have h3 : 0 ≤ CaB * (CaB + Cc) := mul_nonneg hCaB_nn (add_nonneg hCaB_nn hCc_nn)
    linarith [hCq_nn, hCbg_nn, h3]
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 *
      ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2,
    by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hs0, hs1⟩ := hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs0, hs1⟩
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hP_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    rw [hg₁, hP_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hP_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
    δP :=
    gFibreOpBound_mono_of_le (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have hδP_lt1 : δP < 1 := lt_of_le_of_lt hδP_le hδ₁_lt
  have henv := hCsob T T' hR hTball hT'ball s ⟨hs0, hs1⟩ x
  rw [← hP_def, ← hB_def] at henv
  change (∑ k ∈ Finset.range 3,
    tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x)) ≤ B at henv
  have hquad : ∀ v w u : TangentSpace I x,
      covDerivConnDiffSqrt (I := I) g₀ g₁ x v w u ≤
        Cq * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u) := by
    intro v w u
    unfold covDerivConnDiffSqrt
    exact hCq g₁ P (δ := δP) (le_trans hδP_le (le_max_left _ _))
      hδP_bound htie x henv v w u
  have hbg : ∀ v w u : TangentSpace I x,
      covDerivConnDiffSqrt (I := I) g₀ g_bg x v w u ≤
        Cbg * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u) := by
    intro v w u
    unfold covDerivConnDiffSqrt
    exact hCbg x v w u
  have hbase : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      Ca0 * tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
        Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
    intro u v
    have h := hCa0 g₁ P htie (δ := δP) hδP_le hδP_nn hδP_bound x u v
    change Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      Ca0 * tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
        Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) at h
    exact h
  exact deTurckLieConnDiffDerivCoeffField_fiberNormSq_le_of_scalar_bounds
    g₀ g₁ g_bg P x htie hδP_lt1 hδP_bound hδP_le hcoeff hκ_def hκ_nn henv
      hquad hbg hbase (hCc x) hCq_nn hCbg_nn hCc_nn hCa0_nn hCaB_nn hCaB_def
      hCK_def hCK_nn

end DifferentialGeometry.Analysis.Sobolev

end
