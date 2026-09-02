import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseCometricMultiplier
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricPerturbationPath_inverseMetricDifferenceSlotCoefficient_riemannianFiberNormSq_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    {βT βT' : ℝ} (hβT_nn : 0 ≤ βT) (hβT'_nn : 0 ≤ βT')
    (hβT : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) βT)
    (hβT' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') βT')
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((inverseMetricDifferenceSlotCoefficient (I := I) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (max βT βT' / (1 - δ₀))) ^ 2 := by
  set g₁ := metricPerturbationPath (I := I) g₀ T T' hδ hδ' t with hg₁_def
  set δc : ℝ := min ((1 - t) * βT' + t * βT) δ₀ with hδc_def
  have hβconv : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t))
      ((1 - t) * βT' + t * βT) :=
    convexPerturbation_gFibreOpBound (I := I) g₀ T T' hβT hβT' ht.1 ht.2
  have hδconv : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t))
      ((1 - t) * δ' + t * δ) :=
    convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' ht.1 ht.2
  have hδ₀b : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t)) δ₀ :=
    metricCauchySchwarzBound_mono (I := I) (M := M) g₀ _
      (by nlinarith [hδ'_le, hδ_le, ht.1, ht.2]) hδconv
  have hmin : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t)) δc :=
    metricCauchySchwarzBound_min (I := I) (M := M) g₀ _ hβconv hδ₀b
  have hδc_nn : 0 ≤ δc :=
    le_min
      (add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hβT'_nn)
        (mul_nonneg ht.1 hβT_nn))
      hδ₀_nn
  have hδc_lt : δc < 1 := lt_of_le_of_lt (min_le_right _ _) hδ₀
  have htmem : t ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
    Icc_subset_metricPerturbationPathDomain (lt_of_le_of_lt hδ_le hδ₀)
      (lt_of_le_of_lt hδ'_le hδ₀) ht
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t) y v w := by
    intro y v w
    rw [hg₁_def]
    exact metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ' htmem y v w
  have hendo :=
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.riemannianFiberNormSq_gInvDiffSlotEndo_le
      (I := I) (M := M) g₀ g₁ _ htie hδc_lt hδc_nn hmin x
  have hslot : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (δc / (1 - δc))) ^ 2 := by
    rw [show (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection x =
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceSlotEndo
            (I := I) g₀ g₁ x)) from rfl]
    exact hendo
  have hmaxβ_nn : 0 ≤ max βT βT' := le_trans hβT_nn (le_max_left _ _)
  have hδc_le : δc ≤ max βT βT' :=
    (min_le_left _ _).trans
      (by nlinarith [le_max_right βT βT', le_max_left βT βT', ht.1, ht.2])
  have hdenom : 1 - δ₀ ≤ 1 - δc := sub_le_sub_left (min_le_right _ _) 1
  have hratio : δc / (1 - δc) ≤ max βT βT' / (1 - δ₀) :=
    div_le_div₀ hmaxβ_nn hδc_le (sub_pos.mpr hδ₀) hdenom
  refine hslot.trans (pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hδc_nn (sub_nonneg.mpr hδc_lt.le)))
    (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)) 2)

end DifferentialGeometry.Analysis.Spectral
