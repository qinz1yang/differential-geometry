import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalSecondDerivative
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalSobolevTimeNorm

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private theorem chartInverse_eq_ae_of_cutoff
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₁ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₁ : IsOpen Ω₁) (hsub : Ω₁ ⊆ Ω)
    (v : M → ℝ) (f : EuStd → ℝ)
    {η : EuStd → ℝ} (hηone : ∀ z ∈ Ω₁, η z = 1)
    (hv : v =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α (fun z => η z * f z)) :
    (fun z => v ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω₁]
      f := by
  have heq := ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) hv
  have heq' := heq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [heq', ae_restrict_mem hΩ₁.measurableSet] with z hz hzm
  rw [hz]
  have hzt : (toEuclidean (E := EuN)).symm z ∈ (extChartAt I_hs α).target := by
    obtain ⟨y, hy, he⟩ := hΩs (subset_closure (hsub hzm))
    rw [← he, ContinuousLinearEquiv.symm_apply_apply]
    exact interior_subset hy
  have hx : (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z) ∈
      (chartAt (EuclideanHalfSpace n) α).source := by
    simpa only [extChartAt_source] using (extChartAt I_hs α).map_target hzt
  rw [chartPullback_apply_of_mem α _ hx, (extChartAt I_hs α).right_inv hzt,
    ContinuousLinearEquiv.apply_symm_apply, hηone z hzm, one_mul]

theorem ae_memWkp_succ_and_memLp_wkpNorm_of_cutoff_gradient
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {m : ℕ}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₁ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₁ : IsOpen Ω₁) (hsub : Ω₁ ⊆ Ω)
    {u : Z → H1ComplDirichlet q} (hu : MemLp u 2 μ)
    (v : Fin (Module.finrank ℝ EuN) → Z → H1ComplDirichlet q)
    {η : EuStd → ℝ} (hηone : ∀ z ∈ Ω₁, η z = 1)
    (hv : ∀ i, ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v i t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z))
    (hW : ∀ i, ∀ᵐ t ∂μ,
      MemWkp m 2
        (fun z => H1ComplDirichletToLp q (v i t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁)
    (hWnorm : ∀ i, MemLp (fun t => (iteratedWeakSobolevNorm m 2
      (fun z => H1ComplDirichletToLp q (v i t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁).toReal) 2 μ) :
    (∀ᵐ t ∂μ, MemWkp (m + 1) 2
      (fun z => H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁) ∧
      MemLp (fun t => (iteratedWeakSobolevNorm (m + 1) 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁).toReal) 2 μ := by
  let uLp := hu.toLp u
  let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) μ uLp
  let W := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i uLp
  have hU : MemLp (U : Z × EuStd → ℝ) 2 (μ.prod (volume.restrict Ω₁)) :=
    (Lp.memLp U).mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl))
  have heqU : ∀ᵐ t ∂μ, (fun z => U (t, z)) =ᵐ[volume.restrict Ω₁]
      fun z => H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    filter_upwards [dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) μ uLp, hu.coeFn_toLp] with t ht hut
    rw [hut] at ht
    exact ht.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have heqW (i) : ∀ᵐ t ∂μ, (fun z => W i (t, z)) =ᵐ[volume.restrict Ω₁]
      fun z => H1ComplDirichletToLp q (v i t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    filter_upwards [dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i uLp,
      hu.coeFn_toLp, hv i] with t ht hut hvt
    rw [hut] at ht
    exact (ht.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))).trans
      (chartInverse_eq_ae_of_cutoff q α hΩ hΩc hΩs hΩ₁ hsub
        (H1ComplDirichletToLp q (v i t))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) hηone hvt).symm
  have hWmem (i) : ∀ᵐ t ∂μ, MemWkp m 2 (fun z => W i (t, z)) Ω₁ := by
    filter_upwards [hW i, heqW i] with t ht he
    exact (MemWkp_congr_ae (by norm_num) hΩ₁ he).mpr ht
  have hWn (i) : MemLp (fun t => (iteratedWeakSobolevNorm m 2
      (fun z => W i (t, z)) Ω₁).toReal) 2 μ := by
    apply (hWnorm i).ae_eq
    filter_upwards [heqW i] with t ht
    exact congrArg ENNReal.toReal (wkpNorm_congr_ae (by norm_num) hΩ₁ ht.symm)
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t, z)) (fun z => U (t, z)) Ω₁ :=
    (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i uLp).mono
      (fun _ ht => DeGiorgi.HasWeakPartialDeriv.restrict hΩ₁ hsub ht)
  obtain ⟨hmem, hnorm⟩ := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    hΩ₁ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hU hWmem hWn hfirst
  constructor
  · filter_upwards [hmem, heqU] with t ht he
    exact (MemWkp_congr_ae (by norm_num) hΩ₁ he).mp ht
  · apply hnorm.ae_eq
    filter_upwards [heqU] with t ht
    exact congrArg ENNReal.toReal (wkpNorm_congr_ae (by norm_num) hΩ₁ ht)

theorem ae_memWkp_three_and_memLp_wkpNorm_of_cutoff_gradient_timeH1
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b c d : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (hac : a < c) (hdb : d < b)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₁ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₁ : IsOpen Ω₁) (hΩ₁Ω : closure Ω₁ ⊆ Ω)
    {η : EuStd → ℝ} (hηone : ∀ z ∈ Ω₁, η z = 1)
    {u : ℝ → H1ComplDirichlet q}
    {μ : Measure ℝ} (hμ : μ = volume.restrict (Icc a b))
    (hu : MemLp u 2 (μ.restrict (Icc c d)))
    (v : Fin (Module.finrank ℝ EuN) → Lp (H1ComplDirichlet q) 2 μ)
    (f : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (ℓ β : Fin (Module.finrank ℝ EuN) → Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (w : Fin (Module.finrank ℝ EuN) → timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (hrep : ∀ i, ∀ᵐ t ∂μ.restrict (Icc c d),
      (H1ComplDirichletToLp q (v i t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z))
    (hwmass : ∀ i, ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      (w i).toFun s z = inner ℝ (H1ComplDirichletToLp q (v i (a + s)))
        (H1ComplDirichletToLp q z))
    (hwderiv : ∀ i, (w i).deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ i (a + s))
    (hpair : ∀ i, ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, ℓ i t (z t) ∂μ) = (∫ t, β i t (z t) ∂μ) -
        ∫ t, (∑ j, ∑ k, ∫ y in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (v i t) y *
            (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α j k y) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (z t) y) ∂μ)
    (hsource : ∀ i, ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β i t (z t) ∂μ) = ∫ t, (∫ y in Ω,
        f i (t, y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))) ∂μ) :
    (∀ᵐ t ∂μ.restrict (Icc c d),
      MemWkp 3 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁) ∧
      MemLp (fun t => (iteratedWeakSobolevNorm 3 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁).toReal)
        2 (μ.restrict (Icc c d)) := by
  cases hμ
  have hW (i) :
      (∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d), MemWkp 2 2
        (fun z => H1ComplDirichletToLp q (v i t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁) ∧
        MemLp (fun t => (iteratedWeakSobolevNorm 2 2
          (fun z => H1ComplDirichletToLp q (v i t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁).toReal)
          2 ((volume.restrict (Icc a b)).restrict (Icc c d)) := by
    obtain ⟨H, hH, _⟩ := exists_local_dirichlet_second_weak_derivative_of_timeH1_interior
      hG hab hreg q α hΩ hΩc hΩs hac hdb
      (v i) (f i) (ℓ i) (β i) (w i)
      (hwmass i) (hwderiv i) (hpair i) (hsource i) hΩ₁ hΩ₁Ω
    exact ae_memWkp_two_and_memLp_wkpNorm_chartInverse_of_weak_second_partials
      q α hΩ hΩc hΩs hΩ₁ (subset_closure.trans hΩ₁Ω)
      ((Lp.memLp (v i)).mono_measure Measure.restrict_le_self) H hH
  exact ae_memWkp_succ_and_memLp_wkpNorm_of_cutoff_gradient
    q α hΩ hΩc hΩs hΩ₁ (subset_closure.trans hΩ₁Ω) hu (fun i => v i)
    hηone hrep (fun i => (hW i).1) (fun i => (hW i).2)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
