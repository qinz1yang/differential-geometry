import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SliceWkp

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem ae_memWkp_two_and_memLp_wkpNorm_chartInverse_of_weak_second_partials
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hsub : Ω₀ ⊆ Ω)
    {v : Z → H1ComplDirichlet q} (hv : MemLp v 2 μ)
    (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 (μ.prod (volume.restrict Ω₀)))
    (hH : ∀ i k, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) :
    (∀ᵐ t ∂μ, MemWkp 2 2 (fun z => H1ComplDirichletToLp q (v t)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀) ∧
      MemLp (fun t => (iteratedWeakSobolevNorm 2 2
        (fun z => H1ComplDirichletToLp q (v t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀).toReal) 2 μ := by
  let vLp := hv.toLp v
  let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) μ vLp
  let W := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i vLp
  have hmeasure : μ.prod (volume.restrict Ω₀) ≤ μ.prod (volume.restrict Ω) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp (U : Z × EuStd → ℝ) 2 (μ.prod (volume.restrict Ω₀)) :=
    (Lp.memLp U).mono_measure hmeasure
  have hW : ∀ i, MemLp (W i : Z × EuStd → ℝ) 2 (μ.prod (volume.restrict Ω₀)) :=
    fun i => (Lp.memLp (W i)).mono_measure hmeasure
  have heqU : ∀ᵐ t ∂μ, (fun z => U (t, z)) =ᵐ[volume.restrict Ω₀]
      fun z => H1ComplDirichletToLp q (v t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    filter_upwards [dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) μ vLp, hv.coeFn_toLp] with t ht hvt
    rw [hvt] at ht
    exact ht.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have heqW (i) : ∀ᵐ t ∂μ, (fun z => W i (t, z)) =ᵐ[volume.restrict Ω₀]
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) := by
    filter_upwards [dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i vLp,
      hv.coeFn_toLp] with t ht hvt
    rw [hvt] at ht
    exact ht.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hsecond (i k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => H i k (t, z)) (fun z => W i (t, z)) Ω₀ := by
    filter_upwards [hH i k, heqW i] with t ht he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ k he.symm ht
  have hWreg (i) := ae_memWkp_one_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) (hW i)
    (fun k => Lp.memLp (H i k)) (hsecond i)
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t, z)) (fun z => U (t, z)) Ω₀ :=
    (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i vLp).mono
      (fun _ ht => DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht)
  obtain ⟨hmem, hnorm⟩ := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hU
    (fun i => (hWreg i).1) (fun i => (hWreg i).2) hfirst
  constructor
  · filter_upwards [hmem, heqU] with t ht he
    exact (MemWkp_congr_ae (by norm_num) hΩ₀ he).mp ht
  · apply hnorm.ae_eq
    filter_upwards [heqU] with t ht
    exact congrArg ENNReal.toReal (wkpNorm_congr_ae (by norm_num) hΩ₀ ht)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
