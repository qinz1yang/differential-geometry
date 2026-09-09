import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Sobolev.Tools.CutoffDiffQuotLp
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientProductWeakLimitLocal
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.WeakPartial

noncomputable section

open Filter Manifold MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.Dirichlet
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private theorem exists_ae_weak_partial_local_partial_of_diffQuot_bound
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (v : Lp (H1ComplDirichlet q) 2 μ)
    {η : EuStd → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1)
    {δ C : ℝ} (hδ : 0 < δ) (hroom : cthickening δ (tsupport η) ⊆ Ω)
    (hbound : ∀ k h, 0 < |h| → |h| ≤ δ →
      (∫ t, (∑ i, ∫ z, (η z * diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z) ^ 2) ∂μ) ≤ C)
    (i k : Fin (Module.finrank ℝ EuN)) :
    ∃ H : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀ := by
  let A := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i
  let w := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i v
  obtain ⟨L, hL, hinverse⟩ :=
    exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le (μ := μ) hη hηc
  have hnorm : ∀ h : ℝ, 0 < |h| → |h| ≤ δ →
      (∫ t, (∫ z, (η z * diffQuot k h (fun y => w (t, y)) z) ^ 2) ∂μ) ≤ C := by
    intro h hhpos hh
    have hroomh : cthickening |h| (tsupport η) ⊆ Ω :=
      (cthickening_mono hh _).trans hroom
    have heq := integral_sq_cutoff_diffQuot_uncurry_compLpL hΩ.measurableSet A v η k h hroomh
    change (∫ t, (∫ z, (η z * diffQuot k h
      (fun y => Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (A.compLpL 2 μ v) (t,y)) z) ^ 2) ∂μ) ≤ C
    rw [heq]
    have hηLp : MemLp η ∞ volume := hη.continuous.memLp_of_hasCompactSupport hηc
    have hI (j) : Integrable (fun t => ∫ z, (η z * diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (v t)) z) ^ 2) μ :=
      integrable_integral_sq_cutoff_diffQuot_comp hΩ.measurableSet hηLp k h hroomh
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) (Lp.memLp v)
    apply le_trans ?_ (hbound k h hhpos hh)
    apply integral_mono (hI i) (integrable_finsetSum _ fun j _ => hI j)
    intro t
    let f := fun j => ∫ z, (η z * diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (v t)) z) ^ 2
    have hf : ∀ j ∈ Finset.univ, 0 ≤ f j := fun _ _ => integral_nonneg fun _ => sq_nonneg _
    exact Finset.single_le_sum hf (Finset.mem_univ i)
  obtain ⟨H, _, hweak⟩ := hinverse hΩ.measurableSet hΩ₀ hηone (Lp.memLp w) k hδ hroom hnorm
  refine ⟨H, ?_⟩
  have hsub : Ω₀ ⊆ Ω := by
    intro z hz
    apply hroom
    apply self_subset_cthickening
    exact subset_tsupport η (by change η z ≠ 0; rw [hηone z hz]; norm_num)
  filter_upwards [hweak, dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i v]
    with t ht hwt
  have hsource := hwt.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  intro ψ hψ hψc hψs
  have he := ht ψ hψ hψc hψs
  have heq : (∫ z in Ω₀, w (t,z) * fderiv ℝ ψ z (EuclideanSpace.single k 1)) =
      ∫ z in Ω₀, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) z *
        fderiv ℝ ψ z (EuclideanSpace.single k 1) := by
    apply integral_congr_ae
    exact hsource.mono fun z hz => congrArg (fun r => r * fderiv ℝ ψ z (EuclideanSpace.single k 1)) hz
  exact heq.symm.trans he

theorem exists_lp_second_weak_derivative_of_local_diffQuot_bound
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (v : Lp (H1ComplDirichlet q) 2 μ)
    {η : EuStd → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1)
    {δ C : ℝ} (hδ : 0 < δ) (hroom : cthickening δ (tsupport η) ⊆ Ω)
    (hbound : ∀ k h, 0 < |h| → |h| ≤ δ →
      (∫ t, (∑ i, ∫ z, (η z * diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z) ^ 2) ∂μ) ≤ C) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂μ, MemWkp 2 2
        (fun z => H1ComplDirichletToLp q (v t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  have hsecond (i k : Fin (Module.finrank ℝ EuN)) :=
    exists_ae_weak_partial_local_partial_of_diffQuot_bound q α hΩ hΩc hΩs
      v hη hηc hΩ₀ hηone hδ hroom hbound i k
  choose H hH using hsecond
  refine ⟨H, hH, ?_⟩
  have hsecond' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hH i))
  have hHLp := ae_all_iff.mpr (fun i => ae_all_iff.mpr
    (fun k => (Lp.memLp (H i k)).prodMk_left (by norm_num)))
  filter_upwards [hsecond', hHLp] with t hwt hHt
  let g := fun i => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)
  have hsub : Ω₀ ⊆ Ω := by
    intro z hz
    apply hroom
    apply self_subset_cthickening
    exact subset_tsupport η (by change η z ≠ 0; rw [hηone z hz]; norm_num)
  apply memWkp_two_of_hasWeakPartialDeriv (by norm_num) hΩ₀
    ((memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs (v t)).memLp.mono_measure
      (Measure.restrict_mono hsub le_rfl)) (g := fun i z => g i z)
  · intro i
    exact ⟨(Lp.memLp (g i)).mono_measure (Measure.restrict_mono hsub le_rfl),
      fun k => ⟨fun z => H i k (t, z), hHt i k, hwt i k⟩⟩
  · intro i
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t))

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
