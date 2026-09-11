import DifferentialGeometry.Analysis.Integration.Lp.Multiplication
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalForm

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem exists_cutoff_gradient_flux_error_norm_sq_bound
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure ℝ), μ ≤ volume.restrict J →
      ∀ (V : ℝ × EuStd → ℝ) (hV : MemLp V 2 (μ.prod (volume.restrict Ω))),
      ∃ E : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
        (∀ j, E j =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ i,
          (MetricExtension.densityOnEuclid q α p.2 *
            MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
              fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p) ∧
        ∑ j, ‖E j‖ ^ 2 ≤ C * ‖hV.toLp V‖ ^ 2 := by
  let a := fun i j (p : ℝ × EuStd) =>
    (MetricExtension.densityOnEuclid q α p.2 *
      MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
        fderiv ℝ η p.2 (EuclideanSpace.single i 1)
  have htarget : closure Ω ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (image_mono interior_subset)
  have hcont (i j) : ContinuousOn (a i j) (J ×ˢ closure Ω) := by
    have hc : ContinuousOn (fun p : ℝ × EuStd =>
        MetricExtension.densityOnEuclid q α p.2 *
          MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) (J ×ˢ closure Ω) :=
      (((MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
        (fun p hp => htarget hp.2)).mul
          (MetricExtension.invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)).continuousOn
    have hd : Continuous (fun p : ℝ × EuStd => fderiv ℝ η p.2 (EuclideanSpace.single i 1)) :=
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const).comp continuous_snd
    exact hc.mul hd.continuousOn
  have hall : ContinuousOn
      (fun p : ℝ × EuStd => fun i j : Fin (Module.finrank ℝ EuN) => a i j p)
      (J ×ˢ closure Ω) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => hcont i j
  obtain ⟨C₀, hC₀⟩ := (hJc.prod hΩc).exists_bound_of_continuousOn hall
  let C := ∑ j : Fin (Module.finrank ℝ EuN), (∑ _i : Fin (Module.finrank ℝ EuN), max C₀ 0) ^ 2
  refine ⟨C, Finset.sum_nonneg (fun j _ => sq_nonneg _), ?_⟩
  intro μ hμ V hV
  have ha (i j) : MemLp (a i j) ∞ (μ.prod (volume.restrict Ω)) := by
    have h := (hcont i j).memLp_top_of_subset_isCompact (hJc.prod hΩc)
      (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  have hb (i j) : ∀ᵐ p ∂μ.prod (volume.restrict Ω), ‖a i j p‖ ≤ max C₀ 0 := by
    apply ae_mono (Measure.prod_mono hμ le_rfl)
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hJc.measurableSet.prod hΩ.measurableSet)] with p hp
    exact ((norm_le_pi_norm (fun j => a i j p) j).trans
      ((norm_le_pi_norm (fun i j => a i j p) i).trans
        (hC₀ p ⟨hp.1, subset_closure hp.2⟩))).trans (le_max_left _ _)
  exact MeasureTheory.exists_lp_sum_mul_norm_sq_le a ha (fun _ _ => max C₀ 0) hb V hV


end DifferentialGeometry.Analysis.Parabolic.Dirichlet
