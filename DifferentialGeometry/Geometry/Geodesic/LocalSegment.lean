import DifferentialGeometry.Geometry.Geodesic.Local
import DifferentialGeometry.Geometry.Geodesic.Equation.ProjectionDerivative
import DifferentialGeometry.Geometry.Comparison.HopfRinow.GeodesicSpeedBound


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open Filter Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_geodesic_segment_with_initial_velocity
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {U : Set M} (hU : U ∈ 𝓝 p) :
    ∃ (beta : ℝ → M) (epsilon : ℝ),
      0 < epsilon ∧ beta 0 = p ∧
      (mfderiv 𝓘(ℝ, ℝ) I beta 0 1 : E) = (v : E) ∧
      (∀ s ∈ Icc (-epsilon) epsilon, IsGeodesicAt g beta s) ∧
      MapsTo beta (Icc (-epsilon) epsilon) U ∧
      IsCompact (beta '' Icc (-epsilon) epsilon) ∧
      ∀ s ∈ Icc (-epsilon) epsilon,
        Real.sqrt (g.inner (beta s) (mfderiv 𝓘(ℝ, ℝ) I beta s 1)
          (mfderiv 𝓘(ℝ, ℝ) I beta s 1)) ≤ Real.sqrt (g.inner p v v) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨beta, f, hfzero, hbetaf, hbetazero, hf, hbeta⟩ :=
    exists_geodesic_with_initial_velocity_at g p v
  have hvelocity : (mfderiv 𝓘(ℝ, ℝ) I beta 0 1 : E) = (v : E) := by
    have hproj := IsMIntegralCurveAt.mfderiv_proj_one hf (by
      rw [hfzero]
      exact mem_chart_source H p)
    rw [hbetaf]
    exact hproj.trans (congrArg (fun z : TangentBundle I M => (z.snd : E)) hfzero)
  have hUnear : ∀ᶠ s in 𝓝 (0 : ℝ), beta s ∈ U := by
    apply hbeta.continuousAt.preimage_mem_nhds
    rw [hbetazero]
    exact hU
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), IsGeodesicAt g beta s ∧ beta s ∈ U :=
    (DifferentialGeometry.Geometry.eventually_isGeodesicAt hbeta).and hUnear
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hopen (s : ℝ) (hs : s ∈ Ioo (-delta) delta) :
      IsGeodesicAt g beta s ∧ beta s ∈ U := by
    apply hball
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  have hclosed : Icc (-(delta / 2)) (delta / 2) ⊆ Ioo (-delta) delta := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hgeo : IsGeodesicOn g beta (Ioo (-delta) delta) :=
    fun s hs => (hopen s hs).1.hasGeodesicEquationAt g
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 beta (Ioo (-delta) delta) := by
    intro s hs
    exact ((DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt
      (hopen s hs).1).of_le (by simp)).contMDiffWithinAt
  have hcontinuous : ContinuousOn beta (Icc (-(delta / 2)) (delta / 2)) :=
    fun s hs => (hopen s (hclosed hs)).1.continuousAt.continuousWithinAt
  refine ⟨beta, delta / 2, half_pos hdelta, hbetazero, hvelocity,
    (fun s hs => (hopen s (hclosed hs)).1),
    (fun s hs => (hopen s (hclosed hs)).2),
    isCompact_Icc.image_of_continuousOn hcontinuous, ?_⟩
  intro s hs
  have hsopen := hclosed hs
  have hspan : Icc (min 0 s) (max 0 s) ⊆ Ioo (-delta) delta := by
    intro r hr
    exact ⟨(lt_min (by linarith : -delta < 0) hsopen.1).trans_le hr.1,
      hr.2.trans_lt (max_lt hdelta hsopen.2)⟩
  have hspeed := HopfRinow.isGeodesicOn_speedSq_const g
    (t₀ := 0) (t₁ := s) isOpen_Ioo hgeo hsmooth hspan
  have hspeed' : g.inner p v v =
      g.inner (beta s) (mfderiv 𝓘(ℝ, ℝ) I beta s 1)
        (mfderiv 𝓘(ℝ, ℝ) I beta s 1) := by
    cases hbetazero
    simpa only [hvelocity] using hspeed
  exact le_of_eq (congrArg Real.sqrt hspeed'.symm)

end DifferentialGeometry.Geometry.Riemannian.Geodesic
