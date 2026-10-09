import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientUniqueContinuation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The critical points of the original Morrey disk are finite on each compact
subset of the open unit disk. -/
theorem IsMorreyDisk.finite_mfderiv_eq_zero_of_isCompact
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ ball (0 : ℂ) 1) :
    {z ∈ K | mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z = 0}.Finite := by
  have hregular :
      {z : ℂ | mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z ≠ 0} ∈
        codiscreteWithin (ball (0 : ℂ) 1) := by
    change ∀ᶠ z in codiscreteWithin (ball (0 : ℂ) 1),
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z ≠ 0
    apply eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
    intro a ha
    obtain ⟨R, hR, _, _, A_R, _, _, P, _, _, _, _, _, _, hfactor⟩ :=
      hu.exists_analytic_complex_gradient_gauge ha
    dsimp only at hfactor
    obtain ⟨_, _, _, _, _, _, hF, _, _, hzero⟩ := hfactor
    have haR : a ∈ ball a R := mem_ball_self hR
    rcases (hF a haR).eventually_eq_zero_or_eventually_ne_zero with hvanish | hnonzero
    · exfalso
      apply hu.not_eventually_mfderiv_eq_zero hγ ha
      filter_upwards [hvanish, isOpen_ball.mem_nhds haR] with z hz hzR
      exact (hzero z hzR).mp hz
    · filter_upwards [hnonzero,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_ball.mem_nhds haR)] with z hz hzR
      intro _ hdzero
      exact hz ((hzero z hzR).mpr hdzero)
  have hfinite := hK.finite_sdiff_of_mem_codiscreteWithin
    ((Filter.codiscreteWithin_mono hKD) hregular)
  apply hfinite.subset
  intro z hz
  exact ⟨hz.1, fun hne => hne hz.2⟩

end DifferentialGeometry.Geometry
