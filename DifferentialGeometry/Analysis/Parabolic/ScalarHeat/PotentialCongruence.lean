import DifferentialGeometry.Analysis.Parabolic.ScalarHeat.TimeDependent

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem congr
    {D : RealTimeInterval} {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    {V u v : ℝ → M → ℝ} (hu : IsHeatPotOn D G V u)
    (huv : ∀ t ∈ D.carrier, ∀ x : M, u t x = v t x) :
    IsHeatPotOn D G V v where
  jointSmooth := hu.jointSmooth.congr (fun p hp => (huv p.1 (D.regular_subset hp.1) p.2).symm)
  jointCont := hu.jointCont.congr (fun p hp => (huv p.1 hp.1 p.2).symm)
  sliceSmooth t ht := (hu.sliceSmooth t ht).congr (fun x => (huv t ht x).symm)
  equation t ht x := by
    have hfun : u t = v t := funext (huv t (D.regular_subset ht))
    have heventually : (fun s => v s x) =ᶠ[nhds t] fun s => u s x := by
      filter_upwards [D.regular_mem_nhds ht] with s hs
      exact (huv s hs x).symm
    have h := (hu.equation t ht x).congr_of_eventuallyEq heventually
    rwa [hfun] at h

end DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
