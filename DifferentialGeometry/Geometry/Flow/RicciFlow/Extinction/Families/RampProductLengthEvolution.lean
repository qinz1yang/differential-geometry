import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductLengthEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampLengthEvolution

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [T2Space Q] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

theorem ramp_length_evolution (B : RicciBackground (I := I) (M := Q) D a b) :
    RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B := by
  intro lambda hlambda _ c hsol s t has hst htb
  have h := c.length_energy_bounds B lambda hlambda (uniqueDiffOn_Icc B.lt) hsol
    B.lt Subset.rfl Subset.rfl
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hs : s ∈ Icc a b := ⟨has, hst.trans htb⟩
  refine ⟨h.1.continuousOn.mono hsub, (h.2.1.mono hsub).intervalIntegrable_of_Icc hst,
    fun v _ => productCurve_energy_nonneg c B.family.metric lambda v,
    (h.2.2 s hs t ⟨hst, htb⟩).2, ?_⟩
  intro v hv
  exact (h.2.2 s hs v ⟨hv.1, hv.2.trans htb⟩).1

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
