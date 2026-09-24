import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance comparisonTimeComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem MetricComparisonOn.jet_contDiffOn_of_solutions
    {D₁ D₂ : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D₁) (hS : IsSolutionOn S)
    (T : SolutionOn (I := I3) (M := M) D₂) (hT : IsSolutionOn T)
    {a₁ a₂ c b : ℝ} (ha₁ : a₁ < c) (ha₂ : a₂ < c) (hcb : c < b)
    (hSdomain : Icc a₁ b ⊆ D₁.carrier) (hSregular : Ioo a₁ b ⊆ D₁.regular)
    (hTdomain : Icc a₂ b ⊆ D₂.carrier) (hTregular : Ioo a₂ b ⊆ D₂.regular)
    {F : N → M} {U : Set N} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn S.base.metric T.base.metric F U (Icc c b) order eps)
    (q : ℕ) (y : N) (hy : y ∈ U) (v : Fin 2 → TangentSpace I y) :
    ContDiffOn ℝ ∞ (fun s => C.jet q s y v) (Icc c b) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let : Subsingleton E := hE
    let : Subsingleton (TangentSpace I y) := inferInstanceAs (Subsingleton E)
    have hz : (fun s => C.jet q s y v) = fun _ => 0 := by
      funext s
      exact (C.jet q s y).map_coord_zero 0 (Subsingleton.elim (v 0) 0)
    rw [hz]
    exact contDiffOn_const
  · let : Nontrivial E := hE
    let : NeZero (Module.finrank ℝ E) := ⟨ne_of_gt (Module.finrank_pos (R := ℝ) (M := E))⟩
    let w : Fin 2 → TangentSpace I3 (F y) := fun j => mfderiv I I3 F y (v j)
    have htarget := (tensor0SEvalCLM (I := I3) (x := F y) w).contDiff.comp_contDiffOn
      (metricTensor_contDiffOn_time T hT ha₂ hcb hTdomain hTregular (F y))
    have hsource := (tensor0SEvalCLM (I := I) (x := y) v).contDiff.comp_contDiffOn
      (metricTensor_contDiffOn_time S hS ha₁ hcb hSdomain hSregular y)
    have hzero : ContDiffOn ℝ ∞ (fun s => C.jet 0 s y v) (Icc c b) := by
      apply (htarget.sub hsource).congr
      intro s _hs
      rw [C.jet_zero s y v, C.pullback_eq s y hy v]
      rfl
    intro s hs
    exact DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower
      (f := fun b r => C.jet b r y v) (uniqueDiffOn_Icc hcb) hs
      (hzero s hs) (fun b r hr => C.jet_succ b r hr y hy v) q

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
