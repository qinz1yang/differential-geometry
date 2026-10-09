import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Analysis.ODE.AreaUpperBarrier

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Analysis
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

def hasExteriorDiskComparisonsAfter {P : OrientedThreeStage.{u}} {g : P.Metric}
    (O : ObservationTower P g) (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) : Prop :=
  ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ →
      (∀ u : C(closedDisk, (postStage O t₀).Carrier), isExteriorSpanningDisk (W t₀) (γ t₀ ht₀) u →
        Geometry.riemannianDiskArea (postMetric O t₀) u = exteriorDiskArea O W T γ t₀ →
        ∃ v : C(closedDisk, (postStage O t).Carrier), isExteriorSpanningDisk (W t) (γ t ht) v ∧
          Geometry.riemannianDiskArea (postMetric O t) v ≤ Real.exp ε * Geometry.riemannianDiskArea (postMetric O t₀) u) ∧
      (∀ v : C(closedDisk, (postStage O t).Carrier), isExteriorSpanningDisk (W t) (γ t ht) v →
        Geometry.riemannianDiskArea (postMetric O t) v = exteriorDiskArea O W T γ t →
        ∃ u : C(closedDisk, (postStage O t₀).Carrier), isExteriorSpanningDisk (W t₀) (γ t₀ ht₀) u ∧
          Geometry.riemannianDiskArea (postMetric O t₀) u ≤ Real.exp ε * Geometry.riemannianDiskArea (postMetric O t) v)

theorem continuousOn_exteriorDiskArea_of_local_comparisons
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (O : ObservationTower P g) (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)
    (hmin : hasExteriorDiskMinimizersAfter O W T γ)
    (hcomp : hasExteriorDiskComparisonsAfter O W T γ) :
    ContinuousOn (exteriorDiskArea O W T γ) (Ici T) := by
  apply continuousOn_leastExteriorDiskArea_of_local_disk_comparisons
    (fun t => (postStage O t).Carrier) (postMetric O) W T γ
  · intro t ht
    simpa only [exteriorDiskArea_eq O W T γ t ht] using hmin t ht
  · intro t₀ ht₀ ε hε
    obtain ⟨δ, hδ, hc⟩ := hcomp t₀ ht₀ ε hε
    refine ⟨δ, hδ, ?_⟩
    intro t ht hd
    simpa only [exteriorDiskArea_eq O W T γ t₀ ht₀, exteriorDiskArea_eq O W T γ t ht]
      using hc t ht hd


end GC.LongTime
