import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.OpenTarget
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance

noncomputable section

open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem weaklyMonotoneDiskCompetitors_component_inclusion_iff
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (q : C(closedDisk, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) :
    q ∈ weaklyMonotoneDiskCompetitors
        (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) (loopInComponent γ) ↔
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0), M)).comp q) ∈
          weaklyMonotoneDiskCompetitors g γ := by
  constructor
  · rintro ⟨⟨τ, hτ, ht⟩, L, hL⟩
    refine ⟨⟨τ, hτ, ?_⟩, L, ?_⟩
    · ext θ
      exact congrArg Subtype.val (congrArg (fun w => w θ) ht)
    · intro x y
      simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        Metric.edistOf_restrictOpen_connCompOpen] using hL x y
  · rintro ⟨⟨τ, hτ, ht⟩, L, hL⟩
    refine ⟨⟨τ, hτ, ?_⟩, L, ?_⟩
    · ext θ
      exact congrArg (fun w => w θ) ht
    · intro x y
      rw [Metric.edistOf_restrictOpen_connCompOpen]
      exact hL x y

theorem disk_energy_values_eq_component
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    ((fun q : C(closedDisk, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)) =>
      riemannianDiskEnergy (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) q) ''
      weaklyMonotoneDiskCompetitors
        (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) (loopInComponent γ)) =
      ((fun q : C(closedDisk, M) => riemannianDiskEnergy g q) ''
        weaklyMonotoneDiskCompetitors g γ) := by
  ext a
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(⟨Subtype.val, continuous_subtype_val⟩ :
      C(connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0), M)).comp q,
      (weaklyMonotoneDiskCompetitors_component_inclusion_iff g γ q).mp hq, ?_⟩
    exact (riemannianDiskEnergy_restrictOpen g _ q).symm
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨τ, _, ht⟩ := hq.1
    let qC := diskInLoopComponent γ τ q ht
    refine ⟨qC, ?_, ?_⟩
    · exact (weaklyMonotoneDiskCompetitors_component_inclusion_iff g γ qC).mpr hq
    · exact riemannianDiskEnergy_restrictOpen g
        (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)) qC

theorem disk_energy_inf_eq_component
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    sInf ((fun q : C(closedDisk, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)) =>
      riemannianDiskEnergy (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) q) ''
      weaklyMonotoneDiskCompetitors
        (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) (loopInComponent γ)) =
      sInf ((fun q : C(closedDisk, M) => riemannianDiskEnergy g q) ''
        weaklyMonotoneDiskCompetitors g γ) :=
  congrArg sInf (disk_energy_values_eq_component g γ)

end DifferentialGeometry.Geometry
