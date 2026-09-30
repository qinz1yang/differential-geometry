import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.AreaTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.AreaBridge
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MinimalDiskAreaDensityFrontier
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

theorem smoothDiskAreaDensity_of_plateauDiskDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContinuousFreeLoop Q) (h : PlateauDiskDensity (I := 𝓘(ℝ, E)) (Q := Q) g γ) :
    Geometry.SmoothDiskAreaDensity (E := E) g γ := by
  intro v hv
  obtain ⟨htr, hlip⟩ := (mem_spanningDiskCompetitors_iff g γ v).mp hv
  let v' : DiskCompetitor g γ := ⟨⟨v, hlip⟩, htr⟩
  obtain ⟨w, hwtr, htend⟩ := h v'
  have hdata (j : ℕ) : ∃ U : ℂ → Q, Geometry.SmoothDiskExtension (E := E) (w j).map U :=
    (Geometry.diskSmoothUpToBoundary_iff_exists_smoothDiskExtension (w j).map).mp
      (SmoothDisk.diskSmoothUpToBoundary (w j))
  choose U hU using hdata
  have htend' : Tendsto (fun j => Geometry.riemannianDiskArea g ((w j).map)) atTop
      (𝓝 (Geometry.riemannianDiskArea g v)) := by
    have hv' : ⇑v'.1.map = v := rfl
    have hflat : (fun j => diskArea g (w j).map) =
        fun j => Geometry.riemannianDiskArea g ((w j).map) := by
      funext j
      exact diskArea_eq_riemannianDiskArea g ((w j).map)
    have htarget : diskArea g v'.1.map = Geometry.riemannianDiskArea g v := by
      rw [hv']
      exact diskArea_eq_riemannianDiskArea g v
    rw [hflat, htarget] at htend
    exact htend
  exact Geometry.diskAreaDensityAt_of_tendsto g (fun j => hU j)
    (fun j => (diskTrace_eq_iff (w j).map γ).mpr (hwtr j)) htend'

omit [FiniteDimensional ℝ E] in
theorem plateauDiskDensity_of_smoothDiskAreaDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (γ : ContinuousFreeLoop Q) (h : Geometry.SmoothDiskAreaDensity (E := E) g γ) :
    PlateauDiskDensity (I := 𝓘(ℝ, E)) (Q := Q) g γ := by
  intro v
  have hv : v.1.map ∈ Geometry.spanningDiskCompetitors g γ :=
    (mem_spanningDiskCompetitors_iff g γ v.1.map).mpr
      ⟨v.2, v.1.isLipschitz⟩
  obtain ⟨vj, Uj, hdata, htend⟩ :=
    Geometry.exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_density g h hv
  refine ⟨fun j => smoothDiskOfSmoothDiskExtension (hdata j).1, ?_, ?_⟩
  · intro j θ
    have hmap : ⇑(smoothDiskOfSmoothDiskExtension (hdata j).1).map = vj j := rfl
    rw [hmap]
    exact (diskTrace_eq_iff (vj j) γ).mp (hdata j).2 θ
  · have hflat : (fun j => diskArea g
        (⇑(smoothDiskOfSmoothDiskExtension (hdata j).1).map)) =
        fun j => Geometry.riemannianDiskArea g (vj j) := by
      funext j
      exact diskArea_eq_riemannianDiskArea g (vj j)
    have htarget : diskArea g v.1.map = Geometry.riemannianDiskArea g ((v.1.map : Disk → Q)) :=
      diskArea_eq_riemannianDiskArea g (v.1.map : Disk → Q)
    rw [hflat, htarget]
    exact htend

theorem smoothDiskAreaDensity_of_subsingleton [Subsingleton Q] [Nonempty Q]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : ContinuousFreeLoop Q) :
    Geometry.SmoothDiskAreaDensity (E := E) g γ :=
  smoothDiskAreaDensity_of_plateauDiskDensity g γ (plateauDiskDensity_of_subsingleton g γ)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
