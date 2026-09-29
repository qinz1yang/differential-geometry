import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.InteriorDiskTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ConformalDiskFromMorrey

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
  [T2Space Q] [T2Space A] [I.Boundaryless]

theorem hasConformalMinimizingInteriorDisk_of_diffeomorph
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (gamma : RegularLoop I Q)
    (h : HasConformalMinimizingInteriorDisk (Diffeomorph.pullbackMetricCross g Φ.symm)
      (gamma.postcomposeDiffeomorph Φ)) : HasConformalMinimizingInteriorDisk g gamma := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hminL, hminS⟩ := h
  let v := InteriorSmoothDisk.compDiffeomorph Φ.symm u
  refine ⟨v, u.isConformal_comp_diffeomorph_symm Φ g hconf,
    u.isHarmonic_comp_diffeomorph_symm Φ g hharm, ?_, ?_, ?_, ?_⟩
  · have ht := htrace.comp_diffeomorph Φ.symm
    have heq : (⟨Φ.symm, Φ.symm.continuous⟩ : C(A, Q)).comp
        (gamma.postcomposeDiffeomorph Φ).toContinuousLoop = gamma.toContinuousLoop := by
      ext z
      exact Φ.symm_apply_apply (gamma z)
    rw [heq] at ht
    exact ht
  · exact hfinite.congr_fun_ae (diskJacobian_pullbackMetricCross_ae g Φ u.map)
  · intro w hw
    obtain ⟨w', _, _, harea⟩ :=
      exists_spanning_disk_of_postcomposeDiffeomorph g Φ gamma.toContinuousLoop w hw
    calc diskArea g v.map = diskArea (Diffeomorph.pullbackMetricCross g Φ.symm) u.map :=
        (diskArea_pullbackMetricCross g Φ.symm u.map).symm
      _ ≤ diskArea (Diffeomorph.pullbackMetricCross g Φ.symm) w'.1.map := hminL w'.1 w'.2
      _ = diskArea g w.map := harea
  · intro w hw
    let w' := SmoothDisk.compDiffeomorph Φ w
    have htr : ∀ theta, w'.map (diskBoundary theta) = (gamma.postcomposeDiffeomorph Φ) theta :=
      fun theta => congrArg Φ (hw theta)
    calc diskArea g v.map = diskArea (Diffeomorph.pullbackMetricCross g Φ.symm) u.map :=
        (diskArea_pullbackMetricCross g Φ.symm u.map).symm
      _ ≤ diskArea (Diffeomorph.pullbackMetricCross g Φ.symm) w'.map := hminS w' htr
      _ = diskArea g w.map := by
        rw [diskArea_pullbackMetricCross]
        congr 1
        funext z
        exact Φ.symm_apply_apply (w.map z)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
