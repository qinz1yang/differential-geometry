import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Metric.Pullback.Basic



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]



theorem riemannianAreaDensity_pullback
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) {U : ℂ → M} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :
    riemannianAreaDensity (Diffeomorph.pullbackMetric g Φ) U z =
      riemannianAreaDensity g (Φ ∘ U) z := by
  have hd := mfderiv_comp z (Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU
  simp only [riemannianAreaDensity, tangentTwoJacobian, Diffeomorph.pullbackMetric_inner,
    hd]
  rfl



theorem SmoothDiskExtension.area_pullback
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) :
    riemannianDiskArea (Diffeomorph.pullbackMetric g Φ) u =
      riemannianDiskArea g ((⟨Φ, Φ.contMDiff.continuous⟩ : C(M, M)).comp u) := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  rw [riemannianDiskArea_eq_of_extension (Diffeomorph.pullbackMetric g Φ) u U heq,
    riemannianDiskArea_eq_of_extension g ((⟨Φ, Φ.contMDiff.continuous⟩ : C(M, M)).comp u) (Φ ∘ U)
      (fun z => congrArg Φ (heq z))]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro z hz
  exact riemannianAreaDensity_pullback g Φ
    (((hU z (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).mdifferentiableAt (by simp))

end DifferentialGeometry.Geometry
