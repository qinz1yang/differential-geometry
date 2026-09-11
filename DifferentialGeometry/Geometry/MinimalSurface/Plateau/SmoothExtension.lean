import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskTrace
import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz







noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



def SmoothDiskExtension (u : C(closedDisk, M)) (U : ℂ → M) : Prop :=
  (∀ z : closedDisk, U z = u z) ∧ ∃ N : Set ℂ, IsOpen N ∧
    Metric.closedBall (0 : ℂ) 1 ⊆ N ∧ ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U N



theorem SmoothDiskExtension.smoothUpToBoundary {u : C(closedDisk, M)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E) u U) : DiskSmoothUpToBoundary (E := E) u := by
  obtain ⟨heq, N, _, hDN, hU⟩ := h
  apply (hU.mono hDN).congr
  intro z hz
  exact (diskExtension_coe u ⟨z, hz⟩).trans (heq ⟨z, hz⟩).symm



theorem SmoothDiskExtension.comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (f : C(M, N)) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    SmoothDiskExtension (E := F) (f.comp u) (f ∘ U) := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  exact ⟨fun z => congrArg f (heq z), s, hs, hDs, hf.comp_contMDiffOn hU⟩

variable [IsManifold 𝓘(ℝ, E) ∞ M]



theorem SmoothDiskExtension.lipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {U : ℂ → M} (h : SmoothDiskExtension (E := E) u U) :
    ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := h
  have hU1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U N := hU.of_le (by simp)
  obtain ⟨L, hL⟩ := exists_compact_source_mfderiv_bound g hN hU1
    (isCompact_closedBall (0 : ℂ) 1) hDN
  refine ⟨L, fun z w => ?_⟩
  rw [← heq z, ← heq w]
  exact riemannian_edist_le_on_convex_source g hN hU1 hDN
    (convex_closedBall (0 : ℂ) 1) hL z.property w.property

end DifferentialGeometry.Geometry
