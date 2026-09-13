import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskTrace
import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import DifferentialGeometry.Topology.Manifold.SmoothExtension







noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ComplexConjugate ENNReal NNReal

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

theorem SmoothDiskExtension.eventuallyEq_diskExtension {u : C(closedDisk, M)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E) u U) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    U =ᶠ[𝓝 z] diskExtension u := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := h
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  have hwD : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hw
  rw [diskExtension_coe u ⟨w, hwD⟩]
  exact heq ⟨w, hwD⟩

theorem SmoothDiskExtension.comp_diskReflection {u : C(closedDisk, M)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E) u U) :
    SmoothDiskExtension (E := E) (u.comp ⟨diskReflection, diskReflection.continuous⟩) (U ∘ conj) := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := h
  refine ⟨fun z => ?_, conj ⁻¹' N, hN.preimage Complex.continuous_conj, fun z hz => ?_, ?_⟩
  · have hc : conj (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using z.property
    have hz' : (⟨conj (z : ℂ), hc⟩ : closedDisk) = diskReflection z := Subtype.ext rfl
    have huse := heq ⟨conj (z : ℂ), hc⟩
    rw [hz'] at huse
    change U (conj (z : ℂ)) = u (diskReflection z)
    exact huse
  · exact hDN (by simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz)
  · exact hU.comp ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contMDiff.contMDiffOn) (fun z hz => hz)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_smoothDiskExtension_of_locally_extendable
    (u : C(closedDisk, M))
    (hloc : ∀ x : closedDisk, ∃ U : ℂ → M, ∃ V : Set ℂ,
      IsOpen V ∧ (x : ℂ) ∈ V ∧ ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U V ∧
        ∀ y : closedDisk, (y : ℂ) ∈ V → U y = u y) :
    ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U := by
  obtain ⟨U, _, heq, N, hN, hKN, hUs⟩ :=
    DifferentialGeometry.Topology.exists_contMDiffOn_extension_closedBall
      (I := 𝓘(ℝ, E)) (n := ⊤) (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) u hloc
  exact ⟨U, heq, N, hN, hKN, hUs⟩




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
