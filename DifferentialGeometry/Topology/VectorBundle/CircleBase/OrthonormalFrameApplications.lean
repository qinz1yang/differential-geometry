import DifferentialGeometry.Topology.VectorBundle.CircleBase.OrthonormalFrame
import DifferentialGeometry.Topology.VectorBundle.FrameTrivialization

/-!
# Consumer of P1a: oriented rank-two bundles over the circle are isometrically trivial

With the built 51-F (`exists_normPreserving_trivialization_of_orthonormal`), the frame of P1a
(`exists_orthonormal_frame_of_orientable_totalSpace_circle`) identifies a smooth Riemannian rank-two
bundle over `S¹ = AddCircle 1` with orientable total space with `S¹ × ℝ²`, by a smooth
diffeomorphism of total spaces that covers the identity and is an isometry on every fibre
(`exists_normPreserving_trivialization_of_orientable_totalSpace_circle`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology.VectorBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]

/-- **Oriented rank-two bundles over the circle are isometrically trivial.** A smooth Riemannian
rank-two bundle over `AddCircle 1` whose total space carries a smooth orientation is identified with
`S¹ × ℝ²` by a smooth diffeomorphism of total spaces over the identity that preserves fibre
norms. -/
theorem exists_normPreserving_trivialization_of_orientable_totalSpace_circle
    (hF : Module.finrank ℝ F = 2)
    (oV : DifferentialGeometry.Topology.Manifold.SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (TotalSpace F V)) :
    ∃ Φ : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
        (TotalSpace (EuclideanSpace ℝ (Fin 2))
          (Trivial (AddCircle (1 : ℝ)) (EuclideanSpace ℝ (Fin 2))))
        (TotalSpace F V) ∞,
      (∀ z, (Φ z).proj = z.proj) ∧ ∀ z, ‖(Φ z).2‖ = ‖z.2‖ := by
  obtain ⟨s, hs, hon⟩ := exists_orthonormal_frame_of_orientable_totalSpace_circle hF oV
  obtain ⟨Φ, hΦ, hn⟩ := exists_normPreserving_trivialization_of_orthonormal hF s hs hon
  exact ⟨Φ, fun z => congrArg TotalSpace.proj (hΦ z.proj z.2), hn⟩

end DifferentialGeometry.Topology.VectorBundle
