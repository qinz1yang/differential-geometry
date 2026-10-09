import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceTypes
import DifferentialGeometry.Geometry.Curvature.Surface.FiniteFlatCoverApplications

/-!
# Complete finite surface classification and flat Euclidean cover

The finite surface row keeps the actual compact smooth types and the noncompact soul-based
homeomorphisms. Its flat clause supplies a simply connected Euclidean covering with finite
local diffeomorphism regularity and literal derivative metric preservation, without orientation.
-/

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry.Geometry.Collapse

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

theorem finiteSurface_complete_row
  {r : ℕ∞}
  (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
    (TangentSpace (𝓡 2) : Z → Type _)) (hr : 3 ≤ r)
  (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x),
    ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
  (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    (∀ _o : ManifoldOrientation (𝓡 2) Z 2,
    (Nonempty (Z ≃ₜ S2) ∨
      (Nonempty (Z ≃ₜ T2) ∧
        ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0) ∨
      Nonempty (Z ≃ₜ E2) ∨ Nonempty (Z ≃ₜ AddCircle (1 : ℝ) × ℝ)) ∧
    ((CompactSpace Z ∧ (Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) ∨
      (Nonempty (Z ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ T2) ∧
        ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0))) ∨
      (NoncompactSpace Z ∧
        (Nonempty (Z ≃ₜ E2) ∨ Nonempty (Z ≃ₜ AddCircle (1 : ℝ) × ℝ))))) ∧
    ((∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0) →
      ∃ f : E2 → Z, SimplyConnectedSpace E2 ∧ ContMDiff (𝓡 2) (𝓡 2) r f ∧
        IsLocalDiffeomorph (𝓡 2) (𝓡 2) r f ∧
        (∀ x v w, k.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x v)
          (mfderiv (𝓡 2) (𝓡 2) f x w) = inner ℝ v w) ∧
        IsCoveringMap f ∧ Function.Surjective f) := by
  refine ⟨fun o => ⟨finiteSurface_homeomorph_types o k hr hnorm hK,
    finiteSurface_types o k hr hnorm hK⟩, ?_⟩
  intro hflat
  exact FiniteFlatSurface.exists_universalEuclideanCover_of_finite_flat k hr hnorm hflat

theorem euclideanFiniteMetric_complete_row :
    (∀ _o : ManifoldOrientation (𝓡 2) E2 2,
    (Nonempty (E2 ≃ₜ S2) ∨
      (Nonempty (E2 ≃ₜ T2) ∧
        ∀ x (v w : TangentSpace (𝓡 2) x),
          FiniteFlatSurface.euclideanFiniteMetric.sectionalCurvature x v w = 0) ∨
      Nonempty (E2 ≃ₜ E2) ∨ Nonempty (E2 ≃ₜ AddCircle (1 : ℝ) × ℝ)) ∧
    ((CompactSpace E2 ∧ (Nonempty (E2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) ∨
      (Nonempty (E2 ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ T2) ∧
        ∀ x (v w : TangentSpace (𝓡 2) x),
          FiniteFlatSurface.euclideanFiniteMetric.sectionalCurvature x v w = 0))) ∨
      (NoncompactSpace E2 ∧
        (Nonempty (E2 ≃ₜ E2) ∨ Nonempty (E2 ≃ₜ AddCircle (1 : ℝ) × ℝ))))) ∧
      ∃ f : E2 → E2, SimplyConnectedSpace E2 ∧ ContMDiff (𝓡 2) (𝓡 2) 3 f ∧
        IsLocalDiffeomorph (𝓡 2) (𝓡 2) 3 f ∧
        (∀ x v w, FiniteFlatSurface.euclideanFiniteMetric.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x v)
          (mfderiv (𝓡 2) (𝓡 2) f x w) = inner ℝ v w) ∧
        IsCoveringMap f ∧ Function.Surjective f := by
  have hnorm : ∀ (x : E2) (v : TangentSpace (𝓡 2) x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (FiniteFlatSurface.euclideanFiniteMetric.inner x v v)) := by
    intro x v
    change ‖(v : E2)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (v : E2) v))
    rw [← norm_eq_sqrt_real_inner, ofReal_norm]
  have hK : ∀ x (v w : TangentSpace (𝓡 2) x),
      0 ≤ FiniteFlatSurface.euclideanFiniteMetric.sectionalCurvature x v w := by
    intro x v w
    rw [FiniteFlatSurface.euclideanFiniteMetric_flat]
  have hrow := finiteSurface_complete_row (r := 3)
    FiniteFlatSurface.euclideanFiniteMetric le_rfl hnorm hK
  exact ⟨hrow.1, hrow.2 FiniteFlatSurface.euclideanFiniteMetric_flat⟩

end DifferentialGeometry.Geometry.Collapse
