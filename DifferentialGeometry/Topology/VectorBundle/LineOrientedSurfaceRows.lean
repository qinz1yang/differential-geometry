import DifferentialGeometry.Topology.VectorBundle.UnitTangentCover
import DifferentialGeometry.Topology.VectorBundle.LineSurfaceRows

/-!
# The orientable surface rows from an oriented actual total space

The unit sphere is the actual tangent orientation cover. A base orientation makes this cover
split, so its disconnectedness is derived before the smooth line trivialization and the
original-metric sphere or flat-torus classification are applied.
-/

set_option autoImplicit false

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.VectorBundle

variable {F : Type*} [fibreNormGroup : NormedAddCommGroup F] [fibreNormSpace : NormedSpace ℝ F]
    [fibreFinite : FiniteDimensional ℝ F]
  {B : Type*} [baseTopology : TopologicalSpace B]
  [baseCharts : ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
  [baseManifold : IsManifold (𝓡 2) ∞ B] [baseCompact : CompactSpace B] [baseT2 : T2Space B]
    [baseConnected : ConnectedSpace B]
  {V : B → Type*} [totalTopology : TopologicalSpace (TotalSpace F V)]
  [fibreGroups : ∀ b, NormedAddCommGroup (V b)]
  [fibreInnerProducts : ∀ b, InnerProductSpace ℝ (V b)]
  [fibreBundle : FiberBundle F V] [vectorBundle : VectorBundle ℝ F V] [smoothBundle :
    ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [smoothMetric : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

theorem exists_oriented_total_surface_line_rows (o : ManifoldOrientation (𝓡 2) B 2)
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : ContMDiffRiemannianMetric (𝓡 2) n (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : B → Type _))
    (hK : ∀ (b : B) (v w : TangentSpace (𝓡 2) b), 0 ≤ k.sectionalCurvature b v w)
    (hF : finrank ℝ F = 1)
    (oTotal : ManifoldOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) :
    (∃ Ψ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        EuclideanSpace ℝ (Fin 1)) ≃ₘ⟮(𝓡 2).prod (𝓡 1),
          (𝓡 2).prod 𝓘(ℝ, F)⟯ TotalSpace F V,
      ∀ z, ‖(Ψ z).2‖ = ‖z.2‖) ∨
    ((∃ Ψ : ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ×
        EuclideanSpace ℝ (Fin 1)) ≃ₘ⟮
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 1),
          (𝓡 2).prod 𝓘(ℝ, F)⟯ TotalSpace F V,
      ∀ z, ‖(Ψ z).2‖ = ‖z.2‖) ∧
      ∀ (b : B) (v w : TangentSpace (𝓡 2) b), k.sectionalCurvature b v w = 0) := by
  let continuousMetric : IsContinuousRiemannianBundle F V := by
    obtain ⟨g, hg, heq⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := 𝓡 2) (n := ∞) (F := F) (E := V)
    exact ⟨g, hg.continuous, heq⟩
  have hS := sphere_not_preconnected_of_total_and_base_orientation
    (EB := EuclideanSpace ℝ (Fin 2)) (V := V) (by simp) hF oTotal o
  exact exists_orientable_surface_line_rows o hn k hK hF hS

end DifferentialGeometry.Topology.VectorBundle
