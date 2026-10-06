import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.HalfCollarOfEmbeddingHCOL

/-!
# Consumer of the half-collar kernel (lane S-COLLAR, G1, suffix `_HCOL`)

`halfCollar_instance_torusIcc_HCOL`: the compiled, non-trivial instance of
`halfCollar_of_boundary_embedding_general_HCOL`: `T² × [0, 1]` (model `torusModel.prod (𝓡∂ 1)`,
range the half-space `{v₂ ≥ 0}`) embedded into itself by the identity; the half-collar
`T² × [0, 1/2)` is a partial diffeomorphism of `T² × H¹` with source `halfCollarSource`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff
open Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold.Assembly

namespace DifferentialGeometry.Topology.HalfCollarHCOL

/-- **Compiled instance of the kernel: `T² × [0, 1]` collared in itself.**  The identity of
`T² × [0, 1]` (model `torusModel.prod (𝓡∂ 1)`, whose range is the half-space `{v₂ ≥ 0}`) is a smooth
embedding with `Φ (t, 0)` on the boundary; the kernel gives the half-collar
`T² × [0, 1/2) ⊆ T² × [0, 1]` as a partial diffeomorphism of `T² × H¹`. -/
theorem halfCollar_instance_torusIcc_HCOL :
    ∃ d : PartialDiffeomorph halfCollarModel halfCollarModel (Torus × EuclideanHalfSpace 1)
      (Torus × Icc (0 : ℝ) 1) ∞,
      d.source = halfCollarSource ∧ d.target = {p | (p.2 : ℝ) < 1 / 2} ∧
      ∀ (t : Torus) (s : EuclideanHalfSpace 1) (z : Icc (0 : ℝ) 1),
        s.val 0 < 1 → (z : ℝ) = s.val 0 / 2 → d (t, s) = (t, z) := by
  have h0 : ∀ t : Torus, (torusModel.prod (𝓡∂ 1)).IsBoundaryPoint ((t, iccEnd false) :
      Torus × Icc (0 : ℝ) 1) := by
    intro t
    have hb : (iccEnd false : Icc (0 : ℝ) 1) = ⊥ := by
      ext
      simp [iccEnd]
    change (t, iccEnd false) ∈ (torusModel.prod (𝓡∂ 1)).boundary (Torus × Icc (0 : ℝ) 1)
    rw [ModelWithCorners.boundary_of_boundaryless_left]
    refine ⟨trivial, ?_⟩
    rw [hb]
    exact Icc_isBoundaryPoint_bot
  have hne : ((EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) :
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ)
      ≠ 0 := by
    intro h
    have := congrArg (fun L : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ => L ((0, 0), EuclideanSpace.single 0 1)) h
    simp at this
  obtain ⟨d, hs, ht, hv⟩ := halfCollar_of_boundary_embedding_general_HCOL
    (J := torusModel.prod (𝓡∂ 1)) rfl (Or.inr ⟨_, hne, range_halfCollarModel_HCOL⟩)
    (id : Torus × Icc (0 : ℝ) 1 → Torus × Icc (0 : ℝ) 1)
    (IsSmoothEmbedding.id (I := torusModel.prod (𝓡∂ 1)) (n := ∞)) h0
  refine ⟨d, hs, ?_, hv⟩
  rw [ht, image_id]

end DifferentialGeometry.Topology.HalfCollarHCOL
