/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelTopology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

theorem Section34CutFrame.exists_vertex_pair_cell
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (a b : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
    (hinter : src (.vertexBall a) ∩ src (.vertexBall b) = src (.splitDisk e)) :
    ∃ B, IsPLCellOn 3
      (section34VertexBallImage src f₁ a ∪ section34VertexBallImage src f₁ b) B := by
  obtain ⟨-, -, -, hcell, -, -, -, -, hcover, -⟩ := id hcut
  have hsrcU (l : Section34CutLabelOf 𝒦 𝒦') : src l ⊆ U := by
    rw [← hcover]
    exact subset_iUnion src l
  let A := 𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.vertexBall a)
  let B := 𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.vertexBall b)
  have hA : IsPLBall 3 A := 𝒦.isPLBall_preimage_of_isPLCellOn
    (hcell (.vertexBall a)) (hsrcU (.vertexBall a))
  have hB : IsPLBall 3 B := 𝒦.isPLBall_preimage_of_isPLCellOn
    (hcell (.vertexBall b)) (hsrcU (.vertexBall b))
  have hI : IsPLBall 2 (A ∩ B) := by
    have heq : A ∩ B = 𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.splitDisk e) := by
      rw [← hinter]
      ext x
      simp only [A, B, mem_inter_iff, mem_preimage]
      tauto
    rw [heq]
    exact 𝒦.isPLBall_preimage_of_isPLCellOn (hcell (.splitDisk e)) (hsrcU (.splitDisk e))
  have hball := 𝒦.isPLBall_union_of_inter_isPLBall_two hA hB
    inter_subset_left inter_subset_left hI
  obtain ⟨Bd, hAB⟩ := 𝒦.exists_isPLCellOn_image
    (union_subset inter_subset_left inter_subset_left) (by decide : 3 ≤ 3) hball
  have himage : 𝒦.map '' (A ∪ B) = src (.vertexBall a) ∪ src (.vertexBall b) := by
    have hpart (w : Section34VertexIndex 𝒦 𝒦') :
        𝒦.map '' (𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.vertexBall w)) =
          src (.vertexBall w) := by
      apply Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact hx.2
      · intro y hy
        obtain ⟨x, hx, hxy⟩ := 𝒦.bijOn.surjOn (hsrcU (.vertexBall w) hy)
        exact ⟨x, ⟨hx, by change 𝒦.map x ∈ src (.vertexBall w); rwa [hxy]⟩, hxy⟩
    rw [image_union, hpart a, hpart b]
  rw [himage] at hAB
  have hN : src (.vertexBall a) ∪ src (.vertexBall b) ⊆ section34CutNeighborhood src :=
    union_subset (subset_iUnion (fun w => src (.vertexBall w)) a)
      (subset_iUnion (fun w => src (.vertexBall w)) b)
  have htarget := hAB.image_of_subset hf₁ hN
  rw [image_union] at htarget
  exact ⟨f₁ '' Bd, htarget⟩

end DifferentialGeometry.Topology.PiecewiseLinear
