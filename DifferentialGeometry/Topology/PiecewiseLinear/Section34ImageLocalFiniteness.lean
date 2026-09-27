/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem exists_section34VertexBallImage_finite_neighborhood
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {y : M₂} (hy : y ∈ f₁ '' section34CutNeighborhood src) :
    ∃ O : Set M₂, IsOpen O ∧ y ∈ O ∧
      {w : Section34VertexIndex 𝒦 𝒦' |
        (section34VertexBallImage src f₁ w ∩ O).Nonempty}.Finite := by
  classical
  obtain ⟨x, hx, rfl⟩ := hy
  have : Nonempty M₁ := ⟨x⟩
  obtain ⟨-, -, -, -, -, -, -, hLF, hcover, -⟩ := id hcut
  have hNU : section34CutNeighborhood src ⊆ U := by
    rintro z hz
    obtain ⟨w, hw⟩ := mem_iUnion.mp hz
    rw [← hcover]
    exact mem_iUnion.mpr ⟨.vertexBall w, hw⟩
  obtain ⟨V, hV, hfin⟩ := hLF x (hNU hx)
  have hfinV : {w : Section34VertexIndex 𝒦 𝒦' |
      (src (.vertexBall w) ∩ V).Nonempty}.Finite := by
    apply Set.Finite.of_finite_image (f := fun w : Section34VertexIndex 𝒦 𝒦' =>
      (Section34Label.vertexBall w : Section34CutLabelOf 𝒦 𝒦'))
    · apply hfin.subset
      rintro _ ⟨w, hw, rfl⟩
      exact hw
    · intro a _ b _ hab
      simpa only [Section34Label.vertexBall.injEq] using hab
  have hpre : Function.invFunOn f₁ (section34CutNeighborhood src) ⁻¹' V ∈
      𝓝[f₁ '' section34CutNeighborhood src] (f₁ x) :=
    (hf₁.isPLOn_inverse hf₁.injOn.leftInvOn_invFunOn (f₁ x) ⟨x, hx, rfl⟩).continuousWithinAt
      |>.preimage_mem_nhdsWithin (by
        simpa only [hf₁.injOn.leftInvOn_invFunOn hx] using hV)
  obtain ⟨O, hO, hxO, hOV⟩ := mem_nhdsWithin.mp hpre
  refine ⟨O, hO, hxO, hfinV.subset ?_⟩
  rintro w ⟨z, ⟨a, ha, rfl⟩, hzO⟩
  have haN : a ∈ section34CutNeighborhood src := mem_iUnion.mpr ⟨w, ha⟩
  have haV := hOV ⟨hzO, ⟨a, haN, rfl⟩⟩
  refine ⟨a, ha, ?_⟩
  simpa only [mem_preimage, hf₁.injOn.leftInvOn_invFunOn haN] using haV

end DifferentialGeometry.Topology.PiecewiseLinear
