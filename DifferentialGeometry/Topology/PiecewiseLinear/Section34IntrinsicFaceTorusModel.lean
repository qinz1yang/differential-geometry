/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallModel
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceCellImage
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelCellRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceTetraBuffer

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

open Classical in
theorem exists_section34FaceTorus_intrinsic_model
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (s : Section34SimplexIndex 𝒦 3) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂),
      IsCombinatorialSolidTorus P ∧ IsPLHomeomorphInto 3 u P ∧
      u '' P = section34FaceTorus (section34VertexBallImage src f₁) s ∧
      u '' frontier P = frontier (section34FaceTorus (section34VertexBallImage src f₁) s) := by
  classical
  obtain ⟨n, v, -, -, hC, hnext, hdis, htriple, hcover⟩ :=
    exists_section34SourceFaceTorus_cycle hcut s
  obtain ⟨-, -, -, -, -, -, -, -, hcoverU, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hfaces⟩ := id hcut
  obtain ⟨t, hst⟩ := hfaces s
  have hbuffer := isPLBall_section34SourceTetra_union_faceTorus_model hcut s t hst
  let C : Fin (n + 3) → Set Ea := fun i =>
    𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.vertexBall (v i))
  have hCB (i : Fin (n + 3)) : C i ⊆ 𝒦.complex.space ∩ 𝒦.map ⁻¹'
      (src (.tetraBall t) ∪ section34FaceTorus (fun w => src (.vertexBall w)) s) := by
    intro x hx
    have hxS : x ∈ 𝒦.complex.space ∩
        𝒦.map ⁻¹' section34FaceTorus (fun w => src (.vertexBall w)) s :=
      hcover ▸ mem_iUnion.mpr ⟨i, hx⟩
    exact ⟨hxS.1, Or.inr hxS.2⟩
  obtain ⟨P, g, hP, hg⟩ := exists_isCombinatorialSolidTorus_model_of_cycle_in_ball
    hbuffer C hC hCB hnext hdis htriple
  rw [hcover] at hg
  let S := section34FaceTorus (fun w => src (.vertexBall w)) s
  have hSN : S ⊆ section34CutNeighborhood src := by
    rintro y hy
    obtain ⟨a, -, hya⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion.mpr ⟨a.1.2, hya⟩
  have hSU : S ⊆ U := by
    rintro y hy
    obtain ⟨a, -, hya⟩ := mem_iUnion₂.mp hy
    rw [← hcoverU]
    exact mem_iUnion.mpr ⟨.vertexBall a.1.2, hya⟩
  have hgK : MapsTo g P 𝒦.complex.space := fun x hx => (hg.bijOn.mapsTo hx).1
  have hgN : MapsTo (𝒦.map ∘ g) P (section34CutNeighborhood src) := fun x hx =>
    hSN (hg.bijOn.mapsTo hx).2
  have hfg := hgraph.2.2.1
  let u := f₁ ∘ 𝒦.map ∘ g
  have huPL : IsPLOn 3 3 u P :=
    IsPLOn.comp_of_mapsTo hfg.isPLOn (𝒦.isPLOn_comp hg.isPiecewiseAffineOn hgK) hgN
  have huinj : InjOn u P := by
    intro x hx y hy hxy
    apply hg.bijOn.injOn hx hy
    apply 𝒦.bijOn.injOn (hgK hx) (hgK hy)
    exact hfg.injOn (hgN hx) (hgN hy) hxy
  have hu : IsPLHomeomorphInto 3 u P :=
    huPL.isPLHomeomorphInto_of_isCompact hP.isPolyhedron.isCompact huinj
  have hκimage : 𝒦.map '' (𝒦.complex.space ∩ 𝒦.map ⁻¹' S) = S := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := 𝒦.bijOn.surjOn (hSU hy)
      exact ⟨x, ⟨hx, by change 𝒦.map x ∈ S; rwa [hxy]⟩, hxy⟩
  have himage : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s := by
    change (f₁ ∘ 𝒦.map ∘ g) '' P = _
    rw [image_comp, image_comp, hg.image_eq, hκimage]
    simp only [S, section34FaceTorus, section34VertexBallImage, image_iUnion]
  refine ⟨P, u, hP, hu, himage, ?_⟩
  rw [hu.image_frontier_of_isCompact hP.isPolyhedron.isCompact, himage]

end DifferentialGeometry.Topology.PiecewiseLinear
