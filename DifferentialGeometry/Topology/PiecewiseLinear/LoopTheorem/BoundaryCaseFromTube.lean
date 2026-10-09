/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundarySurgeryCellPredicate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

private theorem exists_resolved_surgery_with_boundaryWordWitness
    [T2Space M] {U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) {G cell : SingularTwoCell M}
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hG : hD.IsCrossRegluedCell c G)
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {W : Set M} (hside : MapsTo (⇑D) D.domain W)
    (htubeW : T.chart '' spliceCylinder ⊆ W)
    (hbufferD : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hendBuffer : ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z)
    {X : Type v} [TopologicalSpace X] {ρ : X → M}
    (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ) {word : freeLoop X}
    (Wraw : BoundaryWordWitness G ρ word)
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂)
    (hcover : Ω₁ ∪ Ω₂ = univ)
    (hcocont : ContinuousOn (fun θ => coord ↑(Wraw.param θ)) Ω₁)
    (hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder)
    (hΩ₁max : ∀ θ, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder → θ ∈ Ω₁)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (coord ↑(Wraw.param θ)).2.1 ∈ spliceSquareBoundary) :
    ∃ Sg : hD.DescendingSurgery,
      MapsTo (⇑Sg.cell) Sg.cell.domain W ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
      Nonempty (BoundaryWordWitness Sg.cell ρ word) := by
  classical
  have hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder := by
    rw [hD.doublePointSet_eq_of_isCrossRegluedCell hG]
  let Rdata : CrossSeamRegluedData T G :=
    { cell := cell, domain_eq := hdomain, coord := coord, bijOn_coord := hcoord,
      reglued_eq := hreglued, resolved_eq := hresolved, eqOn_compl := hcompl }
  have hdouble : doublePointSet cell cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c :=
    Rdata.doublePointSet_cell_eq hGD
  have hcell : NormalSingularCellData cell BdM B :=
    Rdata.normalOfTube hGD (hD.locallyInjective_of_isCrossRegluedCell hG)
      (hD.fiber_le_two_of_isCrossRegluedCell hG)
      (hD.range_boundary_subset_of_isCrossRegluedCell hG)
      (hD.image_inter_boundary_of_isCrossRegluedCell hG)
      (hD.crossing_outside_of_isCrossRegluedCell hG T.branchCarrier_subset_tube) hendDisks
      hends htubeBdM hBdM
  have hdom : ∀ θ : loopCircle, (Wraw.param θ : EuclideanSpace ℝ (Fin 2)) ∈ G.domain :=
    fun θ => G.frontier_subset_domain (Wraw.param θ).2
  have hmem₁ : ∀ θ ∈ Ω₁, (Wraw.param θ : EuclideanSpace ℝ (Fin 2)) ∈
      G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder) :=
    fun θ hθ => ⟨hdom θ, hΩ₁tube θ hθ⟩
  have hrest : ∀ θ ∈ Ω₂, ⇑cell ↑(Wraw.param θ) = ⇑G ↑(Wraw.param θ) := by
    intro θ hθ
    by_cases hcyl : ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder
    · have hmem : (Wraw.param θ : EuclideanSpace ℝ (Fin 2)) ∈
          G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder) := ⟨hdom θ, hcyl⟩
      have hq : coord ↑(Wraw.param θ) ∈ bentSource := hcoord.mapsTo hmem
      have hlat := hlateral θ ⟨hΩ₁max θ hcyl, hθ⟩
      have hmodel : crossSeamResolve (coord ↑(Wraw.param θ)) =
          crossSeamInclude (coord ↑(Wraw.param θ)) :=
        ((crossSeamResolveHomotopy_one _).symm.trans
            (crossSeamResolveHomotopy_eq_of_mem_lateral 1 hq hlat)).trans
          ((crossSeamResolveHomotopy_eq_of_mem_lateral 0 hq hlat).symm.trans
            (crossSeamResolveHomotopy_zero _))
      exact (hresolved hmem).trans ((congrArg T.chart hmodel).trans (hreglued hmem).symm)
    · exact hcompl ⟨hdom θ, hcyl⟩
  have hdisk : T.chart '' spliceEndDisks ⊆ Set.range ρ := Subset.trans hendDisks hrange
  obtain ⟨Wcross⟩ := exists_boundaryWordWitness_of_crossSeamBoundary (cell := cell) hρ hdomain
    T.isTube.continuousOn_chart Wraw hΩ₁ hΩ₂ hcover
    (co := fun θ => coord ↑(Wraw.param θ)) hcocont (fun θ hθ => hcoord.mapsTo (hmem₁ θ hθ))
    (fun θ hθ => hreglued (hmem₁ θ hθ)) (fun θ hθ => hresolved (hmem₁ θ hθ)) hrest hlateral
    (fun θ hθ => (hends _ (hmem₁ θ hθ)).mp (Wraw.param θ).2) hdisk
  have hcellside : MapsTo (⇑cell) cell.domain W := by
    intro z hz
    have hzG : z ∈ G.domain := hdomain ▸ hz
    by_cases hzTube : G z ∈ T.chart '' spliceCylinder
    · exact htubeW (Rdata.mapsTo_cell_tube ⟨hzG, hzTube⟩)
    · obtain ⟨y, hy, heq⟩ := hD.image_subset_of_isCrossRegluedCell hG
        ⟨z, hzG, (hcompl ⟨hzG, hzTube⟩).symm⟩
      exact heq ▸ hside hy
  have hcellbuffer : ∀ z ∈ Set.range cell.boundary, B ∈ 𝓝[BdM] z := by
    rintro z ⟨t, rfl⟩
    have htcell : (t : EuclideanSpace ℝ (Fin 2)) ∈ cell.domain :=
      cell.frontier_subset_domain t.property
    have htG : (t : EuclideanSpace ℝ (Fin 2)) ∈ G.domain := hdomain ▸ htcell
    have htBd : cell t ∈ BdM := hBdM (hcell.boundary_image_subset ⟨t, rfl⟩)
    by_cases htTube : G t ∈ T.chart '' spliceCylinder
    · exact hendBuffer _ (htubeBdM ⟨Rdata.mapsTo_cell_tube ⟨htG, htTube⟩, htBd⟩)
    · apply hbufferD
      apply hD.image_inter_boundary.subset
      exact ⟨hD.image_subset_of_isCrossRegluedCell hG
        ⟨t, htG, (hcompl ⟨htG, htTube⟩).symm⟩, htBd⟩
  let Sg := (crossSeamResolutionDataOfTube (T := T) (G := G) Rdata hcell
    (hD.image_subset_of_isCrossRegluedCell hG) hGD
    (hD.deletedBranchEquiv hcell c hdouble)
    (fun b => hD.branchCarrier_deletedBranchEquiv hcell c hdouble b)).toDescendingSurgery
  exact ⟨Sg, hcellside, hcellbuffer, ⟨Wcross⟩⟩

theorem exists_descendingSurgery_side_buffer_of_crossSeamTube_reversing
    [T2Space M] {U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) {G cell : SingularTwoCell M}
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hG : hD.IsCrossRegluedCell c G)
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {W : Set M} (hside : MapsTo (⇑D) D.domain W)
    (htubeW : T.chart '' spliceCylinder ⊆ W)
    (hbufferD : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hendBuffer : ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z)
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm)))
    (Wraw : BoundaryWordWitness G ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ)))))
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂)
    (hcover : Ω₁ ∪ Ω₂ = univ)
    (hcocont : ContinuousOn (fun θ => coord ↑(Wraw.param θ)) Ω₁)
    (hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder)
    (hΩ₁max : ∀ θ, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder → θ ∈ Ω₁)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (coord ↑(Wraw.param θ)).2.1 ∈ spliceSquareBoundary) :
    ∃ (Sg : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier Sg.cell.domain)
      (δ : freeLoop X),
      MapsTo (⇑Sg.cell) Sg.cell.domain W ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
      (∀ θ, ρ (δ θ) = Sg.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  classical
  obtain ⟨hnormal⟩ := hD.nonempty_normalSingularCellData_of_isBoundarySurgeryCell hGd
  obtain ⟨origin, hinj, hmiss⟩ := hD.exists_branchOrigin_of_isBoundarySurgeryCell hGd hnormal
  have hdirectSide : MapsTo (⇑Gd) Gd.domain W := by
    intro z hz
    obtain ⟨y, hy, heq⟩ := hD.image_subset_of_isBoundarySurgeryCell hGd ⟨z, hz, rfl⟩
    exact heq ▸ hside hy
  have hdirectBuffer : ∀ z ∈ Set.range Gd.boundary, B ∈ 𝓝[BdM] z := by
    intro z hz
    have hzd := hnormal.image_inter_boundary.symm.subset hz
    exact hbufferD z (hD.image_inter_boundary.subset
      ⟨hD.image_subset_of_isBoundarySurgeryCell hGd hzd.1, hzd.2⟩)
  obtain ⟨Sg, hSgside, hSgbuffer, ⟨Wcross⟩⟩ :=
    exists_resolved_surgery_with_boundaryWordWitness T hdomain hcoord hreglued hresolved
      hcompl hG hendDisks hends htubeBdM hBdM hside htubeW hbufferD hendBuffer
      hρ hrange Wraw hΩ₁ hΩ₂ hcover hcocont hΩ₁tube hΩ₁max hlateral
  rcases not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b)
    hσ hτ hυ hφ γ hγ N hγN with hdir | hcross
  · exact ⟨DescendingSurgery.ofBranchInjection hD hnormal origin hinj hmiss,
      Wdirect.param, Wdirect.loop, hdirectSide, hdirectBuffer, Wdirect.realizes,
      fun h => hdir ((Wdirect.loopClassMeets_iff x N).mp h)⟩
  · exact ⟨Sg, Wcross.param, Wcross.loop, hSgside, hSgbuffer, Wcross.realizes,
      fun h => hcross ((Wcross.loopClassMeets_iff x N).mp h)⟩

theorem exists_descendingSurgery_side_buffer_of_crossSeamTube_preserving
    [T2Space M] {U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) {G cell : SingularTwoCell M}
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hG : hD.IsCrossRegluedCell c G)
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {W : Set M} (hside : MapsTo (⇑D) D.domain W)
    (htubeW : T.chart '' spliceCylinder ⊆ W)
    (hbufferD : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hendBuffer : ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z)
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ)))
    (Wraw : BoundaryWordWitness G ρ
      (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))))
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂)
    (hcover : Ω₁ ∪ Ω₂ = univ)
    (hcocont : ContinuousOn (fun θ => coord ↑(Wraw.param θ)) Ω₁)
    (hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder)
    (hΩ₁max : ∀ θ, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder → θ ∈ Ω₁)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (coord ↑(Wraw.param θ)).2.1 ∈ spliceSquareBoundary) :
    ∃ (Sg : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier Sg.cell.domain)
      (δ : freeLoop X),
      MapsTo (⇑Sg.cell) Sg.cell.domain W ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
      (∀ θ, ρ (δ θ) = Sg.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  classical
  obtain ⟨hnormal⟩ := hD.nonempty_normalSingularCellData_of_isBoundarySurgeryCell hGd
  obtain ⟨origin, hinj, hmiss⟩ := hD.exists_branchOrigin_of_isBoundarySurgeryCell hGd hnormal
  have hdirectSide : MapsTo (⇑Gd) Gd.domain W := by
    intro z hz
    obtain ⟨y, hy, heq⟩ := hD.image_subset_of_isBoundarySurgeryCell hGd ⟨z, hz, rfl⟩
    exact heq ▸ hside hy
  have hdirectBuffer : ∀ z ∈ Set.range Gd.boundary, B ∈ 𝓝[BdM] z := by
    intro z hz
    have hzd := hnormal.image_inter_boundary.symm.subset hz
    exact hbufferD z (hD.image_inter_boundary.subset
      ⟨hD.image_subset_of_isBoundarySurgeryCell hGd hzd.1, hzd.2⟩)
  obtain ⟨Sg, hSgside, hSgbuffer, ⟨Wcross⟩⟩ :=
    exists_resolved_surgery_with_boundaryWordWitness T hdomain hcoord hreglued hresolved
      hcompl hG hendDisks hends htubeBdM hBdM hside htubeW hbufferD hendBuffer
      hρ hrange Wraw hΩ₁ hΩ₂ hcover hcocont hΩ₁tube hΩ₁max hlateral
  rcases not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b)
    hσ hτ hυ hφ γ hγ N hγN with hdir | hcross
  · exact ⟨DescendingSurgery.ofBranchInjection hD hnormal origin hinj hmiss,
      Wdirect.param, Wdirect.loop, hdirectSide, hdirectBuffer, Wdirect.realizes,
      fun h => hdir ((Wdirect.loopClassMeets_iff x N).mp h)⟩
  · exact ⟨Sg, Wcross.param, Wcross.loop, hSgside, hSgbuffer, Wcross.realizes,
      fun h => hcross ((Wcross.loopClassMeets_iff x N).mp h)⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
