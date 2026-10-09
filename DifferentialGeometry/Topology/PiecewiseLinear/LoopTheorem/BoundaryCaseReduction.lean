/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWitnessDoors
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ResolvedCellNormal
import DifferentialGeometry.Topology.PiecewiseLinear.SeamBoundaryHomotopy

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_descendingSurgery_of_crossSeamTube_reversing [T2Space M]
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) {G cell : SingularTwoCell M}
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hGim : ⇑G '' G.domain ⊆ ⇑D '' D.domain)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
    (hGinj : ∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn G V)
    (hGfiber : ∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2)
    (hGboundary : Set.range ⇑G.boundary ⊆ B)
    (hGimage : ⇑G '' G.domain ∩ BdM = Set.range ⇑G.boundary)
    (hGcrossing : ∀ y ∈ doublePointSet G G.domain, y ∉ U →
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ ⇑G ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y))
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (origin : hGd.singularSet.Branch → hD.singularSet.Branch)
    (hinj : Function.Injective origin) (hmiss : ∀ b, origin b ≠ c)
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
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  classical
  let R : CrossSeamRegluedData T G :=
    { cell := cell, domain_eq := hdomain, coord := coord, bijOn_coord := hcoord,
      reglued_eq := hreglued, resolved_eq := hresolved, eqOn_compl := hcompl }
  have hdouble : doublePointSet cell cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c :=
    R.doublePointSet_cell_eq hGD
  have hcell : NormalSingularCellData cell BdM B :=
    R.normalOfTube hGD hGinj hGfiber hGboundary hGimage hGcrossing hendDisks hends htubeBdM
      hBdM
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
  exact exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_injection hGd origin
    hinj hmiss
    (crossSeamResolutionDataOfTube (T := T) (G := G) R hcell hGim hGD
      (hD.deletedBranchEquiv hcell c hdouble)
      fun b => hD.branchCarrier_deletedBranchEquiv hcell c hdouble b)
    σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN Wdirect Wcross

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
