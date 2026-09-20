/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ResolvedCellNormal
import DifferentialGeometry.Topology.PiecewiseLinear.SeamBoundaryHomotopy

/-!
# The boundary case of Moise's Lemma 2, assembled

This file contains no new geometry.  It wires together the modules that carry the boundary
branch case of Moise's Lemma 2 and states, as a single theorem, exactly what that case now
reduces to.  Every gap that is still open appears as a *named hypothesis* of
`NormalSingularCellData.exists_descendingSurgery_of_crossSeamTube_reversing`, so the whole
boundary case can be read, and counted, in one place.

## The chain that is closed

Given a normal crossing product tube `T` around a boundary branch `c` and the cross reglued
cell `G` read in the normal form of that tube:

* the double point equality of the resolved cell is obtained inside the proof from
  `CrossSeamTubeData.doublePointSet_resolved_subset` and
  `CrossSeamTubeData.doublePointSet_sdiff_image_spliceCylinder`.  It is *not* taken from
  `CrossSeamRegluedData.doublePointSet_cell_eq`, because that statement needs the bundle whose
  field `normal` is exactly what is being produced;
* `CrossSeamTubeData.normalOfResolvedCell` then makes the resolved cell normal;
* `NormalSingularCellData.deletedBranchEquiv` and
  `NormalSingularCellData.branchCarrier_deletedBranchEquiv` supply the branch correspondence
  that `crossSeamResolutionDataOfTube` asks for, so the cross candidate reaches
  `CrossSeamResolutionData` with no branch bookkeeping left open;
* `exists_boundaryWordWitness_of_crossSeamBoundary` turns a boundary word witness for the raw
  cross reglued cell into one for the resolved cell, over the same four arc word.  Its seven
  boundary trace hypotheses are derived here from the five geometric fields of the normal form
  plus a closed cover of the boundary circle, so only the cover itself stays open;
* `NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing_witness`
  selects between the cross candidate and the direct candidate by the four arc word dichotomy.

## Two hypotheses that turned out to be one

The end disk hypothesis `hdisk` of `exists_boundaryWordWitness_of_crossSeamBoundary`, that the
two end cross sections of the tube lie in the image of the inclusion `ρ` of the ambient loop
space, is *not* listed below.  It is derived from `hendDisks`, which is already a tube level
hypothesis of `CrossSeamTubeData.normalOfResolvedCell`, together with `B ⊆ Set.range ρ`.  The
two modules therefore agree: the ambient loop space has to contain the boundary surface `B`,
and once it does, the end disks are automatically in it.  In particular the end disk
hypothesis of the homotopy producer and the tube's own hypotheses are jointly satisfiable, and
the second implies the first.

## The shape of the cover that must not be used

`hrest`, the hypothesis of `exists_boundaryWordWitness_of_crossSeamBoundary` that the two cells
agree over `Ω₂`, is *not* the restriction of `CrossSeamRegluedData.eqOn_compl` to the boundary
circle, and stating `Ω₂` as the part of the circle lying off the parametrised cylinder makes
the cover hypotheses degenerate: `Ω₁ ∩ Ω₂` is then empty, so `Ω₁` and `Ω₂` are complementary
closed subsets of the connected `loopCircle`, one of them is the whole circle and the other is
empty, and `hlateral` is vacuous.  The cover is instead pinned down from the `Ω₁` side, by
`hΩ₁tube` and `hΩ₁max`, and `Ω₂` is left free; `Ω₁` the preimage of the cylinder and `Ω₂` the
closure of its complement then satisfy all of them.  Over the overlap the two cells agree not
because the resolution is not defined there but because it is *stationary* there, which is
`crossSeamResolveHomotopy_eq_of_mem_lateral` at the two times `0` and `1`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-- **The boundary case of Moise's Lemma 2, reduced to its open hypotheses.**  A normal
crossing product tube `T` around a boundary branch `c`, the cross reglued cell `G` and its
chord resolution `cell` read in the normal form of that tube, the normality facts of `G`, the
four tube level facts about the boundary of the manifold, the direct candidate `Gd` with its
branch bookkeeping, a boundary word witness for each of the two raw candidates, the closed
cover of the boundary circle along the wall of the tube, and the four arc cut of the boundary
circle of `D` together produce a single descending surgery whose boundary curve still avoids
the normal subgroup `N`.

This is Moise's endpoint reversing case; the endpoint preserving case is
`NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving_witness`
applied to the same tube data, with the same list of open hypotheses and the other two
boundary words.

Nothing geometric is proved here.  The content of the statement is that the open hypotheses
are exactly the following list, which names for each of them the file it would come from and
whether it is a genuine mathematical obligation or bookkeeping.

*The tube.*

* `T`: `LoopTheorem.CrossSeamTube`, whose `IsCrossSeamTubeProducer` is the relative regular
  neighbourhood statement that would build it.  Genuine theorem, and the largest one left.

*The cross reglued cell in the normal form of the tube, `LoopTheorem.CrossSeamTube`.*

* `hdomain`, `hcoord`, `hreglued`, `hresolved`, `hcompl`: the five geometric fields of
  `CrossSeamRegluedData`, that is, the placement of the cross reglued cell and its chord
  resolution in the normal form of the tube.  Genuine theorem; they are the statement that
  the cross reglue can be *read* in the tube.

*The cross reglued cell itself, `LoopTheorem.CutAndPaste`.*

* `hGim`: proved there, as a conclusion of
  `NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch`.  Bookkeeping.
* `hGD`, that the cross reglue changes no double point outside the parametrised cylinder: not
  recorded by that producer.  Genuine theorem.
* `hGinj`, `hGfiber`, `hGboundary`, `hGimage`: the four elementary normality facts of the
  cross reglued cell.  Genuine theorem: that producer does not assert the normality of the
  cross reglued cell at all, so these are not available to be transcribed.  Were it to assert
  it, all four would become the fields `locallyInjective`, `fiber_le_two`,
  `boundary_image_subset` and `image_inter_boundary`, which they match verbatim.
* `hGcrossing`: the normal double crossing condition at the double points of `G` lying outside
  the tube, with the extra clause that the crossing chart misses the parametrised cylinder.
  Genuine theorem, and strictly stronger than the field `crossing` of
  `NormalSingularCellData`, which carries no such clause; the extra clause is what makes the
  crossing condition survive the resolution, and it is not obtained by shrinking a chart,
  since a shrunk chart need not lie in `atlas`.

*The tube level hypotheses of `CrossSeamTubeData.normalOfResolvedCell`,
`LoopTheorem.ResolvedCellNormal`.*

* `hendDisks`, `hends`, `htubeBdM`, `hBdM`.  Genuine theorem, except `hBdM`, which is
  bookkeeping about the two boundary sets.

*The direct candidate.*

* `hGd`: the cell is produced by
  `NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch` in
  `LoopTheorem.BoundaryBranchDescent`, which returns its normality as a `Nonempty`.
  Bookkeeping.
* `ebranch`: genuine theorem, and known to be the wrong shape.  `LoopTheorem.BranchInjection`
  proves that every branch other than `c` is wholly kept or wholly lost by the direct surgery,
  which yields an *injection* `NormalSingularCellData.DescendingSurgery.ofBranchInjection` and
  not the bijection asked for here.  The selection theorem consumed below still routes the
  direct candidate through `DescendingSurgery.ofBranchEquiv`.

*The ambient loop space and the boundary homotopy, `SeamBoundaryHomotopy`.*

* `hρ`, that `ρ` is a topological embedding, and `hrange`, that the boundary surface lies in
  its image.  Bookkeeping about the choice of ambient loop space; together they supply the
  end disk hypothesis of the homotopy producer.
* `Wdirect`, `Wraw`: boundary word witnesses for the direct candidate and for the *raw* cross
  reglued cell, over the two four arc words.  Genuine theorem, and the sharpest remaining
  obligation after the tube.  Both recorded boundary descriptions are two arc words *in the
  manifold*: `NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` ends in
  `∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ` with `σ ω` paths of `M`, and
  `NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch` ends the same
  way.  A witness asks instead for a word of the ambient loop space `X`, and for four arcs;
  the passage from `M` to `X` is what `ρ` is for, the passage from two arcs to four is the
  obligation.
* `hΩ₁`, `hΩ₂`, `hcover`, `hΩ₁tube`, `hΩ₁max`, `hcocont`, `hlateral`: the closed cover of the
  boundary circle of `G` by the part lying over the parametrised cylinder and the closure of
  the rest, with lateral overlap.  Genuine theorem; it is the transversality of the boundary
  circle to the wall of the tube.  `hΩ₁tube` and `hΩ₁max` say that `Ω₁` is exactly the part
  lying over the cylinder, which is what lets `hraw`, `hres` and `hrest` be derived rather
  than assumed.

*The four arc cut of the boundary circle of `D`.*

* `σ₀`, `τ₀`, `υ₀`, `φ₀`, `ev`, `hev`, `hσ`, `hτ`, `hυ`, `hφ`, `γ`, `hγ`, `hγN`: the inputs of
  `LoopTheorem.BoundaryWordElimination` as instantiated in `LoopTheorem.BoundaryWordConnectors`.
  These are hypotheses of the induction step and not gaps.

## What the assembled statement does not say

The hypothesis `hD.singularSet.IsBoundaryBranch c` does not occur.  Every producer that
consumes it returns its cell existentially, while the two witnesses have to *name* the produced
cells; so at this level the boundary branch hypothesis has already been spent by the producers
whose outputs are taken as arguments here. -/
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
        Disjoint e.source (T.chart '' spliceCylinder) ∧
          HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ ⇑G ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y))
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (ebranch : hGd.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
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
  -- The resolved cell deletes exactly the carrier of the branch `c`.
  have hdouble : doublePointSet cell cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
    rw [T.doublePointSet_sdiff_image_spliceCylinder, ← hGD]
    refine Subset.antisymm
      (T.doublePointSet_resolved_subset hdomain hcoord hresolved hcompl) ?_
    rintro y ⟨⟨x₁, hx₁, x₂, hx₂, hne, hy₁, hy₂⟩, hycyl⟩
    have h₁ : ⇑G x₁ ∉ T.chart '' spliceCylinder := by rw [hy₁]; exact hycyl
    have h₂ : ⇑G x₂ ∉ T.chart '' spliceCylinder := by rw [hy₂]; exact hycyl
    refine ⟨x₁, ?_, x₂, ?_, hne, (hcompl ⟨hx₁, h₁⟩).trans hy₁, (hcompl ⟨hx₂, h₂⟩).trans hy₂⟩
    · rw [hdomain]; exact hx₁
    · rw [hdomain]; exact hx₂
  -- The resolved cell is again a normal singular cell over the same boundary data.
  have hcell : NormalSingularCellData cell BdM B :=
    T.normalOfResolvedCell hdomain hcoord hreglued hresolved hcompl hdouble hGinj hGfiber
      hGboundary hGimage hGcrossing hendDisks hends htubeBdM hBdM
  -- The boundary circle of `G` lies in the source disk of `G`.
  have hdom : ∀ θ : loopCircle, (Wraw.param θ : EuclideanSpace ℝ (Fin 2)) ∈ G.domain :=
    fun θ => G.frontier_subset_domain (Wraw.param θ).2
  have hmem₁ : ∀ θ ∈ Ω₁, (Wraw.param θ : EuclideanSpace ℝ (Fin 2)) ∈
      G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder) :=
    fun θ hθ => ⟨hdom θ, hΩ₁tube θ hθ⟩
  -- On the overlap of the cover the resolution is stationary, so the two cells agree on the
  -- whole of `Ω₂`, not only off the parametrised cylinder.
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
  -- The end disks of the tube lie in the ambient loop space, because they lie in `B`.
  have hdisk : ∀ p ∈ spliceSquare, ∀ t : ℝ, t = 0 ∨ t = 1 →
      T.chart (p, t) ∈ Set.range ρ := by
    intro p hp t ht
    have htmem : t ∈ ({0, 1} : Set ℝ) := by rcases ht with h | h <;> simp [h]
    exact hrange (hendDisks ⟨(p, t), ⟨hp, htmem⟩, rfl⟩)
  -- The resolved cell inherits the boundary word witness of the raw cross reglue.
  obtain ⟨Wcross⟩ := exists_boundaryWordWitness_of_crossSeamBoundary (cell := cell) hρ hdomain
    T.isTube.continuousOn_chart Wraw hΩ₁ hΩ₂ hcover
    (co := fun θ => coord ↑(Wraw.param θ)) hcocont (fun θ hθ => hcoord.mapsTo (hmem₁ θ hθ))
    (fun θ hθ => hreglued (hmem₁ θ hθ)) (fun θ hθ => hresolved (hmem₁ θ hθ)) hrest hlateral
    (fun θ hθ => (hends _ (hmem₁ θ hθ)).mp (Wraw.param θ).2) hdisk
  exact exists_descendingSurgery_not_loopClassMeets_reversing_witness hGd ebranch
    (crossSeamResolutionDataOfTube (T := T) (G := G)
      { cell := cell, domain_eq := hdomain, coord := coord, bijOn_coord := hcoord,
        reglued_eq := hreglued, resolved_eq := hresolved, eqOn_compl := hcompl,
        normal := hcell } hGim hGD (hD.deletedBranchEquiv hcell c hdouble)
      fun b => hD.branchCarrier_deletedBranchEquiv hcell c hdouble b)
    σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN Wdirect Wcross

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
