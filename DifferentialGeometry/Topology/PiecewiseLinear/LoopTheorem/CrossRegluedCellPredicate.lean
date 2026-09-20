/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCaseReduction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedCellCrossing

/-!
# Naming the cross reglued cell of a boundary branch

`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` of
`LoopTheorem.CutAndPaste` returns the cross reglued cell `G` of a boundary branch
existentially, together with the whole cutting and regluing datum that built it.  The boundary
case assembly
`NormalSingularCellData.exists_descendingSurgery_of_crossSeamTube_reversing`
of `LoopTheorem.BoundaryCaseReduction` cannot consume it in that form: its hypotheses
`hdomain`, `hcoord`, `hreglued`, `hresolved`, `hcompl` and `Wraw` all mention `G`, so `G` has
to be *named* before the assembly can be stated at all.

This file names it.  `NormalSingularCellData.IsCrossRegluedCell hD c G` is the conclusion of
that producer with `G` fixed and every other object it produces existentially quantified, the
conjuncts being those of the producer in its own order.  The predicate is inhabited exactly
where the producer applies: `NormalSingularCellData.exists_isCrossRegluedCell_of_boundaryBranch`
is the producer read through it.

## Why a predicate, and not a list of recorded conclusions

The obvious alternative, a corollary quantified over every cell `G` satisfying the conclusions
the producer records, is vacuous in the worst way: `G = D` satisfies all of them.  The original
cell has the same image as itself, the same double point set, is locally injective, has fibres
of at most two points, crosses normally at the double points lying off the branch, and its
boundary circle is a two arc word.  A hypothesis of that shape could therefore never single out
the cross reglue among the cells cut from `D`, and the assembly would be about nothing.
Pinning `G` to the construction is what the predicate is for.

## The projections

Each of the five fields of the assembly that the cross reglue itself is responsible for is read
off the predicate here:

* `NormalSingularCellData.image_subset_of_isCrossRegluedCell`,
  `NormalSingularCellData.branchCarrier_subset_of_isCrossRegluedCell` and
  `NormalSingularCellData.exists_boundaryArcs_of_isCrossRegluedCell` are conclusions the
  producer records;
* `NormalSingularCellData.doublePointSet_eq_of_isCrossRegluedCell`,
  `NormalSingularCellData.locallyInjective_of_isCrossRegluedCell` and
  `NormalSingularCellData.fiber_le_two_of_isCrossRegluedCell` come from
  `LoopTheorem.CrossRegluedCellFields`;
* `NormalSingularCellData.crossing_of_isCrossRegluedCell` and its enlarged form
  `NormalSingularCellData.crossing_outside_of_isCrossRegluedCell` come from
  `LoopTheorem.CrossRegluedCellCrossing`;
* `NormalSingularCellData.range_boundary_subset_of_isCrossRegluedCell` and
  `NormalSingularCellData.image_inter_boundary_of_isCrossRegluedCell` are the two remaining
  elementary fields, both read off
  `NormalSingularCellData.image_frontier_eq_of_isCrossRegluedCell`, the recorded equality
  `G '' frontier G.domain = D '' frontier D.domain`.  The injective source parametrisations of
  the two boundary arcs come out of
  `NormalSingularCellData.exists_injective_boundaryArcs_of_isCrossRegluedCell`.

The two assemblies
`NormalSingularCellData.exists_descendingSurgery_of_crossSeamTube_reversing_of_isCrossRegluedCell`
and its endpoint preserving twin then restate the boundary case with the five hypotheses
`hGim`, `hGD`, `hGinj`, `hGfiber`, `hGcrossing`, `hGboundary` and `hGimage` replaced by the
single hypothesis `hD.IsCrossRegluedCell c G`.  The passage from the crossing off the branch
to the crossing off the tube is `CrossSeamTubeData.branchCarrier_subset_tube`, and `hGD` is
the double point equality restricted to the complement of the parametrised cylinder.  The
last two come from `NormalSingularCellData.image_frontier_eq_of_isCrossRegluedCell`: the
producer now records that the cross reglue sweeps out the same boundary curve as `D`, so the
two elementary fields left open in `LoopTheorem.CrossRegluedCellFields` are consequences of
the construction as well.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-! ### The predicate -/

/-- **The cross reglued cell of a boundary branch, as a predicate on the cell.**  A cell `G`
is a cross reglued cell of the branch `c` of `hD` when the whole cutting and regluing datum of
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` exists with `G` as its
output: the two crosscuts `A` and `C` of the branch preimage with the PL identification `g`
between them, the three pieces `U₁`, `U₂`, `U₃` they cut `D.domain` into, the intermediate cell
`H` glued from the first two, the cell `G` itself glued from `H` and the third piece along the
displaced seam `A'`, and the cut of the boundary circle of `G` into the two arcs `R` and `T`
that carry its two arc boundary word.  The conjuncts are those of the producer, in its order. -/
def IsCrossRegluedCell (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (G : SingularTwoCell M) : Prop :=
  ∃ A C U₁ U₂ U₃ P Q P' Q' A' R T : Set (EuclideanSpace ℝ (Fin 2)),
  ∃ p q r s a b : EuclideanSpace ℝ (Fin 2),
  ∃ g f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
  ∃ H : SingularTwoCell M,
    IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
    hD.branchPreimage c = A ∪ C ∧
    IsPLHomeomorphOn g A C ∧ EqOn D (D ∘ g) A ∧
    p ∈ A ∧ q ∈ A ∧ r ∈ C ∧ s ∈ C ∧
    ((g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r)) ∧
    U₁ ∪ U₂ ∪ U₃ = D.domain ∧ U₁ ∩ U₂ = A ∧ U₂ ∩ U₃ = C ∧
    Disjoint U₁ U₃ ∧
    IsPLBall 2 P ∧ IsPLBall 2 Q ∧ H.domain = P ∪ Q ∧
    IsPLHomeomorphOn f₁ P U₁ ∧ IsPLHomeomorphOn f₂ Q U₂ ∧
    f₁ '' (P ∩ Q) = A ∧ f₂ '' (P ∩ Q) = C ∧
    EqOn H (D ∘ f₁) P ∧ EqOn H (D ∘ f₂) Q ∧
    A' = Function.invFunOn f₂ Q '' A ∧ IsPLBall 1 A' ∧ Disjoint A' (P ∩ Q) ∧
    A' ⊆ frontier H.domain ∧ IsPLHomeomorphOn (g ∘ f₂) A' C ∧
    IsPLBall 2 P' ∧ IsPLBall 2 Q' ∧ G.domain = P' ∪ Q' ∧
    IsPLHomeomorphOn h P' H.domain ∧ IsPLHomeomorphOn f₃ Q' U₃ ∧
    h '' (P' ∩ Q') = A' ∧ f₃ '' (P' ∩ Q') = C ∧
    EqOn G (H ∘ h) P' ∧ EqOn G (D ∘ f₃) Q' ∧
    Schoenflies.IsCutPair (frontier P') a b (P' ∩ Q') R ∧
    Schoenflies.IsCutPair (frontier Q') a b (P' ∩ Q') T ∧
    IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
    h a = Function.invFunOn f₂ Q p ∧ h b = Function.invFunOn f₂ Q q ∧
    f₃ a = g p ∧ f₃ b = g q ∧
    G '' G.domain ⊆ D '' D.domain ∧
    hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain ∧
    ∃ (x y : M) (σ : Path x y) (ω : Path y x)
        (e : loopCircle ≃ₜ frontier G.domain),
      Set.range σ = G '' R ∧ Set.range ω = G '' T ∧
        (∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ) ∧
        G '' R = D '' ((U₁ ∪ U₂) ∩ frontier D.domain) ∧
        G '' T = D '' (U₃ ∩ frontier D.domain) ∧
        G '' frontier G.domain = D '' frontier D.domain ∧
        ∃ (a' b' : frontier G.domain) (ρ : Path a' b') (κ : Path b' a'),
          Function.Injective ρ ∧ Function.Injective κ ∧
          Set.range (fun t => ((ρ t : frontier G.domain) :
            EuclideanSpace ℝ (Fin 2))) = R ∧
          Set.range (fun t => ((κ t : frontier G.domain) :
            EuclideanSpace ℝ (Fin 2))) = T ∧
          ∀ θ, e θ = pathToCircle (ρ.trans κ) θ

/-- **The predicate is inhabited at every boundary branch.**  This is
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` read through
`NormalSingularCellData.IsCrossRegluedCell`: the cell it produces is a cross reglued cell of
the branch, and the two statements have the same content. -/
theorem exists_isCrossRegluedCell_of_boundaryBranch [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ G : SingularTwoCell M, hD.IsCrossRegluedCell c G := by
  obtain ⟨A, C, U₁, U₂, U₃, P, Q, P', Q', A', R, T, p, q, r, s, a, b, g, f₁, f₂, h, f₃, H, G,
    hrest⟩ := hD.exists_cross_reglued_cell_of_boundaryBranch hc
  exact ⟨G, A, C, U₁, U₂, U₃, P, Q, P', Q', A', R, T, p, q, r, s, a, b, g, f₁, f₂, h, f₃, H,
    hrest⟩

/-! ### The projections -/

/-- The cross reglued cell is carried by the image of the cell it was cut from. -/
theorem image_subset_of_isCrossRegluedCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    ⇑G '' G.domain ⊆ ⇑D '' D.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hGim, -, _, _, _, _, _, -, -, -, -⟩ := hG
  exact hGim

/-- The regluing keeps the carrier of the branch it was cut along inside the double point set
of the new cell: this is the branch that the chord resolution of the tube later deletes. -/
theorem branchCarrier_subset_of_isCrossRegluedCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbranch, _, _, _, _, _, -, -, -, -⟩ := hG
  exact hbranch

/-- **The cross reglue changes no double point**, the conclusion of
`NormalSingularCellData.doublePointSet_crossReglued_eq` read off the predicate. -/
theorem doublePointSet_eq_of_isCrossRegluedCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    doublePointSet G G.domain = doublePointSet D D.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, hAC,
    hcover, hg, hcompat, -, -, -, -, -, hdomains, hinter₁₂, hinter₂₃, hdisjoint₁₃, -, -,
    hHdomain, hf₁, hf₂, -, hf₂seam, hH₁, hH₂, -, -, -, -, -, -, -, hGdomain, hh, hf₃, -,
    hf₃seam, hGH, hG₃, -, -, -, -, -, -, -, -, -, -, hbranch, _, _, _, _, _, -, -, -,
    -⟩ := hG
  exact hD.doublePointSet_crossReglued_eq hAC hcover hg hcompat hdomains hinter₁₂ hinter₂₃
    hdisjoint₁₃ hHdomain hf₁ hf₂ hf₂seam hH₁ hH₂ hGdomain hh hf₃ hf₃seam hGH hG₃ hbranch

/-- **The cross reglued cell is locally injective**, the field `locallyInjective` of
`NormalSingularCellData`, read off the predicate. -/
theorem locallyInjective_of_isCrossRegluedCell [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    ∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn (⇑G) V := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, hAC,
    hcover, hg, hcompat, -, -, -, -, -, hdomains, hinter₁₂, hinter₂₃, hdisjoint₁₃, hP, hQ,
    hHdomain, hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂, hA'def, -, hA'seam, -, -, hP', hQ',
    hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃, -, -, -, -, -, -, -, -, -, -, -, _, _, _,
    _, _, -, -, -, -⟩ := hG
  exact hD.locallyInjective_crossReglued hAC hcover hg hcompat hdomains hinter₁₂ hinter₂₃
    hdisjoint₁₃ hP hQ hHdomain hf₁ hf₂ hf₁seam hf₂seam hH₁ hH₂ hA'def hA'seam hP' hQ'
    hGdomain hh hf₃ hhseam hf₃seam hGH hG₃

/-- **The cross reglued cell has fibres of at most two points**, the field `fiber_le_two` of
`NormalSingularCellData`, read off the predicate. -/
theorem fiber_le_two_of_isCrossRegluedCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    ∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, hAC,
    -, hg, hcompat, -, -, -, -, -, hdomains, hinter₁₂, hinter₂₃, hdisjoint₁₃, -, -, hHdomain,
    hf₁, hf₂, -, hf₂seam, hH₁, hH₂, -, -, -, -, -, -, -, hGdomain, hh, hf₃, -, hf₃seam, hGH,
    hG₃, -, -, -, -, -, -, -, -, -, -, -, _, _, _, _, _, -, -, -, -⟩ := hG
  exact hD.fiber_le_two_crossReglued hAC hg hcompat hdomains hinter₁₂ hinter₂₃ hdisjoint₁₃
    hHdomain hf₁ hf₂ hf₂seam hH₁ hH₂ hGdomain hh hf₃ hf₃seam hGH hG₃

/-- **The cross reglued cell crosses normally off the branch carrier**, the field `crossing`
of `NormalSingularCellData` at every double point lying outside the carrier of the reglued
branch, read off the predicate.  The crossing genuinely fails on the branch carrier itself,
as the module docstring of `LoopTheorem.CrossRegluedCellFields` explains. -/
theorem crossing_of_isCrossRegluedCell [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    ∀ y ∈ doublePointSet G G.domain, y ∉ hD.singularSet.branchCarrier c →
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑G) (G.domain ∩ ⇑G ⁻¹' e.source)
          (⇑e '' (e.source ∩ BdM)) (e y) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, hAC,
    hcover, hg, hcompat, -, -, -, -, -, hdomains, hinter₁₂, hinter₂₃, hdisjoint₁₃, hP, hQ,
    hHdomain, hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂, hA'def, -, -, -, -, hP', hQ', hGdomain,
    hh, hf₃, hhseam, hf₃seam, hGH, hG₃, -, -, -, -, -, -, -, -, -, -, hbranch, _, _, _, _, _,
    -, -, -, -⟩ := hG
  exact hD.crossing_crossReglued_of_notMem_branchCarrier hAC hcover hg hcompat hdomains
    hinter₁₂ hinter₂₃ hdisjoint₁₃ hP hQ hHdomain hf₁ hf₂ hf₁seam hf₂seam hH₁ hH₂ hA'def hP'
    hQ' hGdomain hh hf₃ hhseam hf₃seam hGH hG₃ hbranch

/-- **The cross reglued cell crosses normally outside any neighbourhood of the branch.**  The
form consumed by the boundary case assembly, whose tube contains the branch carrier. -/
theorem crossing_outside_of_isCrossRegluedCell [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) {U : Set M}
    (hU : hD.singularSet.branchCarrier c ⊆ U) :
    ∀ y ∈ doublePointSet G G.domain, y ∉ U →
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑G) (G.domain ∩ ⇑G ⁻¹' e.source)
          (⇑e '' (e.source ∩ BdM)) (e y) :=
  fun y hy hyU => hD.crossing_of_isCrossRegluedCell hG y hy fun hmem => hyU (hU hmem)

/-- **The boundary word of the cross reglued cell.**  Its boundary circle is cut by the two
points `a` and `b` of the producer into two PL arcs `R` and `T`, and is traversed by the
concatenation of a path along the image of the first and a path along the image of the
second. -/
theorem exists_boundaryArcs_of_isCrossRegluedCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
      ∃ (x y : M) (σ : Path x y) (ω : Path y x) (e : loopCircle ≃ₜ frontier G.domain),
        Set.range σ = ⇑G '' R ∧ Set.range ω = ⇑G '' T ∧
          ∀ θ, ⇑G (e θ) = pathToCircle (σ.trans ω) θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, R, T, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, hR, hT, hfrontG, -, -, -, -, -, -, x, y, σ, ω, e, hσrange, hωrange,
    hparam, -⟩ := hG
  exact ⟨R, T, hR, hT, hfrontG, x, y, σ, ω, e, hσrange, hωrange, hparam⟩

/-- **The cross reglue does not move the boundary curve.**  Its two boundary arcs are the `D`
images of the traces of `U₁ ∪ U₂` and of `U₃` on `frontier D.domain`, and those two traces
cover `frontier D.domain`, so the reglued boundary sweeps out exactly the old one. -/
theorem image_frontier_eq_of_isCrossRegluedCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    ⇑G '' frontier G.domain = ⇑D '' frontier D.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, _, _, _, _, _, -, -, -, -, -, hfront, -⟩ := hG
  exact hfront

/-- **The boundary of the cross reglued cell lies in the distinguished boundary set**, the
field `boundary_image_subset` of `NormalSingularCellData`, read off the predicate through the
boundary equality. -/
theorem range_boundary_subset_of_isCrossRegluedCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    Set.range ⇑G.boundary ⊆ B := by
  rw [G.range_boundary_eq_image_frontier, hD.image_frontier_eq_of_isCrossRegluedCell hG,
    ← D.range_boundary_eq_image_frontier]
  exact hD.boundary_image_subset

/-- **The cross reglued cell meets the boundary exactly along its own boundary curve**, the
field `image_inter_boundary` of `NormalSingularCellData`.  A point of the reglued image on
`BdM` lies in the image of `D`, hence on the boundary curve of `D`, which is the boundary
curve of `G`; conversely that curve lies in the reglued image and on `BdM`. -/
theorem image_inter_boundary_of_isCrossRegluedCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    ⇑G '' G.domain ∩ BdM = Set.range ⇑G.boundary := by
  have hfront := hD.image_frontier_eq_of_isCrossRegluedCell hG
  have hGrange : Set.range ⇑G.boundary = ⇑D '' frontier D.domain := by
    rw [G.range_boundary_eq_image_frontier, hfront]
  have hDrange : ⇑D '' frontier D.domain = ⇑D '' D.domain ∩ BdM := by
    rw [← D.range_boundary_eq_image_frontier, hD.image_inter_boundary]
  apply Subset.antisymm
  · intro y hy
    rw [hGrange, hDrange]
    exact ⟨hD.image_subset_of_isCrossRegluedCell hG hy.1, hy.2⟩
  · intro y hy
    have hyD : y ∈ ⇑D '' D.domain ∩ BdM := by
      rw [← hDrange, ← hGrange]
      exact hy
    refine ⟨?_, hyD.2⟩
    rw [G.range_boundary_eq_image_frontier] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, G.frontier_subset_domain hz, rfl⟩

/-- **The boundary circle of the cross reglued cell, parametrised in the source.**  The two
arcs `R` and `T` of `frontier G.domain` carry *injective* paths of the frontier itself, whose
concatenation parametrises the boundary circle through the recorded homeomorphism.  This is
the form `Path.Homotopic.of_injective_of_range_eq` consumes when a boundary word has to be
compared with a finer subdivision of the same circle. -/
theorem exists_injective_boundaryArcs_of_isCrossRegluedCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
    ∃ (a' b' : frontier G.domain) (ρ : Path a' b') (κ : Path b' a')
        (e : loopCircle ≃ₜ frontier G.domain),
      IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
      Function.Injective ρ ∧ Function.Injective κ ∧
      Set.range (fun t => ((ρ t : frontier G.domain) : EuclideanSpace ℝ (Fin 2))) = R ∧
      Set.range (fun t => ((κ t : frontier G.domain) : EuclideanSpace ℝ (Fin 2))) = T ∧
      (∀ θ, e θ = pathToCircle (ρ.trans κ) θ) ∧
      ⇑G '' R ∪ ⇑G '' T = ⇑D '' frontier D.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, R, T, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, hR, hT, hfrontG, -, -, -, -, -, -, _, _, _, _, e, -, -, -, -, -, hfront,
    a', b', ρ, κ, hρinj, hκinj, hρrange, hκrange, heparam⟩ := hG
  refine ⟨R, T, a', b', ρ, κ, e, hR, hT, hfrontG, hρinj, hκinj, hρrange, hκrange, heparam, ?_⟩
  rw [← image_union, ← hfrontG]
  exact hfront

/-! ### The boundary case assemblies -/

/-- **The boundary case of Moise's Lemma 2, endpoint reversing, with the cross reglued cell
named.**  This is `NormalSingularCellData.exists_descendingSurgery_of_crossSeamTube_reversing`
with its five hypotheses about the cross reglued cell `G` — the image bound `hGim`, the double
point equality `hGD` off the parametrised cylinder, the local injectivity `hGinj`, the fibre
bound `hGfiber` and the crossing `hGcrossing` outside the tube — together with the two
elementary fields `hGboundary` and `hGimage`, replaced by the single hypothesis that `G` *is*
the cross reglued cell of the branch `c`.  All seven are consequences of the construction, so
the boundary case no longer carries any of them as open obligations. -/
theorem exists_descendingSurgery_of_crossSeamTube_reversing_of_isCrossRegluedCell [T2Space M]
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
    (hG : hD.IsCrossRegluedCell c G)
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
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_of_crossSeamTube_reversing T hdomain hcoord hreglued hresolved
    hcompl (hD.image_subset_of_isCrossRegluedCell hG)
    (by rw [hD.doublePointSet_eq_of_isCrossRegluedCell hG])
    (hD.locallyInjective_of_isCrossRegluedCell hG)
    (hD.fiber_le_two_of_isCrossRegluedCell hG)
    (hD.range_boundary_subset_of_isCrossRegluedCell hG)
    (hD.image_inter_boundary_of_isCrossRegluedCell hG)
    (hD.crossing_outside_of_isCrossRegluedCell hG T.branchCarrier_subset_tube) hendDisks hends
    htubeBdM hBdM hGd origin hinj hmiss σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN hρ hrange
    Wdirect Wraw hΩ₁ hΩ₂ hcover hcocont hΩ₁tube hΩ₁max hlateral

/-- **The boundary case of Moise's Lemma 2, endpoint preserving, with the cross reglued cell
named.**  The endpoint preserving twin of
`NormalSingularCellData.exists_descendingSurgery_of_crossSeamTube_reversing_of_isCrossRegluedCell`,
in the other relative direction of the cut: the second and the fourth arc of the boundary word
are loops, the direct candidate traverses `σ.trans υ` and the raw cross candidate
`σ.trans (τ.symm.trans (υ.trans φ.symm))`.  Nothing else changes; in particular
`exists_boundaryWordWitness_of_crossSeamBoundary` transports a boundary word witness over any
word, so the resolved cell inherits the witness of the raw cross reglue exactly as in the
endpoint reversing case. -/
theorem exists_descendingSurgery_of_crossSeamTube_preserving_of_isCrossRegluedCell [T2Space M]
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
    (hG : hD.IsCrossRegluedCell c G)
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
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  classical
  -- The double point equality off the parametrised cylinder, from the construction of `G`.
  have hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder := by
    rw [hD.doublePointSet_eq_of_isCrossRegluedCell hG]
  -- The cross reglued cell and its chord resolution, bundled in the normal form of the tube.
  let Rdata : CrossSeamRegluedData T G :=
    { cell := cell, domain_eq := hdomain, coord := coord, bijOn_coord := hcoord,
      reglued_eq := hreglued, resolved_eq := hresolved, eqOn_compl := hcompl }
  -- The resolved cell deletes exactly the carrier of the branch `c`.
  have hdouble : doublePointSet cell cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c :=
    Rdata.doublePointSet_cell_eq hGD
  -- The resolved cell is again a normal singular cell over the same boundary data.
  have hcell : NormalSingularCellData cell BdM B :=
    Rdata.normalOfTube hGD (hD.locallyInjective_of_isCrossRegluedCell hG)
      (hD.fiber_le_two_of_isCrossRegluedCell hG)
      (hD.range_boundary_subset_of_isCrossRegluedCell hG)
      (hD.image_inter_boundary_of_isCrossRegluedCell hG)
      (hD.crossing_outside_of_isCrossRegluedCell hG T.branchCarrier_subset_tube) hendDisks
      hends htubeBdM hBdM
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
  have hdisk : T.chart '' spliceEndDisks ⊆ Set.range ρ := Subset.trans hendDisks hrange
  -- The resolved cell inherits the boundary word witness of the raw cross reglue.
  obtain ⟨Wcross⟩ := exists_boundaryWordWitness_of_crossSeamBoundary (cell := cell) hρ hdomain
    T.isTube.continuousOn_chart Wraw hΩ₁ hΩ₂ hcover
    (co := fun θ => coord ↑(Wraw.param θ)) hcocont (fun θ hθ => hcoord.mapsTo (hmem₁ θ hθ))
    (fun θ hθ => hreglued (hmem₁ θ hθ)) (fun θ hθ => hresolved (hmem₁ θ hθ)) hrest hlateral
    (fun θ hθ => (hends _ (hmem₁ θ hθ)).mp (Wraw.param θ).2) hdisk
  exact exists_descendingSurgery_not_loopClassMeets_preserving_witness_of_injection hGd origin
    hinj hmiss
    (crossSeamResolutionDataOfTube (T := T) (G := G) Rdata hcell
      (hD.image_subset_of_isCrossRegluedCell hG) hGD
      (hD.deletedBranchEquiv hcell c hdouble)
      fun b => hD.branchCarrier_deletedBranchEquiv hcell c hdouble b)
    σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN Wdirect Wcross

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
