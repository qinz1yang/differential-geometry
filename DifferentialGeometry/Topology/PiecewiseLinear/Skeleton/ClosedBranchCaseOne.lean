/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LoopSpace.BasedCircle
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedBranchOrientability
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneCollar
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneSource
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTubeCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoOrientable
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneMarkedChart
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTransport

/-!
# Sorry-first skeleton of lane C-or1: the one circle closed case in an orientable manifold

The assembly `NormalSingularCellData.not_branchPreimage_eq_of_isOrientable` and its
specialisation `NormalSystem.not_branchPreimage_eq_of_isOrientableManifold` to the double are
proved for real from the two leaves below and from the proved producers
`exists_isBranchDeckInvolution_of_branchPreimage_eq`,
`exists_isTwoSidedBranchCollar_of_branchPreimage_eq`, `isPLBall_of_isPLSphere_one`,
`isOrientable_derivedNeighborhood_of_isSubdivision`, `branchProjection_isCoveringMap`,
`branchProjection_fiber_encard_eq_two`, `connectedSpace_branchPreimage_of_isPLSphere_one`,
`Covering.not_exists_continuous_section_of_fiber_card_two` and
`IsCylindricalDiagram.not_closedBranchCase1`.  No `sorry` occurs inside an assembly.

The predicates `NormalSingularCellData.IsMarkedCrossingChartAt`,
`NormalSingularCellData.IsMarkedBranchCollar` and `IsSourceTrackedBranchTube`, the structure
`SourceRayTransport` and every proved lemma of this chain live in
`LoopTheorem/ClosedBranchCaseOneTransport.lean`, a real module with no `sorry`; only the open
leaf and the assembly remain here.

Proved since, and imported: `NormalSingularCellData.exists_isMarkedCrossingChartAt` (item 4,
`LoopTheorem/ClosedBranchCaseOneMarkedChart.lean`, the frozen statement verbatim): at every
point of the source circle `J` a crossing chart of the ambient manifold in which the sheet
through that point is `(e z).2.2 = 0`, the sheet through its deck partner is `(e z).2.1 = 0`,
the branch carrier is `(e z).2 = 0`, and on each sheet the positive half is the half that the
proved two sided collar puts on the `Q` side of `J`.

The leaf.

* `exists_isSourceTrackedBranchTube` (item 8, owner W-B, reviewed 2026-09-21, frozen): a
  cylindrical diagram over a `2`-ball cross section whose target is `derivedNeighborhood R Lc` for
  a finite subdivision `R` of the ambient complex and some complex `Lc`, containing the branch
  carrier in its intrinsic interior, whose cross section circle meets the trace of the cell in
  exactly four marked points at every level, together with the parametrisation of that circle
  putting the four rays in cyclic order and with the source realisation of the four rays along
  the branch.  It carries no orientability hypothesis and no orientability clause.  The clause
  `derived` does not ask that `Lc` be a subcomplex of `R`, nor that `Lc.space` be the branch; the
  intended producer takes `Lc = restrict R Γ` for a common subdivision `R` in which the branch
  and the image of the cell are subcomplexes, and must choose `R`, the tube, the cylindrical
  parametrisation and the source arcs together.  The labels come from the alternating four rays
  of the crossing, transported along the given collar; they cannot be chosen after the fact.
  The cyclic order `0, 1, 2, 3` and the pairing `0`–`2`, `1`–`3` (the two sides of one source
  sheet) are compatible: on the Möbius fixture `r = ((δ,0), (0,δ), (-δ,0), (0,-δ))`,
  `a 0 = a 2 = [t]`, `a 1 = a 3 = [t+1]`, signs `(+,+,-,-)`, and the end map is the reflection
  `(0 1)(2 3)`, which `cyclic` does not ask to preserve the order.  The substance of the leaf is
  the marked cell normalisation and gluing relative to the given `ρ`: the existing unmarked
  link and cylinder normalisation controls set images only, not the four continuous source
  arcs over the same collar.

The 2026-09-21 external review of the snapshot `06a96eb1de64` found the old item 8 vacuous (its
input was the orientable closed case itself) and the old items 9 and 10 false: an abstractly
glued external solid torus with half turn, respectively quarter turn, end map satisfies every
clause of the old `IsAdaptedBranchTube` and refutes the sheet exchange, respectively the square
of the end map fixing the rays.  Both counterexamples are excluded here by two new clauses of
`IsSourceTrackedBranchTube`: the tube is a derived neighbourhood inside the ambient complex, and
each of the four rays is realised by a continuous source arc `a i` in `J` over one circuit of the
branch, on a fixed collar side `s i`, with the four pairs `(a i 0, sign (s i 0))` distinct and
with the alternating pairing `a 0 0 = a 2 0`, `a 1 0 = a 3 0`, `a 0 0 ≠ a 1 0`.

The old departure note claiming that the transport of the marking along the branch is "an
obligation inside item 8" is withdrawn: the transport is now recorded explicitly in the source
realisation clause, and it is consumed here by the proved
`exists_sourceRayTransport_of_isSourceTrackedBranchTube`, which derives the seam identification
`lift i 0 = lift j 1` from the equality of the two `D` images of collar points off `J`, from
`doublePointPreimage D D.domain ∩ C = J` and from injectivity of `ρ`, and by the proved
`SourceRayTransport.square_fixes_rays` and `SourceRayTransport.isSheetExchange`, which replace
the two false leaves by consequences of one transport statement.  The covering input is that a
lift of one circuit in a connected two sheeted cover of the circle ends at the other fibre point,
which is `apply_one_ne_apply_zero_of_fiber_encard_eq_two` together with the two element fibre.
Orientability of the tube is no longer assumed: it is derived in the assembly from ambient
orientability through `isOrientable_derivedNeighborhood_of_isSubdivision`.  Recording the
derived neighbourhood presentation is an interface choice made because that lemma exists; it is
not a mathematical necessity.  The inclusion `N.space ⊆ L.space`, which `derived` implies, would
serve as well together with a general restriction lemma for orientability in equal dimension
(common subdivision, `IsOrientable.of_le`, invariance under subdivision).

Three adaptations of the reviewed interface.  `BranchTime` is spelled `unitInterval`, so that
`pathToCircle_coe` and `unitInterval_to_loopCircle_surjective` apply without a translation.  The
deck involution `τ` is not a parameter of the predicate: the alternating pairing of the source
arcs is what the transport consumes, and an unused parameter would be a warning.  The two
finiteness arguments are not parameters either, since with `IsOrientable 3 N` removed no clause
uses them; the leaf produces them beside the predicate, as the assembly needs them.

Departures from `consult/C-or1-design.md`, forced by the proved pieces or by types.

* The collar sign is the proved one: `ρ '' (J ×ˢ Icc 0 1) = C ∩ Q`, so `0 < s` is the `Q` side,
  the opposite of the design's `κ`.  All in/out clauses use `Ioc 0 1`.
* The marked chart is indexed by the source point `a ∈ J`, not by the branch point `⇑D a`.  The
  design's clause `∀ y ∈ Γ, ∀ a ∈ J, ⇑D a = y → IsMarkedCrossingChartAt … y a (sheet y)` is not
  unsatisfiable: one chart `e` would have to present both the sheet through `a` and the sheet
  through `τ a` as `(e z).2.2 = 0`, forcing the two sheets to agree near `⇑D a`, while the same
  chart makes their intersection the `1`-dimensional set `(e z).2 = 0`.
* The chart carries no `IsPiecewiseAffineOn` clause.  `IsPiecewiseAffineOn e e.source` for
  `e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)` is ill typed for a charted `M`, which is not a normed
  space; piecewise linearity of the tube comes from the simplicial side instead.
* Item 5 is not stated as a comparison of two charts.  Its content is retained in the output of
  item 8: the source arcs `a i` and the signs `s i` are exactly the marking transported along the
  branch, and they are compared only through the collar, where the normal forms hold.
* The final theorem needs no clean disk `Q`: `isPLBall_of_isPLSphere_one` produces a `2`-ball
  with frontier `J` from `IsPLSphere 1 J` alone, which is what the collar producer consumes.  Its
  hypotheses are exactly those of the already stated leaf `not_branchPreimage_eq_of_isOrientable`
  of `Skeleton/DescentStepOrientable.lean`.
* The four arc sphere normalisation is not a leaf here: `FourArcSphere.lean` already proves
  `exists_isPLHomeomorphOn_fourArcSphere_of_isPLHomeomorphOn_Icc` in the required form.  It is a
  tool of item 8 and is not consumed by this assembly, so this skeleton does not test its
  interface; that file is deliberately not imported.  Its application at every branch vertex,
  with actual four arc parametrisations, the two separation hypotheses and the permutation
  condition, remains part of item 8.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

open Classical in
theorem exists_isMarkedBranchCollar [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hpre : hD.branchPreimage c = J) :
    ∃ (Q C : Set (EuclideanSpace ℝ (Fin 2)))
      (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
      (sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph M (ℝ × ℝ × ℝ)),
      hD.IsMarkedBranchCollar c J Q C τ ρ sheet := by
  classical
  obtain ⟨Q, hQ, hfrontQ, -⟩ := isPLBall_of_isPLSphere_one hJ
  obtain ⟨τ, hτ⟩ := hD.exists_isBranchDeckInvolution_of_branchPreimage_eq c hpre
  obtain ⟨C, ρ, hρ⟩ := hD.exists_isTwoSidedBranchCollar_of_branchPreimage_eq hc hJ hpre hQ hfrontQ
  obtain ⟨a₀, ha₀⟩ := hτ.2.1
  obtain ⟨e₀, -⟩ := hD.exists_isMarkedCrossingChartAt hc hτ hρ ha₀
  refine ⟨Q, C, τ, ρ,
    fun a => if h : a ∈ J then (hD.exists_isMarkedCrossingChartAt hc hτ hρ h).choose else e₀,
    hτ, hρ, fun a ha => ?_⟩
  change hD.IsMarkedCrossingChartAt c J τ ρ a
    (if h : a ∈ J then (hD.exists_isMarkedCrossingChartAt hc hτ hρ h).choose else e₀)
  rw [dif_pos ha]
  exact (hD.exists_isMarkedCrossingChartAt hc hτ hρ ha).choose_spec

end NormalSingularCellData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

open Classical in
theorem exists_isSourceTrackedBranchTube (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ (D : SingularTwoCell L.space) (BdM B : Set L.space)
      (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch),
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ (J Q C : Set (EuclideanSpace ℝ (Fin 2)))
        (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
        (sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph L.space (ℝ × ℝ × ℝ)),
        IsPLSphere 1 J → hD.IsMarkedBranchCollar c J Q C τ ρ sheet →
        ∃ (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) (_ : Finite Pc.faces)
          (N : Geometry.SimplicialComplex ℝ E) (_ : Finite N.faces) (φ : (ℝ × ℝ) × ℝ → E)
          (u : ℝ × ℝ → ℝ × ℝ) (r : Fin 4 → ℝ × ℝ),
          IsSourceTrackedBranchTube hD c Subtype.val L J ρ N Pc φ u r := by
  sorry

open Classical in
theorem NormalSingularCellData.not_branchPreimage_eq_of_isOrientable
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsCombinatorialManifold 3 L)
    (hor : IsOrientable 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J : Set (EuclideanSpace ℝ (Fin 2))}, IsPLSphere 1 J →
        hD.branchPreimage c = J → False := by
  classical
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc J hJ hpre
  obtain ⟨Q, C, τ, ρ, sheet, hmc⟩ := hD.exists_isMarkedBranchCollar hc hJ hpre
  obtain ⟨Pc, hPc, N, hN, φ, u, r, htube⟩ :=
    exists_isSourceTrackedBranchTube L hL D BdM B hD c hc J Q C τ ρ sheet hJ hmc
  have : Finite Pc.faces := hPc
  have : Finite N.faces := hN
  have : ConnectedSpace (hD.branchPreimage c) :=
    hD.connectedSpace_branchPreimage_of_isPLSphere_one c hJ hpre
  obtain ⟨R, Lc, hRfin, hRL, hNeq⟩ := htube.derived
  have : Finite R.faces := hRfin.to_subtype
  have hNor : IsOrientable 3 N := by
    subst hNeq
    exact (isOrientable_derivedNeighborhood_of_isSubdivision hL hor hRL Lc).1
  obtain ⟨g, v, hgc, hgb, hv01, hv12, hv23, hv30, hr⟩ := htube.cyclic
  obtain ⟨p, hpcov, hpcard, T, hl02, hl13⟩ :=
    exists_sourceRayTransport_of_isSourceTrackedBranchTube hD Subtype.val_injective hmc.2.1 htube
  have hconf : IsSheetExchange u g (v 0) (v 1) (v 2) (v 3) :=
    T.isSheetExchange hpcov hpcard htube.mapsTo hl02 hl13 hr hv01 hv12 hv23 hv30
  have hsq : u (u (g ((v 0 : ℝ) : loopCircle))) = g ((v 0 : ℝ) : loopCircle) := by
    rw [← hr 0]
    exact T.square_fixes_rays hpcov hpcard htube.mapsTo 0
  exact IsCylindricalDiagram.not_closedBranchCase1 Pc N htube.isPLBall htube.isManifold hNor
    htube.isCylindrical htube.isEndMap htube.seam hgc hgb hconf hsq

open Classical in
theorem NormalSystem.not_branchPreimage_eq_of_isOrientableManifold {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (S : NormalSystem F)
    (hor : S.IsOrientableManifold) :
    letI : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 S.manifoldComplex)
      (isCombinatorialManifold_double_succ_succ S.manifoldComplex S.isManifold)
    ∀ {D : SingularTwoCell (double 3 S.manifoldComplex).space}
      {BdM B : Set (double 3 S.manifoldComplex).space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J : Set (EuclideanSpace ℝ (Fin 2))}, IsPLSphere 1 J →
        hD.branchPreimage c = J → False := by
  classical
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 S.manifoldComplex)
    (isCombinatorialManifold_double_succ_succ S.manifoldComplex S.isManifold)
  intro D BdM B hD c hc J hJ hpre
  exact NormalSingularCellData.not_branchPreimage_eq_of_isOrientable
    (double 3 S.manifoldComplex)
    (isCombinatorialManifold_double_succ_succ S.manifoldComplex S.isManifold)
    (S.isOrientable_double_manifoldComplex hor) hD hc hJ hpre

end DifferentialGeometry.Topology.PiecewiseLinear
