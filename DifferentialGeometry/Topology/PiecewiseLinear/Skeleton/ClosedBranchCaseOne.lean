/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedBranchOrientability
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneCollar
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneSource
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTubeCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoOrientable

/-!
# Sorry-first skeleton of lane C-or1: the one circle closed case in an orientable manifold

The assembly `NormalSingularCellData.not_branchPreimage_eq_of_isOrientable` and its
specialisation `NormalSystem.not_branchPreimage_eq_of_isOrientableManifold` to the double are
proved for real from the leaves below and from the proved producers
`exists_isBranchDeckInvolution_of_branchPreimage_eq`,
`exists_isTwoSidedBranchCollar_of_branchPreimage_eq`, `isPLBall_of_isPLSphere_one` and
`IsCylindricalDiagram.not_closedBranchCase1`.  No `sorry` occurs inside an assembly.

The leaves, none of them reviewed.

* `NormalSingularCellData.exists_isMarkedCrossingChartAt` (item 4, owner W-A): at every point of
  the source circle `J` a crossing chart of the ambient manifold in which the sheet through that
  point is `(e z).2.2 = 0`, the sheet through its deck partner is `(e z).2.1 = 0`, the branch
  carrier is `(e z).2 = 0`, and on each sheet the positive half is the half that the proved two
  sided collar puts on the `Q` side of `J`.
* `exists_isAdaptedBranchTube` (item 8, owner W-B): a cylindrical diagram over a `2`-ball cross
  section, with an orientable combinatorial tube as target, containing the branch carrier, whose
  cross section circle meets the trace of the cell in exactly four marked points at every level,
  the end map permuting those four points.
* `exists_isSheetExchange_of_isAdaptedBranchTube` (item 9, owner W-B): a parametrisation of the
  cross section circle whose four marked parameters are the four rays, in cyclic order, with
  `IsSheetExchange` for the end map.  It is stated so that the four rays are only required to be
  the set of the four marked points, which leaves both cyclic orders open.
* `apply_apply_eq_self_of_isAdaptedBranchTube` (item 10, owner W-B): the square of the end map
  fixes each of the four rays, from the two sidedness of the proved collar over all of
  `J ×ˢ Icc (-1) 1`.

Departures from `consult/C-or1-design.md`, forced by the proved pieces or by types.

* The collar sign is the proved one: `ρ '' (J ×ˢ Icc 0 1) = C ∩ Q`, so `0 < s` is the `Q` side,
  the opposite of the design's `κ`.  All in/out clauses use `Ioc 0 1`.
* The marked chart is indexed by the source point `a ∈ J`, not by the branch point `⇑D a`.  The
  design's clause `∀ y ∈ Γ, ∀ a ∈ J, ⇑D a = y → IsMarkedCrossingChartAt … y a (sheet y)` is not
  satisfiable: one chart `e` would have to present both the sheet through `a` and the sheet
  through `τ a` as `(e z).2.2 = 0`, forcing the two sheets to agree near `⇑D a`, while the same
  chart makes their intersection the `1`-dimensional set `(e z).2 = 0`.
* The chart carries no `IsPiecewiseAffineOn` clause.  `IsPiecewiseAffineOn e e.source` for
  `e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)` is ill typed for a charted `M`, which is not a normed
  space; piecewise linearity of the tube comes from the simplicial side instead.
* Item 5 is not stated.  Both readings fail: for `a' = τ a` a preconnected `S ⊆ J` joining them
  has `⇑D '' S = Γ`, and the conclusion would identify the two sheets; and comparing two charts
  at one point needs an anchor convention for the label that the design defers to phase 2.  The
  transport of the marking along the branch is therefore an obligation inside item 8.
* The final theorem needs no clean disk `Q`: `isPLBall_of_isPLSphere_one` produces a `2`-ball
  with frontier `J` from `IsPLSphere 1 J` alone, which is what the collar producer consumes.  Its
  hypotheses are exactly those of the already stated leaf `not_branchPreimage_eq_of_isOrientable`
  of `Skeleton/DescentStepOrientable.lean`.
* The four arc sphere normalisation is not a leaf here: `FourArcSphere.lean` already proves
  `exists_isPLHomeomorphOn_fourArcSphere_of_isPLHomeomorphOn_Icc` in the required form.  It is a
  tool of item 8 and is not consumed by this assembly, so this skeleton does not test its
  interface; that file is deliberately not imported.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

def IsMarkedCrossingChartAt (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (J : Set (EuclideanSpace ℝ (Fin 2)))
    (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
    (a : EuclideanSpace ℝ (Fin 2)) (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) : Prop :=
  a ∈ J ∧ ⇑D a ∈ e.source ∧ e (⇑D a) = 0 ∧
    ∃ Pa Pb : Set (EuclideanSpace ℝ (Fin 2)),
      a ∈ Pa ∧ τ a ∈ Pb ∧ Disjoint Pa Pb ∧ Pa ⊆ D.domain ∧ Pb ⊆ D.domain ∧
      Pa ∈ 𝓝 a ∧ Pb ∈ 𝓝 (τ a) ∧ InjOn (⇑D) Pa ∧ InjOn (⇑D) Pb ∧
      MapsTo (⇑D) Pa e.source ∧ MapsTo (⇑D) Pb e.source ∧
      (∀ᶠ z in 𝓝 (⇑D a), z ∈ ⇑D '' Pa ↔ (e z).2.2 = 0) ∧
      (∀ᶠ z in 𝓝 (⇑D a), z ∈ ⇑D '' Pb ↔ (e z).2.1 = 0) ∧
      (∀ᶠ z in 𝓝 (⇑D a), z ∈ hD.singularSet.branchCarrier c ↔ (e z).2 = 0) ∧
      (∀ x ∈ Pa, 0 < (e (⇑D x)).2.1 ↔ ∃ s ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, s)) ∧
      ∀ x ∈ Pb, 0 < (e (⇑D x)).2.2 ↔ ∃ s ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, s)

def IsMarkedBranchCollar (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (J Q C : Set (EuclideanSpace ℝ (Fin 2)))
    (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
    (sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) : Prop :=
  hD.IsBranchDeckInvolution c J τ ∧ hD.IsTwoSidedBranchCollar c J Q C ρ ∧
    ∀ a ∈ J, hD.IsMarkedCrossingChartAt c J τ ρ a (sheet a)

theorem exists_isMarkedCrossingChartAt (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hτ : hD.IsBranchDeckInvolution c J τ) (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ), hD.IsMarkedCrossingChartAt c J τ ρ a e := by
  sorry

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
def IsAdaptedBranchTube (Z Γ : Set E) (N : Geometry.SimplicialComplex ℝ E)
    (hN : Finite N.faces) (Pc : Geometry.SimplicialComplex ℝ V) (hPc : Finite Pc.faces)
    (φ : V × ℝ → E) (u : V → V) (r : Fin 4 → V) : Prop :=
  letI := hN
  letI := hPc
  IsPLBall 2 Pc.space ∧ IsCombinatorialManifoldWithBoundary 3 N ∧ IsOrientable 3 N ∧
    IsCylindricalDiagram φ Pc.space N.space ∧ IsPLHomeomorphOn u Pc.space Pc.space ∧
    (∀ x ∈ Pc.space, φ (x, 0) = φ (u x, 1)) ∧ Γ ⊆ N.space ∧ Function.Injective r ∧
    (∀ i, r i ∈ (boundaryComplex 2 Pc).space) ∧ MapsTo u (Set.range r) (Set.range r) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      φ '' ((boundaryComplex 2 Pc).space ×ˢ {t}) ∩ Z = Set.range fun i => φ (r i, t)

open Classical in
theorem exists_isAdaptedBranchTube (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) (hor : IsOrientable 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ (D : SingularTwoCell L.space) (BdM B : Set L.space)
      (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch),
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ (J Q C : Set (EuclideanSpace ℝ (Fin 2)))
        (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
        (sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph L.space (ℝ × ℝ × ℝ)),
        IsPLSphere 1 J → hD.branchPreimage c = J →
        hD.IsMarkedBranchCollar c J Q C τ ρ sheet →
        ∃ (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) (hPc : Finite Pc.faces)
          (N : Geometry.SimplicialComplex ℝ E) (hN : Finite N.faces) (φ : (ℝ × ℝ) × ℝ → E)
          (u : ℝ × ℝ → ℝ × ℝ) (r : Fin 4 → ℝ × ℝ),
          IsAdaptedBranchTube (Subtype.val '' (⇑D '' D.domain))
            (Subtype.val '' hD.singularSet.branchCarrier c) N hN Pc hPc φ u r := by
  sorry

open Classical in
theorem exists_isSheetExchange_of_isAdaptedBranchTube (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ (D : SingularTwoCell L.space) (BdM B : Set L.space)
      (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch),
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ (J Q C : Set (EuclideanSpace ℝ (Fin 2)))
        (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
        (sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph L.space (ℝ × ℝ × ℝ)),
        IsPLSphere 1 J → hD.branchPreimage c = J →
        hD.IsMarkedBranchCollar c J Q C τ ρ sheet →
        ∀ (Pc : Geometry.SimplicialComplex ℝ V) (hPc : Finite Pc.faces)
          (N : Geometry.SimplicialComplex ℝ E) (hN : Finite N.faces) (φ : V × ℝ → E) (u : V → V)
          (r : Fin 4 → V),
          IsAdaptedBranchTube (Subtype.val '' (⇑D '' D.domain))
            (Subtype.val '' hD.singularSet.branchCarrier c) N hN Pc hPc φ u r →
          ∃ (g : loopCircle → V) (α β γ δ : ℝ),
            Continuous g ∧ BijOn g univ (boundaryComplex 2 Pc).space ∧
              Set.range r = {g (α : loopCircle), g (β : loopCircle), g (γ : loopCircle),
                g (δ : loopCircle)} ∧
              IsSheetExchange u g α β γ δ := by
  sorry

open Classical in
theorem apply_apply_eq_self_of_isAdaptedBranchTube (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ (D : SingularTwoCell L.space) (BdM B : Set L.space)
      (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch),
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ (J Q C : Set (EuclideanSpace ℝ (Fin 2)))
        (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
        (sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph L.space (ℝ × ℝ × ℝ)),
        IsPLSphere 1 J → hD.branchPreimage c = J →
        hD.IsMarkedBranchCollar c J Q C τ ρ sheet →
        ∀ (Pc : Geometry.SimplicialComplex ℝ V) (hPc : Finite Pc.faces)
          (N : Geometry.SimplicialComplex ℝ E) (hN : Finite N.faces) (φ : V × ℝ → E) (u : V → V)
          (r : Fin 4 → V),
          IsAdaptedBranchTube (Subtype.val '' (⇑D '' D.domain))
            (Subtype.val '' hD.singularSet.branchCarrier c) N hN Pc hPc φ u r →
          ∀ i, u (u (r i)) = r i := by
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
    exists_isAdaptedBranchTube L hL hor D BdM B hD c hc J Q C τ ρ sheet hJ hpre hmc
  obtain ⟨hball, hman, hNor, hcyl, hu, hfu, -, -, -, -, -⟩ := id htube
  obtain ⟨g, α, β, γ, δ, hgc, hgb, hrange, hconf⟩ :=
    exists_isSheetExchange_of_isAdaptedBranchTube L hL D BdM B hD c hc J Q C τ ρ sheet hJ hpre
      hmc Pc hPc N hN φ u r htube
  have hsq : u (u (g (α : loopCircle))) = g (α : loopCircle) := by
    obtain ⟨i, hi⟩ : g (α : loopCircle) ∈ Set.range r := by
      rw [hrange]
      exact Set.mem_insert _ _
    rw [← hi]
    exact apply_apply_eq_self_of_isAdaptedBranchTube L hL D BdM B hD c hc J Q C τ ρ sheet hJ hpre
      hmc Pc hPc N hN φ u r htube i
  exact IsCylindricalDiagram.not_closedBranchCase1 Pc N hball hman hNor hcyl hu hfu hgc hgb hconf
    hsq

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
