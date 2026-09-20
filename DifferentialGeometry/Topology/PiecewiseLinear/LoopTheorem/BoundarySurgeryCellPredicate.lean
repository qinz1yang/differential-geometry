/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedCellPredicate

/-!
# Naming the direct boundary surgery cell of a boundary branch

`NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` of
`LoopTheorem.CutAndPaste` returns the *direct* candidate of a boundary branch cut
existentially, together with the whole cutting datum that built it: the two crosscuts `A` and
`C` of the branch preimage with the identification `g` between them, the two boundary arcs
`U` and `V` swept out in `M`, the pullback of the glued cell into `D.domain`, the injective
source parametrisations of the two arcs, and the three closed pieces `U₁`, `U₂`, `U₃` that
the crosscuts cut `D.domain` into.  The boundary case assemblies of
`LoopTheorem.CrossRegluedCellPredicate` cannot consume it in that form: they take the direct
candidate as a normality datum `hGd` together with the raw branch bookkeeping `origin`,
`hinj`, `hmiss`, and the producer hands out none of those three.

This file names it, exactly as `LoopTheorem.CrossRegluedCellPredicate` names the cross
reglued cell.  `NormalSingularCellData.IsBoundarySurgeryCell hD c Gd` is the conclusion of
that producer with `Gd` fixed and every other object it produces existentially quantified,
the conjuncts being those of the producer in its own order.  The predicate is inhabited
exactly where the producer applies, by
`NormalSingularCellData.exists_isBoundarySurgeryCell_of_boundaryBranch`.

## Why a predicate, and not a list of recorded conclusions

The same trap as for the cross reglue applies: a corollary quantified over every cell
satisfying the conclusions the producer *records* would be satisfied by cells that the
construction never produces, and the recorded conclusions alone do not locate the pullback
image inside `D.domain`, which is what the branch injection needs.  Pinning `Gd` to the
construction is what the predicate is for.  Here the predicate is in addition never satisfied
by `D` itself: `NormalSingularCellData.not_isBoundarySurgeryCell_self` reads that off the
recorded disjointness of the new double point set from the carrier of the branch `c`, whose
carrier is a nonempty subset of the double point set of `D`.

## The projections

* `NormalSingularCellData.nonempty_normalSingularCellData_of_isBoundarySurgeryCell`: the
  direct candidate is again a normal singular two cell over the same boundary data.  The datum
  comes out of a `Nonempty`, so no canonical one exists; every statement below is therefore
  made for an *arbitrary* normality datum `hG`, and the assemblies eliminate the `Nonempty`
  into their own `Prop` valued goal and use that one datum throughout.
* `NormalSingularCellData.doublePointSet_subset_of_isBoundarySurgeryCell` and
  `NormalSingularCellData.disjoint_doublePointSet_branchCarrier_of_isBoundarySurgeryCell`: the
  double points of the direct candidate are double points of `D`, and the branch `c` is gone.
* `NormalSingularCellData.image_subset_of_isBoundarySurgeryCell`: the direct candidate is
  carried by the image of `D`.
* `NormalSingularCellData.exists_injective_boundaryArcs_of_isBoundarySurgeryCell`: the two arc
  boundary word of the direct candidate, with the injective source parametrisations of its two
  arcs.
* `NormalSingularCellData.exists_branchOrigin_of_isBoundarySurgeryCell`: the branch
  bookkeeping.  This is `NormalSingularCellData.DescendingSurgery.ofBoundarySurgery` stopped
  one step early — at `branchOrigin`, `injective_branchOrigin_of_subset_or_disjoint` and
  `branchOrigin_ne` — because the assemblies want the injection itself and not the descending
  surgery it builds.

## The boundary case assemblies

`exists_descendingSurgery_of_crossSeamTube_reversing_of_isBoundarySurgeryCell`
and its endpoint preserving twin restate the two assemblies of
`LoopTheorem.CrossRegluedCellPredicate` with the four hypotheses `hGd`, `origin`, `hinj`,
`hmiss` replaced by the single hypothesis `hD.IsBoundarySurgeryCell c Gd`, taking the count of
explicit hypotheses from thirty nine to thirty six.  Everything else is verbatim; in
particular `Wdirect` still names the cell `Gd`, which is legitimate because
`BoundaryWordWitness Gd ρ w` depends on the cell alone and not on any normality datum for it.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-! ### The predicate -/

/-- **The direct boundary surgery cell of a boundary branch, as a predicate on the cell.**  A
cell `Gd` is a direct boundary surgery cell of the branch `c` of `hD` when the whole cutting
datum of `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` exists with
`Gd` as its output: the two crosscuts `A` and `C` of the branch preimage with the PL
identification `g` between them and the four marked points `p`, `q` on `A` and `r`, `s` on
`C`, the two arcs `U` and `V` of the boundary circle of `D`, the injective pullback of `Gd`
into `D.domain` missing `C`, the normality of `Gd` over the same boundary data, the two arc
boundary word of `Gd` with injective source parametrisations of its arcs, and the three closed
pieces `U₁`, `U₂`, `U₃` cut out by the two crosscuts, relative to which the pullback keeps
everything outside the middle piece and discards the middle band.  The conjuncts are those of
the producer, in its order. -/
def IsBoundarySurgeryCell (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (Gd : SingularTwoCell M) : Prop :=
  ∃ A C U V : Set (EuclideanSpace ℝ (Fin 2)),
  ∃ p q r s : EuclideanSpace ℝ (Fin 2),
  ∃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
  ∃ pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
    hD.branchPreimage c = A ∪ C ∧
    IsPLBall 1 U ∧ IsPLBall 1 V ∧ Disjoint U V ∧
    IsPLHomeomorphOn g A C ∧
    p ∈ A ∧ q ∈ A ∧ r ∈ C ∧ s ∈ C ∧
    EqOn D (D ∘ g) A ∧
    ((g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r)) ∧
    MapsTo pullback Gd.domain D.domain ∧
    InjOn pullback Gd.domain ∧
    EqOn (D ∘ pullback) Gd Gd.domain ∧
    Disjoint (pullback '' Gd.domain) C ∧
    Gd '' Gd.domain ⊆ D '' D.domain ∧
    Set.range Gd.boundary = D '' (U ∪ V) ∧
    Gd '' Gd.domain ∩ BdM = Set.range Gd.boundary ∧
    Set.range Gd.boundary ⊆ B ∧ Gd '' Gd.domain ∩ BdM ⊆ B ∧
    (∀ x ∈ Gd.domain, ∃ W ∈ 𝓝[Gd.domain] x, Set.InjOn Gd W) ∧
    (∀ y, (Gd.domain ∩ Gd ⁻¹' {y}).encard ≤ 2) ∧
    doublePointSet Gd Gd.domain ⊆ doublePointSet D D.domain ∧
    Disjoint (doublePointSet Gd Gd.domain) (hD.singularSet.branchCarrier c) ∧
    Nonempty (NormalSingularSetTriangulation Gd BdM) ∧
    Nonempty (NormalSingularCellData Gd BdM B) ∧
    ∃ (x y : M) (σ : Path x y) (ω : Path y x)
        (e : loopCircle ≃ₜ frontier Gd.domain),
      Set.range σ = D '' U ∧ Set.range ω = D '' V ∧
        (∀ θ, Gd (e θ) = pathToCircle (σ.trans ω) θ) ∧
        ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
        ∃ (a' b' : frontier Gd.domain) (ρ : Path a' b') (κ : Path b' a'),
          frontier Gd.domain = R ∪ T ∧
          Gd '' R = D '' U ∧ Gd '' T = D '' V ∧
          Function.Injective ρ ∧ Function.Injective κ ∧
          Set.range (fun t => ((ρ t : frontier Gd.domain) :
            EuclideanSpace ℝ (Fin 2))) = R ∧
          Set.range (fun t => ((κ t : frontier Gd.domain) :
            EuclideanSpace ℝ (Fin 2))) = T ∧
          (∀ θ, e θ = pathToCircle (ρ.trans κ) θ) ∧
          ∃ U₁ U₂ U₃ : Set (EuclideanSpace ℝ (Fin 2)),
            IsClosed U₁ ∧ IsClosed U₂ ∧ IsClosed U₃ ∧
            U₁ ∪ U₂ ∪ U₃ = D.domain ∧ U₁ ∩ U₂ = A ∧ U₂ ∩ U₃ = C ∧
            D.domain \ U₂ ⊆ pullback '' Gd.domain ∧
            Disjoint (pullback '' Gd.domain) (U₂ \ A)

/-- **The predicate is inhabited at every boundary branch.**  This is
`NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` read through
`NormalSingularCellData.IsBoundarySurgeryCell`: the cell it produces is a direct boundary
surgery cell of the branch, and the two statements have the same content. -/
theorem exists_isBoundarySurgeryCell_of_boundaryBranch [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ Gd : SingularTwoCell M, hD.IsBoundarySurgeryCell c Gd := by
  obtain ⟨A, C, U, V, p, q, r, s, g, Gd, pullback, hrest⟩ :=
    hD.exists_boundary_surgery_cell_of_boundaryBranch hc
  exact ⟨Gd, A, C, U, V, p, q, r, s, g, pullback, hrest⟩

/-! ### The projections -/

/-- **The direct boundary surgery cell is again normal** over the same boundary data.  The
datum is produced inside a `Nonempty`, so there is no canonical choice of it; consumers
eliminate the `Nonempty` into their own `Prop` valued goal. -/
theorem nonempty_normalSingularCellData_of_isBoundarySurgeryCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd) :
    Nonempty (NormalSingularCellData Gd BdM B) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hN, -⟩ := hGd
  exact hN

/-- The direct boundary surgery cell is carried by the image of the cell it was cut from. -/
theorem image_subset_of_isBoundarySurgeryCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {Gd : SingularTwoCell M}
    (hGd : hD.IsBoundarySurgeryCell c Gd) : ⇑Gd '' Gd.domain ⊆ ⇑D '' D.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, him, -⟩ := hGd
  exact him

/-- **The direct boundary surgery creates no double point**: every double point of the
candidate is a double point of the cell it was cut from. -/
theorem doublePointSet_subset_of_isBoundarySurgeryCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {Gd : SingularTwoCell M}
    (hGd : hD.IsBoundarySurgeryCell c Gd) :
    doublePointSet Gd Gd.domain ⊆ doublePointSet D D.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hsub, -⟩ := hGd
  exact hsub

/-- **The direct boundary surgery deletes the branch it was cut along**: the carrier of `c`
meets the double point set of the candidate nowhere. -/
theorem disjoint_doublePointSet_branchCarrier_of_isBoundarySurgeryCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd) :
    Disjoint (doublePointSet Gd Gd.domain) (hD.singularSet.branchCarrier c) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, hmissc, -⟩ := hGd
  exact hmissc

/-- **The cell it was cut from is never a direct boundary surgery cell of one of its own
branches.**  The predicate records that the double point set of the candidate misses the
carrier of `c`, while the carrier of `c` is a nonempty set of double points of `D`.  So the
degenerate instantiation `Gd = D`, which satisfies every *recorded conclusion* of the weaker
corollary shape, is excluded outright here. -/
theorem not_isBoundarySurgeryCell_self (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) : ¬ hD.IsBoundarySurgeryCell c D := by
  intro hGd
  obtain ⟨z, hz⟩ := (hD.singularSet.branchCarrier_isConnected c).nonempty
  exact Set.disjoint_right.mp
    (hD.disjoint_doublePointSet_branchCarrier_of_isBoundarySurgeryCell hGd) hz
    (hD.singularSet.branchCarrier_subset_doublePointSet c hz)

/-- **The two arc boundary word of the direct boundary surgery cell, parametrised in the
source.**  Its boundary circle splits into two PL arcs `R` and `T` whose images are traversed
by `σ` and `ω`, and both arcs carry *injective* paths of the frontier itself whose
concatenation parametrises the boundary circle through the recorded homeomorphism.  This is
the form `Path.Homotopic.of_injective_of_range_eq` consumes when a boundary word has to be
compared with a finer subdivision of the same circle. -/
theorem exists_injective_boundaryArcs_of_isBoundarySurgeryCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd) :
    ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
    ∃ (x y : M) (σ : Path x y) (ω : Path y x) (e : loopCircle ≃ₜ frontier Gd.domain),
    ∃ (a' b' : frontier Gd.domain) (ρ : Path a' b') (κ : Path b' a'),
      frontier Gd.domain = R ∪ T ∧
      Set.range σ = ⇑Gd '' R ∧ Set.range ω = ⇑Gd '' T ∧
      (∀ θ, Gd (e θ) = pathToCircle (σ.trans ω) θ) ∧
      Function.Injective ρ ∧ Function.Injective κ ∧
      Set.range (fun t => ((ρ t : frontier Gd.domain) :
        EuclideanSpace ℝ (Fin 2))) = R ∧
      Set.range (fun t => ((κ t : frontier Gd.domain) :
        EuclideanSpace ℝ (Fin 2))) = T ∧
      (∀ θ, e θ = pathToCircle (ρ.trans κ) θ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -,
    x, y, σ, ω, e, hσ, hω, hparam, R, T, a', b', ρ, κ,
    hfront, hRim, hTim, hρinj, hκinj, hρrange, hκrange, heparam, -⟩ := hGd
  exact ⟨R, T, x, y, σ, ω, e, a', b', ρ, κ, hfront, hσ.trans hRim.symm, hω.trans hTim.symm,
    hparam, hρinj, hκinj, hρrange, hκrange, heparam⟩

/-- **The branch bookkeeping of the direct boundary surgery.**  For *any* normality datum `hG`
of the candidate, its branches inject into the branches of `D` missing `c`.  This is the body
of `NormalSingularCellData.DescendingSurgery.ofBoundarySurgery` stopped one step before
`ofBranchInjection`: the recorded three piece decomposition and the recorded pullback identify
the double point set of the candidate with the double point set of `D` on the kept region, so
`NormalSingularCellData.branchCarrier_subset_or_disjoint_doublePointSet` says that no branch
other than `c` is cut in half, and
`NormalSingularSetTriangulation.injective_branchOrigin_of_subset_or_disjoint` turns that into
injectivity.  The datum `hG` is taken as an argument rather than chosen, because the type of
`origin` depends on it and consumers have their own datum in hand. -/
theorem exists_branchOrigin_of_isBoundarySurgeryCell [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    (hG : NormalSingularCellData Gd BdM B) :
    ∃ origin : hG.singularSet.Branch → hD.singularSet.Branch,
      Function.Injective origin ∧ ∀ b, origin b ≠ c := by
  obtain ⟨_, _, _, _, _, _, _, _, _, pb,
    -, -, -, hpre, -, -, -, -, -, -,
    -, -, -, -, hmaps, hinjp, heqp, -, -, -,
    -, -, -, -, -, hsub, hmissc, -, -,
    _, _, _, _, _, -, -, -, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -,
    U₁, U₂, U₃, h₁, h₂, h₃, hunion, h₁₂, h₂₃, hout, hin⟩ := hGd
  have hPD : pb '' Gd.domain ⊆ D.domain := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps hx
  have hdps : doublePointSet Gd Gd.domain = doublePointSet D (pb '' Gd.domain) :=
    doublePointSet_eq_image_of_pullback hinjp heqp
  have hwhole : ∀ a : hD.singularSet.Branch,
      hD.singularSet.branchCarrier a ⊆ doublePointSet Gd Gd.domain ∨
        Disjoint (hD.singularSet.branchCarrier a) (doublePointSet Gd Gd.domain) := by
    intro a
    by_cases hac : a = c
    · refine Or.inr ?_
      rw [hac]
      exact hmissc.symm
    · rw [hdps]
      exact hD.branchCarrier_subset_or_disjoint_doublePointSet h₁ h₂ h₃ hpre hunion h₁₂ h₂₃
        hPD hout hin hac
  exact ⟨hD.singularSet.branchOrigin hG.singularSet hsub,
    hD.singularSet.injective_branchOrigin_of_subset_or_disjoint hG.singularSet hsub hwhole,
    hD.singularSet.branchOrigin_ne hG.singularSet hsub hmissc⟩

/-! ### The boundary case assemblies -/

/-- **The boundary case of Moise's Lemma 2, endpoint reversing, with both candidates named.**
This is
`NormalSingularCellData.exists_descendingSurgery_of_crossSeamTube_reversing_of_isCrossRegluedCell`
with its four hypotheses about the direct candidate — the normality datum `hGd`, the branch
injection `origin` and its two properties `hinj` and `hmiss` — replaced by the single
hypothesis that `Gd` *is* the direct boundary surgery cell of the branch `c`, taking the count
of explicit hypotheses from thirty nine to thirty six.  All four are consequences of the
construction, so the boundary case no longer carries any of them as open obligations.  The
normality datum is not chosen: the recorded `Nonempty` is eliminated into the `Prop` valued
goal, and the branch injection is taken for that one datum, which is legitimate because
`Wdirect` constrains the cell `Gd` alone. -/
theorem exists_descendingSurgery_of_crossSeamTube_reversing_of_isBoundarySurgeryCell
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
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  obtain ⟨hnormal⟩ := hD.nonempty_normalSingularCellData_of_isBoundarySurgeryCell hGd
  obtain ⟨origin, hinj, hmiss⟩ := hD.exists_branchOrigin_of_isBoundarySurgeryCell hGd hnormal
  exact exists_descendingSurgery_of_crossSeamTube_reversing_of_isCrossRegluedCell T hdomain
    hcoord hreglued hresolved hcompl hG hendDisks hends htubeBdM hBdM hnormal origin hinj
    hmiss σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN hρ hrange Wdirect Wraw hΩ₁ hΩ₂ hcover
    hcocont hΩ₁tube hΩ₁max hlateral

/-- **The boundary case of Moise's Lemma 2, endpoint preserving, with both candidates named.**
The endpoint preserving twin of
`exists_descendingSurgery_of_crossSeamTube_reversing_of_isBoundarySurgeryCell`,
in the other relative direction of the cut: the second and the fourth arc of the boundary word
are loops, the direct candidate traverses `σ.trans υ` and the raw cross candidate
`σ.trans (τ.symm.trans (υ.trans φ.symm))`.  Nothing else changes. -/
theorem exists_descendingSurgery_of_crossSeamTube_preserving_of_isBoundarySurgeryCell
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
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  obtain ⟨hnormal⟩ := hD.nonempty_normalSingularCellData_of_isBoundarySurgeryCell hGd
  obtain ⟨origin, hinj, hmiss⟩ := hD.exists_branchOrigin_of_isBoundarySurgeryCell hGd hnormal
  exact exists_descendingSurgery_of_crossSeamTube_preserving_of_isCrossRegluedCell T hdomain
    hcoord hreglued hresolved hcompl hG hendDisks hends htubeBdM hBdM hnormal origin hinj
    hmiss σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN hρ hrange Wdirect Wraw hΩ₁ hΩ₂ hcover
    hcocont hΩ₁tube hΩ₁max hlateral

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
