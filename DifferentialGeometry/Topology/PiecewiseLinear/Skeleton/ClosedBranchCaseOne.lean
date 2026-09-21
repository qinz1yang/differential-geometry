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

The leaves.

* `NormalSingularCellData.exists_isMarkedCrossingChartAt` (item 4, owner W-A, reviewed
  2026-09-21, frozen): at every point of the source circle `J` a crossing chart of the ambient
  manifold in which the sheet through that point is `(e z).2.2 = 0`, the sheet through its deck
  partner is `(e z).2.1 = 0`, the branch carrier is `(e z).2 = 0`, and on each sheet the positive
  half is the half that the proved two sided collar puts on the `Q` side of `J`.
* `exists_isSourceTrackedBranchTube` (item 8, owner W-B, new, unreviewed): a cylindrical diagram
  over a `2`-ball cross section whose target is a derived neighbourhood of a subcomplex of a
  subdivision of the ambient complex, containing the branch carrier in its intrinsic interior,
  whose cross section circle meets the trace of the cell in exactly four marked points at every
  level, together with the parametrisation of that circle putting the four rays in cyclic order
  and with the source realisation of the four rays along the branch.  It carries no orientability
  hypothesis and no orientability clause.

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
orientability through `isOrientable_derivedNeighborhood_of_isSubdivision`, which is why the
predicate records the derived neighbourhood presentation and not a bare inclusion of spaces.

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
  satisfiable: one chart `e` would have to present both the sheet through `a` and the sheet
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

/-! ### Elementary inputs of the transport argument -/

theorem eq_of_mem_of_ne_of_encard_eq_two {X : Type*} {F : Set X} (hF : F.encard = 2) {x y z : X}
    (hx : x ∈ F) (hy : y ∈ F) (hz : z ∈ F) (hxz : x ≠ z) (hyz : y ≠ z) : x = y := by
  obtain ⟨w, w', hww', hFeq⟩ := Set.encard_eq_two.mp hF
  subst hFeq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hz with hz | hz
  · rcases hx with hx | hx
    · exact absurd (hx.trans hz.symm) hxz
    · rcases hy with hy | hy
      · exact absurd (hy.trans hz.symm) hyz
      · exact hx.trans hy.symm
  · rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact hx.trans hy.symm
      · exact absurd (hy.trans hz.symm) hyz
    · exact absurd (hx.trans hz.symm) hxz

theorem pos_iff_pos_of_forall_ne_zero {f : C(unitInterval, ℝ)} (hf : ∀ t, f t ≠ 0)
    (t₀ t₁ : unitInterval) : 0 < f t₀ ↔ 0 < f t₁ := by
  have key : ∀ a b : unitInterval, 0 < f a → 0 < f b := by
    intro a b ha
    by_contra hb
    have hblt : f b < 0 := lt_of_le_of_ne (not_lt.mp hb) (hf b)
    obtain ⟨t, ht⟩ := intermediate_value_univ b a f.continuous ⟨hblt.le, ha.le⟩
    exact hf t ht
  exact ⟨fun h => key t₀ t₁ h, fun h => key t₁ t₀ h⟩

theorem loopCircle_coe_one_eq_coe_zero : ((1 : ℝ) : loopCircle) = ((0 : ℝ) : loopCircle) := by
  have h := loopCircle_coe_add_one (0 : ℝ)
  rwa [zero_add] at h

theorem apply_one_ne_apply_zero_of_fiber_encard_eq_two {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [T2Space X] {p : X → loopCircle} (hp : IsCoveringMap p)
    (hcard : ∀ θ, (p ⁻¹' {θ}).encard = 2) (cl : C(unitInterval, X))
    (hcl : ∀ t : unitInterval, p (cl t) = ((t : ℝ) : loopCircle)) : cl 1 ≠ cl 0 := by
  have : Nonempty loopCircle := ⟨0⟩
  intro hloop
  refine Covering.not_exists_continuous_section_of_fiber_card_two hp hcard
    ⟨pathToCircle (⟨cl, rfl, hloop⟩ : Path (cl 0) (cl 0)), ?_⟩
  intro θ
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  rw [pathToCircle_coe]
  exact hcl t

/-! ### The transport of the four rays along the branch -/

structure SourceRayTransport {X : Type*} [TopologicalSpace X] {W : Type*}
    (p : X → loopCircle) (u : W → W) (r : Fin 4 → W) where
  lift : Fin 4 → C(unitInterval, X)
  side : Fin 4 → Prop
  over_base : ∀ (i : Fin 4) (t : unitInterval), p (lift i t) = ((t : ℝ) : loopCircle)
  label_injective : Function.Injective fun i => (lift i 0, side i)
  seam : ∀ i j : Fin 4, u (r i) = r j → lift i 0 = lift j 1 ∧ side i = side j

namespace SourceRayTransport

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [T2Space X] {W : Type*}
  {p : X → loopCircle} {u : W → W} {r : Fin 4 → W}

theorem square_fixes_rays (hp : IsCoveringMap p) (hcard : ∀ θ, (p ⁻¹' {θ}).encard = 2)
    (T : SourceRayTransport p u r) (hperm : MapsTo u (Set.range r) (Set.range r)) (i : Fin 4) :
    u (u (r i)) = r i := by
  obtain ⟨j, hj⟩ := hperm (Set.mem_range_self i)
  obtain ⟨k, hk⟩ := hperm (Set.mem_range_self j)
  have hij := T.seam i j hj.symm
  have hjk := T.seam j k hk.symm
  have hne : ∀ m : Fin 4, T.lift m 1 ≠ T.lift m 0 := fun m =>
    apply_one_ne_apply_zero_of_fiber_encard_eq_two hp hcard (T.lift m) (T.over_base m)
  have hzero : ∀ m : Fin 4, T.lift m 0 ∈ p ⁻¹' {((0 : ℝ) : loopCircle)} :=
    fun m => T.over_base m 0
  have h1 : T.lift k 0 ≠ T.lift j 0 := by
    rw [hjk.1]
    exact (hne k).symm
  have h2 : T.lift i 0 ≠ T.lift j 0 := by
    rw [hij.1]
    exact hne j
  have hki : T.lift k 0 = T.lift i 0 :=
    eq_of_mem_of_ne_of_encard_eq_two (hcard _) (hzero k) (hzero i) (hzero j) h1 h2
  have hside : T.side k = T.side i := (hij.2.trans hjk.2).symm
  have hlabel : ((T.lift k 0, T.side k) : X × Prop) = (T.lift i 0, T.side i) := by
    rw [hki, hside]
  have hkeq : k = i := T.label_injective hlabel
  calc u (u (r i)) = u (r j) := by rw [hj]
    _ = r k := hk.symm
    _ = r i := by rw [hkeq]

theorem isSheetExchange (hp : IsCoveringMap p) (hcard : ∀ θ, (p ⁻¹' {θ}).encard = 2)
    (T : SourceRayTransport p u r) (hperm : MapsTo u (Set.range r) (Set.range r))
    (h02 : T.lift 0 0 = T.lift 2 0) (h13 : T.lift 1 0 = T.lift 3 0) {g : loopCircle → W}
    {v : Fin 4 → ℝ} (hr : ∀ i, r i = g ((v i : ℝ) : loopCircle)) (hv01 : v 0 < v 1)
    (hv12 : v 1 < v 2) (hv23 : v 2 < v 3) (hv30 : v 3 < v 0 + 1) :
    IsSheetExchange u g (v 0) (v 1) (v 2) (v 3) := by
  have hfour : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  have hne : ∀ m : Fin 4, T.lift m 1 ≠ T.lift m 0 := fun m =>
    apply_one_ne_apply_zero_of_fiber_encard_eq_two hp hcard (T.lift m) (T.over_base m)
  have hpartner : ∀ i : Fin 4, ∃ j : Fin 4, u (r i) = r j := by
    intro i
    obtain ⟨j, hj⟩ := hperm (Set.mem_range_self i)
    exact ⟨j, hj.symm⟩
  refine ⟨hv01, hv12, hv23, hv30, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hr 0, ← hr 1, ← hr 3]
    obtain ⟨j, hj⟩ := hpartner 0
    have hl := (T.seam 0 j hj).1
    rcases hfour j with rfl | rfl | rfl | rfl
    · exact absurd hl.symm (hne 0)
    · exact Or.inl hj
    · exact absurd (hl.symm.trans h02) (hne 2)
    · exact Or.inr hj
  · rw [← hr 0, ← hr 1, ← hr 2]
    obtain ⟨j, hj⟩ := hpartner 1
    have hl := (T.seam 1 j hj).1
    rcases hfour j with rfl | rfl | rfl | rfl
    · exact Or.inl hj
    · exact absurd hl.symm (hne 1)
    · exact Or.inr hj
    · exact absurd (hl.symm.trans h13) (hne 3)
  · rw [← hr 1, ← hr 2, ← hr 3]
    obtain ⟨j, hj⟩ := hpartner 2
    have hl := (T.seam 2 j hj).1
    rcases hfour j with rfl | rfl | rfl | rfl
    · exact absurd (hl.symm.trans h02.symm) (hne 0)
    · exact Or.inl hj
    · exact absurd hl.symm (hne 2)
    · exact Or.inr hj
  · rw [← hr 0, ← hr 2, ← hr 3]
    obtain ⟨j, hj⟩ := hpartner 3
    have hl := (T.seam 3 j hj).1
    rcases hfour j with rfl | rfl | rfl | rfl
    · exact Or.inl hj
    · exact absurd (hl.symm.trans h13.symm) (hne 1)
    · exact Or.inr hj
    · exact absurd hl.symm (hne 3)
  · rw [← hr 0, ← hr 2]
    intro heq
    obtain ⟨k, hk⟩ := hpartner 2
    have hs0 := (T.seam 0 k (heq.trans hk)).2
    have hs2 := (T.seam 2 k hk).2
    have hlabel : ((T.lift 0 0, T.side 0) : X × Prop) = (T.lift 2 0, T.side 2) := by
      rw [h02, hs0, hs2]
    exact absurd (T.label_injective hlabel) (by decide)
  · rw [← hr 1, ← hr 3]
    intro heq
    obtain ⟨k, hk⟩ := hpartner 3
    have hs1 := (T.seam 1 k (heq.trans hk)).2
    have hs3 := (T.seam 3 k hk).2
    have hlabel : ((T.lift 1 0, T.side 1) : X × Prop) = (T.lift 3 0, T.side 3) := by
      rw [h13, hs1, hs3]
    exact absurd (T.label_injective hlabel) (by decide)

end SourceRayTransport

/-! ### The orientation free, source tracked tube -/

open Classical in
structure IsSourceTrackedBranchTube {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) (ι : M → E)
    (L : Geometry.SimplicialComplex ℝ E) (J : Set (EuclideanSpace ℝ (Fin 2)))
    (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
    (N : Geometry.SimplicialComplex ℝ E) (Pc : Geometry.SimplicialComplex ℝ V)
    (φ : V × ℝ → E) (u : V → V) (r : Fin 4 → V) : Prop where
  isPLBall : IsPLBall 2 Pc.space
  isManifold : IsCombinatorialManifoldWithBoundary 3 N
  isCylindrical : IsCylindricalDiagram φ Pc.space N.space
  isEndMap : IsPLHomeomorphOn u Pc.space Pc.space
  seam : ∀ x ∈ Pc.space, φ (x, 0) = φ (u x, 1)
  mapsTo : MapsTo u (Set.range r) (Set.range r)
  trace : ∀ t ∈ Icc (0 : ℝ) 1,
    φ '' ((boundaryComplex 2 Pc).space ×ˢ {t}) ∩ ι '' (⇑D '' D.domain) =
      Set.range fun i => φ (r i, t)
  derived : ∃ R Lc : Geometry.SimplicialComplex ℝ E,
    R.faces.Finite ∧ IsSubdivision R L ∧ N = derivedNeighborhood R Lc
  branchInterior : ι '' hD.singularSet.branchCarrier c ⊆ N.space \ (boundaryComplex 3 N).space
  cyclic : ∃ (g : loopCircle → V) (v : Fin 4 → ℝ), Continuous g ∧
    BijOn g univ (boundaryComplex 2 Pc).space ∧ v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧
      v 3 < v 0 + 1 ∧ ∀ i, r i = g ((v i : ℝ) : loopCircle)
  realisation : ∃ (e : loopCircle ≃ₜ (hD.singularSet.branchComplex c).space)
    (a : Fin 4 → C(unitInterval, EuclideanSpace ℝ (Fin 2))) (s : Fin 4 → C(unitInterval, ℝ)),
    (∀ i t, a i t ∈ J) ∧ (∀ i t, s i t ∈ Icc (-1 : ℝ) 1) ∧ (∀ i t, s i t ≠ 0) ∧
      (∀ (i : Fin 4) (t : unitInterval), ⇑D (a i t) =
        (hD.singularSet.branchPieceIn c).map ↑(e ((t : ℝ) : loopCircle))) ∧
      (∀ (i : Fin 4) (t : unitInterval), φ (r i, (t : ℝ)) = ι (⇑D (ρ (a i t, s i t)))) ∧
      (∀ i j : Fin 4, a i 0 = a j 0 → (0 < s i 0 ↔ 0 < s j 0) → i = j) ∧
      a 0 0 = a 2 0 ∧ a 1 0 = a 3 0 ∧ a 0 0 ≠ a 1 0

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem eq_of_apply_eq_of_isTwoSidedBranchCollar (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ) {w w' : EuclideanSpace ℝ (Fin 2)} {v v' : ℝ}
    (hw : w ∈ J) (hv : v ∈ Icc (-1 : ℝ) 1) (hv0 : v ≠ 0) (hw' : w' ∈ J)
    (hv' : v' ∈ Icc (-1 : ℝ) 1) (heq : ⇑D (ρ (w, v)) = ⇑D (ρ (w', v'))) : w = w' ∧ v = v' := by
  obtain ⟨-, -, hCint, -, -, hρpl, hρ0, hdpp, -, -, -, -, -⟩ := hρ
  have hx : ρ (w, v) ∈ C := hρpl.bijOn.mapsTo ⟨hw, hv⟩
  have hy : ρ (w', v') ∈ C := hρpl.bijOn.mapsTo ⟨hw', hv'⟩
  have hxd : ρ (w, v) ∈ D.domain := interior_subset (hCint hx)
  have hyd : ρ (w', v') ∈ D.domain := interior_subset (hCint hy)
  have hsame : ρ (w, v) = ρ (w', v') := by
    by_contra hne
    have hmem : ρ (w, v) ∈ doublePointPreimage (⇑D) D.domain :=
      ⟨hxd, ρ (w, v), hxd, ρ (w', v'), hyd, hne, rfl, heq.symm⟩
    have hJmem : ρ (w, v) ∈ J := hdpp.subset ⟨hmem, hx⟩
    have hpair : ((ρ (w, v), (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) = (w, v) :=
      hρpl.bijOn.injOn ⟨hJmem, by constructor <;> norm_num⟩ ⟨hw, hv⟩ (hρ0 _ hJmem)
    exact hv0 (congrArg Prod.snd hpair).symm
  have hpair : ((w, v) : EuclideanSpace ℝ (Fin 2) × ℝ) = (w', v') :=
    hρpl.bijOn.injOn ⟨hw, hv⟩ ⟨hw', hv'⟩ hsame
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

end NormalSingularCellData

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

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
open Classical in
theorem exists_sourceRayTransport_of_isSourceTrackedBranchTube {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M] {D : SingularTwoCell M}
    {BdM B : Set M} (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {ι : M → E} (hι : Function.Injective ι) {L : Geometry.SimplicialComplex ℝ E}
    {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ) {N : Geometry.SimplicialComplex ℝ E}
    {Pc : Geometry.SimplicialComplex ℝ V} {φ : V × ℝ → E} {u : V → V} {r : Fin 4 → V}
    (h : IsSourceTrackedBranchTube hD c ι L J ρ N Pc φ u r) :
    ∃ p : hD.branchPreimage c → loopCircle, IsCoveringMap p ∧
      (∀ θ, (p ⁻¹' {θ}).encard = 2) ∧
        ∃ T : SourceRayTransport p u r, T.lift 0 0 = T.lift 2 0 ∧ T.lift 1 0 = T.lift 3 0 := by
  classical
  obtain ⟨e, a, s, hmemJ, hmemS, hnz, hbase, hreal, hlab, h02, h13, -⟩ := h.realisation
  obtain ⟨g, v, -, hgb, -, -, -, -, hr⟩ := h.cyclic
  have hpre : hD.branchPreimage c = J := hρ.1
  have hmemP : ∀ (i : Fin 4) (t : unitInterval), a i t ∈ hD.branchPreimage c := by
    intro i t
    rw [hpre]
    exact hmemJ i t
  have hrmem : ∀ i : Fin 4, r i ∈ Pc.space := by
    intro i
    rw [hr i]
    exact boundaryComplex_space_subset 2 Pc (hgb.mapsTo (mem_univ _))
  have hproj : ∀ (i : Fin 4) (t : unitInterval),
      hD.branchProjection c ⟨a i t, hmemP i t⟩ = e ((t : ℝ) : loopCircle) := by
    intro i t
    apply Subtype.ext
    have hmem1 : hD.branchCoordinate c (a i t) ∈
        (hD.singularSet.branchPieceIn c).complex.space :=
      hD.branchCoordinate_mem c (hmemP i t)
    have hmem2 : (e ((t : ℝ) : loopCircle)).1 ∈
        (hD.singularSet.branchPieceIn c).complex.space := (e ((t : ℝ) : loopCircle)).2
    exact (hD.singularSet.branchPieceIn c).bijOn.injOn hmem1 hmem2
      ((hD.branchPieceIn_map_branchCoordinate c (hmemP i t)).trans (hbase i t))
  refine ⟨⇑e.symm ∘ hD.branchProjection c,
    (hD.branchProjection_isCoveringMap c).homeomorph_comp e.symm, ?_, ?_⟩
  · intro θ
    have hset : (⇑e.symm ∘ hD.branchProjection c) ⁻¹' {θ} =
        hD.branchProjection c ⁻¹' {e θ} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
      constructor
      · intro hx
        rw [← hx, Homeomorph.apply_symm_apply]
      · intro hx
        rw [hx, Homeomorph.symm_apply_apply]
    rw [hset]
    exact hD.branchProjection_fiber_encard_eq_two c (e θ)
  · refine ⟨⟨fun i => ⟨fun t => ⟨a i t, hmemP i t⟩, (a i).continuous.subtype_mk (hmemP i)⟩,
      fun i => 0 < s i 0, ?_, ?_, ?_⟩, Subtype.ext h02, Subtype.ext h13⟩
    · intro i t
      change e.symm (hD.branchProjection c ⟨a i t, hmemP i t⟩) = ((t : ℝ) : loopCircle)
      rw [hproj i t, Homeomorph.symm_apply_apply]
    · intro i j hij
      have hw : a i 0 = a j 0 := congrArg Subtype.val (congrArg Prod.fst hij)
      have hs : (0 < s i 0) = (0 < s j 0) := congrArg Prod.snd hij
      exact hlab i j hw (by rw [hs])
    · intro i j hij
      have hfi : φ (r i, (0 : ℝ)) = ι (⇑D (ρ (a i 0, s i 0))) := hreal i 0
      have hfj : φ (r j, (1 : ℝ)) = ι (⇑D (ρ (a j 1, s j 1))) := hreal j 1
      have hφ : φ (r i, (0 : ℝ)) = φ (r j, (1 : ℝ)) := by
        rw [h.seam (r i) (hrmem i), hij]
      have hDeq : ⇑D (ρ (a i 0, s i 0)) = ⇑D (ρ (a j 1, s j 1)) :=
        hι (by rw [← hfi, ← hfj]; exact hφ)
      obtain ⟨hwa, hvs⟩ := hD.eq_of_apply_eq_of_isTwoSidedBranchCollar hρ (hmemJ i 0)
        (hmemS i 0) (hnz i 0) (hmemJ j 1) (hmemS j 1) hDeq
      refine ⟨Subtype.ext hwa, ?_⟩
      rw [hvs]
      exact propext (pos_iff_pos_of_forall_ne_zero (f := s j) (hnz j) 1 0)

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
