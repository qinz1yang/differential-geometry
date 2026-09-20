/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.LoopClassReparametrization

/-!
# Parametrizing the boundary circle of a proper PL embedded disk

`EmbeddedDisk.boundary_range` records only an equality of image sets,
`range (fun θ => (boundaryLoop θ : E)) = map '' frontier domain`.  A boundary word argument
needs an actual parametrization of the source boundary circle.  This file provides one and
measures exactly how far the stored loop is from that parametrized single traversal.

Main results.

* `EmbeddedDisk.nonempty_boundaryParam`: the frontier of the domain is a PL `1`-sphere, so it
  is the homeomorphic image of `loopCircle`.
* `EmbeddedDisk.paramLoop`: the single traversal `θ ↦ D.map (a θ)` attached to such a
  parametrization `a`; it is an injective loop in the boundary neighborhood whose image set is
  `D.map '' frontier D.domain`, that is, the image set of `D.boundaryLoop`.
* `EmbeddedDisk.exists_reparametrization`: the stored loop factors as `paramLoop a ∘ ρ` for a
  continuous surjection `ρ` of `loopCircle` onto itself.  This is the precise sense in which
  `D.boundaryLoop` runs over the single traversal, and it is what equality of image sets
  actually gives.
* `EmbeddedDisk.not_loopClassMeets_paramLoop_of_injective` and
  `EmbeddedDisk.exists_param_boundaryLoop_of_injective`: the avoidance condition transfers
  from `D.boundaryLoop` to the single traversal once `ρ` is invertible, for which injectivity
  of the stored loop suffices.
* `exists_real_lift_intShift` and `EmbeddedDisk.exists_reparametrization_intShift`: `ρ` lifts
  through the covering `ℝ → loopCircle` to a continuous real map whose shift over one period is
  a constant integer `n`.  This is the exact sense in which the stored boundary loop runs `n`
  times around the parametrized boundary circle.
* `not_conjugacyClassMeets_of_not_conjugacyClassMeets_zpow` and
  `EmbeddedDisk.not_loopClassMeets_paramLoop_of_conjugacyClass_eq_zpow`: granted that the free
  homotopy class of the stored loop is the `n`-th power of the class of the single traversal,
  the avoidance condition transfers, with no injectivity hypothesis.

Two of the transfers are qualified, and deliberately so.  The structure `EmbeddedDisk` relates
`boundaryLoop` to `map` only through equality of image sets, so nothing in it forces `ρ` to have
degree `±1`.  What is still missing is the identification of the free homotopy class of
`paramLoop a ∘ ρ` with the `n`-th power of the class of `paramLoop a`, the hypothesis `hpow`
of the last theorem.  That step needs a degree theory for self maps of `loopCircle`, which is
not developed here.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The frontier of the domain of an embedded disk is contained in that domain. -/
theorem EmbeddedDisk.frontier_domain_subset {S : NormalSystem E} (D : EmbeddedDisk S) :
    frontier D.domain ⊆ D.domain :=
  D.isPLBall_domain.isPolyhedron.isClosed.frontier_subset

/-- The frontier of the domain of an embedded disk is a piecewise linear `1`-sphere. -/
theorem EmbeddedDisk.isPLSphere_frontier_domain {S : NormalSystem E} (D : EmbeddedDisk S) :
    IsPLSphere 1 (frontier D.domain) :=
  D.isPLBall_domain.isPLSphere_frontier

/-- The source boundary circle of an embedded disk has a parametrization by `loopCircle`. -/
theorem EmbeddedDisk.nonempty_boundaryParam {S : NormalSystem E} (D : EmbeddedDisk S) :
    Nonempty (loopCircle ≃ₜ frontier D.domain) :=
  nonempty_homeomorph_loopCircle_of_isPLSphere_one D.isPLSphere_frontier_domain

/-- The boundary image of an embedded disk lies in the boundary neighborhood of the system. -/
theorem EmbeddedDisk.image_frontier_subset {S : NormalSystem E} (D : EmbeddedDisk S) :
    D.map '' frontier D.domain ⊆ S.boundaryNeighborhood.space := by
  rw [← D.boundary_range]
  rintro _ ⟨θ, rfl⟩
  exact (D.boundaryLoop θ).2

/-- The single traversal of the boundary circle of an embedded disk determined by a
parametrization `a` of `frontier D.domain`. -/
noncomputable def EmbeddedDisk.paramLoop {S : NormalSystem E} (D : EmbeddedDisk S)
    (a : loopCircle ≃ₜ frontier D.domain) : freeLoop S.boundaryNeighborhoodSpace where
  toFun θ := ⟨D.map (a θ), D.image_frontier_subset (mem_image_of_mem D.map (a θ).2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hcont : ContinuousOn D.map (frontier D.domain) :=
      D.isPLHomeomorphOn.isPiecewiseAffineOn.continuousOn.mono D.frontier_domain_subset
    exact hcont.comp_continuous (continuous_subtype_val.comp a.continuous) fun θ => (a θ).2

/-- The single traversal evaluates to `D.map` applied to the parametrization. -/
theorem EmbeddedDisk.paramLoop_apply_coe {S : NormalSystem E} (D : EmbeddedDisk S)
    (a : loopCircle ≃ₜ frontier D.domain) (θ : loopCircle) :
    (D.paramLoop a θ : E) = D.map (a θ) := rfl

/-- The single traversal has exactly the image set recorded by `EmbeddedDisk.boundary_range`. -/
theorem EmbeddedDisk.paramLoop_range {S : NormalSystem E} (D : EmbeddedDisk S)
    (a : loopCircle ≃ₜ frontier D.domain) :
    range (fun θ => (D.paramLoop a θ : E)) = D.map '' frontier D.domain := by
  have hval : range (fun θ : loopCircle => ((a θ : EuclideanSpace ℝ (Fin 2)))) =
      frontier D.domain := by
    rw [show (fun θ : loopCircle => ((a θ : EuclideanSpace ℝ (Fin 2)))) =
        Subtype.val ∘ (a : loopCircle → frontier D.domain) from rfl,
      range_comp, a.surjective.range_eq, image_univ, Subtype.range_coe]
  rw [show (fun θ => (D.paramLoop a θ : E)) =
      D.map ∘ (fun θ : loopCircle => ((a θ : EuclideanSpace ℝ (Fin 2)))) from rfl,
    range_comp, hval]

/-- The single traversal is an injective loop, that is, a simple closed curve. -/
theorem EmbeddedDisk.paramLoop_injective {S : NormalSystem E} (D : EmbeddedDisk S)
    (a : loopCircle ≃ₜ frontier D.domain) : Function.Injective (D.paramLoop a) := by
  intro θ η h
  have hval : D.map (a θ) = D.map (a η) := congrArg Subtype.val h
  exact a.injective (Subtype.ext (D.isPLHomeomorphOn.bijOn.injOn
    (D.frontier_domain_subset (a θ).2) (D.frontier_domain_subset (a η).2) hval))

/-- Equality of image sets upgrades to a factorization: the stored boundary loop of an
embedded disk is the single traversal precomposed with a continuous surjection of
`loopCircle` onto itself. -/
theorem EmbeddedDisk.exists_reparametrization {S : NormalSystem E} (D : EmbeddedDisk S)
    (a : loopCircle ≃ₜ frontier D.domain) :
    ∃ ρ : C(loopCircle, loopCircle), Function.Surjective ρ ∧
      D.boundaryLoop = (D.paramLoop a).comp ρ := by
  classical
  have : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  set g : freeLoop S.boundaryNeighborhoodSpace := D.paramLoop a with hgdef
  have hginj : Function.Injective g := D.paramLoop_injective a
  have hrange : range (fun θ => (g θ : E)) = range (fun θ => (D.boundaryLoop θ : E)) := by
    rw [D.boundary_range, hgdef]
    exact D.paramLoop_range a
  have hmem : ∀ θ, D.boundaryLoop θ ∈ range g := by
    intro θ
    obtain ⟨η, hη⟩ : (D.boundaryLoop θ : E) ∈ range (fun θ => (g θ : E)) := by
      rw [hrange]
      exact ⟨θ, rfl⟩
    exact ⟨η, Subtype.ext hη⟩
  have hmem' : ∀ η, g η ∈ range (fun θ => D.boundaryLoop θ) := by
    intro η
    obtain ⟨θ, hθ⟩ : (g η : E) ∈ range (fun θ => (D.boundaryLoop θ : E)) := by
      rw [← hrange]
      exact ⟨η, rfl⟩
    exact ⟨θ, Subtype.ext hθ⟩
  let e : loopCircle ≃ₜ range g :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective g hginj)
      (Continuous.subtype_mk g.continuous _)
  have hcoe : ∀ θ, ((e θ : range g) : S.boundaryNeighborhoodSpace) = g θ := fun _ => rfl
  refine ⟨⟨fun θ => e.symm ⟨D.boundaryLoop θ, hmem θ⟩,
      e.symm.continuous.comp (Continuous.subtype_mk D.boundaryLoop.continuous _)⟩, ?_, ?_⟩
  · intro η
    obtain ⟨θ, hθ⟩ := hmem' η
    refine ⟨θ, ?_⟩
    have hEq : (⟨D.boundaryLoop θ, hmem θ⟩ : range g) = e η :=
      Subtype.ext (by rw [hcoe]; exact hθ)
    change e.symm ⟨D.boundaryLoop θ, hmem θ⟩ = η
    rw [hEq, e.symm_apply_apply]
  · refine ContinuousMap.ext fun θ => ?_
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨D.boundaryLoop θ, hmem θ⟩)).symm

/-- The conjugacy class condition stored on an embedded disk, in `loopClassMeets` form. -/
theorem EmbeddedDisk.not_loopClassMeets_boundaryLoop {S : NormalSystem E}
    [PathConnectedSpace S.boundaryNeighborhoodSpace] (D : EmbeddedDisk S) :
    ¬loopClassMeets D.boundaryLoop S.basepoint S.normalSubgroup := by
  have hclass : FreeLoop.conjugacyClass D.boundaryLoop S.basepoint =
      normalSystemLoopConjugacyClass S.basepoint D.boundaryLoop D.connector :=
    FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong D.connector
      (⟨D.boundaryLoop, rfl⟩ : basedCircleLoop (D.boundaryLoop 0))
  intro hmeet
  exact D.loopClass_avoids_normal (hclass ▸ hmeet)

/-- If the stored boundary loop of an embedded disk is injective, then the reparametrization
produced by `EmbeddedDisk.exists_reparametrization` is a homeomorphism of `loopCircle`, and the
avoidance condition transfers to the parametrized single traversal. -/
theorem EmbeddedDisk.not_loopClassMeets_paramLoop_of_injective {S : NormalSystem E}
    [PathConnectedSpace S.boundaryNeighborhoodSpace] (D : EmbeddedDisk S)
    (a : loopCircle ≃ₜ frontier D.domain) (hinj : Function.Injective D.boundaryLoop) :
    ¬loopClassMeets (D.paramLoop a) S.basepoint S.normalSubgroup := by
  classical
  have : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have := S.normal
  obtain ⟨ρ, hsurj, hfac⟩ := D.exists_reparametrization a
  have happ : ∀ ζ, D.boundaryLoop ζ = D.paramLoop a (ρ ζ) := by
    intro ζ
    rw [hfac]
    rfl
  have hρinj : Function.Injective ρ := by
    intro θ η h
    exact hinj (by rw [happ θ, happ η, h])
  let ψ : loopCircle ≃ₜ loopCircle :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ρ ⟨hρinj, hsurj⟩) ρ.continuous
  have hψ : (⟨ψ, ψ.continuous⟩ : C(loopCircle, loopCircle)) = ρ := by
    ext θ
    rfl
  intro hmeet
  refine D.not_loopClassMeets_boundaryLoop ?_
  rw [hfac, ← hψ]
  exact (loopClassMeets_comp_circleHomeomorph_iff (D.paramLoop a) ψ S.basepoint
    S.normalSubgroup).mpr hmeet

/-- Parametrized form of the boundary condition of an embedded disk, under the hypothesis that
the stored boundary loop traverses its image once.  The loop `γ` is an honest parametrization
of the boundary circle: it is `D.map` composed with a homeomorphism from `loopCircle` onto
`frontier D.domain`, and it avoids the normal subgroup. -/
theorem EmbeddedDisk.exists_param_boundaryLoop_of_injective {S : NormalSystem E}
    [PathConnectedSpace S.boundaryNeighborhoodSpace] (D : EmbeddedDisk S)
    (hinj : Function.Injective D.boundaryLoop) :
    ∃ (a : loopCircle ≃ₜ frontier D.domain) (γ : freeLoop S.boundaryNeighborhoodSpace),
      (∀ θ, (γ θ : E) = D.map (a θ)) ∧
        range (fun θ => (γ θ : E)) = D.map '' frontier D.domain ∧
        ¬loopClassMeets γ S.basepoint S.normalSubgroup := by
  obtain ⟨a⟩ := D.nonempty_boundaryParam
  exact ⟨a, D.paramLoop a, fun _ => rfl, D.paramLoop_range a,
    D.not_loopClassMeets_paramLoop_of_injective a hinj⟩

/-- A real number that is an integer is not an integer plus one half. -/
theorem intCast_ne_intCast_add_half (i j : ℤ) : (i : ℝ) ≠ (j : ℝ) + 1 / 2 := by
  intro h
  have h2 : ((2 * i : ℤ) : ℝ) = ((2 * j + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have h3 : (2 * i : ℤ) = 2 * j + 1 := Int.cast_injective h2
  omega

/-- Every continuous self map of `loopCircle` lifts to a continuous real map whose shift over
one period is a constant integer.  That integer is the degree of the map. -/
theorem exists_real_lift_intShift (ρ : C(loopCircle, loopCircle)) :
    ∃ (F : C(ℝ, ℝ)) (n : ℤ),
      (∀ t : ℝ, ((F t : ℝ) : loopCircle) = ρ ((t : ℝ) : loopCircle)) ∧
        ∀ t : ℝ, F (t + 1) = F t + (n : ℝ) := by
  classical
  have hcov : IsCoveringMap (fun t : ℝ => (t : loopCircle)) :=
    AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (ρ ((0 : ℝ) : loopCircle))
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (ρ.comp ⟨fun t : ℝ => (t : loopCircle), AddCircle.continuous_mk' (1 : ℝ)⟩) 0 c (by
      change ((c : ℝ) : loopCircle) = ρ (((0 : ℝ)) : loopCircle)
      exact hc)
  have hF : ∀ t : ℝ, ((F t : ℝ) : loopCircle) = ρ ((t : ℝ) : loopCircle) :=
    fun t => congrFun hFlift t
  have hshift : ∀ t : ℝ, ∃ j : ℤ, F (t + 1) - F t = (j : ℝ) := by
    intro t
    have hzero : ((F (t + 1) - F t : ℝ) : loopCircle) = 0 := by
      rw [AddCircle.coe_sub, hF, hF, AddCircle.coe_add_period, sub_self]
    obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hzero
    exact ⟨j, by simpa using hj.symm⟩
  choose k hk using hshift
  have hcont : Continuous fun t : ℝ => F (t + 1) - F t :=
    (F.continuous.comp (continuous_id.add continuous_const)).sub F.continuous
  have hconst : ∀ t : ℝ, k t = k 0 := by
    intro t
    by_contra hne
    have hivt := intermediate_value_uIcc (a := t) (b := (0 : ℝ))
      (f := fun s : ℝ => F (s + 1) - F s) hcont.continuousOn
    have hmemx : ∃ x : ℝ, (∃ j : ℤ, x = (j : ℝ) + 1 / 2) ∧
        x ∈ Set.uIcc (F (t + 1) - F t) (F (0 + 1) - F 0) := by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · refine ⟨(k t : ℝ) + 1 / 2, ⟨k t, rfl⟩, Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
        · rw [hk t]
          linarith
        · rw [hk 0]
          have hle : k t + 1 ≤ k 0 := by omega
          have hcast : ((k t + 1 : ℤ) : ℝ) ≤ ((k 0 : ℤ) : ℝ) := Int.cast_le.mpr hle
          push_cast at hcast
          linarith
      · refine ⟨(k 0 : ℝ) + 1 / 2, ⟨k 0, rfl⟩, Set.mem_uIcc.mpr (Or.inr ⟨?_, ?_⟩)⟩
        · rw [hk 0]
          linarith
        · rw [hk t]
          have hle : k 0 + 1 ≤ k t := by omega
          have hcast : ((k 0 + 1 : ℤ) : ℝ) ≤ ((k t : ℤ) : ℝ) := Int.cast_le.mpr hle
          push_cast at hcast
          linarith
    obtain ⟨x, ⟨j, hj⟩, hx⟩ := hmemx
    obtain ⟨s, -, hs⟩ := hivt hx
    exact intCast_ne_intCast_add_half (k s) j ((hk s).symm.trans (hs.trans hj))
  refine ⟨F, k 0, hF, fun t => ?_⟩
  have ht := hk t
  rw [hconst t] at ht
  linarith

/-- A conjugacy class meets a normal subgroup exactly when one, equivalently every,
representative of the class lies in the subgroup. -/
theorem conjugacyClassMeets_mk_iff_mem {G : Type*} [Group G] (g : G) (N : Subgroup G)
    [N.Normal] : conjugacyClassMeets (ConjClasses.mk g) N ↔ g ∈ N := by
  refine ⟨fun h => (conjugacyClassMeets_iff_carrier_subset _ N).mp h
    (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl),
    fun h => ⟨g, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, h⟩⟩

/-- If the class of an integer power of `g` avoids a normal subgroup, then so does the class of
`g` itself.  This is the group theoretic half of the passage from a boundary word that traverses
the boundary circle several times to a single traversal. -/
theorem not_conjugacyClassMeets_of_not_conjugacyClassMeets_zpow {G : Type*} [Group G] (g : G)
    (n : ℤ) (N : Subgroup G) [N.Normal]
    (h : ¬conjugacyClassMeets (ConjClasses.mk (g ^ n)) N) :
    ¬conjugacyClassMeets (ConjClasses.mk g) N := fun hg =>
  h ((conjugacyClassMeets_mk_iff_mem _ N).mpr
    (N.zpow_mem ((conjugacyClassMeets_mk_iff_mem g N).mp hg) n))

/-- Conditional transfer of the avoidance condition to the single traversal.  The hypothesis
`hpow` is exactly the topological input that `EmbeddedDisk` does not record: that the free
homotopy class of the stored boundary loop is the `n`-th power of the class of the parametrized
single traversal.  Granting it, the avoidance condition transfers. -/
theorem EmbeddedDisk.not_loopClassMeets_paramLoop_of_conjugacyClass_eq_zpow
    {S : NormalSystem E} [PathConnectedSpace S.boundaryNeighborhoodSpace] (D : EmbeddedDisk S)
    (a : loopCircle ≃ₜ frontier D.domain) (n : ℤ)
    (hpow : FreeLoop.conjugacyClass D.boundaryLoop S.basepoint =
      ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative (D.paramLoop a) S.basepoint ^ n)) :
    ¬loopClassMeets (D.paramLoop a) S.basepoint S.normalSubgroup := by
  have := S.normal
  have hbase : loopClassMeets (D.paramLoop a) S.basepoint S.normalSubgroup ↔
      FreeLoop.fundamentalGroupRepresentative (D.paramLoop a) S.basepoint ∈ S.normalSubgroup :=
    conjugacyClassMeets_mk_iff_mem _ _
  intro hmeet
  refine D.not_loopClassMeets_boundaryLoop ?_
  change conjugacyClassMeets (FreeLoop.conjugacyClass D.boundaryLoop S.basepoint) S.normalSubgroup
  rw [hpow]
  exact (conjugacyClassMeets_mk_iff_mem _ _).mpr
    (S.normalSubgroup.zpow_mem (hbase.mp hmeet) n)

/-- The reparametrization relating the stored boundary loop of an embedded disk to the single
traversal has a well defined degree: it lifts to a continuous real map whose shift over one
period is the constant integer `n`.  This is the precise content of the statement that
`D.boundaryLoop` runs `n` times around the parametrized boundary circle. -/
theorem EmbeddedDisk.exists_reparametrization_intShift {S : NormalSystem E} (D : EmbeddedDisk S)
    (a : loopCircle ≃ₜ frontier D.domain) :
    ∃ (ρ : C(loopCircle, loopCircle)) (F : C(ℝ, ℝ)) (n : ℤ),
      Function.Surjective ρ ∧ D.boundaryLoop = (D.paramLoop a).comp ρ ∧
        (∀ t : ℝ, ((F t : ℝ) : loopCircle) = ρ ((t : ℝ) : loopCircle)) ∧
          ∀ t : ℝ, F (t + 1) = F t + (n : ℝ) := by
  obtain ⟨ρ, hsurj, hfac⟩ := D.exists_reparametrization a
  obtain ⟨F, n, hF, hshift⟩ := exists_real_lift_intShift ρ
  exact ⟨ρ, F, n, hsurj, hfac, hF, hshift⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
