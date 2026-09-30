/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchPreimage
import DifferentialGeometry.Topology.Covering.Sheets
import DifferentialGeometry.Topology.Covering.TwoSheetSection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem continuous_fiberSwap_of_isCoveringMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {p : X → Y} (hp : IsCoveringMap p)
    (hcard : ∀ y, (p ⁻¹' {y}).encard = 2) :
    Continuous (Covering.fiberSwap p hcard) := by
  classical
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨a, b, hab, hfiber⟩ := Set.encard_eq_two.mp (hcard (p x))
  have ha : a ∈ p ⁻¹' {p x} := by rw [hfiber]; exact Or.inl rfl
  have hb : b ∈ p ⁻¹' {p x} := by rw [hfiber]; exact Or.inr rfl
  have hev : IsEvenlyCovered p (p x) (p ⁻¹' {p x}) := hp (p x)
  have : DiscreteTopology (p ⁻¹' {p x} : Set X) := hev.1
  have : Nonempty (p ⁻¹' {p x} : Set X) := ⟨⟨a, ha⟩⟩
  have hbase : p x ∈ hev.toTrivialization.baseSet := hev.mem_toTrivialization_baseSet
  obtain ⟨v, hvu⟩ : ∃ v : (p ⁻¹' {p x} : Set X), v ≠ (hev.toTrivialization x).2 := by
    by_cases hcase : (hev.toTrivialization x).2 = ⟨a, ha⟩
    · exact ⟨⟨b, hb⟩, fun h => hab (congrArg Subtype.val (h.trans hcase)).symm⟩
    · exact ⟨⟨a, ha⟩, fun h => hcase h.symm⟩
  have hSopen : IsOpen (Covering.sheet hev.toTrivialization (hev.toTrivialization x).2).source :=
    (Covering.sheet hev.toTrivialization (hev.toTrivialization x).2).open_source
  have hxS : x ∈ (Covering.sheet hev.toTrivialization (hev.toTrivialization x).2).source :=
    ⟨hev.toTrivialization.mem_source.mpr hbase, rfl⟩
  have hmapsto : MapsTo p (Covering.sheet hev.toTrivialization (hev.toTrivialization x).2).source
      (Covering.sheet hev.toTrivialization v).target :=
    fun z hz => hev.toTrivialization.mem_source.mp hz.1
  have hcont : ContinuousOn (fun z => (Covering.sheet hev.toTrivialization v).symm (p z))
      (Covering.sheet hev.toTrivialization (hev.toTrivialization x).2).source :=
    (Covering.sheet hev.toTrivialization v).continuousOn_symm.comp
      hp.continuous.continuousOn hmapsto
  have heq : EqOn (fun z => (Covering.sheet hev.toTrivialization v).symm (p z))
      (Covering.fiberSwap p hcard)
      (Covering.sheet hev.toTrivialization (hev.toTrivialization x).2).source := by
    intro z hz
    have hzb : p z ∈ (Covering.sheet hev.toTrivialization v).target :=
      hev.toTrivialization.mem_source.mp hz.1
    have hw := (Covering.sheet hev.toTrivialization v).map_target hzb
    have hpw : p ((Covering.sheet hev.toTrivialization v).symm (p z)) = p z :=
      (Covering.sheet hev.toTrivialization v).right_inv hzb
    have hwz : (Covering.sheet hev.toTrivialization v).symm (p z) ≠ z := by
      intro hzz
      refine hvu ?_
      have h1 : (hev.toTrivialization
          ((Covering.sheet hev.toTrivialization v).symm (p z))).2 = v := hw.2
      rw [hzz] at h1
      exact h1.symm.trans hz.2
    rcases Covering.eq_or_eq_fiberSwap p hcard z
      ((Covering.sheet hev.toTrivialization v).symm (p z)) hpw with h | h
    · exact absurd h hwz
    · exact h
  exact (hcont.continuousAt (hSopen.mem_nhds hxS)).congr
    (Filter.eventuallyEq_of_mem (hSopen.mem_nhds hxS) heq)

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem connectedSpace_branchPreimage_of_isPLSphere_one
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hpre : hD.branchPreimage c = J) :
    ConnectedSpace (hD.branchPreimage c) := by
  subst hpre
  exact Subtype.connectedSpace (IsPLSphere.isConnected (n := 0) hJ)

theorem not_exists_rightInverse_branchProjection_of_isPLSphere_one [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hpre : hD.branchPreimage c = J) :
    ¬∃ s : C((hD.singularSet.branchComplex c).space, hD.branchPreimage c),
      Function.RightInverse s (hD.branchProjection c) := by
  have : ConnectedSpace (hD.branchPreimage c) :=
    hD.connectedSpace_branchPreimage_of_isPLSphere_one c hJ hpre
  have : Nonempty (hD.singularSet.branchComplex c).space :=
    (hD.singularSet.branchComplex_space_isConnected c).nonempty.to_subtype
  exact Covering.not_exists_continuous_section_of_fiber_card_two
    (hD.branchProjection_isCoveringMap c) (hD.branchProjection_fiber_encard_eq_two c)

def IsBranchDeckInvolution (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (J : Set (EuclideanSpace ℝ (Fin 2)))
    (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) : Prop :=
  hD.branchPreimage c = J ∧ J.Nonempty ∧ ContinuousOn τ J ∧ MapsTo τ J J ∧ BijOn τ J J ∧
    (∀ x ∈ J, τ x ≠ x) ∧ (∀ x ∈ J, τ (τ x) = x) ∧ (∀ x ∈ J, D (τ x) = D x) ∧
      ∀ x ∈ J, ∀ y ∈ J, D x = D y ↔ y = x ∨ y = τ x

open Classical in
theorem exists_isBranchDeckInvolution_of_branchPreimage_eq [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hpre : hD.branchPreimage c = J) :
    ∃ τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      hD.IsBranchDeckInvolution c J τ := by
  classical
  subst hpre
  obtain ⟨σ, hcont, hproj, hnes, hinv, hfib⟩ :
      ∃ σ : hD.branchPreimage c → hD.branchPreimage c, Continuous σ ∧
        (∀ z, hD.branchProjection c (σ z) = hD.branchProjection c z) ∧ (∀ z, σ z ≠ z) ∧
          (∀ z, σ (σ z) = z) ∧
            ∀ z w, hD.branchProjection c w = hD.branchProjection c z → w = z ∨ w = σ z := by
    have hcard : ∀ y, ((hD.branchProjection c) ⁻¹' {y}).encard = 2 :=
      hD.branchProjection_fiber_encard_eq_two c
    refine ⟨Covering.fiberSwap (hD.branchProjection c) hcard,
      continuous_fiberSwap_of_isCoveringMap (hD.branchProjection_isCoveringMap c) hcard,
      fun z => (Covering.fiberSwap_spec (hD.branchProjection c) hcard z).1,
      fun z => (Covering.fiberSwap_spec (hD.branchProjection c) hcard z).2, fun z => ?_,
      fun z w hw => Covering.eq_or_eq_fiberSwap (hD.branchProjection c) hcard z w hw⟩
    rcases Covering.eq_or_eq_fiberSwap (hD.branchProjection c) hcard z
      (Covering.fiberSwap (hD.branchProjection c) hcard
        (Covering.fiberSwap (hD.branchProjection c) hcard z))
      ((Covering.fiberSwap_spec (hD.branchProjection c) hcard
        (Covering.fiberSwap (hD.branchProjection c) hcard z)).1.trans
          (Covering.fiberSwap_spec (hD.branchProjection c) hcard z).1) with h | h
    · exact h
    · exact absurd h (Covering.fiberSwap_spec (hD.branchProjection c) hcard
        (Covering.fiberSwap (hD.branchProjection c) hcard z)).2
  obtain ⟨τ, hval⟩ : ∃ τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ∀ (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ hD.branchPreimage c),
        τ x = (σ ⟨x, hx⟩ : EuclideanSpace ℝ (Fin 2)) :=
    ⟨fun x => if hx : x ∈ hD.branchPreimage c then (σ ⟨x, hx⟩ : EuclideanSpace ℝ (Fin 2)) else x,
      fun x hx => dite_eq_left hx⟩
  refine ⟨τ, ?_⟩
  have hmaps : MapsTo τ (hD.branchPreimage c) (hD.branchPreimage c) := by
    intro x hx
    rw [hval x hx]
    exact (σ ⟨x, hx⟩).2
  have hinvol : ∀ x ∈ hD.branchPreimage c, τ (τ x) = x := by
    intro x hx
    have h2 : τ x ∈ hD.branchPreimage c := hmaps hx
    have h3 : (⟨τ x, h2⟩ : hD.branchPreimage c) = σ ⟨x, hx⟩ := Subtype.ext (hval x hx)
    calc τ (τ x) = (σ ⟨τ x, h2⟩ : EuclideanSpace ℝ (Fin 2)) := hval (τ x) h2
      _ = (σ (σ ⟨x, hx⟩) : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val (congrArg σ h3)
      _ = x := congrArg Subtype.val (hinv ⟨x, hx⟩)
  have hDeq : ∀ x ∈ hD.branchPreimage c, D (τ x) = D x := by
    intro x hx
    have hcoord : hD.branchCoordinate c (τ x) = hD.branchCoordinate c x := by
      rw [hval x hx]
      exact congrArg Subtype.val (hproj ⟨x, hx⟩)
    calc D (τ x) = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c (τ x)) :=
          (hD.branchPieceIn_map_branchCoordinate c (hmaps hx)).symm
      _ = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c x) :=
          congrArg (hD.singularSet.branchPieceIn c).map hcoord
      _ = D x := hD.branchPieceIn_map_branchCoordinate c hx
  refine ⟨rfl, hD.branchPreimage_nonempty c, ?_, hmaps,
    Set.InvOn.bijOn ⟨fun x hx => hinvol x hx, fun x hx => hinvol x hx⟩ hmaps hmaps, ?_, hinvol,
      hDeq, ?_⟩
  · refine continuousOn_iff_continuous_domRestrict.mpr ?_
    have hrestrict : (hD.branchPreimage c).domRestrict τ =
        fun z => (σ z : EuclideanSpace ℝ (Fin 2)) := by
      funext z
      exact hval (z : EuclideanSpace ℝ (Fin 2)) z.2
    rw [hrestrict]
    exact continuous_subtype_val.comp hcont
  · intro x hx hfixed
    exact hnes ⟨x, hx⟩ (Subtype.ext ((hval x hx).symm.trans hfixed))
  · intro x hx y hy
    constructor
    · intro hxy
      have hcoord : hD.branchCoordinate c y = hD.branchCoordinate c x :=
        congrArg (Function.invFunOn (hD.singularSet.branchPieceIn c).map
          (hD.singularSet.branchPieceIn c).complex.space) hxy.symm
      rcases hfib ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext hcoord) with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr ((congrArg Subtype.val h).trans (hval x hx).symm)
    · rintro (rfl | rfl)
      · rfl
      · exact (hDeq x hx).symm

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
