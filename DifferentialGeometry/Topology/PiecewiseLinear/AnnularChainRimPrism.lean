/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimRadial
import Mathlib.Topology.Homeomorph.Lemmas

open Set Topology
open DifferentialGeometry.Simplex

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Triangle" => Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
local notation "Interval" => Icc (-1 : ℝ) 1

theorem exists_prism_rim_retraction
    {X : Type*} [TopologicalSpace X] {Q D R : Set X} {P : X}
    (e : (Triangle × Interval) ≃ₜ Q)
    (hD : range (fun p : Triangle => (e (p, ⟨0, by norm_num⟩) : X)) = D)
    (hR : range (fun b : boundary (Fin 3) => (e (b.val, ⟨0, by norm_num⟩) : X)) = R)
    (hP : (e (Convexity.StdSimplex.coordinateBarycenter, ⟨0, by norm_num⟩) : X) = P) :
    ∃ (U : Set Q) (r : C(U, R)), IsOpen U ∧
      (∀ x : R, ∃ y : U, ((y : Q) : X) = x ∧ r y = x) ∧
      ∃ d : C(↥(D \ (R ∪ {P})), U), (∀ x, ((d x : Q) : X) = x) ∧
        ∃ s : C(R, ↥(D \ (R ∪ {P}))), ∀ x, r (d (s x)) = x := by
  classical
  let t₀ : Interval := ⟨0, by norm_num⟩
  let fB : boundary (Fin 3) → X := fun b => (e (b.val, t₀) : X)
  have hB : IsEmbedding fB := IsEmbedding.subtypeVal.comp
    (e.isEmbedding.comp ((isEmbedding_prodMkLeft t₀).comp IsEmbedding.subtypeVal))
  let eB : boundary (Fin 3) ≃ₜ R :=
    hB.toHomeomorph.trans (Homeomorph.setCongr hR)
  have heB (b : boundary (Fin 3)) : (eB b : X) = e (b.val, t₀) := rfl
  let U : Set Q := {q | (e.symm q).1 ≠ Convexity.StdSimplex.coordinateBarycenter}
  have hU : IsOpen U :=
    isOpen_compl_singleton.preimage (continuous_fst.comp e.symm.continuous)
  let p : C(U, punctured (Fin 3)) :=
    ⟨fun y => ⟨(e.symm y.val).1, y.property⟩,
      (continuous_fst.comp (e.symm.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  let r : C(U, R) := (⟨eB, eB.continuous⟩ : C(boundary (Fin 3), R)).comp (radialRetraction.comp p)
  have hrim : ∀ x : R, ∃ y : U, ((y : Q) : X) = x ∧ r y = x := by
    intro x
    let b := eB.symm x
    have hb : (e (b.val, t₀)) ∈ U := by
      change (e.symm (e (b.val, t₀))).1 ≠ Convexity.StdSimplex.coordinateBarycenter
      rw [e.symm_apply_apply]
      exact boundary_ne_barycenter b.property
    refine ⟨⟨e (b.val, t₀), hb⟩, ?_, ?_⟩
    · exact (heB b).symm.trans (congrArg Subtype.val (eB.apply_symm_apply x))
    · change eB (radialRetraction (p ⟨e (b.val, t₀), hb⟩)) = x
      have hp : p ⟨e (b.val, t₀), hb⟩ = boundaryInclusion b := by
        apply Subtype.ext
        change (e.symm (e (b.val, t₀))).1 = b.val
        rw [e.symm_apply_apply]
      rw [hp, radialRetraction_boundary, eB.apply_symm_apply]
  have hDQ : D ⊆ Q := by
    rw [← hD]
    rintro _ ⟨a, rfl⟩
    exact (e (a, t₀)).property
  have hDU (x : ↥(D \ (R ∪ {P}))) : (⟨x.val, hDQ x.property.1⟩ : Q) ∈ U := by
    have hxD := hD.symm.subset x.property.1
    obtain ⟨a, ha⟩ := hxD
    have haQ : e (a, t₀) = ⟨x.val, hDQ x.property.1⟩ := Subtype.ext ha
    change (e.symm ⟨x.val, hDQ x.property.1⟩).1 ≠ Convexity.StdSimplex.coordinateBarycenter
    rw [← haQ, e.symm_apply_apply]
    intro haP
    change a = Convexity.StdSimplex.coordinateBarycenter at haP
    apply x.property.2
    right
    exact ha.symm.trans (by simpa only [haP] using hP)
  let d : C(↥(D \ (R ∪ {P})), U) :=
    ⟨fun x => ⟨⟨x.val, hDQ x.property.1⟩, hDU x⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  obtain ⟨s₀, hs₀⟩ := exists_open_simplex_radial_section
  let f : R → X := fun x => (e (((s₀ (eB.symm x)).val.val), t₀) : X)
  have hfD (x : R) : f x ∈ D \ (R ∪ {P}) := by
    constructor
    · rw [← hD]
      exact ⟨(s₀ (eB.symm x)).val.val, rfl⟩
    · rintro (hxR | hxP)
      · rw [← hR] at hxR
        obtain ⟨b, hb⟩ := hxR
        have heq := e.injective (Subtype.ext hb)
        have hfirst : b.val = (s₀ (eB.symm x)).val.val := congrArg Prod.fst heq
        obtain ⟨i, hi⟩ := b.property
        have hp := (s₀ (eB.symm x)).property i
        rw [← hfirst, hi] at hp
        exact (lt_irrefl 0 hp)
      · have heq : e (((s₀ (eB.symm x)).val.val), t₀) =
            e (Convexity.StdSimplex.coordinateBarycenter, t₀) := Subtype.ext (hxP.trans hP.symm)
        exact (s₀ (eB.symm x)).val.property (congrArg Prod.fst (e.injective heq))
  let s : C(R, ↥(D \ (R ∪ {P}))) :=
    ⟨fun x => ⟨f x, hfD x⟩, by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (e.continuous.comp
        (((continuous_subtype_val.comp continuous_subtype_val).comp
          (s₀.continuous.comp eB.symm.continuous)).prodMk continuous_const))⟩
  refine ⟨U, r, hU, hrim, d, fun _ => rfl, s, fun x => ?_⟩
  have hp : p (d (s x)) = (s₀ (eB.symm x)).val := by
    apply Subtype.ext
    change (e.symm (e (((s₀ (eB.symm x)).val.val), t₀))).1 = _
    rw [e.symm_apply_apply]
  change eB (radialRetraction (p (d (s x)))) = x
  rw [hp, hs₀, eB.apply_symm_apply]

end DifferentialGeometry.Topology.PiecewiseLinear
