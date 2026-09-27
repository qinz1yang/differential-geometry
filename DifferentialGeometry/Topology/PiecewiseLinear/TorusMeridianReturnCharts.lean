/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingChartExtrema
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelTopology
import DifferentialGeometry.Topology.PiecewiseLinear.TorusMeridianReturnLift

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem surjective_fundamentalGroup_map_homeomorph
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (e : Y ≃ₜ Z) (y : Y) :
    Function.Surjective (FundamentalGroup.map (e : C(Y, Z)) y) := by
  have h := (fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    e.toHomotopyEquiv y (e y) rfl).2
  change Function.Surjective (FundamentalGroup.mapOfEq (e : C(Y, Z))
    (rfl : e y = e y)) at h
  have heq : FundamentalGroup.mapOfEq (e : C(Y, Z)) (rfl : e y = e y) =
      FundamentalGroup.map (e : C(Y, Z)) y := by
    ext u
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  rwa [heq] at h

private theorem product_fiber_mem_iff
    {E : Type*} [TopologicalSpace E] {M Q X : Set E}
    (φ : (M × Q) ≃ₜ X) (q : Q) (x : X) :
    (x : E) ∈ range (fun m : M => (φ (m, q) : E)) ↔ (φ.symm x).2 = q := by
  constructor
  · rintro ⟨m, hm⟩
    have hmx : φ (m, q) = x := Subtype.ext hm
    rw [← hmx, φ.symm_apply_apply]
  · intro hx
    refine ⟨(φ.symm x).1, ?_⟩
    have heq : ((φ.symm x).1, q) = φ.symm x := Prod.ext rfl hx.symm
    change (φ ((φ.symm x).1, q) : E) = (x : E)
    rw [heq, φ.apply_symm_apply]

private theorem surjective_fundamentalGroup_circle_conjugate
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (eY : loopCircle ≃ₜ Y) (eZ : loopCircle ≃ₜ Z) (f : C(Y, Z))
    (hf : ∀ y, Function.Surjective (FundamentalGroup.map f y)) :
    Function.Surjective (FundamentalGroup.map
      ((eZ.symm : C(Z, loopCircle)).comp (f.comp (eY : C(loopCircle, Y)))) 0) := by
  intro u
  obtain ⟨v, hv⟩ := surjective_fundamentalGroup_map_homeomorph eZ.symm (f (eY 0)) u
  obtain ⟨w, hw⟩ := hf (eY 0) v
  obtain ⟨z, hz⟩ := surjective_fundamentalGroup_map_homeomorph eY 0 w
  refine ⟨z, ?_⟩
  change (Path.Homotopic.Quotient.map z
    ((eZ.symm : C(Z, loopCircle)).comp (f.comp (eY : C(loopCircle, Y))))) = u
  rw [Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.map_comp]
  change FundamentalGroup.map (eZ.symm : C(Z, loopCircle)) (f (eY 0))
    (FundamentalGroup.map f (eY 0) (FundamentalGroup.map (eY : C(loopCircle, Y)) 0 z)) = u
  rw [hz, hw, hv]

theorem exists_returning_arc_of_primitive_longitude_in_charts
    {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace E3 N]
    {ι : Type*} [Finite ι] {J M Q X P : Set E3} {u : E3 → N}
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q) (hX : IsPolyhedron X)
    (hu : IsPLHomeomorphInto 3 u P) (hXP : X ⊆ P)
    (φ : (M × Q) ≃ₜ X) (hJX : J ⊆ X) (q : ι → Q)
    (hcross : ∀ i x, x ∈ (u '' J) ∩
      (u '' range (fun m : M => (φ (m, q i) : E3))) →
      ∃ c : OpenPartialHomeomorph N E3, x ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' ((u '' X) ∩ c.source))
          (c '' ((u '' J) ∩ c.source))
          (c '' ((u '' range (fun m : M => (φ (m, q i) : E3))) ∩ c.source)) (c x))
    (honto : ∀ x : J, Function.Surjective (FundamentalGroup.map
      (ContinuousMap.snd.comp ((φ.symm : C(X, M × Q)).comp
        (⟨inclusion hJX, continuous_inclusion hJX⟩ : C(J, X)))) x))
    (hmore : ∃ i, (J ∩ range (fun m : M => (φ (m, q i) : E3))).Nontrivial) :
    ∃ (i : ι) (B : Set E3) (γ : ℝ → E3), IsPLHomeomorphOn γ (Icc 0 1) B ∧ B ⊆ J ∧
      ({γ 0, γ 1} : Set E3) ⊆ range (fun m : M => (φ (m, q i) : E3)) ∧
      B ∩ (⋃ k, range (fun m : M => (φ (m, q k) : E3))) = {γ 0, γ 1} := by
  obtain ⟨eJ⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ
  obtain ⟨eQ⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hQ
  let π : C(J, Q) := ContinuousMap.snd.comp ((φ.symm : C(X, M × Q)).comp
    ⟨inclusion hJX, continuous_inclusion hJX⟩)
  let ρ : C(loopCircle, loopCircle) :=
    (eQ.symm : C(Q, loopCircle)).comp (π.comp (eJ : C(loopCircle, J)))
  have hρonto : Function.Surjective (FundamentalGroup.map ρ 0) :=
    surjective_fundamentalGroup_circle_conjugate eJ eQ π honto
  obtain ⟨F, hlift, hperiod⟩ := exists_primitive_real_lift ρ hρonto
  have hproj (t : ℝ) : eQ (F t : loopCircle) = π (eJ (t : loopCircle)) := by
    rw [hlift]
    exact eQ.apply_symm_apply _
  have huX : IsPLHomeomorphInto 3 u X :=
    (hu.isPLOn.mono_of_isPolyhedron hX hXP).isPLHomeomorphInto_of_isCompact
      hX.isCompact (hu.injOn.mono hXP)
  have huJpl := hu.isPLOn.mono_of_isPolyhedron hJ.isPolyhedron (hJX.trans hXP)
  have huJ : IsPLHomeomorphInto 3 u J :=
    huJpl.isPLHomeomorphInto_of_isCompact hJ.isPolyhedron.isCompact
      (hu.injOn.mono (hJX.trans hXP))
  let v := huX.compactModelHomeomorph hX.isCompact
  let w := huJ.compactModelHomeomorph hJ.isPolyhedron.isCompact
  let p : ℝ → u '' J := fun t => w (eJ (t : loopCircle))
  let ψ : (u '' X) → Q := fun y => (φ.symm (v.symm y)).2
  have hp : IsLocalHomeomorph p := w.isLocalHomeomorph.comp
    (eJ.isLocalHomeomorph.comp (AddCircle.isLocalHomeomorph_coe (1 : ℝ)))
  have hψ : Continuous ψ := continuous_snd.comp (φ.symm.continuous.comp v.symm.continuous)
  have hψopen : IsOpenMap ψ := isOpenMap_snd.comp
    (φ.symm.isOpenMap.comp v.symm.isOpenMap)
  have hactualproj (t : ℝ) :
      ψ ⟨p t, (image_mono hJX) (p t).property⟩ = eQ (F t : loopCircle) := by
    change (φ.symm (v.symm
      (v ⟨eJ (t : loopCircle), hJX (eJ (t : loopCircle)).property⟩))).2 = _
    rw [v.symm_apply_apply]
    exact (hproj t).symm
  have hno : ∀ t i, eQ (F t : loopCircle) = q i → ¬ IsLocalExtr F t := by
    intro t i ht
    have hpoint : (eJ (t : loopCircle) : E3) ∈
        range (fun m : M => (φ (m, q i) : E3)) :=
      (product_fiber_mem_iff φ (q i) _).mpr ((hproj t).symm.trans ht)
    obtain ⟨c, hpc, hc⟩ := hcross i (p t)
      ⟨(p t).property, mem_image_of_mem u hpoint⟩
    apply HasPLCurveCrossingOnAt.not_isLocalExtr_lift_in_chart c hpc hc (image_mono hJX)
      ψ hψ hψopen hp (fun r : ℝ => eQ (r : loopCircle))
      (eQ.isLocalHomeomorph.comp (AddCircle.isLocalHomeomorph_coe (1 : ℝ)))
      F F.continuous hactualproj
    intro y
    rw [ht]
    constructor
    · intro hy
      let m := (φ.symm (v.symm y)).1
      have hφ : φ (m, q i) = v.symm y := by
        rw [← hy]
        exact φ.apply_symm_apply _
      refine ⟨(φ (m, q i) : E3), ⟨m, rfl⟩, ?_⟩
      exact congrArg Subtype.val ((congrArg v hφ).trans (v.apply_symm_apply y))
    · rintro ⟨z, ⟨m, hm⟩, hzy⟩
      have hv : v (φ (m, q i)) = y := Subtype.ext ((congrArg u hm).trans hzy)
      have hcoord := congrArg (fun z : u '' X => (φ.symm (v.symm z)).2) hv
      simpa only [v.symm_apply_apply, φ.symm_apply_apply] using hcoord.symm
  exact exists_returning_arc_of_periodic_longitude_lift hJ φ hJX q eJ eQ F hproj
    hperiod hno hmore

end DifferentialGeometry.Topology.PiecewiseLinear
