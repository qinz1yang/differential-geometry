/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LoopSpace.Rotation

noncomputable section

namespace Path.Homotopic

theorem of_injective_of_range_eq {X : Type*} [TopologicalSpace X] [T2Space X] {a b : X}
    {γ₁ γ₂ : Path a b} (hinj : Function.Injective γ₂)
    (hrange : Set.range γ₁ = Set.range γ₂) : γ₁.Homotopic γ₂ := by
  have hemb : Topology.IsEmbedding ⇑γ₂ := (γ₂.continuous.isClosedEmbedding hinj).toIsEmbedding
  have hmem : ∀ t : unitInterval, γ₁ t ∈ Set.range ⇑γ₂ := by
    intro t
    rw [← hrange]
    exact Set.mem_range_self t
  obtain ⟨φ, hcont, hzero, hone, happ⟩ :
      ∃ φ : unitInterval → unitInterval, Continuous φ ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, γ₂ (φ t) = γ₁ t := by
    refine ⟨fun t => hemb.toHomeomorph.symm ⟨γ₁ t, hmem t⟩,
      hemb.toHomeomorph.symm.continuous.comp (γ₁.continuous.subtype_mk hmem), ?_, ?_, ?_⟩
    · change hemb.toHomeomorph.symm ⟨γ₁ 0, hmem 0⟩ = 0
      have hval : (⟨γ₁ 0, hmem 0⟩ : Set.range ⇑γ₂) = ⟨γ₂ 0, Set.mem_range_self 0⟩ :=
        Subtype.ext (γ₁.source.trans γ₂.source.symm)
      rw [hval]
      exact hemb.toHomeomorph_symm_apply 0
    · change hemb.toHomeomorph.symm ⟨γ₁ 1, hmem 1⟩ = 1
      have hval : (⟨γ₁ 1, hmem 1⟩ : Set.range ⇑γ₂) = ⟨γ₂ 1, Set.mem_range_self 1⟩ :=
        Subtype.ext (γ₁.target.trans γ₂.target.symm)
      rw [hval]
      exact hemb.toHomeomorph_symm_apply 1
    · intro t
      change γ₂ (hemb.toHomeomorph.symm ⟨γ₁ t, hmem t⟩) = γ₁ t
      obtain ⟨s, hs⟩ := hmem t
      have hval : (⟨γ₁ t, hmem t⟩ : Set.range ⇑γ₂) = ⟨γ₂ s, Set.mem_range_self s⟩ :=
        Subtype.ext hs.symm
      rw [hval, hemb.toHomeomorph_symm_apply s]
      exact hs
  have hre : γ₂.reparam φ hcont hzero hone = γ₁ := by
    ext t
    exact happ t
  have hhom : γ₂.Homotopic (γ₂.reparam φ hcont hzero hone) :=
    ⟨Path.Homotopy.reparam γ₂ φ hcont hzero hone⟩
  rw [hre] at hhom
  exact hhom.symm

theorem symm_of_injective_of_range_eq {X : Type*} [TopologicalSpace X] [T2Space X] {a b : X}
    {γ₁ : Path a b} {γ₂ : Path b a} (hinj : Function.Injective γ₂)
    (hrange : Set.range γ₁ = Set.range γ₂) : γ₁.Homotopic γ₂.symm := by
  have hsymm : Function.Injective γ₂.symm := by
    intro s t hst
    have h : γ₂ (unitInterval.symm s) = γ₂ (unitInterval.symm t) := hst
    exact unitInterval.symm_bijective.injective (hinj h)
  have hr : Set.range γ₁ = Set.range γ₂.symm := by
    rw [γ₂.symm_range]
    exact hrange
  exact of_injective_of_range_eq hsymm hr

theorem map_of_injective_of_range_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] {S : Set X} {a b : S} {γ₁ γ₂ : Path a b} {f : X → Y} (hf : Continuous f)
    (hinj : Function.Injective γ₂) (hrange : Set.range γ₁ = Set.range γ₂) :
    (γ₁.map (hf.comp continuous_subtype_val)).Homotopic
      (γ₂.map (hf.comp continuous_subtype_val)) := by
  exact (of_injective_of_range_eq hinj hrange).map ⟨fun s => f s, hf.comp continuous_subtype_val⟩

end Path.Homotopic

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem pathToCircle_symm_apply (p : Path x x) (θ : loopCircle) :
    pathToCircle p.symm θ = pathToCircle p (-θ) := by
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  have hmem : (1 - (t : ℝ)) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [t.property.2], by linarith [t.property.1]⟩
  have hneg : -((t : ℝ) : loopCircle) = ((1 - (t : ℝ) : ℝ) : loopCircle) := by
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  rw [hneg, pathToCircle_coe_eq_extend p hmem, pathToCircle_coe_eq_extend p.symm t.property]
  exact p.extend_symm_apply _

theorem pathToCircle_symm (p : Path x x) :
    pathToCircle p.symm = (pathToCircle p).comp ⟨fun θ => -θ, continuous_neg⟩ :=
  ContinuousMap.ext fun θ => pathToCircle_symm_apply p θ

def unitSegmentPath : Path (0 : ℝ) 1 where
  toFun t := (t : ℝ)
  continuous_toFun := continuous_subtype_val
  source' := rfl
  target' := rfl

def unitSegmentSquarePath : Path (0 : ℝ) 1 where
  toFun t := (t : ℝ) ^ 2
  continuous_toFun := by fun_prop
  source' := by norm_num
  target' := by norm_num

theorem unitSegmentPath_homotopic_unitSegmentSquarePath :
    unitSegmentPath.Homotopic unitSegmentSquarePath := by
  have hsq : ∀ t : unitInterval, (t : ℝ) ^ 2 ∈ unitInterval := fun t =>
    ⟨sq_nonneg _, by nlinarith [t.property.1, t.property.2]⟩
  have hcont : Continuous fun t : unitInterval => (⟨(t : ℝ) ^ 2, hsq t⟩ : unitInterval) := by
    fun_prop
  have hzero : (⟨((0 : unitInterval) : ℝ) ^ 2, hsq 0⟩ : unitInterval) = 0 :=
    Subtype.ext (by norm_num)
  have hone : (⟨((1 : unitInterval) : ℝ) ^ 2, hsq 1⟩ : unitInterval) = 1 :=
    Subtype.ext (by norm_num)
  have hrep : unitSegmentSquarePath =
      unitSegmentPath.reparam (fun t => ⟨(t : ℝ) ^ 2, hsq t⟩) hcont hzero hone := by
    ext t
    rfl
  have hrange : Set.range unitSegmentPath = Set.range unitSegmentSquarePath := by
    rw [hrep, Path.range_reparam]
  have hinj : Function.Injective unitSegmentSquarePath := by
    intro s t hst
    have hsquare : (s : ℝ) ^ 2 = (t : ℝ) ^ 2 := hst
    have hfac : ((s : ℝ) - (t : ℝ)) * ((s : ℝ) + (t : ℝ)) = 0 := by
      have h : ((s : ℝ) - (t : ℝ)) * ((s : ℝ) + (t : ℝ)) = (s : ℝ) ^ 2 - (t : ℝ) ^ 2 := by ring
      rw [h, hsquare, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Subtype.ext (by linarith)
    · exact Subtype.ext (by linarith [s.property.1, t.property.1])
  exact Path.Homotopic.of_injective_of_range_eq hinj hrange

theorem unitSegmentPath_ne_unitSegmentSquarePath :
    unitSegmentPath ≠ unitSegmentSquarePath := by
  intro hEq
  have hhalf : ((1 : ℝ) / 2) = ((1 : ℝ) / 2) ^ 2 :=
    congrArg (fun γ : Path (0 : ℝ) 1 => γ ⟨1 / 2, by norm_num, by norm_num⟩) hEq
  norm_num at hhalf

end DifferentialGeometry.Topology

end
