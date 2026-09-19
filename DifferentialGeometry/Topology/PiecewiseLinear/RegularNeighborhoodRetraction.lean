/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homotopy.DeformationRetract
import Mathlib.Topology.NhdsWithin

/-!
# Compatible regular-neighborhood retractions
-/

open Set Topology
open unitInterval
open DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X}

noncomputable def homeomorphImage (r : StrongDeformationRetract A) (e : X ≃ₜ Y) :
    StrongDeformationRetract (e '' A) where
  retraction := ⟨fun y => ⟨e (r.retraction (e.symm y)), by
    exact ⟨(r.retraction (e.symm y) : X), (r.retraction (e.symm y)).2, rfl⟩⟩,
    (e.continuous.comp (continuous_subtype_val.comp
      (r.retraction.continuous.comp e.symm.continuous))).subtype_mk (fun y => by
        change e (r.retraction (e.symm y) : X) ∈ e '' A
        exact ⟨(r.retraction (e.symm y) : X), (r.retraction (e.symm y)).2, rfl⟩)⟩
  homotopy := {
    toHomotopy := {
      toContinuousMap := ⟨fun z => e (r.homotopy (z.1, e.symm z.2)),
        e.continuous.comp (r.homotopy.continuous.comp
          (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))⟩
      map_zero_left := by
        intro y
        change e (r.homotopy (0, e.symm y)) = y
        rw [r.homotopy.apply_zero]
        simpa only [ContinuousMap.id_apply] using e.apply_symm_apply y
      map_one_left := by
        intro y
        change e (r.homotopy (1, e.symm y)) = e (r.retraction (e.symm y))
        rw [r.homotopy.apply_one]
        simp only [ContinuousMap.comp_apply, ContinuousMap.restrict_apply,
          ContinuousMap.id_apply]
    }
    prop' := by
      intro t y hy
      obtain ⟨x, hx, rfl⟩ := hy
      change e (r.homotopy (t, e.symm (e x))) = e x
      rw [e.symm_apply_apply, r.homotopy_fixed_on t hx]
  }

noncomputable def embeddingImage (r : StrongDeformationRetract A) (f : X → Y)
    (hf : IsEmbedding f) :
    StrongDeformationRetract {y : Set.range f | (y : Y) ∈ f '' A} := by
  let e : X ≃ₜ Set.range f := hf.toHomeomorph
  apply StrongDeformationRetract.congr _ (r.homeomorphImage e)
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    exact congrArg Subtype.val hxy
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    exact hxy

end DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {X : Type u} [TopologicalSpace X]

def regularNeighborhoodStageCore (A B : Set X) : Set B :=
  {x | (x : X) ∈ A}

def regularNeighborhoodExhaustionCore (A B : ℕ → Set X) : Set (⋃ i, B i) :=
  {x | (x : X) ∈ ⋃ i, A i}

def regularNeighborhoodStageInUnion (B : ℕ → Set X) (i : ℕ) : Set (⋃ j, B j) :=
  {x | (x : X) ∈ B i}

def strongDeformationRetractionValue {A B : Set X}
    (r : StrongDeformationRetract (regularNeighborhoodStageCore A B)) (x : B) : X :=
  r.retraction x

def strongDeformationHomotopyValue {A B : Set X}
    (r : StrongDeformationRetract (regularNeighborhoodStageCore A B)) (t : I) (x : B) : X :=
  r.homotopy (t, x)

structure CompatibleStrongDeformationRetractSystem (A B : ℕ → Set X) where
  core_subset : ∀ i, A i ⊆ B i
  stage : ∀ i, StrongDeformationRetract (regularNeighborhoodStageCore (A i) (B i))
  retraction_compatible : ∀ {i j}, i ≤ j → ∀ {x : X} (hxi : x ∈ B i) (hxj : x ∈ B j),
    strongDeformationRetractionValue (stage j) ⟨x, hxj⟩ =
      strongDeformationRetractionValue (stage i) ⟨x, hxi⟩
  homotopy_compatible : ∀ {i j}, i ≤ j → ∀ (t : I) {x : X}
    (hxi : x ∈ B i) (hxj : x ∈ B j),
    strongDeformationHomotopyValue (stage j) t ⟨x, hxj⟩ =
      strongDeformationHomotopyValue (stage i) t ⟨x, hxi⟩
  ambient_mem_nhdsWithin : ∀ i {x : X}, x ∈ B i → B (i + 1) ∈ 𝓝[⋃ j, B j] x

namespace CompatibleStrongDeformationRetractSystem

variable {A B : ℕ → Set X}

open Classical in
noncomputable def exhaustionIndex (B : ℕ → Set X) (x : ⋃ i, B i) : ℕ :=
  Nat.find (by simpa only [mem_iUnion] using x.2)

omit [TopologicalSpace X] in
open Classical in
theorem mem_exhaustionIndex (B : ℕ → Set X) (x : ⋃ i, B i) :
    (x : X) ∈ B (exhaustionIndex B x) := by
  unfold exhaustionIndex
  exact Nat.find_spec (by simpa only [mem_iUnion] using x.2)

omit [TopologicalSpace X] in
open Classical in
theorem exhaustionIndex_le_of_mem (B : ℕ → Set X) (x : ⋃ i, B i)
    {i : ℕ} (hx : (x : X) ∈ B i) : exhaustionIndex B x ≤ i := by
  unfold exhaustionIndex
  exact Nat.find_min' (by simpa only [mem_iUnion] using x.2) hx

noncomputable def retractionValue (R : CompatibleStrongDeformationRetractSystem A B)
    (x : ⋃ i, B i) : X :=
  strongDeformationRetractionValue (R.stage (exhaustionIndex B x))
    ⟨x, mem_exhaustionIndex B x⟩

noncomputable def homotopyValue (R : CompatibleStrongDeformationRetractSystem A B)
    (t : I) (x : ⋃ i, B i) : X :=
  strongDeformationHomotopyValue (R.stage (exhaustionIndex B x)) t
    ⟨x, mem_exhaustionIndex B x⟩

theorem retractionValue_eq_stage (R : CompatibleStrongDeformationRetractSystem A B)
    (x : ⋃ i, B i) {i : ℕ} (hx : (x : X) ∈ B i) :
    R.retractionValue x =
      strongDeformationRetractionValue (R.stage i) ⟨x, hx⟩ :=
  (R.retraction_compatible (exhaustionIndex_le_of_mem B x hx)
    (mem_exhaustionIndex B x) hx).symm

theorem homotopyValue_eq_stage (R : CompatibleStrongDeformationRetractSystem A B)
    (t : I) (x : ⋃ i, B i) {i : ℕ} (hx : (x : X) ∈ B i) :
    R.homotopyValue t x =
      strongDeformationHomotopyValue (R.stage i) t ⟨x, hx⟩ :=
  (R.homotopy_compatible (exhaustionIndex_le_of_mem B x hx) t
    (mem_exhaustionIndex B x) hx).symm

theorem retractionValue_mem_core (R : CompatibleStrongDeformationRetractSystem A B)
    (x : ⋃ i, B i) : R.retractionValue x ∈ ⋃ i, A i := by
  apply mem_iUnion.mpr
  exact ⟨exhaustionIndex B x,
    (R.stage (exhaustionIndex B x)).retraction ⟨x, mem_exhaustionIndex B x⟩ |>.2⟩

theorem retractionValue_mem_ambient (R : CompatibleStrongDeformationRetractSystem A B)
    (x : ⋃ i, B i) : R.retractionValue x ∈ ⋃ i, B i := by
  apply mem_iUnion.mpr
  exact ⟨exhaustionIndex B x,
    (R.stage (exhaustionIndex B x)).retraction ⟨x, mem_exhaustionIndex B x⟩ |>.1.2⟩

theorem homotopyValue_mem_ambient (R : CompatibleStrongDeformationRetractSystem A B)
    (t : I) (x : ⋃ i, B i) : R.homotopyValue t x ∈ ⋃ i, B i := by
  apply mem_iUnion.mpr
  exact ⟨exhaustionIndex B x,
    (R.stage (exhaustionIndex B x)).homotopy
      (t, ⟨x, mem_exhaustionIndex B x⟩) |>.2⟩

theorem continuousOn_retractionValue_stage
    (R : CompatibleStrongDeformationRetractSystem A B) (i : ℕ) :
    ContinuousOn R.retractionValue (regularNeighborhoodStageInUnion B i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let inclusion : regularNeighborhoodStageInUnion B i → B i :=
    fun x => ⟨x, x.2⟩
  have hinclusion : Continuous inclusion :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hcontinuous : Continuous (fun x : regularNeighborhoodStageInUnion B i =>
      strongDeformationRetractionValue (R.stage i) (inclusion x)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      ((R.stage i).retraction.continuous.comp hinclusion))
  convert hcontinuous using 1
  funext x
  exact R.retractionValue_eq_stage x.1 x.2

theorem continuous_retractionValue (R : CompatibleStrongDeformationRetractSystem A B) :
    Continuous R.retractionValue := by
  apply continuous_of_cover_nhds (s := fun i => regularNeighborhoodStageInUnion B (i + 1))
  · intro x
    refine ⟨exhaustionIndex B x, ?_⟩
    change ((↑) : (⋃ i, B i) → X) ⁻¹' B (exhaustionIndex B x + 1) ∈ 𝓝 x
    exact preimage_coe_mem_nhds_subtype.mpr
      (R.ambient_mem_nhdsWithin (exhaustionIndex B x) (mem_exhaustionIndex B x))
  · intro i
    exact R.continuousOn_retractionValue_stage (i + 1)

theorem continuousOn_homotopyValue_stage
    (R : CompatibleStrongDeformationRetractSystem A B) (i : ℕ) :
    ContinuousOn (fun z : I × (⋃ j, B j) => R.homotopyValue z.1 z.2)
      {z | (z.2 : X) ∈ B i} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let inclusion : {z : I × (⋃ j, B j) | (z.2 : X) ∈ B i} → I × B i :=
    fun z => (z.1.1, ⟨z.1.2, z.2⟩)
  have hinclusion : Continuous inclusion := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · exact (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  have hcontinuous : Continuous (fun z : {z : I × (⋃ j, B j) | (z.2 : X) ∈ B i} =>
      strongDeformationHomotopyValue (R.stage i) z.1.1 ⟨z.1.2, z.2⟩) :=
    continuous_subtype_val.comp ((R.stage i).homotopy.continuous.comp hinclusion)
  convert hcontinuous using 1
  funext z
  exact R.homotopyValue_eq_stage z.1.1 z.1.2 z.2

theorem continuous_homotopyValue (R : CompatibleStrongDeformationRetractSystem A B) :
    Continuous (fun z : I × (⋃ j, B j) => R.homotopyValue z.1 z.2) := by
  apply continuous_of_cover_nhds (s := fun i : ℕ =>
    {z : I × (⋃ j, B j) | (z.2 : X) ∈ B (i + 1)})
  · intro z
    refine ⟨exhaustionIndex B z.2, ?_⟩
    change Prod.snd ⁻¹' (((↑) : (⋃ i, B i) → X) ⁻¹'
      B (exhaustionIndex B z.2 + 1)) ∈ 𝓝 z
    exact continuousAt_snd.preimage_mem_nhds
      (preimage_coe_mem_nhds_subtype.mpr
        (R.ambient_mem_nhdsWithin (exhaustionIndex B z.2)
          (mem_exhaustionIndex B z.2)))
  · intro i
    exact R.continuousOn_homotopyValue_stage (i + 1)

open Classical in
noncomputable def toStrongDeformationRetract
    (R : CompatibleStrongDeformationRetractSystem A B) :
    StrongDeformationRetract (regularNeighborhoodExhaustionCore A B) where
  retraction := ⟨fun x => ⟨⟨R.retractionValue x, R.retractionValue_mem_ambient x⟩,
    R.retractionValue_mem_core x⟩,
    ((R.continuous_retractionValue.subtype_mk _).subtype_mk _)⟩
  homotopy := {
    toHomotopy := {
      toContinuousMap := ⟨fun z => ⟨R.homotopyValue z.1 z.2,
        R.homotopyValue_mem_ambient z.1 z.2⟩,
        R.continuous_homotopyValue.subtype_mk _⟩
      map_zero_left := by
        intro x
        apply Subtype.ext
        simp only [ContinuousMap.id_apply]
        exact congrArg Subtype.val
          ((R.stage (exhaustionIndex B x)).homotopy.apply_zero
            ⟨x, mem_exhaustionIndex B x⟩)
      map_one_left := by
        intro x
        apply Subtype.ext
        simp only [ContinuousMap.comp_apply, ContinuousMap.restrict_apply,
          ContinuousMap.id_apply]
        exact congrArg Subtype.val
          ((R.stage (exhaustionIndex B x)).homotopy.apply_one
            ⟨x, mem_exhaustionIndex B x⟩)
    }
    prop' := by
      intro t x hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      apply Subtype.ext
      simp only [ContinuousMap.id_apply]
      change R.homotopyValue t x = (x : X)
      rw [R.homotopyValue_eq_stage t x (R.core_subset i hxi)]
      exact congrArg Subtype.val ((R.stage i).homotopy_fixed_on t hxi)
  }

def const {A B : Set X} (hAB : A ⊆ B)
    (r : StrongDeformationRetract (regularNeighborhoodStageCore A B)) :
    CompatibleStrongDeformationRetractSystem (fun _ => A) (fun _ => B) where
  core_subset := fun _ => hAB
  stage := fun _ => r
  retraction_compatible := by
    intro i j hij x hxi hxj
    congr
  homotopy_compatible := by
    intro i j hij t x hxi hxj
    congr
  ambient_mem_nhdsWithin := by
    intro i x hx
    simpa only [iUnion_const] using (self_mem_nhdsWithin : B ∈ 𝓝[B] x)

end CompatibleStrongDeformationRetractSystem

end DifferentialGeometry.Topology.PiecewiseLinear
