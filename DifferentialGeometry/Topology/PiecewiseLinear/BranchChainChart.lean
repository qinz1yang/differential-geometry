/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.VertexBranchChartPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem isPLHomeomorphOn_iUnion_of_forall {ι : Type*} {U : ι → Set E}
    {V : ι → Set (ℝ × ℝ × ℝ)} {Φ : E → ℝ × ℝ × ℝ} (hU : ∀ i, IsOpen (U i))
    (hV : ∀ i, IsOpen (V i))
    (hPL : ∀ i, IsPLHomeomorphOn Φ (U i) (V i)) (hinj : InjOn Φ (⋃ i, U i)) :
    IsPLHomeomorphOn Φ (⋃ i, U i) (⋃ i, V i) := by
  have himage : Φ '' (⋃ i, U i) = ⋃ i, V i := by
    rw [image_iUnion]
    exact iUnion_congr fun i => (hPL i).image_eq
  refine ⟨himage ▸ hinj.bijOn_image, ?_, ?_⟩
  · refine isPiecewiseAffineOn_of_locally fun x hx => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    refine ⟨U i, hU i, hi, ?_⟩
    rw [inter_eq_right.mpr (subset_iUnion U i)]
    exact (hPL i).isPiecewiseAffineOn
  · refine isPiecewiseAffineOn_of_locally fun z hz => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    refine ⟨V i, hV i, hi, ?_⟩
    rw [inter_eq_right.mpr (subset_iUnion V i)]
    refine ((hPL i).isPiecewiseAffineOn_invFunOn).congr fun w hw => ?_
    have h1 : Function.invFunOn Φ (U i) w ∈ U i := (hPL i).bijOn.surjOn.mapsTo_invFunOn hw
    have h2 : Φ (Function.invFunOn Φ (U i) w) = w := (hPL i).bijOn.invOn_invFunOn.2 hw
    have hwU : w ∈ Φ '' (⋃ i, U i) := by
      rw [himage]
      exact mem_iUnion.mpr ⟨i, hw⟩
    have h3 : Function.invFunOn Φ (⋃ i, U i) w ∈ ⋃ i, U i :=
      (hinj.bijOn_image).surjOn.mapsTo_invFunOn hwU
    have h4 : Φ (Function.invFunOn Φ (⋃ i, U i) w) = w :=
      (hinj.bijOn_image).invOn_invFunOn.2 hwU
    exact hinj h3 (mem_iUnion.mpr ⟨i, h1⟩) (h4.trans h2.symm)

omit [FiniteDimensional ℝ E] in
theorem exists_chart_branch_chain {ι : Type*} {U : ι → Set E} {V : ι → Set (ℝ × ℝ × ℝ)}
    {Φ : E → ℝ × ℝ × ℝ} {A B S T W : Set E}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hPL : ∀ i, IsPLHomeomorphOn Φ (U i) (V i)) (hinj : InjOn Φ (⋃ i, U i))
    (hA : ∀ i, ∀ y ∈ U i, y ∈ A → (Φ y).2.2 = 0)
    (hB : ∀ i, ∀ y ∈ U i, y ∈ B → (Φ y).2.1 = 0)
    (hthird : ∀ i, U i ∩ T = ∅)
    (hSU : S ⊆ ⋃ i, U i) (hUW : (⋃ i, U i) ⊆ W) :
    ∃ O : Set E, IsOpen O ∧ S ⊆ O ∧ O ⊆ W ∧ O ∩ T = ∅ ∧
      IsPLHomeomorphOn Φ O (⋃ i, V i) ∧
        (∀ y ∈ O, y ∈ A → (Φ y).2.2 = 0) ∧ (∀ y ∈ O, y ∈ B → (Φ y).2.1 = 0) := by
  refine ⟨⋃ i, U i, isOpen_iUnion hU, hSU, hUW, ?_,
    isPLHomeomorphOn_iUnion_of_forall hU hV hPL hinj, ?_, ?_⟩
  · rw [iUnion_inter]
    exact iUnion_eq_empty.mpr hthird
  · intro y hy hyA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hA i y hi hyA
  · intro y hy hyB
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hB i y hi hyB

theorem exists_openPartialHomeomorph_branch_chain {ι : Type*} {U : ι → Set E}
    {V : ι → Set (ℝ × ℝ × ℝ)} {Φ : E → ℝ × ℝ × ℝ} {A B S T W : Set E}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hPL : ∀ i, IsPLHomeomorphOn Φ (U i) (V i)) (hinj : InjOn Φ (⋃ i, U i))
    (hA : ∀ i, ∀ y ∈ U i, y ∈ A → (Φ y).2.2 = 0)
    (hB : ∀ i, ∀ y ∈ U i, y ∈ B → (Φ y).2.1 = 0)
    (hthird : ∀ i, U i ∩ T = ∅)
    (hSU : S ⊆ ⋃ i, U i) (hUW : (⋃ i, U i) ⊆ W) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ), S ⊆ e.source ∧ e.source ⊆ W ∧
      e.source ∩ T = ∅ ∧ IsPiecewiseAffineOn e e.source ∧
        IsPiecewiseAffineOn e.symm e.target ∧
          (∀ y ∈ e.source, y ∈ A → (e y).2.2 = 0) ∧
            (∀ y ∈ e.source, y ∈ B → (e y).2.1 = 0) := by
  have hglue := isPLHomeomorphOn_iUnion_of_forall hU hV hPL hinj
  refine ⟨hglue.toOpenPartialHomeomorph (isOpen_iUnion hU) (isOpen_iUnion hV), hSU, hUW, ?_,
    hglue.isPiecewiseAffineOn, hglue.isPiecewiseAffineOn_invFunOn, ?_, ?_⟩
  · change (⋃ i, U i) ∩ T = ∅
    rw [iUnion_inter]
    exact iUnion_eq_empty.mpr hthird
  · intro y hy hyA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hA i y hi hyA
  · intro y hy hyB
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hB i y hi hyB

theorem image_inter_source_eq_of_forall_mem_iff {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) {P : Set X} {Q : Set Y}
    (h : ∀ y ∈ e.source, y ∈ P ↔ e y ∈ Q) : e '' (P ∩ e.source) = e.target ∩ Q := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyP, hys⟩, rfl⟩
    exact ⟨e.map_source hys, (h y hys).mp hyP⟩
  · rintro ⟨hzt, hzQ⟩
    refine ⟨e.symm z, ⟨(h _ (e.map_target hzt)).mpr ?_, e.map_target hzt⟩, e.right_inv hzt⟩
    rw [e.right_inv hzt]
    exact hzQ

theorem exists_openPartialHomeomorph_branch_chain_slab {ι : Type*} {U : ι → Set E}
    {V : ι → Set (ℝ × ℝ × ℝ)} {Φ : E → ℝ × ℝ × ℝ} {A B S T W M BdM : Set E} {c : ℝ}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hPL : ∀ i, IsPLHomeomorphOn Φ (U i) (V i)) (hinj : InjOn Φ (⋃ i, U i))
    (hA : ∀ i, ∀ y ∈ U i, y ∈ A → (Φ y).2.2 = 0)
    (hB : ∀ i, ∀ y ∈ U i, y ∈ B → (Φ y).2.1 = 0)
    (hM : ∀ i, ∀ y ∈ U i, y ∈ M ↔ 0 ≤ (Φ y).1 ∧ (Φ y).1 ≤ c)
    (hBd : ∀ i, ∀ y ∈ U i, y ∈ BdM ↔ (Φ y).1 = 0 ∨ (Φ y).1 = c)
    (hthird : ∀ i, U i ∩ T = ∅)
    (hSU : S ⊆ ⋃ i, U i) (hUW : (⋃ i, U i) ⊆ W) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ), S ⊆ e.source ∧ e.source ⊆ W ∧
      e.source ∩ T = ∅ ∧ IsPiecewiseAffineOn e e.source ∧
        IsPiecewiseAffineOn e.symm e.target ∧
          (∀ y ∈ e.source, y ∈ A → (e y).2.2 = 0) ∧
            (∀ y ∈ e.source, y ∈ B → (e y).2.1 = 0) ∧
              (∀ y ∈ e.source, y ∈ M ↔ 0 ≤ (e y).1 ∧ (e y).1 ≤ c) ∧
                (∀ y ∈ e.source, y ∈ BdM ↔ (e y).1 = 0 ∨ (e y).1 = c) ∧
                  e '' (M ∩ e.source) = e.target ∩ {p | 0 ≤ p.1 ∧ p.1 ≤ c} ∧
                    e '' (BdM ∩ e.source) = e.target ∩ {p | p.1 = 0 ∨ p.1 = c} := by
  have hglue := isPLHomeomorphOn_iUnion_of_forall hU hV hPL hinj
  have hM' : ∀ y ∈ ⋃ i, U i, y ∈ M ↔ 0 ≤ (Φ y).1 ∧ (Φ y).1 ≤ c := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hM i y hi
  have hBd' : ∀ y ∈ ⋃ i, U i, y ∈ BdM ↔ (Φ y).1 = 0 ∨ (Φ y).1 = c := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hBd i y hi
  refine ⟨hglue.toOpenPartialHomeomorph (isOpen_iUnion hU) (isOpen_iUnion hV), hSU, hUW, ?_,
    hglue.isPiecewiseAffineOn, hglue.isPiecewiseAffineOn_invFunOn, ?_, ?_, hM', hBd',
    image_inter_source_eq_of_forall_mem_iff _ hM', image_inter_source_eq_of_forall_mem_iff _ hBd'⟩
  · change (⋃ i, U i) ∩ T = ∅
    rw [iUnion_inter]
    exact iUnion_eq_empty.mpr hthird
  · intro y hy hyA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hA i y hi hyA
  · intro y hy hyB
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hB i y hi hyB

theorem exists_slab_branch_chain_instance {c : ℝ} (hc : 0 < c) :
    ∃ (S M BdM A B : Set (ℝ × ℝ × ℝ)) (p q : ℝ × ℝ × ℝ),
      p ≠ q ∧ p ∈ BdM ∧ q ∈ BdM ∧ S = A ∩ B ∩ M ∧ p ∈ S ∧ q ∈ S ∧
        ∃ e : OpenPartialHomeomorph (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ), S ⊆ e.source ∧
          (∀ y ∈ e.source, y ∈ A → (e y).2.2 = 0) ∧
            (∀ y ∈ e.source, y ∈ B → (e y).2.1 = 0) ∧
              (∀ y ∈ e.source, y ∈ M ↔ 0 ≤ (e y).1 ∧ (e y).1 ≤ c) ∧
                (∀ y ∈ e.source, y ∈ BdM ↔ (e y).1 = 0 ∨ (e y).1 = c) := by
  have hid : IsPLHomeomorphOn (id : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) univ univ :=
    ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ,
      (isPiecewiseAffineOn_id isOpen_univ).congr fun _ hx => (bijOn_id univ).invOn_invFunOn.1 hx⟩
  refine ⟨{p | 0 ≤ p.1 ∧ p.1 ≤ c ∧ p.2 = 0}, {p | 0 ≤ p.1 ∧ p.1 ≤ c}, {p | p.1 = 0 ∨ p.1 = c},
    {p | p.2.2 = 0}, {p | p.2.1 = 0}, (0, 0, 0), (c, 0, 0), fun h => hc.ne (congrArg Prod.fst h),
    Or.inl rfl, Or.inr rfl, ?_, ⟨le_rfl, hc.le, rfl⟩, ⟨hc.le, le_rfl, rfl⟩, ?_⟩
  · ext p
    change (0 ≤ p.1 ∧ p.1 ≤ c ∧ p.2 = 0) ↔ (p.2.2 = 0 ∧ p.2.1 = 0) ∧ (0 ≤ p.1 ∧ p.1 ≤ c)
    rw [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
    tauto
  · obtain ⟨e, hS, -, -, -, -, hA, hB, hM, hBd, -, -⟩ :=
      exists_openPartialHomeomorph_branch_chain_slab (ι := Unit) (U := fun _ => univ)
        (V := fun _ => univ) (Φ := id) (A := {p | p.2.2 = 0}) (B := {p | p.2.1 = 0})
        (S := {p | 0 ≤ p.1 ∧ p.1 ≤ c ∧ p.2 = 0}) (T := ∅) (W := univ)
        (M := {p | 0 ≤ p.1 ∧ p.1 ≤ c}) (BdM := {p | p.1 = 0 ∨ p.1 = c}) (c := c)
        (fun _ => isOpen_univ) (fun _ => isOpen_univ) (fun _ => hid) (injOn_id _)
        (fun _ y _ hy => hy) (fun _ y _ hy => hy) (fun _ y _ => Iff.rfl) (fun _ y _ => Iff.rfl)
        (fun _ => inter_empty _) ((subset_univ _).trans (subset_iUnion (fun _ : Unit => (univ : Set
            (ℝ × ℝ × ℝ))) ()))
        (subset_univ _)
    exact ⟨e, hS, hA, hB, hM, hBd⟩

end DifferentialGeometry.Topology.PiecewiseLinear
