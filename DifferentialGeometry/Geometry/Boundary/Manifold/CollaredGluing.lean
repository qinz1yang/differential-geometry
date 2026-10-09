import DifferentialGeometry.Geometry.Boundary.Manifold.Component
import DifferentialGeometry.Topology.Attachment.BoundaryGluing
import Mathlib.Geometry.Manifold.Instances.Real

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Boundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
variable {ι : Type v} [Finite ι]

structure CollaredGluing (I : ModelWithCorners ℝ E H) (X : Type u) [TopologicalSpace X]
    [ChartedSpace H X] (ι : Type v) [Finite ι] where
  left : ι → BoundaryComponent I X
  right : ι → BoundaryComponent I X
  blocks_injective : Function.Injective fun p : ι × Bool => cond p.2 (left p.1) (right p.1)
  ε : ι → ℝ
  ε_pos : ∀ i, 0 < ε i
  collarLeft : ∀ i, C(↥(left i).carrier × Icc (0 : ℝ) (ε i), X)
  collarRight : ∀ i, C(↥(right i).carrier × Icc (0 : ℝ) (ε i), X)
  collarLeft_zero : ∀ (i : ι) (z : ↥(left i).carrier),
    collarLeft i (z, ⟨0, le_rfl, (ε_pos i).le⟩) = z
  collarRight_zero : ∀ (i : ι) (z : ↥(right i).carrier),
    collarRight i (z, ⟨0, le_rfl, (ε_pos i).le⟩) = z
  collarLeft_injective : ∀ i, Function.Injective (collarLeft i)
  collarRight_injective : ∀ i, Function.Injective (collarRight i)
  collarLeft_inward : ∀ (i : ι) (z : ↥(left i).carrier) (t : Icc (0 : ℝ) (ε i)),
    0 < (t : ℝ) → ¬ I.IsBoundaryPoint (collarLeft i (z, t))
  collarRight_inward : ∀ (i : ι) (z : ↥(right i).carrier) (t : Icc (0 : ℝ) (ε i)),
    0 < (t : ℝ) → ¬ I.IsBoundaryPoint (collarRight i (z, t))
  collar_disjoint : ∀ i, Disjoint (range (collarLeft i)) (range (collarRight i))
  attaching : ∀ i, ↥(left i).carrier ≃ₜ ↥(right i).carrier

namespace CollaredGluing

variable {G : CollaredGluing I X ι}

theorem left_ne_right (i : ι) : G.left i ≠ G.right i := by
  intro h
  have hc := G.blocks_injective (a₁ := (i, true)) (a₂ := (i, false)) (by
    simp only [Bool.cond_true, Bool.cond_false]
    exact h)
  nomatch (Prod.mk.inj hc).2

theorem left_ne_left {i j : ι} (h : i ≠ j) : G.left i ≠ G.left j := by
  intro hij
  exact h (Prod.mk.inj (G.blocks_injective (a₁ := (i, true)) (a₂ := (j, true)) (by
    simp only [Bool.cond_true]
    exact hij))).1

theorem left_ne_right' (i j : ι) : G.left i ≠ G.right j := by
  intro hij
  exact nomatch (Prod.mk.inj (G.blocks_injective (a₁ := (i, true)) (a₂ := (j, false)) (by
    simp only [Bool.cond_true, Bool.cond_false]
    exact hij))).2

theorem right_ne_right {i j : ι} (h : i ≠ j) : G.right i ≠ G.right j := by
  intro hij
  exact h (Prod.mk.inj (G.blocks_injective (a₁ := (i, false)) (a₂ := (j, false)) (by
    simp only [Bool.cond_false]
    exact hij))).1

theorem disjoint_blocks {i j : ι} (h : i ≠ j) :
    Disjoint ((G.left i).carrier ∪ (G.right i).carrier)
      ((G.left j).carrier ∪ (G.right j).carrier) := by
  rw [Set.disjoint_left]
  rintro x (hx | hx) (hy | hy)
  · exact G.left_ne_left h (BoundaryComponent.eq_of_mem_carrier hx hy)
  · exact G.left_ne_right' i j (BoundaryComponent.eq_of_mem_carrier hx hy)
  · exact G.left_ne_right' j i (BoundaryComponent.eq_of_mem_carrier hy hx)
  · exact G.right_ne_right h (BoundaryComponent.eq_of_mem_carrier hx hy)

theorem disjoint_left_right (i : ι) :
    Disjoint (G.left i).carrier (G.right i).carrier :=
  BoundaryComponent.disjoint_carrier (G.left_ne_right i)

def toBoundaryGluing [IsManifold I 1 X] (G : CollaredGluing I X ι) :
    Topology.BoundaryGluing X ι where
  left i := (G.left i).carrier
  right i := (G.right i).carrier
  attaching i := G.attaching i
  isClosed_left i := (G.left i).isClosed_carrier
  isClosed_right i := (G.right i).isClosed_carrier
  disjoint_left_right i := G.disjoint_left_right i
  disjoint_blocks i j hij := G.disjoint_blocks (i := i) (j := j) hij

theorem t2Space_quotient [IsManifold I 1 X] [T2Space X] [CompactSpace X]
    (G : CollaredGluing I X ι) : T2Space (Quotient G.toBoundaryGluing.setoid) :=
  Topology.BoundaryGluing.instT2SpaceQuotient G.toBoundaryGluing

theorem block_subset_boundary [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι) :
    (G.toBoundaryGluing).block i ⊆ I.boundary X := by
  rintro x (hx | hx)
  · exact BoundaryComponent.carrier_subset_boundary (G.left i) hx
  · exact BoundaryComponent.carrier_subset_boundary (G.right i) hx

theorem notMem_block_of_not_isBoundaryPoint [IsManifold I 1 X] (G : CollaredGluing I X ι)
    {x : X} (hx : ¬ I.IsBoundaryPoint x) (i : ι) : x ∉ (G.toBoundaryGluing).block i :=
  fun h => hx (G.block_subset_boundary i h)

theorem rel_iff_of_mem_block [IsManifold I 1 X] (G : CollaredGluing I X ι) {i : ι} {x y : X}
    (hx : x ∈ (G.toBoundaryGluing).block i) (h : (G.toBoundaryGluing).rel x y) :
    y = x ∨ y = (G.toBoundaryGluing).flip i x := by
  rcases h with rfl | ⟨j, hxj, hy⟩
  · exact Or.inl rfl
  · by_cases hij : i = j
    · subst hij
      exact Or.inr hy
    · exact ((Set.disjoint_left.mp (G.disjoint_blocks hij)) hx hxj).elim

theorem notMem_range_collarLeft_of_mem_range_collarRight (G : CollaredGluing I X ι)
    (i : ι) {x : X} (hx : x ∈ range (G.collarRight i)) : x ∉ range (G.collarLeft i) :=
  fun hy => (Set.disjoint_left.mp (G.collar_disjoint i)) hy hx

theorem notMem_range_collarRight_of_mem_range_collarLeft (G : CollaredGluing I X ι)
    (i : ι) {x : X} (hx : x ∈ range (G.collarLeft i)) : x ∉ range (G.collarRight i) :=
  fun hy => (Set.disjoint_left.mp (G.collar_disjoint i)) hx hy

def seamChart [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι) :
    C(↥(G.left i).carrier × Icc (-(G.ε i)) (G.ε i), Quotient G.toBoundaryGluing.setoid) where
  toFun p := if 0 ≤ (p.2 : ℝ) then
      Quotient.mk'' (G.collarRight i (G.attaching i p.1,
        ⟨max (p.2 : ℝ) 0, le_max_right _ _, max_le p.2.2.2 (G.ε_pos i).le⟩))
    else
      Quotient.mk'' (G.collarLeft i (p.1,
        ⟨max (-(p.2 : ℝ)) 0, le_max_right _ _, max_le (by linarith [p.2.2.1])
          (G.ε_pos i).le⟩))
  continuous_toFun := by
    classical
    refine Continuous.if ?_ ?_ ?_
    · intro p hp
      have hh := (continuous_subtype_val.comp continuous_snd).frontier_preimage_subset
        (Ici (0 : ℝ)) hp
      have ht : (p.2 : ℝ) = 0 := by
        simpa only [mem_preimage, frontier_Ici, mem_singleton_iff,
          Function.comp_apply] using hh
      have hR : (⟨max (p.2 : ℝ) 0, le_max_right _ _,
            max_le p.2.2.2 (G.ε_pos i).le⟩ : Icc (0 : ℝ) (G.ε i))
          = ⟨0, le_rfl, (G.ε_pos i).le⟩ := by
        refine Subtype.ext ?_
        simp [ht]
      have hL : (⟨max (-(p.2 : ℝ)) 0, le_max_right _ _,
            max_le (by linarith [p.2.2.1]) (G.ε_pos i).le⟩ : Icc (0 : ℝ) (G.ε i))
          = ⟨0, le_rfl, (G.ε_pos i).le⟩ := by
        refine Subtype.ext ?_
        simp [ht]
      rw [hR, G.collarRight_zero i (G.attaching i p.1), hL, G.collarLeft_zero i p.1]
      exact Quotient.sound' (G.toBoundaryGluing.rel_of_attaching i p.1)
    · have hmid : Continuous fun p : ↥(G.left i).carrier × Icc (-(G.ε i)) (G.ε i) =>
          ((G.attaching i) p.1,
            (⟨max (p.2 : ℝ) 0, le_max_right _ _,
              max_le p.2.2.2 (G.ε_pos i).le⟩ : Icc (0 : ℝ) (G.ε i))) := by fun_prop
      exact (continuous_quotient_mk'.comp (G.collarRight i).continuous).comp hmid
    · have hmid : Continuous fun p : ↥(G.left i).carrier × Icc (-(G.ε i)) (G.ε i) =>
          (p.1, (⟨max (-(p.2 : ℝ)) 0, le_max_right _ _,
              max_le (by linarith [p.2.2.1]) (G.ε_pos i).le⟩ :
                Icc (0 : ℝ) (G.ε i))) := by fun_prop
      exact (continuous_quotient_mk'.comp (G.collarLeft i).continuous).comp hmid

theorem seamChart_apply_of_nonneg [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι)
    (p : ↥(G.left i).carrier × Icc (-(G.ε i)) (G.ε i)) (hp : 0 ≤ (p.2 : ℝ)) :
    G.seamChart i p = Quotient.mk'' (G.collarRight i (G.attaching i p.1,
      ⟨(p.2 : ℝ), hp, p.2.2.2⟩)) := by
  simp only [seamChart, ContinuousMap.coe_mk, ite_eq_left hp]
  refine congrArg (Quotient.mk'' (s₁ := (G.toBoundaryGluing).setoid)) ?_
  refine congrArg (G.collarRight i : ↥(G.right i).carrier × Icc (0 : ℝ) (G.ε i) → X) ?_
  exact Prod.ext rfl (Subtype.ext (max_eq_left hp))

theorem seamChart_apply_of_nonpos [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι)
    (p : ↥(G.left i).carrier × Icc (-(G.ε i)) (G.ε i)) (hp : (p.2 : ℝ) ≤ 0) :
    G.seamChart i p = Quotient.mk'' (G.collarLeft i (p.1,
      ⟨-(p.2 : ℝ), neg_nonneg.mpr hp, by linarith [p.2.2.1]⟩)) := by
  rcases lt_or_eq_of_le hp with h | h
  · simp only [seamChart, ContinuousMap.coe_mk, ite_eq_right h.not_ge]
    refine congrArg (Quotient.mk'' (s₁ := (G.toBoundaryGluing).setoid)) ?_
    refine congrArg (G.collarLeft i : ↥(G.left i).carrier × Icc (0 : ℝ) (G.ε i) → X) ?_
    exact Prod.ext rfl (Subtype.ext (max_eq_left (neg_nonneg.mpr hp)))
  · have h0 : (⟨(p.2 : ℝ), le_of_eq h.symm, p.2.2.2⟩ : Icc (0 : ℝ) (G.ε i))
        = ⟨0, le_rfl, (G.ε_pos i).le⟩ := Subtype.ext h
    have h1 : (⟨-(p.2 : ℝ), neg_nonneg.mpr hp, by linarith [p.2.2.1]⟩ :
        Icc (0 : ℝ) (G.ε i)) = ⟨0, le_rfl, (G.ε_pos i).le⟩ := by
      refine Subtype.ext ?_
      dsimp only
      rw [h, neg_zero]
    rw [seamChart_apply_of_nonneg G i p (le_of_eq h.symm), h0,
      G.collarRight_zero i (G.attaching i p.1), h1, G.collarLeft_zero i p.1]
    exact Quotient.sound' (G.toBoundaryGluing.rel_of_attaching i p.1)

theorem seamChart_zero [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι)
    (z : ↥(G.left i).carrier) :
    G.seamChart i (z, ⟨0, neg_nonpos.mpr (G.ε_pos i).le, (G.ε_pos i).le⟩)
      = Quotient.mk'' (z : X) := by
  rw [seamChart_apply_of_nonneg G i _ le_rfl, G.collarRight_zero i (G.attaching i z)]
  exact Quotient.sound' (G.toBoundaryGluing.rel_of_attaching i z)

theorem seamChart_injective [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι) :
    Function.Injective (G.seamChart i) := by
  intro p p' h
  have hrel : ∀ {a b : X}, Quotient.mk'' (s₁ := (G.toBoundaryGluing).setoid) a
      = Quotient.mk'' (s₁ := (G.toBoundaryGluing).setoid) b → (G.toBoundaryGluing).rel a b :=
    fun hh => (Quotient.eq'' (s₁ := (G.toBoundaryGluing).setoid)).mp hh
  have hmem_right (z : ↥(G.right i).carrier) :
      (z : X) ∈ (G.toBoundaryGluing).block i := Or.inr z.2
  have hval : ∀ {a b : Icc (0 : ℝ) (G.ε i)}, a = b → (a : ℝ) = (b : ℝ) :=
    fun hh => congrArg (fun t : Icc (0 : ℝ) (G.ε i) => (t : ℝ)) hh
  by_cases hp : 0 ≤ (p.2 : ℝ) <;> by_cases hp' : 0 ≤ (p'.2 : ℝ)
  · rw [G.seamChart_apply_of_nonneg i p hp, G.seamChart_apply_of_nonneg i p' hp'] at h
    rcases lt_or_eq_of_le hp with ht | ht
    · have hnb := G.collarRight_inward i (G.attaching i p.1) ⟨(p.2 : ℝ), hp, p.2.2.2⟩ ht
      have heq := (G.toBoundaryGluing).eq_of_rel_of_notMem
        (fun j => G.notMem_block_of_not_isBoundaryPoint hnb j) (hrel h)
      obtain ⟨hz, htt⟩ := Prod.mk.inj (G.collarRight_injective i heq)
      exact Prod.ext ((G.attaching i).injective hz)
        (Subtype.ext (hval htt))
    · have h0 : (⟨(p.2 : ℝ), hp, p.2.2.2⟩ : Icc (0 : ℝ) (G.ε i))
          = ⟨0, le_rfl, (G.ε_pos i).le⟩ := Subtype.ext ht.symm
      rw [h0, G.collarRight_zero i (G.attaching i p.1)] at h
      rcases G.rel_iff_of_mem_block (hmem_right (G.attaching i p.1)) (hrel h) with heq | hflip
      · have h2 := heq.trans (G.collarRight_zero i (G.attaching i p.1)).symm
        obtain ⟨hz, htt⟩ := Prod.mk.inj (G.collarRight_injective i h2)
        exact Prod.ext ((G.attaching i).injective hz.symm)
          (Subtype.ext (ht.symm.trans (hval htt).symm))
      · have h3 : G.collarRight i (G.attaching i p'.1, ⟨(p'.2 : ℝ), hp', p'.2.2.2⟩) = (p.1 : X) :=
          hflip.trans ((G.toBoundaryGluing).flip_attaching i p.1)
        have hmemL : (p.1 : X) ∈ range (G.collarLeft i) := ⟨(p.1, ⟨0, le_rfl, (G.ε_pos i).le⟩),
          G.collarLeft_zero i p.1⟩
        have hmemR : (p.1 : X) ∈ range (G.collarRight i) := ⟨_, h3⟩
        exact ((Set.disjoint_left.mp (G.collar_disjoint i)) hmemL hmemR).elim
  · rw [G.seamChart_apply_of_nonneg i p hp,
      G.seamChart_apply_of_nonpos i p' (le_of_lt (lt_of_not_ge hp'))] at h
    rcases lt_or_eq_of_le hp with ht | ht
    · have hnb := G.collarRight_inward i (G.attaching i p.1) ⟨(p.2 : ℝ), hp, p.2.2.2⟩ ht
      have heq := (G.toBoundaryGluing).eq_of_rel_of_notMem
        (fun j => G.notMem_block_of_not_isBoundaryPoint hnb j) (hrel h)
      have hmemL : G.collarLeft i (p'.1, ⟨-(p'.2 : ℝ), neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp')),
          by linarith [p'.2.2.1]⟩) ∈ range (G.collarLeft i) := ⟨_, rfl⟩
      have hmemR : G.collarLeft i (p'.1, ⟨-(p'.2 : ℝ), neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp')),
          by linarith [p'.2.2.1]⟩) ∈ range (G.collarRight i) := ⟨_, heq⟩
      exact ((Set.disjoint_left.mp (G.collar_disjoint i)) hmemL hmemR).elim
    · have h0 : (⟨(p.2 : ℝ), hp, p.2.2.2⟩ : Icc (0 : ℝ) (G.ε i))
          = ⟨0, le_rfl, (G.ε_pos i).le⟩ := Subtype.ext ht.symm
      rw [h0, G.collarRight_zero i (G.attaching i p.1)] at h
      rcases G.rel_iff_of_mem_block (hmem_right (G.attaching i p.1)) (hrel h) with heq | hflip
      · have hmemR : G.collarLeft i (p'.1, ⟨-(p'.2 : ℝ),
            neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp')),
            by linarith [p'.2.2.1]⟩) ∈ range (G.collarRight i) :=
          ⟨_, (G.collarRight_zero i (G.attaching i p.1)).trans heq.symm⟩
        exact ((Set.disjoint_left.mp (G.collar_disjoint i)) ⟨_, rfl⟩ hmemR).elim
      · have h3 : G.collarLeft i (p'.1, ⟨-(p'.2 : ℝ), neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp')),
              by linarith [p'.2.2.1]⟩) = G.collarLeft i (p.1, ⟨0, le_rfl, (G.ε_pos i).le⟩) :=
          (hflip.trans ((G.toBoundaryGluing).flip_attaching i p.1)).trans
            (G.collarLeft_zero i p.1).symm
        obtain ⟨hz, htt⟩ := Prod.mk.inj (G.collarLeft_injective i h3)
        exact Prod.ext hz.symm (Subtype.ext (ht.symm.trans
          (neg_eq_zero.mp (hval htt)).symm))
  · rw [G.seamChart_apply_of_nonpos i p (le_of_lt (lt_of_not_ge hp)),
      G.seamChart_apply_of_nonneg i p' hp'] at h
    rcases lt_or_eq_of_le hp' with ht | ht
    · have hnb := G.collarRight_inward i (G.attaching i p'.1) ⟨(p'.2 : ℝ), hp', p'.2.2.2⟩ ht
      have heq := (G.toBoundaryGluing).eq_of_rel_of_notMem
        (fun j => G.notMem_block_of_not_isBoundaryPoint hnb j)
        ((G.toBoundaryGluing).setoid.symm (hrel h))
      have hmemL : G.collarLeft i (p.1, ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp)),
          by linarith [p.2.2.1]⟩) ∈ range (G.collarLeft i) := ⟨_, rfl⟩
      have hmemR : G.collarLeft i (p.1, ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp)),
          by linarith [p.2.2.1]⟩) ∈ range (G.collarRight i) := ⟨_, heq⟩
      exact ((Set.disjoint_left.mp (G.collar_disjoint i)) hmemL hmemR).elim
    · have h0 : (⟨(p'.2 : ℝ), hp', p'.2.2.2⟩ : Icc (0 : ℝ) (G.ε i))
          = ⟨0, le_rfl, (G.ε_pos i).le⟩ := Subtype.ext ht.symm
      rw [h0, G.collarRight_zero i (G.attaching i p'.1)] at h
      rcases G.rel_iff_of_mem_block (hmem_right (G.attaching i p'.1))
        ((G.toBoundaryGluing).setoid.symm (hrel h)) with heq | hflip
      · have hmemL : G.collarLeft i (p.1, ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp)),
            by linarith [p.2.2.1]⟩) ∈ range (G.collarRight i) :=
          ⟨_, (G.collarRight_zero i (G.attaching i p'.1)).trans heq.symm⟩
        exact ((Set.disjoint_left.mp (G.collar_disjoint i)) ⟨_, rfl⟩ hmemL).elim
      · have h3 : G.collarLeft i (p.1, ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp)),
              by linarith [p.2.2.1]⟩) = G.collarLeft i (p'.1, ⟨0, le_rfl, (G.ε_pos i).le⟩) :=
          (hflip.trans ((G.toBoundaryGluing).flip_attaching i p'.1)).trans
            (G.collarLeft_zero i p'.1).symm
        obtain ⟨hz, htt⟩ := Prod.mk.inj (G.collarLeft_injective i h3)
        exact Prod.ext hz (Subtype.ext ((neg_eq_zero.mp (hval htt)).trans ht))
  · rw [G.seamChart_apply_of_nonpos i p (le_of_lt (lt_of_not_ge hp)),
      G.seamChart_apply_of_nonpos i p' (le_of_lt (lt_of_not_ge hp'))] at h
    have hnb := G.collarLeft_inward i p.1
      ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp)), by linarith [p.2.2.1]⟩
      (neg_pos.mpr (lt_of_not_ge hp))
    have heq := (G.toBoundaryGluing).eq_of_rel_of_notMem
      (fun j => G.notMem_block_of_not_isBoundaryPoint hnb j) (hrel h)
    obtain ⟨hz, htt⟩ := Prod.mk.inj (G.collarLeft_injective i heq)
    exact Prod.ext hz (Subtype.ext (neg_inj.mp (hval htt)))

end CollaredGluing

section UnitInterval

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

def unitIntervalCollaredGluing : CollaredGluing (𝓡∂ 1) (Icc (0 : ℝ) 1) (Fin 1) := by
  classical
  haveI : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  haveI : Fact ((0 : ℝ) ≤ 1) := ⟨by norm_num⟩
  let X := Icc (0 : ℝ) 1
  let B := BoundaryManifold (𝓡∂ 1) X
  let g : B → X := fun y => (y : X)
  have hbound : (𝓡∂ 1).boundary X = {⊥, ⊤} := boundary_Icc
  have hg : Continuous g := continuous_subtype_val
  have hdich : ∀ y : B, g y = ⊥ ∨ g y = ⊤ := by
    intro y
    have hy : (y : X) ∈ ({⊥, ⊤} : Set X) := hbound ▸ y.2
    simpa [g] using hy
  let Yb : B := ⟨⊥, by rw [hbound]; exact Or.inl rfl⟩
  let Yt : B := ⟨⊤, by rw [hbound]; exact Or.inr rfl⟩
  let Cb : BoundaryComponent (𝓡∂ 1) X := ConnectedComponents.mk Yb
  let Ct : BoundaryComponent (𝓡∂ 1) X := ConnectedComponents.mk Yt
  have hclopen_b : IsClopen {y : B | g y = ⊥} := by
    refine ⟨?_, ?_⟩
    · have hset : {y : B | g y = ⊥} = g ⁻¹' ({⊥} : Set X) := rfl
      rw [hset]
      exact isClosed_singleton.preimage hg
    · have hset : {y : B | g y = ⊥} = g ⁻¹' {x : X | (x : ℝ) < 1 / 2} := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage]
        constructor
        · intro hy
          rw [hy]
          change (0 : ℝ) < 1 / 2
          norm_num
        · intro hy
          rcases hdich y with h | h
          · exact h
          · rw [h] at hy
            change (1 : ℝ) < 1 / 2 at hy
            norm_num at hy
      rw [hset]
      exact (isOpen_lt continuous_subtype_val continuous_const).preimage hg
  have hclopen_t : IsClopen {y : B | g y = ⊤} := by
    refine ⟨?_, ?_⟩
    · have hset : {y : B | g y = ⊤} = g ⁻¹' ({⊤} : Set X) := rfl
      rw [hset]
      exact isClosed_singleton.preimage hg
    · have hset : {y : B | g y = ⊤} = g ⁻¹' {x : X | (1 / 2 : ℝ) < (x : ℝ)} := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage]
        constructor
        · intro hy
          rw [hy]
          change (1 / 2 : ℝ) < 1
          norm_num
        · intro hy
          rcases hdich y with h | h
          · rw [h] at hy
            change (1 / 2 : ℝ) < 0 at hy
            norm_num at hy
          · exact h
      rw [hset]
      exact (isOpen_lt continuous_const continuous_subtype_val).preimage hg
  have hmem_b (z : ↥(BoundaryComponent.carrier Cb)) : (z : X) = ⊥ := by
    obtain ⟨y, hy, hyz⟩ := z.2
    have hz : y ∈ connectedComponent Yb := ConnectedComponents.coe_eq_coe'.mp hy
    have h1 : g y = ⊥ := hclopen_b.connectedComponent_subset rfl hz
    rw [← hyz]
    simpa [g] using h1
  have hmem_t (z : ↥(BoundaryComponent.carrier Ct)) : (z : X) = ⊤ := by
    obtain ⟨y, hy, hyz⟩ := z.2
    have hz : y ∈ connectedComponent Yt := ConnectedComponents.coe_eq_coe'.mp hy
    have h1 : g y = ⊤ := hclopen_t.connectedComponent_subset rfl hz
    rw [← hyz]
    simpa [g] using h1
  have hne : Cb ≠ Ct := by
    intro h
    have hbot : (⊥ : X) ∈ BoundaryComponent.carrier Ct := by
      rw [← h]
      exact BoundaryComponent.mk_mem_carrier Yb
    have hz := hmem_t ⟨⊥, hbot⟩
    have hval := congrArg (fun x : X => (x : ℝ)) hz
    dsimp only [g] at hval
    change (0 : ℝ) = 1 at hval
    norm_num at hval
  have hsub_b : Subsingleton ↥(BoundaryComponent.carrier Cb) :=
    ⟨fun a b => Subtype.ext (by rw [hmem_b a, hmem_b b])⟩
  have hsub_t : Subsingleton ↥(BoundaryComponent.carrier Ct) :=
    ⟨fun a b => Subtype.ext (by rw [hmem_t a, hmem_t b])⟩
  haveI := hsub_b
  haveI := hsub_t
  have hval_b (z : ↥(BoundaryComponent.carrier Cb)) : ((z : X) : ℝ) = 0 := by
    rw [hmem_b z]
    rfl
  have hval_t (z : ↥(BoundaryComponent.carrier Ct)) : ((z : X) : ℝ) = 1 := by
    rw [hmem_t z]
    rfl
  refine
    { left := fun _ => Cb
      right := fun _ => Ct
      blocks_injective := ?_
      ε := fun _ => 1 / 4
      ε_pos := fun _ => by norm_num
      collarLeft := fun _ =>
        ⟨fun p => ⟨((p.1 : X) : ℝ) + (p.2 : ℝ), by
            rw [hval_b p.1]
            linarith [p.2.2.1], by
            rw [hval_b p.1]
            linarith [p.2.2.2]⟩, by fun_prop⟩
      collarRight := fun _ =>
        ⟨fun p => ⟨((p.1 : X) : ℝ) - (p.2 : ℝ), by
            rw [hval_t p.1]
            linarith [p.2.2.2], by
            rw [hval_t p.1]
            linarith [p.2.2.1]⟩, by fun_prop⟩
      collarLeft_zero := ?_
      collarRight_zero := ?_
      collarLeft_injective := ?_
      collarRight_injective := ?_
      collarLeft_inward := ?_
      collarRight_inward := ?_
      collar_disjoint := ?_
      attaching := ?_ }
  · rintro ⟨i, b⟩ ⟨j, c⟩ h
    have hij : i = j := Subsingleton.elim i j
    subst hij
    cases b <;> cases c <;> dsimp only at h
    all_goals first
      | exact absurd h hne
      | exact absurd h hne.symm
      | exact Prod.ext rfl rfl
  · intro i z
    refine Subtype.ext ?_
    change ((z : X) : ℝ) + (0 : ℝ) = ((z : X) : ℝ)
    ring
  · intro i z
    refine Subtype.ext ?_
    change ((z : X) : ℝ) - (0 : ℝ) = ((z : X) : ℝ)
    ring
  · intro i p p' h
    have hz : p.1 = p'.1 := Subsingleton.elim p.1 p'.1
    have ht : ((p.2 : ℝ)) = ((p'.2 : ℝ)) := by
      have h' := congrArg (fun x : X => (x : ℝ)) h
      change ((p.1 : X) : ℝ) + (p.2 : ℝ) = ((p'.1 : X) : ℝ) + (p'.2 : ℝ) at h'
      rw [congrArg (fun z : ↥(BoundaryComponent.carrier Cb) => ((z : X) : ℝ)) hz] at h'
      linarith
    exact Prod.ext hz (Subtype.ext ht)
  · intro i p p' h
    have hz : p.1 = p'.1 := Subsingleton.elim p.1 p'.1
    have ht : ((p.2 : ℝ)) = ((p'.2 : ℝ)) := by
      have h' := congrArg (fun x : X => (x : ℝ)) h
      change ((p.1 : X) : ℝ) - (p.2 : ℝ) = ((p'.1 : X) : ℝ) - (p'.2 : ℝ) at h'
      rw [congrArg (fun z : ↥(BoundaryComponent.carrier Ct) => ((z : X) : ℝ)) hz] at h'
      linarith
    exact Prod.ext hz (Subtype.ext ht)
  · intro i z t ht hbp
    have hz : ((z : X) : ℝ) = 0 := hval_b z
    rcases hdich ⟨_, hbp⟩ with h | h
    · have h0 : ((z : X) : ℝ) + (t : ℝ) = 0 := by
        have h' := congrArg (fun x : X => (x : ℝ)) h
        dsimp only [g] at h'
        change ((z : X) : ℝ) + (t : ℝ) = 0 at h'
        exact h'
      linarith
    · have h1 : ((z : X) : ℝ) + (t : ℝ) = 1 := by
        have h' := congrArg (fun x : X => (x : ℝ)) h
        dsimp only [g] at h'
        change ((z : X) : ℝ) + (t : ℝ) = 1 at h'
        exact h'
      linarith [t.2.2]
  · intro i z t ht hbp
    have hz : ((z : X) : ℝ) = 1 := hval_t z
    rcases hdich ⟨_, hbp⟩ with h | h
    · have h0 : ((z : X) : ℝ) - (t : ℝ) = 0 := by
        have h' := congrArg (fun x : X => (x : ℝ)) h
        dsimp only [g] at h'
        change ((z : X) : ℝ) - (t : ℝ) = 0 at h'
        exact h'
      linarith [t.2.2]
    · have h1 : ((z : X) : ℝ) - (t : ℝ) = 1 := by
        have h' := congrArg (fun x : X => (x : ℝ)) h
        dsimp only [g] at h'
        change ((z : X) : ℝ) - (t : ℝ) = 1 at h'
        exact h'
      linarith
  · intro i
    rw [Set.disjoint_left]
    rintro x ⟨p, rfl⟩ ⟨q, hq⟩
    have hval : ((q.1 : X) : ℝ) - (q.2 : ℝ) = ((p.1 : X) : ℝ) + (p.2 : ℝ) := by
      have h' := congrArg (fun x : X => (x : ℝ)) hq
      change ((q.1 : X) : ℝ) - (q.2 : ℝ) = ((p.1 : X) : ℝ) + (p.2 : ℝ) at h'
      exact h'
    rw [hval_b p.1, hval_t q.1] at hval
    have h1 := p.2.2.2
    have h2 := q.2.2.2
    linarith
  · intro _
    exact
      { toFun := fun _ => ⟨Yt, BoundaryComponent.mk_mem_carrier Yt⟩
        invFun := fun _ => ⟨Yb, BoundaryComponent.mk_mem_carrier Yb⟩
        left_inv := fun z => Subsingleton.elim _ _
        right_inv := fun z => Subsingleton.elim _ _
        continuous_toFun := continuous_const
        continuous_invFun := continuous_const }

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
