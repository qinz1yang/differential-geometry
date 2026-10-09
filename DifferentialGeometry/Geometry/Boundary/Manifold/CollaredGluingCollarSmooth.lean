import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredGluingRegularity
import Mathlib.Geometry.Manifold.Instances.Icc

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
variable {ι : Type v} [Finite ι]

namespace CollaredGluing

def collarLeftExtend (G : CollaredGluing I X ι) (i : ι)
    (p : BoundaryManifold I X × Icc (0 : ℝ) (G.ε i)) : X :=
  by
    classical
    exact if h : (p.1 : X) ∈ (G.left i).carrier then
      (G.collarLeft i (⟨(p.1 : X), h⟩, p.2) : X)
    else (p.1 : X)

def collarRightExtend (G : CollaredGluing I X ι) (i : ι)
    (p : BoundaryManifold I X × Icc (0 : ℝ) (G.ε i)) : X :=
  by
    classical
    exact if h : (p.1 : X) ∈ (G.right i).carrier then
      (G.collarRight i (⟨(p.1 : X), h⟩, p.2) : X)
    else (p.1 : X)

theorem collarLeftExtend_apply_of_mem (G : CollaredGluing I X ι) (i : ι)
    {y : BoundaryManifold I X} {t : Icc (0 : ℝ) (G.ε i)}
    (h : (y : X) ∈ (G.left i).carrier) :
    G.collarLeftExtend i (y, t) = (G.collarLeft i (⟨(y : X), h⟩, t) : X) := by
  rw [collarLeftExtend]
  simp only [dite_eq_left h]

theorem collarLeftExtend_apply_of_notMem (G : CollaredGluing I X ι) (i : ι)
    {y : BoundaryManifold I X} {t : Icc (0 : ℝ) (G.ε i)}
    (h : (y : X) ∉ (G.left i).carrier) :
    G.collarLeftExtend i (y, t) = (y : X) := by
  rw [collarLeftExtend]
  simp only [dite_eq_right h]

theorem collarRightExtend_apply_of_mem (G : CollaredGluing I X ι) (i : ι)
    {y : BoundaryManifold I X} {t : Icc (0 : ℝ) (G.ε i)}
    (h : (y : X) ∈ (G.right i).carrier) :
    G.collarRightExtend i (y, t) = (G.collarRight i (⟨(y : X), h⟩, t) : X) := by
  rw [collarRightExtend]
  simp only [dite_eq_left h]

theorem collarRightExtend_apply_of_notMem (G : CollaredGluing I X ι) (i : ι)
    {y : BoundaryManifold I X} {t : Icc (0 : ℝ) (G.ε i)}
    (h : (y : X) ∉ (G.right i).carrier) :
    G.collarRightExtend i (y, t) = (y : X) := by
  rw [collarRightExtend]
  simp only [dite_eq_right h]

theorem collarLeftExtend_apply_zero (G : CollaredGluing I X ι) (i : ι)
    {y : BoundaryManifold I X} (h : (y : X) ∈ (G.left i).carrier) :
    G.collarLeftExtend i (y, ⟨0, le_rfl, (G.ε_pos i).le⟩) = (y : X) := by
  rw [collarLeftExtend_apply_of_mem G i h, G.collarLeft_zero]

theorem collarRightExtend_apply_zero (G : CollaredGluing I X ι) (i : ι)
    {y : BoundaryManifold I X} (h : (y : X) ∈ (G.right i).carrier) :
    G.collarRightExtend i (y, ⟨0, le_rfl, (G.ε_pos i).le⟩) = (y : X) := by
  rw [collarRightExtend_apply_of_mem G i h, G.collarRight_zero]

def CollarSmooth (G : CollaredGluing I X ι) [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ X] : Prop :=
  ∀ i, letI : Fact (0 < G.ε i) := ⟨G.ε_pos i⟩;
    ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ (G.collarLeftExtend i) ∧
      ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ (G.collarRightExtend i)

theorem CollarSmooth.collarLeft {G : CollaredGluing I X ι} [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ X] (h : G.CollarSmooth) (i : ι) :
    letI : Fact (0 < G.ε i) := ⟨G.ε_pos i⟩
    ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ (G.collarLeftExtend i) :=
  (h i).1

theorem CollarSmooth.collarRight {G : CollaredGluing I X ι} [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ X] (h : G.CollarSmooth) (i : ι) :
    letI : Fact (0 < G.ε i) := ⟨G.ε_pos i⟩
    ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ (G.collarRightExtend i) :=
  (h i).2

def collarLeftClamp (G : CollaredGluing I X ι) (i : ι) :
    BoundaryManifold I X × ℝ → X :=
  fun p => G.collarLeftExtend i (p.1, Set.projIcc (0 : ℝ) (G.ε i) (G.ε_pos i).le p.2)

def collarRightClamp (G : CollaredGluing I X ι) (i : ι) :
    BoundaryManifold I X × ℝ → X :=
  fun p => G.collarRightExtend i (p.1, Set.projIcc (0 : ℝ) (G.ε i) (G.ε_pos i).le p.2)

private theorem contMDiffOn_projIcc_prod_snd (G : CollaredGluing I X ι) (i : ι)
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ X] [hε : Fact (0 < G.ε i)] :
    ContMDiffOn (hI.boundaryI.prod 𝓘(ℝ)) (hI.boundaryI.prod (𝓡∂ 1)) ∞
      (fun p : BoundaryManifold I X × ℝ =>
        (p.1, Set.projIcc (0 : ℝ) (G.ε i) (G.ε_pos i).le p.2))
      (univ ×ˢ Icc (0 : ℝ) (G.ε i)) := by
  refine ContMDiffOn.prodMk ?_ ?_
  · intro p _
    exact (contMDiff_fst (I := hI.boundaryI) (J := 𝓘(ℝ)) (n := ∞) p).contMDiffWithinAt
  · intro p hp
    rw [Set.mem_prod] at hp
    have hproj : ContMDiffWithinAt 𝓘(ℝ) (𝓡∂ 1) ∞
        (Set.projIcc (0 : ℝ) (G.ε i) (G.ε_pos i).le) (Icc (0 : ℝ) (G.ε i)) p.2 :=
      contMDiffOn_projIcc p.2 hp.2
    exact hproj.comp p
      ((contMDiff_snd (I := hI.boundaryI) (J := 𝓘(ℝ)) (n := ∞) p).contMDiffWithinAt)
      (fun q hq => by rw [Set.mem_prod] at hq; exact hq.2)

theorem CollarSmooth.contMDiffOn_collarLeftClamp {G : CollaredGluing I X ι}
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ X] (h : G.CollarSmooth) (i : ι) :
    ContMDiffOn (hI.boundaryI.prod 𝓘(ℝ)) I ∞ (G.collarLeftClamp i)
      (univ ×ˢ Icc (0 : ℝ) (G.ε i)) := by
  have hε : Fact (0 < G.ε i) := ⟨G.ε_pos i⟩
  intro p hp
  have hc := (h i).1 (p.1, Set.projIcc (0 : ℝ) (G.ε i) (G.ε_pos i).le p.2)
  exact hc.contMDiffWithinAt.comp p
    (G.contMDiffOn_projIcc_prod_snd i p hp) (fun _ _ => mem_univ _)

theorem CollarSmooth.contMDiffOn_collarRightClamp {G : CollaredGluing I X ι}
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ X] (h : G.CollarSmooth) (i : ι) :
    ContMDiffOn (hI.boundaryI.prod 𝓘(ℝ)) I ∞ (G.collarRightClamp i)
      (univ ×ˢ Icc (0 : ℝ) (G.ε i)) := by
  have hε : Fact (0 < G.ε i) := ⟨G.ε_pos i⟩
  intro p hp
  have hc := (h i).2 (p.1, Set.projIcc (0 : ℝ) (G.ε i) (G.ε_pos i).le p.2)
  exact hc.contMDiffWithinAt.comp p
    (G.contMDiffOn_projIcc_prod_snd i p hp) (fun _ _ => mem_univ _)

end CollaredGluing

section UnitInterval

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

private abbrev unitIntervalGluingStrip : Type :=
  BoundaryManifold (𝓡∂ 1) (Icc (0 : ℝ) 1) ×
    Icc (0 : ℝ) (unitIntervalCollaredGluing.ε 0)

private theorem unitIntervalCollaredGluing_eps_le_one :
    unitIntervalCollaredGluing.ε 0 ≤ (1 : ℝ) := by
  rw [show unitIntervalCollaredGluing.ε 0 = (1 : ℝ) / 4 from rfl]
  norm_num

private theorem unitIntervalCollaredGluing_boundary_val
    (y : BoundaryManifold (𝓡∂ 1) (Icc (0 : ℝ) 1)) :
    (y : Icc (0 : ℝ) 1) = ⊥ ∨ (y : Icc (0 : ℝ) 1) = ⊤ := by
  have hy : (y : Icc (0 : ℝ) 1) ∈ ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) :=
    (boundary_Icc (x := (0 : ℝ)) (y := 1)) ▸ y.2
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy

private theorem unitIntervalCollaredGluing_carrier_left_val
    (z : ↥(BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0))) :
    (z : Icc (0 : ℝ) 1) = ⊥ := by
  have hz : (z : Icc (0 : ℝ) 1) ∈ (𝓡∂ 1).boundary (Icc (0 : ℝ) 1) :=
    BoundaryComponent.carrier_subset_boundary (unitIntervalCollaredGluing.left 0) z.2
  rw [boundary_Icc] at hz
  rcases hz with h | h
  · simpa only [Set.mem_singleton_iff] using h
  · exfalso
    have htop : (z : Icc (0 : ℝ) 1) = ⊤ := by simpa only [Set.mem_singleton_iff] using h
    have ht : (1 : ℝ) / 8 ∈ Icc (0 : ℝ) (unitIntervalCollaredGluing.ε 0) := by
      rw [show unitIntervalCollaredGluing.ε 0 = (1 : ℝ) / 4 from rfl]
      norm_num
    have hv := (unitIntervalCollaredGluing.collarLeft 0 (z, ⟨(1 : ℝ) / 8, ht⟩)).2.2
    have hval : ((unitIntervalCollaredGluing.collarLeft 0 (z, ⟨(1 : ℝ) / 8, ht⟩) :
        Icc (0 : ℝ) 1) : ℝ) = ((z : Icc (0 : ℝ) 1) : ℝ) + (1 : ℝ) / 8 := rfl
    rw [hval] at hv
    have hzval : ((z : Icc (0 : ℝ) 1) : ℝ) = 1 := by rw [htop]; rfl
    rw [hzval] at hv
    norm_num at hv

private theorem unitIntervalCollaredGluing_carrier_right_val
    (z : ↥(BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0))) :
    (z : Icc (0 : ℝ) 1) = ⊤ := by
  have hz : (z : Icc (0 : ℝ) 1) ∈ (𝓡∂ 1).boundary (Icc (0 : ℝ) 1) :=
    BoundaryComponent.carrier_subset_boundary (unitIntervalCollaredGluing.right 0) z.2
  rw [boundary_Icc] at hz
  rcases hz with h | h
  · exfalso
    have hbot : (z : Icc (0 : ℝ) 1) = ⊥ := by simpa only [Set.mem_singleton_iff] using h
    have ht : (1 : ℝ) / 8 ∈ Icc (0 : ℝ) (unitIntervalCollaredGluing.ε 0) := by
      rw [show unitIntervalCollaredGluing.ε 0 = (1 : ℝ) / 4 from rfl]
      norm_num
    have hv := (unitIntervalCollaredGluing.collarRight 0 (z, ⟨(1 : ℝ) / 8, ht⟩)).2.1
    have hval : ((unitIntervalCollaredGluing.collarRight 0 (z, ⟨(1 : ℝ) / 8, ht⟩) :
        Icc (0 : ℝ) 1) : ℝ) = ((z : Icc (0 : ℝ) 1) : ℝ) - (1 : ℝ) / 8 := rfl
    rw [hval] at hv
    have hzval : ((z : Icc (0 : ℝ) 1) : ℝ) = 0 := by rw [hbot]; rfl
    rw [hzval] at hv
    norm_num at hv
  · simpa only [Set.mem_singleton_iff] using h

private theorem unitIntervalCollaredGluing_mem_carrier_left :
    (⊥ : Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0) := by
  obtain ⟨y, hy⟩ := BoundaryComponent.carrier_nonempty (unitIntervalCollaredGluing.left 0)
  have h := unitIntervalCollaredGluing_carrier_left_val ⟨y, hy⟩
  rw [← h]
  exact hy

private theorem unitIntervalCollaredGluing_mem_carrier_right :
    (⊤ : Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0) := by
  obtain ⟨y, hy⟩ := BoundaryComponent.carrier_nonempty (unitIntervalCollaredGluing.right 0)
  have h := unitIntervalCollaredGluing_carrier_right_val ⟨y, hy⟩
  rw [← h]
  exact hy

private theorem unitIntervalCollaredGluing_isOpen_carrier_left :
    IsOpen {q : unitIntervalGluingStrip |
      (q.1 : Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0)} := by
  have hset : {q : unitIntervalGluingStrip |
        (q.1 : Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0)}
      = {q | ((q.1 : Icc (0 : ℝ) 1) : ℝ) < 1 / 2} := by
    ext q
    constructor
    · intro hq
      change ((q.1 : Icc (0 : ℝ) 1) : ℝ) < 1 / 2
      change (q.1 : Icc (0 : ℝ) 1) ∈
        BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0) at hq
      rw [unitIntervalCollaredGluing_carrier_left_val ⟨(q.1 : Icc (0 : ℝ) 1), hq⟩]
      norm_num
    · intro hq
      change (q.1 : Icc (0 : ℝ) 1) ∈
        BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0)
      change ((q.1 : Icc (0 : ℝ) 1) : ℝ) < 1 / 2 at hq
      rcases unitIntervalCollaredGluing_boundary_val q.1 with h | h
      · rw [h]
        exact unitIntervalCollaredGluing_mem_carrier_left
      · rw [h] at hq
        norm_num at hq
  rw [hset]
  exact isOpen_lt (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
    continuous_const

private theorem unitIntervalCollaredGluing_isOpen_carrier_left_compl :
    IsOpen {q : unitIntervalGluingStrip |
      (q.1 : Icc (0 : ℝ) 1) ∉ BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0)} := by
  have hset : {q : unitIntervalGluingStrip |
        (q.1 : Icc (0 : ℝ) 1) ∉ BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0)}
      = {q | 1 / 2 < ((q.1 : Icc (0 : ℝ) 1) : ℝ)} := by
    ext q
    constructor
    · intro hq
      change 1 / 2 < ((q.1 : Icc (0 : ℝ) 1) : ℝ)
      change (q.1 : Icc (0 : ℝ) 1) ∉
        BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0) at hq
      rcases unitIntervalCollaredGluing_boundary_val q.1 with h | h
      · exact absurd (h ▸ unitIntervalCollaredGluing_mem_carrier_left) hq
      · rw [h]
        norm_num
    · intro hq
      change (q.1 : Icc (0 : ℝ) 1) ∉
        BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0)
      change 1 / 2 < ((q.1 : Icc (0 : ℝ) 1) : ℝ) at hq
      intro hmem
      have h := unitIntervalCollaredGluing_carrier_left_val ⟨(q.1 : Icc (0 : ℝ) 1), hmem⟩
      rw [h] at hq
      norm_num at hq
  rw [hset]
  exact isOpen_lt continuous_const
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))

private theorem unitIntervalCollaredGluing_isOpen_carrier_right :
    IsOpen {q : unitIntervalGluingStrip |
      (q.1 : Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0)} := by
  have hset : {q : unitIntervalGluingStrip |
        (q.1 : Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0)}
      = {q | 1 / 2 < ((q.1 : Icc (0 : ℝ) 1) : ℝ)} := by
    ext q
    constructor
    · intro hq
      change 1 / 2 < ((q.1 : Icc (0 : ℝ) 1) : ℝ)
      change (q.1 : Icc (0 : ℝ) 1) ∈
        BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0) at hq
      rw [unitIntervalCollaredGluing_carrier_right_val ⟨(q.1 : Icc (0 : ℝ) 1), hq⟩]
      norm_num
    · intro hq
      change (q.1 : Icc (0 : ℝ) 1) ∈
        BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0)
      change 1 / 2 < ((q.1 : Icc (0 : ℝ) 1) : ℝ) at hq
      rcases unitIntervalCollaredGluing_boundary_val q.1 with h | h
      · rw [h] at hq
        norm_num at hq
      · rw [h]
        exact unitIntervalCollaredGluing_mem_carrier_right
  rw [hset]
  exact isOpen_lt continuous_const
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))

private theorem unitIntervalCollaredGluing_isOpen_carrier_right_compl :
    IsOpen {q : unitIntervalGluingStrip |
      (q.1 : Icc (0 : ℝ) 1) ∉ BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0)} := by
  have hset : {q : unitIntervalGluingStrip |
        (q.1 : Icc (0 : ℝ) 1) ∉ BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0)}
      = {q | ((q.1 : Icc (0 : ℝ) 1) : ℝ) < 1 / 2} := by
    ext q
    constructor
    · intro hq
      change ((q.1 : Icc (0 : ℝ) 1) : ℝ) < 1 / 2
      change (q.1 : Icc (0 : ℝ) 1) ∉
        BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0) at hq
      rcases unitIntervalCollaredGluing_boundary_val q.1 with h | h
      · rw [h]
        norm_num
      · exact absurd (h ▸ unitIntervalCollaredGluing_mem_carrier_right) hq
    · intro hq
      change (q.1 : Icc (0 : ℝ) 1) ∉
        BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0)
      change ((q.1 : Icc (0 : ℝ) 1) : ℝ) < 1 / 2 at hq
      intro hmem
      have h := unitIntervalCollaredGluing_carrier_right_val ⟨(q.1 : Icc (0 : ℝ) 1), hmem⟩
      rw [h] at hq
      norm_num at hq
  rw [hset]
  exact isOpen_lt (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
    continuous_const

private theorem unitIntervalCollaredGluing_val_le_one (q : unitIntervalGluingStrip) :
    (q.2 : ℝ) ≤ 1 :=
  le_trans q.2.2.2 unitIntervalCollaredGluing_eps_le_one

private theorem unitIntervalCollaredGluing_one_sub_nonneg (q : unitIntervalGluingStrip) :
    0 ≤ 1 - (q.2 : ℝ) :=
  sub_nonneg.mpr (unitIntervalCollaredGluing_val_le_one q)

private theorem unitIntervalCollaredGluing_one_sub_le_one (q : unitIntervalGluingStrip) :
    1 - (q.2 : ℝ) ≤ 1 := by
  have h := q.2.2.1
  linarith

theorem unitIntervalCollaredGluing_collarSmooth :
    unitIntervalCollaredGluing.CollarSmooth := by
  intro i
  rw [Subsingleton.elim i 0]
  have hε : Fact ((0 : ℝ) < unitIntervalCollaredGluing.ε 0) :=
    ⟨unitIntervalCollaredGluing.ε_pos 0⟩
  constructor
  · classical
    let S : Set unitIntervalGluingStrip :=
      {q | (q.1 : Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0)}
    let A : unitIntervalGluingStrip → Icc (0 : ℝ) 1 :=
      fun q => ⟨(q.2 : ℝ), q.2.2.1, unitIntervalCollaredGluing_val_le_one q⟩
    let B : unitIntervalGluingStrip → Icc (0 : ℝ) 1 := fun _ => ⊤
    have hS : IsOpen S := unitIntervalCollaredGluing_isOpen_carrier_left
    have hSc : IsOpen Sᶜ := unitIntervalCollaredGluing_isOpen_carrier_left_compl
    have hpiece : unitIntervalCollaredGluing.collarLeftExtend 0 = Set.piecewise S A B := by
      funext q
      classical
      by_cases hq : (q.1 : Icc (0 : ℝ) 1) ∈
          BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0)
      · rw [CollaredGluing.collarLeftExtend_apply_of_mem _ _ hq,
          Set.piecewise_eq_of_mem (s := S) (f := A) (g := B) hq]
        refine Subtype.ext ?_
        have hval : ((unitIntervalCollaredGluing.collarLeft 0
            (⟨(q.1 : Icc (0 : ℝ) 1), hq⟩, q.2) : Icc (0 : ℝ) 1) : ℝ)
            = ((⟨(q.1 : Icc (0 : ℝ) 1), hq⟩ : ↥(BoundaryComponent.carrier
                (unitIntervalCollaredGluing.left 0))) : Icc (0 : ℝ) 1) + (q.2 : ℝ) := rfl
        have hbot : ((⊥ : Icc (0 : ℝ) 1) : ℝ) = 0 := rfl
        rw [hval, unitIntervalCollaredGluing_carrier_left_val, hbot, zero_add]
      · rw [CollaredGluing.collarLeftExtend_apply_of_notMem _ _ hq,
          Set.piecewise_eq_of_notMem (s := S) (f := A) (g := B) hq]
        rcases unitIntervalCollaredGluing_boundary_val q.1 with h | h
        · exact absurd (h ▸ unitIntervalCollaredGluing_mem_carrier_left) hq
        · exact h
    rw [hpiece]
    refine ContMDiff.piecewise ?_ ?_ ?_
    · rw [contMDiff_iff_comp_subtypeVal_Icc]
      exact ⟨by fun_prop,
        (contMDiff_subtypeVal_Icc.comp contMDiff_snd).congr (fun q => rfl)⟩
    · exact contMDiff_const
    · intro x hx
      rw [isClopen_iff_frontier_eq_empty.mp ⟨by simpa using hSc.isClosed_compl, hS⟩] at hx
      exact absurd hx (Set.notMem_empty x)
  · classical
    let S : Set unitIntervalGluingStrip :=
      {q | (q.1 : Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0)}
    let A : unitIntervalGluingStrip → Icc (0 : ℝ) 1 :=
      fun q => ⟨1 - (q.2 : ℝ), unitIntervalCollaredGluing_one_sub_nonneg q,
        unitIntervalCollaredGluing_one_sub_le_one q⟩
    let B : unitIntervalGluingStrip → Icc (0 : ℝ) 1 := fun _ => ⊥
    have hS : IsOpen S := unitIntervalCollaredGluing_isOpen_carrier_right
    have hSc : IsOpen Sᶜ := unitIntervalCollaredGluing_isOpen_carrier_right_compl
    have hpiece : unitIntervalCollaredGluing.collarRightExtend 0 = Set.piecewise S A B := by
      funext q
      classical
      by_cases hq : (q.1 : Icc (0 : ℝ) 1) ∈
          BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0)
      · rw [CollaredGluing.collarRightExtend_apply_of_mem _ _ hq,
          Set.piecewise_eq_of_mem (s := S) (f := A) (g := B) hq]
        refine Subtype.ext ?_
        have hval : ((unitIntervalCollaredGluing.collarRight 0
            (⟨(q.1 : Icc (0 : ℝ) 1), hq⟩, q.2) : Icc (0 : ℝ) 1) : ℝ)
            = ((⟨(q.1 : Icc (0 : ℝ) 1), hq⟩ : ↥(BoundaryComponent.carrier
                (unitIntervalCollaredGluing.right 0))) : Icc (0 : ℝ) 1) - (q.2 : ℝ) := rfl
        have htop : ((⊤ : Icc (0 : ℝ) 1) : ℝ) = 1 := rfl
        rw [hval, unitIntervalCollaredGluing_carrier_right_val, htop]
      · rw [CollaredGluing.collarRightExtend_apply_of_notMem _ _ hq,
          Set.piecewise_eq_of_notMem (s := S) (f := A) (g := B) hq]
        rcases unitIntervalCollaredGluing_boundary_val q.1 with h | h
        · exact h
        · exact absurd (h ▸ unitIntervalCollaredGluing_mem_carrier_right) hq
    rw [hpiece]
    refine ContMDiff.piecewise ?_ ?_ ?_
    · rw [contMDiff_iff_comp_subtypeVal_Icc]
      exact ⟨by fun_prop,
        (contMDiff_const.sub (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).congr
          (fun q => rfl)⟩
    · exact contMDiff_const
    · intro x hx
      rw [isClopen_iff_frontier_eq_empty.mp ⟨by simpa using hSc.isClosed_compl, hS⟩] at hx
      exact absurd hx (Set.notMem_empty x)

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
