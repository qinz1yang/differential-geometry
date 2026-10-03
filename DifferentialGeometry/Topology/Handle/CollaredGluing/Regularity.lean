import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Geometry.Boundary.Manifold.BinaryGluing

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Boundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
variable {ι : Type v} [Finite ι]

private def icoToIcc {a b : ℝ} (t : Ico a b) : Icc a b :=
  ⟨(t : ℝ), t.2.1, le_of_lt t.2.2⟩

namespace CollaredGluing

def collarLeftOpen (G : CollaredGluing I X ι) (i : ι) :
    ↥(G.left i).carrier × Ico (0 : ℝ) (G.ε i) → X :=
  fun p => G.collarLeft i (p.1, icoToIcc p.2)

def collarRightOpen (G : CollaredGluing I X ι) (i : ι) :
    ↥(G.right i).carrier × Ico (0 : ℝ) (G.ε i) → X :=
  fun p => G.collarRight i (p.1, icoToIcc p.2)

def CollarOpenEmbedding (G : CollaredGluing I X ι) : Prop :=
  (∀ i, IsOpenEmbedding (G.collarLeftOpen i)) ∧
    (∀ i, IsOpenEmbedding (G.collarRightOpen i))

def attachingExtend (G : CollaredGluing I X ι)
    (i : ι) (y : BoundaryManifold I X) : BoundaryManifold I X := by
  classical
  refine ⟨if h : (y : X) ∈ (G.left i).carrier then
    ((G.attaching i) ⟨(y : X), h⟩ : X) else (y : X), ?_⟩
  split_ifs with h
  · exact (G.right i).carrier_subset_boundary ((G.attaching i) ⟨(y : X), h⟩).2
  · exact y.2

def AttachingSmooth (G : CollaredGluing I X ι) [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ X] : Prop :=
  ∀ i, ContMDiff hI.boundaryI hI.boundaryI ∞ (G.attachingExtend i)

def IsSmoothGluing (G : CollaredGluing I X ι) [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ X] : Prop :=
  G.CollarOpenEmbedding ∧ G.AttachingSmooth

theorem collarLeftOpen_apply (G : CollaredGluing I X ι) (i : ι)
    (p : ↥(G.left i).carrier × Ico (0 : ℝ) (G.ε i)) :
    G.collarLeftOpen i p = G.collarLeft i (p.1, icoToIcc p.2) := rfl

theorem collarRightOpen_apply (G : CollaredGluing I X ι) (i : ι)
    (p : ↥(G.right i).carrier × Ico (0 : ℝ) (G.ε i)) :
    G.collarRightOpen i p = G.collarRight i (p.1, icoToIcc p.2) := rfl

theorem isOpen_range_collarLeftOpen (G : CollaredGluing I X ι)
    (h : G.CollarOpenEmbedding) (i : ι) : IsOpen (range (G.collarLeftOpen i)) :=
  (h.1 i).isOpen_range

theorem isOpen_range_collarRightOpen (G : CollaredGluing I X ι)
    (h : G.CollarOpenEmbedding) (i : ι) : IsOpen (range (G.collarRightOpen i)) :=
  (h.2 i).isOpen_range

theorem attachingExtend_apply_of_mem (G : CollaredGluing I X ι) {i : ι}
    {y : BoundaryManifold I X} (h : (y : X) ∈ (G.left i).carrier) :
    (G.attachingExtend i y : X) = ((G.attaching i) ⟨(y : X), h⟩ : X) := by
  rw [attachingExtend]
  simp only [dite_eq_left h]

theorem attachingExtend_apply_of_notMem (G : CollaredGluing I X ι) {i : ι}
    {y : BoundaryManifold I X} (h : (y : X) ∉ (G.left i).carrier) :
    (G.attachingExtend i y : X) = (y : X) := by
  rw [attachingExtend]
  simp only [dite_eq_right h]

end CollaredGluing

section UnitInterval

private theorem isOpenEmbedding_snd_icoToIcc {α : Type*} [TopologicalSpace α]
    (hs : Subsingleton α) {b c : ℝ} (hbc : b ≤ c) :
    IsOpenEmbedding (fun p : α × ↥(Ico (0 : ℝ) b) =>
      (⟨(p.2 : ℝ), p.2.2.1, le_trans (le_of_lt p.2.2.2) hbc⟩ : ↥(Icc (0 : ℝ) c))) := by
  have hg : IsOpenEmbedding (fun p : α × ↥(Ico (0 : ℝ) b) => p.2) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_snd
      (fun p q h => Prod.ext (hs.elim _ _) h) isOpenMap_snd
  let T : Set ↥(Icc (0 : ℝ) c) := {x | (x : ℝ) < b}
  have hT : IsOpen T := isOpen_Iio.preimage continuous_subtype_val
  let φ : ↥(Ico (0 : ℝ) b) ≃ₜ ↥T :=
    { toFun := fun t => ⟨⟨(t : ℝ), t.2.1, le_trans (le_of_lt t.2.2) hbc⟩, t.2.2⟩
      invFun := fun x => ⟨(x.1 : ℝ), x.1.2.1, x.2⟩
      left_inv := fun t => Subtype.ext rfl
      right_inv := fun x => Subtype.ext (Subtype.ext rfl)
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ (fun t => t.2.2)
        exact Continuous.subtype_mk continuous_subtype_val
          (fun t => ⟨t.2.1, le_trans (le_of_lt t.2.2) hbc⟩)
      continuous_invFun :=
        Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
          (fun x => ⟨x.1.2.1, x.2⟩) }
  have hincl : IsOpenEmbedding (Subtype.val : ↥T → ↥(Icc (0 : ℝ) c)) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_subtype_val
      Subtype.val_injective hT.isOpenMap_subtype_val
  have hcomp := hincl.comp φ.isOpenEmbedding
  have hfun : (Subtype.val ∘ ⇑φ) = (fun p : ↥(Ico (0 : ℝ) b) =>
      (⟨(p : ℝ), p.2.1, le_trans (le_of_lt p.2.2) hbc⟩ : ↥(Icc (0 : ℝ) c))) := by
    funext p
    rfl
  rw [hfun] at hcomp
  exact hcomp.comp hg


private theorem isOpenEmbedding_snd_icoReflect {α : Type*} [TopologicalSpace α]
    (hs : Subsingleton α) {b : ℝ} (hb : b ≤ 1) :
    IsOpenEmbedding (fun p : α × ↥(Ico (0 : ℝ) b) =>
      (⟨1 - (p.2 : ℝ), by linarith [p.2.2.2, hb], by linarith [p.2.2.1]⟩ : ↥(Icc (0 : ℝ) 1))) := by
  have hg : IsOpenEmbedding (fun p : α × ↥(Ico (0 : ℝ) b) => p.2) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_snd
      (fun p q h => Prod.ext (hs.elim _ _) h) isOpenMap_snd
  let T : Set ↥(Icc (0 : ℝ) 1) := {x | 1 - b < (x : ℝ)}
  have hT : IsOpen T := isOpen_Ioi.preimage continuous_subtype_val
  let ψ : ↥(Ico (0 : ℝ) b) ≃ₜ ↥T :=
    { toFun := fun t => ⟨⟨1 - (t : ℝ), by linarith [t.2.2, hb], by linarith [t.2.1]⟩,
        by
          change 1 - b < 1 - (t : ℝ)
          linarith [t.2.2]⟩
      invFun := fun x => ⟨1 - (x.1 : ℝ), by linarith [x.1.2.2],
        by
          have hx : 1 - b < (x.1 : ℝ) := x.2
          change 1 - (x.1 : ℝ) < b
          linarith [hx]⟩
      left_inv := fun t => by
        refine Subtype.ext ?_
        simp only
        ring
      right_inv := fun x => by
        refine Subtype.ext (Subtype.ext ?_)
        simp only
        ring
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ (fun t => by
          change 1 - b < 1 - (t : ℝ)
          linarith [t.2.2])
        refine Continuous.subtype_mk ?_ (fun t => ⟨by linarith [t.2.2, hb],
          by linarith [t.2.1]⟩)
        exact continuous_const.sub continuous_subtype_val
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ (fun x => ⟨by linarith [x.1.2.2],
          by
          have hx : 1 - b < (x.1 : ℝ) := x.2
          change 1 - (x.1 : ℝ) < b
          linarith [hx]⟩)
        exact continuous_const.sub (continuous_subtype_val.comp continuous_subtype_val) }
  have hincl : IsOpenEmbedding (Subtype.val : ↥T → ↥(Icc (0 : ℝ) 1)) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_subtype_val
      Subtype.val_injective hT.isOpenMap_subtype_val
  have hcomp := hincl.comp ψ.isOpenEmbedding
  have hfun : (Subtype.val ∘ ⇑ψ) = (fun p : ↥(Ico (0 : ℝ) b) =>
      (⟨1 - (p : ℝ), by linarith [p.2.2, hb], by linarith [p.2.1]⟩ : ↥(Icc (0 : ℝ) 1))) := by
    funext p
    rfl
  rw [hfun] at hcomp
  exact hcomp.comp hg


private theorem val_eq_bot (z : ↥(unitIntervalCollaredGluing.left 0).carrier) :
    (z : Icc (0:ℝ) 1) = ⊥ := by
  have hb : (z : Icc (0:ℝ) 1) ∈ (𝓡∂ 1).boundary (Icc (0:ℝ) 1) :=
    BoundaryComponent.carrier_subset_boundary _ z.2
  rw [boundary_Icc] at hb
  rcases hb with h | h
  · simpa only [Set.mem_singleton_iff] using h
  · exfalso
    have htop : (z : Icc (0:ℝ) 1) = ⊤ := by simpa only [Set.mem_singleton_iff] using h
    have heps : unitIntervalCollaredGluing.ε 0 = (1:ℝ)/4 := rfl
    have ht : (1:ℝ)/8 ∈ Icc (0:ℝ) (unitIntervalCollaredGluing.ε 0) := by
      rw [heps]; norm_num
    have hv := (unitIntervalCollaredGluing.collarLeft 0 (z, ⟨(1:ℝ)/8, ht⟩)).2.2
    have hval : ((unitIntervalCollaredGluing.collarLeft 0 (z, ⟨(1:ℝ)/8, ht⟩) : Icc (0:ℝ) 1) : ℝ)
        = ((z : Icc (0:ℝ) 1) : ℝ) + (1:ℝ)/8 := rfl
    rw [hval] at hv
    have hzval : ((z : Icc (0:ℝ) 1) : ℝ) = 1 := by rw [htop]; rfl
    rw [hzval] at hv
    norm_num at hv

private theorem val_eq_top (z : ↥(unitIntervalCollaredGluing.right 0).carrier) :
    (z : Icc (0:ℝ) 1) = ⊤ := by
  have hb : (z : Icc (0:ℝ) 1) ∈ (𝓡∂ 1).boundary (Icc (0:ℝ) 1) :=
    BoundaryComponent.carrier_subset_boundary _ z.2
  rw [boundary_Icc] at hb
  rcases hb with h | h
  · exfalso
    have hbot : (z : Icc (0:ℝ) 1) = ⊥ := by simpa only [Set.mem_singleton_iff] using h
    have heps : unitIntervalCollaredGluing.ε 0 = (1:ℝ)/4 := rfl
    have ht : (1:ℝ)/8 ∈ Icc (0:ℝ) (unitIntervalCollaredGluing.ε 0) := by
      rw [heps]; norm_num
    have hv := (unitIntervalCollaredGluing.collarRight 0 (z, ⟨(1:ℝ)/8, ht⟩)).2.1
    have hval : ((unitIntervalCollaredGluing.collarRight 0 (z, ⟨(1:ℝ)/8, ht⟩) : Icc (0:ℝ) 1) : ℝ)
        = ((z : Icc (0:ℝ) 1) : ℝ) - (1:ℝ)/8 := rfl
    rw [hval] at hv
    have hzval : ((z : Icc (0:ℝ) 1) : ℝ) = 0 := by rw [hbot]; rfl
    rw [hzval] at hv
    norm_num at hv
  · simpa only [Set.mem_singleton_iff] using h

private theorem eps_le_one : unitIntervalCollaredGluing.ε 0 ≤ (1:ℝ) := by
  have heps : unitIntervalCollaredGluing.ε 0 = (1:ℝ)/4 := rfl
  rw [heps]
  norm_num

private theorem collarLeftOpen_unitInterval :
    IsOpenEmbedding (unitIntervalCollaredGluing.collarLeftOpen 0) := by
  have hs : Subsingleton ↥(unitIntervalCollaredGluing.left 0).carrier :=
    ⟨fun a b => Subtype.ext (by rw [val_eq_bot a, val_eq_bot b])⟩
  have hfun : (fun p : ↥(unitIntervalCollaredGluing.left 0).carrier ×
        ↥(Ico (0:ℝ) (unitIntervalCollaredGluing.ε 0)) =>
      (⟨(p.2 : ℝ), p.2.2.1, le_trans (le_of_lt p.2.2.2) eps_le_one⟩ : Icc (0:ℝ) 1))
      = unitIntervalCollaredGluing.collarLeftOpen 0 := by
    funext p
    refine Subtype.ext ?_
    rw [CollaredGluing.collarLeftOpen]
    change (p.2 : ℝ)
      = ((unitIntervalCollaredGluing.collarLeft 0 (p.1, icoToIcc p.2) : Icc (0:ℝ) 1) : ℝ)
    have hz : ((p.1 : Icc (0:ℝ) 1) : ℝ) = 0 := by rw [val_eq_bot p.1]; rfl
    have hval : ((unitIntervalCollaredGluing.collarLeft 0 (p.1, icoToIcc p.2) :
        Icc (0:ℝ) 1) : ℝ) = ((p.1 : Icc (0:ℝ) 1) : ℝ) + (p.2 : ℝ) := rfl
    rw [hval, hz, zero_add]
  exact hfun ▸ isOpenEmbedding_snd_icoToIcc (α := ↥(unitIntervalCollaredGluing.left 0).carrier)
    hs eps_le_one

private theorem collarRightOpen_unitInterval :
    IsOpenEmbedding (unitIntervalCollaredGluing.collarRightOpen 0) := by
  have hs : Subsingleton ↥(unitIntervalCollaredGluing.right 0).carrier :=
    ⟨fun a b => Subtype.ext (by rw [val_eq_top a, val_eq_top b])⟩
  have hfun : (fun p : ↥(unitIntervalCollaredGluing.right 0).carrier ×
        ↥(Ico (0:ℝ) (unitIntervalCollaredGluing.ε 0)) =>
      (⟨1 - (p.2 : ℝ), by linarith [p.2.2.2, eps_le_one], by linarith [p.2.2.1]⟩ :
        Icc (0:ℝ) 1))
      = unitIntervalCollaredGluing.collarRightOpen 0 := by
    funext p
    refine Subtype.ext ?_
    rw [CollaredGluing.collarRightOpen]
    change 1 - (p.2 : ℝ)
      = ((unitIntervalCollaredGluing.collarRight 0 (p.1, icoToIcc p.2) : Icc (0:ℝ) 1) : ℝ)
    have hz : ((p.1 : Icc (0:ℝ) 1) : ℝ) = 1 := by rw [val_eq_top p.1]; rfl
    have hval : ((unitIntervalCollaredGluing.collarRight 0 (p.1, icoToIcc p.2) :
        Icc (0:ℝ) 1) : ℝ) = ((p.1 : Icc (0:ℝ) 1) : ℝ) - (p.2 : ℝ) := rfl
    rw [hval, hz]
  exact hfun ▸ isOpenEmbedding_snd_icoReflect (α := ↥(unitIntervalCollaredGluing.right 0).carrier)
    hs eps_le_one

private theorem carrier_left_singleton :
    BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0) = {⊥} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := BoundaryComponent.carrier_nonempty (unitIntervalCollaredGluing.left 0)
    rw [← val_eq_bot ⟨x, hx⟩]
    exact hx
  · intro y hy
    exact val_eq_bot ⟨y, hy⟩

private theorem carrier_right_singleton :
    BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0) = {⊤} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := BoundaryComponent.carrier_nonempty (unitIntervalCollaredGluing.right 0)
    rw [← val_eq_top ⟨x, hx⟩]
    exact hx
  · intro y hy
    exact val_eq_top ⟨y, hy⟩

theorem unitIntervalCollaredGluing_collarOpenEmbedding :
    unitIntervalCollaredGluing.CollarOpenEmbedding := by
  constructor
  · intro i
    rw [Subsingleton.elim i 0]
    exact collarLeftOpen_unitInterval
  · intro i
    rw [Subsingleton.elim i 0]
    exact collarRightOpen_unitInterval

theorem unitIntervalCollaredGluing_attachingSmooth :
    unitIntervalCollaredGluing.AttachingSmooth := by
  have hfact : Fact ((0:ℝ) < 1) := ⟨by norm_num⟩
  intro i
  rw [Subsingleton.elim i 0]
  have htop : (⊤ : Icc (0:ℝ) 1) ∈ (𝓡∂ 1).boundary (Icc (0:ℝ) 1) :=
    @Icc_isBoundaryPoint_top (0:ℝ) (1:ℝ) hfact
  have hconst : unitIntervalCollaredGluing.attachingExtend 0
      = fun _ : BoundaryManifold (𝓡∂ 1) (Icc (0:ℝ) 1) =>
        (⟨⊤, htop⟩ : BoundaryManifold (𝓡∂ 1) (Icc (0:ℝ) 1)) := by
    funext y
    have hy : (y : Icc (0:ℝ) 1) ∈ ({⊥, ⊤} : Set (Icc (0:ℝ) 1)) :=
      (boundary_Icc (x := 0) (y := 1)) ▸ y.2
    by_cases h : (y : Icc (0:ℝ) 1) ∈ (unitIntervalCollaredGluing.left 0).carrier
    · have hmem : ((unitIntervalCollaredGluing.attaching 0
            ⟨(y : Icc (0:ℝ) 1), h⟩ : ↥(unitIntervalCollaredGluing.right 0).carrier) :
            Icc (0:ℝ) 1) ∈ ({⊤} : Set (Icc (0:ℝ) 1)) := by
        rw [← carrier_right_singleton]
        exact (unitIntervalCollaredGluing.attaching 0 ⟨(y : Icc (0:ℝ) 1), h⟩).2
      rw [CollaredGluing.attachingExtend]
      simp only [dite_eq_left h]
      exact Subtype.ext (by simpa only [Set.mem_singleton_iff] using hmem)
    · rw [CollaredGluing.attachingExtend]
      simp only [dite_eq_right h]
      rcases hy with hy | hy
      · rw [carrier_left_singleton, Set.mem_singleton_iff] at h
        exact absurd hy h
      · exact Subtype.ext (by simpa only [Set.mem_singleton_iff] using hy)
  rw [hconst]
  exact contMDiff_const

theorem unitIntervalCollaredGluing_isSmoothGluing :
    unitIntervalCollaredGluing.IsSmoothGluing :=
  ⟨unitIntervalCollaredGluing_collarOpenEmbedding, unitIntervalCollaredGluing_attachingSmooth⟩

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
