import Mathlib.Analysis.Convex.StdSimplex

noncomputable section

namespace DifferentialGeometry.Simplex

variable {ι : Type*} [Fintype ι]

def supportFace (s : Finset ι) : Set (stdSimplex ℝ ι) :=
  {p | ∀ i, i ∉ s → p i = 0}

@[simp]
theorem mem_supportFace (s : Finset ι) (p : stdSimplex ℝ ι) :
    p ∈ supportFace s ↔ ∀ i, i ∉ s → p i = 0 := Iff.rfl

theorem isClosed_supportFace (s : Finset ι) : IsClosed (supportFace s) := by
  have h : supportFace s = ⋂ (i : ι) (_ : i ∉ s), {p : stdSimplex ℝ ι | p i = 0} := by
    ext p
    simp [supportFace]
  rw [h]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
    isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const

theorem supportFace_mono {s t : Finset ι} (h : s ⊆ t) : supportFace s ⊆ supportFace t :=
  fun _ hp i hi ↦ hp i (fun his ↦ hi (h his))

@[simp]
theorem supportFace_inter [DecidableEq ι] (s t : Finset ι) :
    supportFace (s ∩ t) = supportFace s ∩ supportFace t := by
  classical
  ext p
  constructor
  · intro hp
    exact ⟨fun i hi ↦ hp i (by simp [hi]), fun i hi ↦ hp i (by simp [hi])⟩
  · rintro ⟨hs, ht⟩ i hi
    by_cases his : i ∈ s
    · exact ht i (fun hit ↦ hi (Finset.mem_inter.mpr ⟨his, hit⟩))
    · exact hs i his

theorem map_subtype_val_apply_mem (s : Finset ι) (p : stdSimplex ℝ s) (i : s) :
    (stdSimplex.map Subtype.val p) i.val = p i := by
  classical
  change FunOnFinite.linearMap ℝ ℝ Subtype.val p i.val = p i
  rw [FunOnFinite.linearMap_apply_apply]
  simp only [Subtype.val_inj, Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]

theorem map_subtype_val_apply_notMem (s : Finset ι) (p : stdSimplex ℝ s) (i : ι)
    (hi : i ∉ s) : (stdSimplex.map Subtype.val p) i = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ Subtype.val p i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact (hi ((Finset.mem_filter.mp hj).2 ▸ j.property)).elim

def supportFaceInsert (s : Finset ι) : C(stdSimplex ℝ s, supportFace s) :=
  ⟨fun p ↦ ⟨stdSimplex.map Subtype.val p, map_subtype_val_apply_notMem s p⟩,
    (stdSimplex.continuous_map Subtype.val).subtype_mk _⟩

def supportFaceRestrict (s : Finset ι) : C(supportFace s, stdSimplex ℝ s) :=
  ⟨fun p ↦ ⟨fun i ↦ p.val i.val, ⟨fun i ↦ p.val.property.1 _, by
      classical
      rw [Finset.sum_coe_sort]
      exact (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi ↦ p.property i hi)).trans
        p.val.property.2⟩⟩,
    (continuous_pi fun i ↦ (continuous_apply i.val).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

@[simp]
theorem supportFaceRestrict_supportFaceInsert (s : Finset ι) (p : stdSimplex ℝ s) :
    supportFaceRestrict s (supportFaceInsert s p) = p := by
  apply Subtype.ext
  funext i
  exact map_subtype_val_apply_mem s p i

@[simp]
theorem supportFaceInsert_supportFaceRestrict (s : Finset ι) (p : supportFace s) :
    supportFaceInsert s (supportFaceRestrict s p) = p := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ s
  · exact map_subtype_val_apply_mem s (supportFaceRestrict s p) ⟨i, hi⟩
  · exact (map_subtype_val_apply_notMem s _ i hi).trans (p.property i hi).symm

def supportFaceHomeomorph (s : Finset ι) : stdSimplex ℝ s ≃ₜ supportFace s where
  toFun := supportFaceInsert s
  invFun := supportFaceRestrict s
  left_inv := supportFaceRestrict_supportFaceInsert s
  right_inv := supportFaceInsert_supportFaceRestrict s
  continuous_toFun := (supportFaceInsert s).continuous
  continuous_invFun := (supportFaceRestrict s).continuous

@[simp]
theorem supportFaceHomeomorph_apply_val (s : Finset ι) (p : stdSimplex ℝ s) :
    (supportFaceHomeomorph s p).val = stdSimplex.map Subtype.val p := rfl

@[simp]
theorem supportFaceHomeomorph_symm_apply (s : Finset ι) (p : supportFace s) (i : s) :
    (supportFaceHomeomorph s).symm p i = p.val i.val := rfl

end DifferentialGeometry.Simplex
