import DifferentialGeometry.Topology.SimplicialComplex.FaceBarycenter
import DifferentialGeometry.Topology.SimplicialComplex.FaceShell

set_option autoImplicit false
noncomputable section
open Set Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) (s : Finset E)


def faceOpenStar : Set E := K.space \ (geometricFaceCostar K s).space


def puncturedFaceOpenStar : Set E := faceOpenStar K s \ {s.centroid ℝ id}

omit [LinearOrder E] in
@[simp]
theorem faceOpenStar_singleton (p : E) : faceOpenStar K {p} = vertexOpenStar K p := rfl

omit [LinearOrder E] in
@[simp]
theorem puncturedFaceOpenStar_singleton (p : E) :
    puncturedFaceOpenStar K {p} = puncturedVertexOpenStar K p := by
  simp only [puncturedFaceOpenStar, faceOpenStar_singleton, Finset.centroid_singleton,
    id_eq, puncturedVertexOpenStar]

omit [LinearOrder E] in
theorem mem_geometricFaceCostar_iff {x : E} :
    x ∈ (geometricFaceCostar K s).space ↔
      ∃ p ∈ s, x ∈ (geometricFaceCostar K {p}).space := by
  constructor
  · intro hx
    obtain ⟨t, ht, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨p, hp, hpt⟩ := Finset.not_subset.mp ht.2
    exact ⟨p, hp, Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨t, ⟨ht.1, by simpa only [Finset.singleton_subset_iff] using hpt⟩, hx⟩⟩
  · rintro ⟨p, hp, hx⟩
    obtain ⟨t, ht, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨t, ⟨ht.1, fun hst ↦ ht.2 (by simpa only [Finset.singleton_subset_iff] using hst hp)⟩, hx⟩

theorem mem_faceOpenStar_iff [Finite K.faces] (x : K.space) :
    x.val ∈ faceOpenStar K s ↔ ∀ p ∈ s, 0 < vertexHeight K p x := by
  change (x.val ∈ K.space ∧ x.val ∉ (geometricFaceCostar K s).space) ↔ _
  rw [and_iff_right x.prop, mem_geometricFaceCostar_iff]
  simp only [not_exists, not_and]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [vertexHeight_pos_iff]
  exact (and_iff_right x.prop).symm

theorem subset_of_mem_faceOpenStar {x : E} (hx : x ∈ faceOpenStar K s)
    {t : Finset E} (ht : t ∈ K.faces) (hxt : x ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  by_contra hst
  exact hx.2 (Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t, ⟨ht, hst⟩, hxt⟩)


theorem geometricFaceBarycenter_mem_faceOpenStar [Finite K.faces] (hs : s ∈ K.faces) :
    (geometricFaceBarycenter K s hs).val ∈ faceOpenStar K s := by
  rw [mem_faceOpenStar_iff]
  intro p hp
  exact (vertexHeight_geometricFaceBarycenter_pos_iff K s hs p).mpr hp

private theorem face_coordinates [Finite K.faces] {t : Finset E} (ht : t ∈ K.faces)
    (x : K.space) (hx : x.val ∈ convexHull ℝ (t : Set E)) :
    (∑ p ∈ t, vertexHeight K p x = 1) ∧
      (∑ p ∈ t, vertexHeight K p x • p = x.val) := by
  let a := (geometricFaceHomeomorphism K ht).symm ⟨x.val, hx⟩
  have he : (⟨(geometricFaceHomeomorphism K ht a).val,
      Geometry.SimplicialComplex.convexHull_subset_space ht
        (geometricFaceHomeomorphism K ht a).prop⟩ : K.space) = x :=
    Subtype.ext (congrArg (fun z : convexHull ℝ (t : Set E) ↦ z.val)
      ((geometricFaceHomeomorphism K ht).apply_symm_apply ⟨x.val, hx⟩))
  have hh (p : t) : vertexHeight K p.val x = a.val p := by
    rw [← he, vertexHeight_face_of_mem K p.val ht p.prop]
  constructor
  · rw [← Finset.sum_attach]
    change ∑ p : t, vertexHeight K p.val x = 1
    simp only [hh, a.prop.2]
  · rw [← Finset.sum_attach]
    change ∑ p : t, vertexHeight K p.val x • p.val = x.val
    simp only [hh]
    exact congrArg Subtype.val he

def faceHeight [Finite K.faces] (hs : s ∈ K.faces) : C(K.space, ℝ) where
  toFun x := (s.card : ℝ) * s.inf' (K.nonempty_of_mem_faces hs) (fun p ↦ vertexHeight K p x)
  continuous_toFun := continuous_const.mul
    (Continuous.finset_inf'_apply (K.nonempty_of_mem_faces hs) (fun p _ ↦
      (vertexHeight K p).continuous))

@[simp]
theorem faceHeight_singleton [Finite K.faces] (p : E) (hp : {p} ∈ K.faces) :
    faceHeight K {p} hp = vertexHeight K p := by
  ext x
  simp only [faceHeight, ContinuousMap.coe_mk, Finset.card_singleton, Nat.cast_one,
    Finset.inf'_singleton, one_mul]


theorem exists_faceHeight_coordinate [Finite K.faces] (hs : s ∈ K.faces) (x : K.space) :
    ∃ p ∈ s, faceHeight K s hs x = (s.card : ℝ) * vertexHeight K p x := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_inf' (K.nonempty_of_mem_faces hs)
    (fun p ↦ vertexHeight K p x)
  exact ⟨p, hp, congrArg ((s.card : ℝ) * ·) he⟩


theorem faceHeight_nonneg [Finite K.faces] (hs : s ∈ K.faces) (x : K.space) :
    0 ≤ faceHeight K s hs x := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact Finset.le_inf' (K.nonempty_of_mem_faces hs) _
    (fun p _ ↦ (vertexHeight_mem_Icc K p x).1)


theorem faceHeight_pos_iff [Finite K.faces] (hs : s ∈ K.faces) (x : K.space) :
    0 < faceHeight K s hs x ↔ x.val ∈ faceOpenStar K s := by
  have hc : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr
    (K.nonempty_of_mem_faces hs))
  rw [faceHeight, ContinuousMap.coe_mk, mul_pos_iff_of_pos_left hc, mem_faceOpenStar_iff]
  constructor
  · intro h p hp
    exact h.trans_le (Finset.inf'_le _ hp)
  · intro h
    obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_inf' (K.nonempty_of_mem_faces hs)
      (fun p ↦ vertexHeight K p x)
    rw [he]
    exact h p hp


theorem faceHeight_le_one [Finite K.faces] (hs : s ∈ K.faces) (x : K.space) :
    faceHeight K s hs x ≤ 1 := by
  by_cases hpos : 0 < faceHeight K s hs x
  · obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.prop
    have hst := subset_of_mem_faceOpenStar K s ((faceHeight_pos_iff K s hs x).mp hpos) ht hxt
    have hsum : (∑ _p ∈ s, s.inf' (K.nonempty_of_mem_faces hs)
        (fun p ↦ vertexHeight K p x)) ≤ ∑ p ∈ s, vertexHeight K p x :=
      Finset.sum_le_sum (fun p hp ↦ Finset.inf'_le (fun p ↦ vertexHeight K p x) hp)
    have hsum' : faceHeight K s hs x ≤ ∑ p ∈ s, vertexHeight K p x := by
      change (s.card : ℝ) * s.inf' (K.nonempty_of_mem_faces hs)
        (fun p ↦ vertexHeight K p x) ≤ _
      simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
    exact hsum'.trans ((Finset.sum_le_sum_of_subset_of_nonneg hst
      (fun p _ _ ↦ (vertexHeight_mem_Icc K p x).1)).trans_eq (face_coordinates K ht x hxt).1)
  · exact (le_of_not_gt hpos).trans zero_le_one


theorem eq_geometricFaceBarycenter_of_faceHeight_eq_one [Finite K.faces]
    (hs : s ∈ K.faces) (x : K.space) (hx : faceHeight K s hs x = 1) :
    x = geometricFaceBarycenter K s hs := by
  have hc : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr
    (K.nonempty_of_mem_faces hs))
  let m := s.inf' (K.nonempty_of_mem_faces hs) (fun p ↦ vertexHeight K p x)
  change (s.card : ℝ) * m = 1 at hx
  have hm : m = (s.card : ℝ)⁻¹ := by
    apply mul_left_cancel₀ (ne_of_gt hc)
    exact hx.trans (mul_inv_cancel₀ (ne_of_gt hc)).symm
  obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.prop
  have hst := subset_of_mem_faceOpenStar K s
    ((faceHeight_pos_iff K s hs x).mp (show 0 < (s.card : ℝ) * m by rw [hx]; exact zero_lt_one)) ht hxt
  have hsumle : ∑ p ∈ s, vertexHeight K p x ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hst
      (fun p _ _ ↦ (vertexHeight_mem_Icc K p x).1)).trans_eq (face_coordinates K ht x hxt).1
  have hsumge : 1 ≤ ∑ p ∈ s, vertexHeight K p x := by
    have h : (∑ _p ∈ s, m) ≤ ∑ p ∈ s, vertexHeight K p x :=
      Finset.sum_le_sum (fun p hp ↦ Finset.inf'_le (fun p ↦ vertexHeight K p x) hp)
    simpa only [Finset.sum_const, nsmul_eq_mul, show (s.card : ℝ) * m = 1 from hx] using h
  have hsumeq : ∑ p ∈ s, vertexHeight K p x = 1 := le_antisymm hsumle hsumge
  have hcoords (p : E) (hp : p ∈ s) : vertexHeight K p x = (s.card : ℝ)⁻¹ := by
    have heq : ∑ _p ∈ s, m = ∑ p ∈ s, vertexHeight K p x := by
      simpa only [Finset.sum_const, nsmul_eq_mul, hsumeq] using hx
    exact ((Finset.sum_eq_sum_iff_of_le (fun p (hp : p ∈ s) ↦
      Finset.inf'_le (fun p ↦ vertexHeight K p x) hp)).mp heq p hp).symm.trans hm
  have hzero (p : E) (hpt : p ∈ t) (hps : p ∉ s) : vertexHeight K p x = 0 := by
    have hpinsert : insert p s ⊆ t := Finset.insert_subset hpt hst
    have hle := (Finset.sum_le_sum_of_subset_of_nonneg hpinsert
      (fun p _ _ ↦ (vertexHeight_mem_Icc K p x).1)).trans_eq (face_coordinates K ht x hxt).1
    rw [Finset.sum_insert hps, hsumeq] at hle
    exact le_antisymm (by linarith) (vertexHeight_mem_Icc K p x).1
  apply Subtype.ext
  rw [← (face_coordinates K ht x hxt).2, geometricFaceBarycenter_val,
    Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ s (K.nonempty_of_mem_faces hs)),
    ← Finset.sum_subset hst (fun p hpt hps ↦ by rw [hzero p hpt hps, zero_smul])]
  exact Finset.sum_congr rfl (fun p hp ↦ by rw [hcoords p hp]; rfl)


@[simp]
theorem faceHeight_geometricFaceBarycenter [Finite K.faces] (hs : s ∈ K.faces) :
    faceHeight K s hs (geometricFaceBarycenter K s hs) = 1 := by
  obtain ⟨p, hp, he⟩ := exists_faceHeight_coordinate K s hs (geometricFaceBarycenter K s hs)
  rw [he, vertexHeight_geometricFaceBarycenter, if_pos hp]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
    (K.nonempty_of_mem_faces hs)))


theorem faceHeight_eq_one_iff [Finite K.faces] (hs : s ∈ K.faces) (x : K.space) :
    faceHeight K s hs x = 1 ↔ x = geometricFaceBarycenter K s hs := by
  constructor
  · exact eq_geometricFaceBarycenter_of_faceHeight_eq_one K s hs x
  · rintro rfl
    exact faceHeight_geometricFaceBarycenter K s hs

theorem faceHeight_mem_Ioo_iff [Finite K.faces] (hs : s ∈ K.faces) (x : K.space) :
    faceHeight K s hs x ∈ Ioo (0 : ℝ) 1 ↔ x.val ∈ puncturedFaceOpenStar K s := by
  change (0 < faceHeight K s hs x ∧ faceHeight K s hs x < 1) ↔
    (x.val ∈ faceOpenStar K s ∧ x.val ≠ s.centroid ℝ id)
  rw [faceHeight_pos_iff]
  apply and_congr_right
  intro _
  rw [lt_iff_le_and_ne, and_iff_right (faceHeight_le_one K s hs x)]
  exact (not_congr (faceHeight_eq_one_iff K s hs x)).trans
    (not_congr (Subtype.ext_iff))

omit [LinearOrder E] in
private theorem sum_smul_centroid (hs : s ∈ K.faces) (m : ℝ) :
    ∑ p ∈ s, m • p = ((s.card : ℝ) * m) • s.centroid ℝ id := by
  have hc : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero.mpr (K.nonempty_of_mem_faces hs))
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ s (K.nonempty_of_mem_faces hs)),
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finset.centroidWeights_apply, id_eq, smul_smul]
  congr 1
  field_simp

theorem face_normalization_mem_shell [Finite K.faces] (hs : s ∈ K.faces)
    (x : puncturedFaceOpenStar K s) :
    (1 - faceHeight K s hs ⟨x.val, x.prop.1.1⟩)⁻¹ •
      (x.val - faceHeight K s hs ⟨x.val, x.prop.1.1⟩ • s.centroid ℝ id) ∈
        (geometricFaceShell K s).space := by
  let z : K.space := ⟨x.val, x.prop.1.1⟩
  let m := s.inf' (K.nonempty_of_mem_faces hs) (fun p ↦ vertexHeight K p z)
  let h := faceHeight K s hs z
  have hI : h ∈ Ioo (0 : ℝ) 1 := (faceHeight_mem_Ioo_iff K s hs z).mpr x.prop
  have hd : 0 < 1 - h := sub_pos.mpr hI.2
  have hm : (s.card : ℝ) * m = h := rfl
  obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp z.prop
  have hst := subset_of_mem_faceOpenStar K s x.prop.1 ht hxt
  obtain ⟨p, hp, hpm⟩ := Finset.exists_mem_eq_inf' (K.nonempty_of_mem_faces hs)
    (fun p ↦ vertexHeight K p z)
  let w : E → ℝ := fun q ↦ (1 - h)⁻¹ * (vertexHeight K q z - if q ∈ s then m else 0)
  have hw0 (q : E) : 0 ≤ w q := by
    apply mul_nonneg (inv_nonneg.mpr hd.le)
    by_cases hqs : q ∈ s
    · rw [if_pos hqs]
      exact sub_nonneg.mpr (Finset.inf'_le (fun p ↦ vertexHeight K p z) hqs)
    · rw [if_neg hqs, sub_zero]
      exact (vertexHeight_mem_Icc K q z).1
  have hsum : ∑ q ∈ t, w q = 1 := by
    simp only [w, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hst, Finset.sum_const, nsmul_eq_mul,
      (face_coordinates K ht z hxt).1, hm]
    exact inv_mul_cancel₀ (ne_of_gt hd)
  have hwp : w p = 0 := by
    change (1 - h)⁻¹ * (vertexHeight K p z - if p ∈ s then m else 0) = 0
    rw [if_pos hp, show vertexHeight K p z = m from hpm.symm, sub_self, mul_zero]
  have hsumerase : ∑ q ∈ t.erase p, w q = 1 := by
    rw [Finset.sum_erase_eq_sub (hst hp), hsum, hwp, sub_zero]
  have hvec : ∑ q ∈ t, w q • q = (1 - h)⁻¹ • (z.val - h • s.centroid ℝ id) := by
    simp only [w, mul_smul, ← Finset.smul_sum, sub_smul, Finset.sum_sub_distrib,
      (face_coordinates K ht z hxt).2, ite_smul, zero_smul, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hst, sum_smul_centroid K s hs m, hm]
  have hvecerase : ∑ q ∈ t.erase p, w q • q =
      (1 - h)⁻¹ • (z.val - h • s.centroid ℝ id) := by
    rw [Finset.sum_erase_eq_sub (hst hp), hvec, hwp, zero_smul, sub_zero]
  have hh : (1 - h)⁻¹ • (z.val - h • s.centroid ℝ id) ∈
      convexHull ℝ (t.erase p : Set E) := by
    apply Finset.mem_convexHull.mpr
    refine ⟨w, fun q _ ↦ hw0 q, hsumerase, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsumerase]
    exact hvecerase
  have hne : (t.erase p).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hh⟩)
  have hunion : t.erase p ∪ s = t := by
    apply Finset.Subset.antisymm (Finset.union_subset (Finset.erase_subset _ _) hst)
    intro q hqt
    by_cases hqp : q = p
    · exact Finset.mem_union_right _ (hqp.symm ▸ hp)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hqp, hqt⟩)
  exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t.erase p,
    ⟨K.down_closed ht (Finset.erase_subset _ _) hne, hunion.symm ▸ ht,
      fun h ↦ Finset.notMem_erase p t (h hp)⟩, hh⟩

theorem face_cone_mem_space (hs : s ∈ K.faces)
    (y : (geometricFaceShell K s).space) (a : Ioo (0 : ℝ) 1) :
    a.val • s.centroid ℝ id + (1 - a.val) • y.val ∈ K.space := by
  obtain ⟨t, ht, hy⟩ := Geometry.SimplicialComplex.mem_space_iff.mp y.prop
  have hb : s.centroid ℝ id ∈ convexHull ℝ (↑(t ∪ s) : Set E) :=
    convexHull_mono (show (s : Set E) ⊆ ↑(t ∪ s) from Finset.subset_union_right)
      (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))
  have hy' : y.val ∈ convexHull ℝ (↑(t ∪ s) : Set E) :=
    convexHull_mono (show (t : Set E) ⊆ ↑(t ∪ s) from Finset.subset_union_left) hy
  exact Geometry.SimplicialComplex.convexHull_subset_space ht.2.1
    ((convex_convexHull ℝ _) hb hy' a.prop.1.le (sub_nonneg.mpr a.prop.2.le)
      (add_sub_cancel _ _))

theorem faceHeight_cone [Finite K.faces] (hs : s ∈ K.faces)
    (y : (geometricFaceShell K s).space) (a : Ioo (0 : ℝ) 1) :
    faceHeight K s hs
      ⟨a.val • s.centroid ℝ id + (1 - a.val) • y.val, face_cone_mem_space K s hs y a⟩ = a.val := by
  obtain ⟨t, ht, hy⟩ := Geometry.SimplicialComplex.mem_space_iff.mp y.prop
  have hb : s.centroid ℝ id ∈ convexHull ℝ (↑(t ∪ s) : Set E) :=
    convexHull_mono (show (s : Set E) ⊆ ↑(t ∪ s) from Finset.subset_union_right)
      (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))
  have hy' : y.val ∈ convexHull ℝ (↑(t ∪ s) : Set E) :=
    convexHull_mono (show (t : Set E) ⊆ ↑(t ∪ s) from Finset.subset_union_left) hy
  let z : K.space := ⟨a.val • s.centroid ℝ id + (1 - a.val) • y.val,
    face_cone_mem_space K s hs y a⟩
  let yp : K.space := ⟨y.val, Geometry.SimplicialComplex.convexHull_subset_space ht.1 hy⟩
  have hcoord (q : E) (hq : q ∈ s) : vertexHeight K q z =
      a.val * (s.card : ℝ)⁻¹ + (1 - a.val) * vertexHeight K q yp := by
    have h := vertexFunction_combo K (fun p ↦ if p = q then 1 else 0) ht.2.1
      (geometricFaceBarycenter K s hs) yp hb hy' a.prop.1.le
      (sub_nonneg.mpr a.prop.2.le) (add_sub_cancel _ _)
    change vertexHeight K q z = a.val * vertexHeight K q (geometricFaceBarycenter K s hs) +
      (1 - a.val) * vertexHeight K q yp at h
    simpa only [vertexHeight_geometricFaceBarycenter, if_pos hq] using h
  let m := s.inf' (K.nonempty_of_mem_faces hs) (fun q ↦ vertexHeight K q z)
  have hmle : a.val * (s.card : ℝ)⁻¹ ≤ m := by
    apply Finset.le_inf'
    intro q hq
    rw [hcoord q hq]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr a.prop.2.le)
      (vertexHeight_mem_Icc K q yp).1)
  obtain ⟨p, hp, hpt⟩ := Finset.not_subset.mp ht.2.2
  have hpzero : vertexHeight K p yp = 0 := (vertexHeight_eq_zero_iff K p yp).mpr
    (Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨t, ⟨ht.1, by simpa only [Finset.singleton_subset_iff] using hpt⟩, hy⟩)
  have hmge : m ≤ a.val * (s.card : ℝ)⁻¹ := by
    have h := Finset.inf'_le (fun q ↦ vertexHeight K q z) hp
    simpa only [hcoord p hp, hpzero, mul_zero, add_zero] using h
  change (s.card : ℝ) * m = a.val
  rw [le_antisymm hmge hmle]
  have hc : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero.mpr (K.nonempty_of_mem_faces hs))
  field_simp


theorem face_cone_mem_puncturedStar [Finite K.faces] (hs : s ∈ K.faces)
    (y : (geometricFaceShell K s).space) (a : Ioo (0 : ℝ) 1) :
    a.val • s.centroid ℝ id + (1 - a.val) • y.val ∈ puncturedFaceOpenStar K s := by
  apply (faceHeight_mem_Ioo_iff K s hs ⟨_, face_cone_mem_space K s hs y a⟩).mp
  rw [faceHeight_cone K s hs]
  exact a.prop


def faceStarCoordinates [Finite K.faces] (hs : s ∈ K.faces) :
    C(puncturedFaceOpenStar K s, (geometricFaceShell K s).space × Ioo (0 : ℝ) 1) where
  toFun x :=
    (⟨(1 - faceHeight K s hs ⟨x.val, x.prop.1.1⟩)⁻¹ •
        (x.val - faceHeight K s hs ⟨x.val, x.prop.1.1⟩ • s.centroid ℝ id),
      face_normalization_mem_shell K s hs x⟩,
      ⟨faceHeight K s hs ⟨x.val, x.prop.1.1⟩,
        (faceHeight_mem_Ioo_iff K s hs _).mpr x.prop⟩)
  continuous_toFun := by
    have hc : Continuous (fun x : puncturedFaceOpenStar K s ↦
        (⟨x.val, x.prop.1.1⟩ : K.space)) := continuous_subtype_val.subtype_mk _
    have hh := (faceHeight K s hs).continuous.comp hc
    have hi : Continuous (fun x : puncturedFaceOpenStar K s ↦
        (1 - faceHeight K s hs ⟨x.val, x.prop.1.1⟩)⁻¹) :=
      (continuous_const.sub hh).inv₀ (fun x ↦
        (sub_pos.mpr ((faceHeight_mem_Ioo_iff K s hs _).mpr x.prop).2).ne')
    exact ((hi.smul (continuous_subtype_val.sub (hh.smul continuous_const))).subtype_mk _).prodMk
      (hh.subtype_mk _)


def faceStarCone [Finite K.faces] (hs : s ∈ K.faces) :
    C((geometricFaceShell K s).space × Ioo (0 : ℝ) 1, puncturedFaceOpenStar K s) where
  toFun z := ⟨z.2.val • s.centroid ℝ id + (1 - z.2.val) • z.1.val,
    face_cone_mem_puncturedStar K s hs z.1 z.2⟩
  continuous_toFun :=
    (((continuous_subtype_val.comp continuous_snd).smul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (continuous_subtype_val.comp continuous_fst))).subtype_mk _


@[simp]
theorem faceStarCoordinates_fst_val [Finite K.faces] (hs : s ∈ K.faces)
    (x : puncturedFaceOpenStar K s) :
    (faceStarCoordinates K s hs x).1.val =
      (1 - faceHeight K s hs ⟨x.val, x.prop.1.1⟩)⁻¹ •
        (x.val - faceHeight K s hs ⟨x.val, x.prop.1.1⟩ • s.centroid ℝ id) := rfl


@[simp]
theorem faceStarCoordinates_snd_val [Finite K.faces] (hs : s ∈ K.faces)
    (x : puncturedFaceOpenStar K s) :
    (faceStarCoordinates K s hs x).2.val = faceHeight K s hs ⟨x.val, x.prop.1.1⟩ := rfl


@[simp]
theorem faceStarCone_val [Finite K.faces] (hs : s ∈ K.faces)
    (z : (geometricFaceShell K s).space × Ioo (0 : ℝ) 1) :
    (faceStarCone K s hs z).val = z.2.val • s.centroid ℝ id + (1 - z.2.val) • z.1.val := rfl


@[simp]
theorem faceStarCone_coordinates [Finite K.faces] (hs : s ∈ K.faces)
    (x : puncturedFaceOpenStar K s) :
    faceStarCone K s hs (faceStarCoordinates K s hs x) = x := by
  apply Subtype.ext
  let h := faceHeight K s hs ⟨x.val, x.prop.1.1⟩
  have hh : 1 - h ≠ 0 :=
    (sub_pos.mpr ((faceHeight_mem_Ioo_iff K s hs _).mpr x.prop).2).ne'
  change h • s.centroid ℝ id +
    (1 - h) • ((1 - h)⁻¹ • (x.val - h • s.centroid ℝ id)) = x.val
  rw [smul_smul, mul_inv_cancel₀ hh, one_smul, add_sub_cancel]


@[simp]
theorem faceStarCoordinates_cone [Finite K.faces] (hs : s ∈ K.faces)
    (z : (geometricFaceShell K s).space × Ioo (0 : ℝ) 1) :
    faceStarCoordinates K s hs (faceStarCone K s hs z) = z := by
  apply Prod.ext
  · apply Subtype.ext
    change (1 - faceHeight K s hs
      ⟨z.2.val • s.centroid ℝ id + (1 - z.2.val) • z.1.val, _⟩)⁻¹ •
      (z.2.val • s.centroid ℝ id + (1 - z.2.val) • z.1.val -
        faceHeight K s hs ⟨z.2.val • s.centroid ℝ id + (1 - z.2.val) • z.1.val, _⟩ •
          s.centroid ℝ id) = z.1.val
    rw [faceHeight_cone K s hs, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ (sub_pos.mpr z.2.prop.2).ne', one_smul]
  · apply Subtype.ext
    exact faceHeight_cone K s hs z.1 z.2

def puncturedFaceStarHomeomorphism [Finite K.faces] (hs : s ∈ K.faces) :
    puncturedFaceOpenStar K s ≃ₜ (geometricFaceShell K s).space × Ioo (0 : ℝ) 1 where
  toFun := faceStarCoordinates K s hs
  invFun := faceStarCone K s hs
  left_inv := faceStarCone_coordinates K s hs
  right_inv := faceStarCoordinates_cone K s hs
  continuous_toFun := (faceStarCoordinates K s hs).continuous
  continuous_invFun := (faceStarCone K s hs).continuous


@[simp]
theorem puncturedFaceStarHomeomorphism_apply [Finite K.faces] (hs : s ∈ K.faces)
    (x : puncturedFaceOpenStar K s) :
    puncturedFaceStarHomeomorphism K s hs x = faceStarCoordinates K s hs x := rfl


@[simp]
theorem puncturedFaceStarHomeomorphism_symm_apply [Finite K.faces] (hs : s ∈ K.faces)
    (z : (geometricFaceShell K s).space × Ioo (0 : ℝ) 1) :
    (puncturedFaceStarHomeomorphism K s hs).symm z = faceStarCone K s hs z := rfl


theorem geometricFaceShell_disjoint_faceOpenStar :
    Disjoint (geometricFaceShell K s).space (faceOpenStar K s) := by
  rw [Set.disjoint_left]
  intro x hx hstar
  exact hstar.2 (geometricSpace_mono (geometricFaceShell_le_costar K s) hx)

omit [LinearOrder E] in
theorem isOpen_faceOpenStar [Finite K.faces] :
    IsOpen (Subtype.val ⁻¹' faceOpenStar K s : Set K.space) := by
  change IsOpen (Subtype.val ⁻¹' (K.space \ (geometricFaceCostar K s).space))
  have he : (Subtype.val ⁻¹' (K.space \ (geometricFaceCostar K s).space) : Set K.space) =
      (Subtype.val ⁻¹' (geometricFaceCostar K s).space)ᶜ := by
    ext x
    exact and_iff_right x.prop
  rw [he]
  exact ((isCompact_geometricSpace (geometricFaceCostar K s)).isClosed.preimage
    continuous_subtype_val).isOpen_compl

omit [LinearOrder E] in
theorem isOpen_puncturedFaceOpenStar [Finite K.faces] :
    IsOpen (Subtype.val ⁻¹' puncturedFaceOpenStar K s : Set K.space) :=
  (isOpen_faceOpenStar K s).inter
    ((isClosed_singleton.preimage continuous_subtype_val).isOpen_compl)

theorem isEmpty_puncturedFaceOpenStar_iff [Finite K.faces] (hs : s ∈ K.faces) :
    IsEmpty (puncturedFaceOpenStar K s) ↔ IsEmpty (geometricFaceShell K s).space := by
  constructor
  · intro h
    exact ⟨fun y ↦ h.false (faceStarCone K s hs (y, ⟨1 / 2, by constructor <;> norm_num⟩))⟩
  · intro h
    exact ⟨fun x ↦ h.false (faceStarCoordinates K s hs x).1⟩

end DifferentialGeometry.Topology.SimplicialComplex
