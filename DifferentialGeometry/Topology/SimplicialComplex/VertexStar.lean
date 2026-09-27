import DifferentialGeometry.Topology.SimplicialComplex.GeometricLink
import DifferentialGeometry.Topology.SimplicialComplex.VertexFunction
import DifferentialGeometry.Topology.SimplicialComplex.GeometricCompactness

set_option autoImplicit false
noncomputable section
open Set Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) (p : E)


def vertexOpenStar : Set E := K.space \ (geometricFaceCostar K {p}).space


def puncturedVertexOpenStar : Set E := vertexOpenStar K p \ {p}


theorem geometricLink_disjoint_vertexOpenStar :
    Disjoint (geometricLink K {p}).space (vertexOpenStar K p) := by
  rw [Set.disjoint_left]
  intro x hx hstar
  exact hstar.2 (geometricLink_singleton_space_subset_costar K p hx)


def vertexHeight [Finite K.faces] : C(K.space, ℝ) :=
  vertexFunction K (fun q ↦ if q = p then 1 else 0)

theorem vertexHeight_face_of_mem [Finite K.faces] {s : Finset E}
    (hs : s ∈ K.faces) (hp : p ∈ s) (x : stdSimplex ℝ s) :
    vertexHeight K p
      ⟨(geometricFaceHomeomorphism K hs x).val,
        Geometry.SimplicialComplex.convexHull_subset_space hs
          (geometricFaceHomeomorphism K hs x).prop⟩ = x.val ⟨p, hp⟩ := by
  rw [vertexHeight, vertexFunction_geometricFaceHomeomorphism]
  change (∑ i : s, x.val i • (if i.val = p then (1 : ℝ) else 0)) = _
  classical
  rw [Finset.sum_eq_single (⟨p, hp⟩ : s)]
  · simp
  · intro i _ hi
    have hne : i.val ≠ p := fun h ↦ hi (Subtype.ext h)
    simp only [hne, if_false, smul_zero]
  · simp


theorem vertexHeight_face_of_not_mem [Finite K.faces] {s : Finset E}
    (hs : s ∈ K.faces) (hp : p ∉ s) (x : stdSimplex ℝ s) :
    vertexHeight K p
      ⟨(geometricFaceHomeomorphism K hs x).val,
        Geometry.SimplicialComplex.convexHull_subset_space hs
          (geometricFaceHomeomorphism K hs x).prop⟩ = 0 := by
  rw [vertexHeight, vertexFunction_geometricFaceHomeomorphism]
  apply Finset.sum_eq_zero
  intro i _
  have hne : i.val ≠ p := fun h ↦ hp (h ▸ i.prop)
  change x.val i • (if i.val = p then (1 : ℝ) else 0) = 0
  simp only [hne, if_false, smul_zero]

omit [LinearOrder E] in
private theorem geometricFace_induction_on (x : K.space) (P : K.space → Prop)
    (h : ∀ (s : Finset E) (hs : s ∈ K.faces) (a : stdSimplex ℝ s),
      P ⟨(geometricFaceHomeomorphism K hs a).val,
        Geometry.SimplicialComplex.convexHull_subset_space hs
          (geometricFaceHomeomorphism K hs a).prop⟩) : P x := by
  obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.prop
  let a := (geometricFaceHomeomorphism K hs).symm ⟨x.val, hx⟩
  have he : (⟨(geometricFaceHomeomorphism K hs a).val,
      Geometry.SimplicialComplex.convexHull_subset_space hs
        (geometricFaceHomeomorphism K hs a).prop⟩ : K.space) = x :=
    Subtype.ext (congrArg (fun y : convexHull ℝ (s : Set E) ↦ y.val)
      ((geometricFaceHomeomorphism K hs).apply_symm_apply ⟨x.val, hx⟩))
  exact he ▸ h s hs a


theorem vertexHeight_mem_Icc [Finite K.faces] (x : K.space) :
    vertexHeight K p x ∈ Icc (0 : ℝ) 1 := by
  apply geometricFace_induction_on K x
    (fun x ↦ vertexHeight K p x ∈ Icc (0 : ℝ) 1)
  intro s hs a
  by_cases hp : p ∈ s
  · rw [vertexHeight_face_of_mem K p hs hp]
    exact ⟨a.prop.1 _, stdSimplex.le_one a _⟩
  · rw [vertexHeight_face_of_not_mem K p hs hp]
    exact ⟨le_rfl, zero_le_one⟩


theorem vertexHeight_eq_zero_iff [Finite K.faces] (x : K.space) :
    vertexHeight K p x = 0 ↔ x.val ∈ (geometricFaceCostar K {p}).space := by
  constructor
  · apply geometricFace_induction_on K x
      (fun x ↦ vertexHeight K p x = 0 → x.val ∈ (geometricFaceCostar K {p}).space)
    intro s hs a ha
    by_cases hp : p ∈ s
    · rw [vertexHeight_face_of_mem K p hs hp] at ha
      have hh : DifferentialGeometry.Simplex.vertexMap (fun i : s ↦ (i : E)) a ∈
          convexHull ℝ (s.erase p : Set E) := by
        have he : (fun i : s ↦ (i : E)) '' {i | i.val ≠ p} = (s.erase p : Set E) := by
          ext y
          simp only [Set.mem_image, Set.mem_ofPred_eq, mem_coe, mem_erase]
          constructor
          · rintro ⟨i, hi, rfl⟩
            exact ⟨hi, i.prop⟩
          · rintro ⟨hy, hs⟩
            exact ⟨⟨y, hs⟩, hy, rfl⟩
        rw [← he, DifferentialGeometry.Simplex.vertexMap_mem_convexHull_image_iff (K.indep hs)]
        intro i hi
        have he : i = (⟨p, hp⟩ : s) := Subtype.ext (by simpa using hi)
        simpa only [he] using ha
      have hne : (s.erase p).Nonempty :=
        Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hh⟩)
      exact Geometry.SimplicialComplex.mem_space_iff.mpr
        ⟨s.erase p, ⟨K.down_closed hs (Finset.erase_subset _ _) hne,
          by simp only [Finset.singleton_subset_iff, Finset.notMem_erase, not_false_eq_true]⟩, hh⟩
    · exact Geometry.SimplicialComplex.mem_space_iff.mpr
        ⟨s, ⟨hs, by simpa only [Finset.singleton_subset_iff] using hp⟩,
          (geometricFaceHomeomorphism K hs a).prop⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    have hp : p ∉ s := by simpa only [Finset.singleton_subset_iff] using hs.2
    let a := (geometricFaceHomeomorphism K hs.1).symm ⟨x.val, hx⟩
    have he : (⟨(geometricFaceHomeomorphism K hs.1 a).val,
        Geometry.SimplicialComplex.convexHull_subset_space hs.1
          (geometricFaceHomeomorphism K hs.1 a).prop⟩ : K.space) = x :=
      Subtype.ext (congrArg (fun y : convexHull ℝ (s : Set E) ↦ y.val)
        ((geometricFaceHomeomorphism K hs.1).apply_symm_apply ⟨x.val, hx⟩))
    rw [← he]
    exact vertexHeight_face_of_not_mem K p hs.1 hp a


theorem vertexHeight_pos_iff [Finite K.faces] (x : K.space) :
    0 < vertexHeight K p x ↔ x.val ∈ vertexOpenStar K p := by
  change 0 < vertexHeight K p x ↔ x.val ∈ K.space ∧
    x.val ∉ (geometricFaceCostar K {p}).space
  rw [and_iff_right x.prop, ← vertexHeight_eq_zero_iff K p x]
  exact lt_iff_le_and_ne.trans
    ((and_iff_right (vertexHeight_mem_Icc K p x).1).trans (ne_comm))


theorem eq_vertex_of_vertexHeight_eq_one [Finite K.faces] (x : K.space)
    (hx : vertexHeight K p x = 1) : x.val = p := by
  revert hx
  apply geometricFace_induction_on K x
    (fun x ↦ vertexHeight K p x = 1 → x.val = p)
  intro s hs a ha
  by_cases hp : p ∈ s
  · rw [vertexHeight_face_of_mem K p hs hp] at ha
    let i : s := ⟨p, hp⟩
    have hsum : ∑ j ∈ Finset.univ.erase i, a.val j = 0 := by
      have he := Finset.sum_erase_add Finset.univ a.val (Finset.mem_univ i)
      rw [a.prop.2, show a.val i = 1 from ha] at he
      exact add_left_injective 1 (he.trans (zero_add 1).symm)
    have hz (j : s) (hj : j ≠ i) : a.val j = 0 := by
      apply le_antisymm _ (a.prop.1 j)
      have hj' : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
      have hle := Finset.single_le_sum (fun j _ ↦ a.prop.1 j) hj'
      exact hle.trans hsum.le
    change DifferentialGeometry.Simplex.vertexMap (fun j : s ↦ (j : E)) a = p
    rw [DifferentialGeometry.Simplex.vertexMap_apply, Finset.sum_eq_single i]
    · change a.val i • p = p
      rw [show a.val i = 1 from ha, one_smul]
    · intro j _ hj
      rw [hz j hj, zero_smul]
    · simp
  · rw [vertexHeight_face_of_not_mem K p hs hp] at ha
    exact (zero_ne_one ha).elim


theorem vertexHeight_eq_one_iff [Finite K.faces] (hp : {p} ∈ K.faces) (x : K.space) :
    vertexHeight K p x = 1 ↔ x.val = p := by
  constructor
  · exact eq_vertex_of_vertexHeight_eq_one K p x
  · intro hx
    change vertexFunction K (fun q ↦ if q = p then 1 else 0) x = 1
    rw [vertexFunction_vertex K _ hp x hx, if_pos rfl]

theorem vertexHeight_mem_Ioo_iff [Finite K.faces] (hp : {p} ∈ K.faces) (x : K.space) :
    vertexHeight K p x ∈ Ioo (0 : ℝ) 1 ↔ x.val ∈ puncturedVertexOpenStar K p := by
  change (0 < vertexHeight K p x ∧ vertexHeight K p x < 1) ↔
    x.val ∈ vertexOpenStar K p ∧ x.val ∉ {p}
  rw [vertexHeight_pos_iff, Set.mem_singleton_iff,
    lt_iff_le_and_ne, and_iff_right (vertexHeight_mem_Icc K p x).2]
  exact and_congr Iff.rfl (not_congr (vertexHeight_eq_one_iff K p hp x))

private theorem normalize_vertexMap_mem_hull_erase {s : Finset E} (hp : p ∈ s)
    (a : stdSimplex ℝ s) (ha : a.val ⟨p, hp⟩ < 1) :
    (1 - a.val ⟨p, hp⟩)⁻¹ •
      (DifferentialGeometry.Simplex.vertexMap (fun i : s ↦ (i : E)) a - a.val ⟨p, hp⟩ • p) ∈
        convexHull ℝ (s.erase p : Set E) := by
  classical
  let i : s := ⟨p, hp⟩
  have hpos : 0 < 1 - a.val i := sub_pos.mpr ha
  have hsum : ∑ j ∈ Finset.univ.erase i, a.val j = 1 - a.val i := by
    have he := Finset.sum_erase_add Finset.univ a.val (Finset.mem_univ i)
    rw [a.prop.2] at he
    exact eq_sub_of_add_eq he
  have hweights : ∑ j ∈ Finset.univ.erase i, (1 - a.val i)⁻¹ * a.val j = 1 := by
    rw [← Finset.mul_sum, hsum, inv_mul_cancel₀ hpos.ne']
  have hv : ∑ j ∈ Finset.univ.erase i, a.val j • j.val =
      DifferentialGeometry.Simplex.vertexMap (fun j : s ↦ (j : E)) a - a.val i • p := by
    exact eq_sub_of_add_eq
      (Finset.sum_erase_add Finset.univ (fun j : s ↦ a.val j • j.val) (Finset.mem_univ i))
  have hh : (∑ j ∈ Finset.univ.erase i, ((1 - a.val i)⁻¹ * a.val j) • j.val) ∈
      convexHull ℝ (s.erase p : Set E) := by
    apply (convex_convexHull ℝ (s.erase p : Set E)).sum_mem
      (fun j _ ↦ mul_nonneg (inv_nonneg.mpr hpos.le) (a.prop.1 j)) hweights
    intro j hj
    apply subset_convexHull
    have hji := (Finset.mem_erase.mp hj).1
    exact Finset.mem_erase.mpr ⟨fun h ↦ hji (Subtype.ext h), j.prop⟩
  simpa only [mul_smul, ← Finset.smul_sum, hv] using hh

theorem vertex_normalization_mem_link [Finite K.faces] (hp : {p} ∈ K.faces)
    (x : puncturedVertexOpenStar K p) :
    (1 - vertexHeight K p ⟨x.val, x.prop.1.1⟩)⁻¹ •
      (x.val - vertexHeight K p ⟨x.val, x.prop.1.1⟩ • p) ∈ (geometricLink K {p}).space := by
  have hx : vertexHeight K p ⟨x.val, x.prop.1.1⟩ ∈ Ioo (0 : ℝ) 1 :=
    (vertexHeight_mem_Ioo_iff K p hp _).mpr x.prop
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.prop.1.1
  let a := (geometricFaceHomeomorphism K hs).symm ⟨x.val, hxs⟩
  have he : (geometricFaceHomeomorphism K hs a : E) = x.val :=
    congrArg (fun z : convexHull ℝ (s : Set E) ↦ z.val)
      ((geometricFaceHomeomorphism K hs).apply_symm_apply ⟨x.val, hxs⟩)
  have hg : (⟨(geometricFaceHomeomorphism K hs a).val,
      Geometry.SimplicialComplex.convexHull_subset_space hs
        (geometricFaceHomeomorphism K hs a).prop⟩ : K.space) =
      ⟨x.val, x.prop.1.1⟩ := Subtype.ext he
  have hps : p ∈ s := by
    by_contra h
    have hz := vertexHeight_face_of_not_mem K p hs h a
    rw [hg] at hz
    exact hx.1.ne' hz
  have hh := vertexHeight_face_of_mem K p hs hps a
  rw [hg] at hh
  have ha : a.val ⟨p, hps⟩ < 1 := hh ▸ hx.2
  have hn := normalize_vertexMap_mem_hull_erase p hps a ha
  change (1 - a.val ⟨p, hps⟩)⁻¹ •
    ((geometricFaceHomeomorphism K hs a : E) - a.val ⟨p, hps⟩ • p) ∈ _ at hn
  rw [he, ← hh] at hn
  have hne : (s.erase p).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hn⟩)
  apply Geometry.SimplicialComplex.mem_space_iff.mpr
  refine ⟨s.erase p, (mem_geometricLink_singleton K p _).mpr ⟨hne, Finset.notMem_erase _ _, ?_⟩, hn⟩
  simpa only [Finset.insert_erase hps] using hs

theorem vertex_cone_mem_space (y : (geometricLink K {p}).space) (t : Ioo (0 : ℝ) 1) :
    t.val • p + (1 - t.val) • y.val ∈ K.space := by
  obtain ⟨s, hs, hy⟩ := Geometry.SimplicialComplex.mem_space_iff.mp y.prop
  have hs' := (mem_geometricLink_singleton K p s).mp hs
  have hp : p ∈ convexHull ℝ (↑(insert p s) : Set E) :=
    subset_convexHull ℝ _ (by simp)
  have hy' : y.val ∈ convexHull ℝ (↑(insert p s) : Set E) :=
    convexHull_mono (show (s : Set E) ⊆ ↑(insert p s) from Finset.subset_insert _ _) hy
  exact Geometry.SimplicialComplex.convexHull_subset_space hs'.2.2
    ((convex_convexHull ℝ _) hp hy' t.prop.1.le (sub_nonneg.mpr t.prop.2.le)
      (add_sub_cancel _ _))


theorem vertexHeight_cone [Finite K.faces] (hp : {p} ∈ K.faces)
    (y : (geometricLink K {p}).space) (t : Ioo (0 : ℝ) 1) :
    vertexHeight K p ⟨t.val • p + (1 - t.val) • y.val, vertex_cone_mem_space K p y t⟩ = t.val := by
  obtain ⟨s, hs, hy⟩ := Geometry.SimplicialComplex.mem_space_iff.mp y.prop
  have hs' := (mem_geometricLink_singleton K p s).mp hs
  have hps : p ∈ convexHull ℝ (↑(insert p s) : Set E) :=
    subset_convexHull ℝ _ (by simp)
  have hys : y.val ∈ convexHull ℝ (↑(insert p s) : Set E) :=
    convexHull_mono (show (s : Set E) ⊆ ↑(insert p s) from Finset.subset_insert _ _) hy
  let xp : K.space := ⟨p, Geometry.SimplicialComplex.convexHull_subset_space hs'.2.2 hps⟩
  let yp : K.space := ⟨y.val, Geometry.SimplicialComplex.convexHull_subset_space hs'.2.2 hys⟩
  have hxp : vertexHeight K p xp = 1 := (vertexHeight_eq_one_iff K p hp xp).mpr rfl
  have hyp : vertexHeight K p yp = 0 :=
    (vertexHeight_eq_zero_iff K p yp).mpr (geometricLink_singleton_space_subset_costar K p y.prop)
  have h := vertexFunction_combo K (fun q ↦ if q = p then 1 else 0) hs'.2.2
    xp yp hps hys t.prop.1.le (sub_nonneg.mpr t.prop.2.le) (add_sub_cancel _ _)
  change vertexHeight K p ⟨t.val • p + (1 - t.val) • y.val, _⟩ =
    t.val * vertexHeight K p xp + (1 - t.val) * vertexHeight K p yp at h
  simpa only [hxp, hyp, mul_one, mul_zero, add_zero] using h


theorem vertex_cone_mem_puncturedStar [Finite K.faces] (hp : {p} ∈ K.faces)
    (y : (geometricLink K {p}).space) (t : Ioo (0 : ℝ) 1) :
    t.val • p + (1 - t.val) • y.val ∈ puncturedVertexOpenStar K p := by
  apply (vertexHeight_mem_Ioo_iff K p hp
    ⟨_, vertex_cone_mem_space K p y t⟩).mp
  rw [vertexHeight_cone K p hp]
  exact t.prop


def vertexStarCoordinates [Finite K.faces] (hp : {p} ∈ K.faces) :
    C(puncturedVertexOpenStar K p, (geometricLink K {p}).space × Ioo (0 : ℝ) 1) where
  toFun x :=
    (⟨(1 - vertexHeight K p ⟨x.val, x.prop.1.1⟩)⁻¹ •
        (x.val - vertexHeight K p ⟨x.val, x.prop.1.1⟩ • p),
      vertex_normalization_mem_link K p hp x⟩,
      ⟨vertexHeight K p ⟨x.val, x.prop.1.1⟩,
        (vertexHeight_mem_Ioo_iff K p hp _).mpr x.prop⟩)
  continuous_toFun := by
    have hc : Continuous (fun x : puncturedVertexOpenStar K p ↦
        (⟨x.val, x.prop.1.1⟩ : K.space)) := continuous_subtype_val.subtype_mk _
    have hh := (vertexHeight K p).continuous.comp hc
    have hi : Continuous (fun x : puncturedVertexOpenStar K p ↦
        (1 - vertexHeight K p ⟨x.val, x.prop.1.1⟩)⁻¹) :=
      (continuous_const.sub hh).inv₀ (fun x ↦
        (sub_pos.mpr ((vertexHeight_mem_Ioo_iff K p hp _).mpr x.prop).2).ne')
    exact ((hi.smul (continuous_subtype_val.sub (hh.smul continuous_const))).subtype_mk _).prodMk
      (hh.subtype_mk _)

def vertexStarCone [Finite K.faces] (hp : {p} ∈ K.faces) :
    C((geometricLink K {p}).space × Ioo (0 : ℝ) 1, puncturedVertexOpenStar K p) where
  toFun z := ⟨z.2.val • p + (1 - z.2.val) • z.1.val,
    vertex_cone_mem_puncturedStar K p hp z.1 z.2⟩
  continuous_toFun :=
    (((continuous_subtype_val.comp continuous_snd).smul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (continuous_subtype_val.comp continuous_fst))).subtype_mk _


@[simp]
theorem vertexStarCoordinates_fst_val [Finite K.faces] (hp : {p} ∈ K.faces)
    (x : puncturedVertexOpenStar K p) :
    (vertexStarCoordinates K p hp x).1.val =
      (1 - vertexHeight K p ⟨x.val, x.prop.1.1⟩)⁻¹ •
        (x.val - vertexHeight K p ⟨x.val, x.prop.1.1⟩ • p) := rfl


@[simp]
theorem vertexStarCoordinates_snd_val [Finite K.faces] (hp : {p} ∈ K.faces)
    (x : puncturedVertexOpenStar K p) :
    (vertexStarCoordinates K p hp x).2.val = vertexHeight K p ⟨x.val, x.prop.1.1⟩ := rfl


@[simp]
theorem vertexStarCone_val [Finite K.faces] (hp : {p} ∈ K.faces)
    (z : (geometricLink K {p}).space × Ioo (0 : ℝ) 1) :
    (vertexStarCone K p hp z).val = z.2.val • p + (1 - z.2.val) • z.1.val := rfl


@[simp]
theorem vertexStarCone_coordinates [Finite K.faces] (hp : {p} ∈ K.faces)
    (x : puncturedVertexOpenStar K p) :
    vertexStarCone K p hp (vertexStarCoordinates K p hp x) = x := by
  apply Subtype.ext
  let h := vertexHeight K p ⟨x.val, x.prop.1.1⟩
  have hh : 1 - h ≠ 0 :=
    (sub_pos.mpr ((vertexHeight_mem_Ioo_iff K p hp _).mpr x.prop).2).ne'
  change h • p + (1 - h) • ((1 - h)⁻¹ • (x.val - h • p)) = x.val
  rw [smul_smul, mul_inv_cancel₀ hh, one_smul, add_sub_cancel]


@[simp]
theorem vertexStarCoordinates_cone [Finite K.faces] (hp : {p} ∈ K.faces)
    (z : (geometricLink K {p}).space × Ioo (0 : ℝ) 1) :
    vertexStarCoordinates K p hp (vertexStarCone K p hp z) = z := by
  apply Prod.ext
  · apply Subtype.ext
    change (1 - vertexHeight K p ⟨z.2.val • p + (1 - z.2.val) • z.1.val, _⟩)⁻¹ •
      (z.2.val • p + (1 - z.2.val) • z.1.val -
        vertexHeight K p ⟨z.2.val • p + (1 - z.2.val) • z.1.val, _⟩ • p) = z.1.val
    rw [vertexHeight_cone K p hp, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ (sub_pos.mpr z.2.prop.2).ne', one_smul]
  · apply Subtype.ext
    exact vertexHeight_cone K p hp z.1 z.2

def puncturedVertexStarHomeomorphism [Finite K.faces] (hp : {p} ∈ K.faces) :
    puncturedVertexOpenStar K p ≃ₜ (geometricLink K {p}).space × Ioo (0 : ℝ) 1 where
  toFun := vertexStarCoordinates K p hp
  invFun := vertexStarCone K p hp
  left_inv := vertexStarCone_coordinates K p hp
  right_inv := vertexStarCoordinates_cone K p hp
  continuous_toFun := (vertexStarCoordinates K p hp).continuous
  continuous_invFun := (vertexStarCone K p hp).continuous


@[simp]
theorem puncturedVertexStarHomeomorphism_apply [Finite K.faces] (hp : {p} ∈ K.faces)
    (x : puncturedVertexOpenStar K p) :
    puncturedVertexStarHomeomorphism K p hp x = vertexStarCoordinates K p hp x := rfl


@[simp]
theorem puncturedVertexStarHomeomorphism_symm_apply [Finite K.faces] (hp : {p} ∈ K.faces)
    (z : (geometricLink K {p}).space × Ioo (0 : ℝ) 1) :
    (puncturedVertexStarHomeomorphism K p hp).symm z = vertexStarCone K p hp z := rfl


theorem isOpen_vertexOpenStar [Finite K.faces] :
    IsOpen ((Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p) := by
  have he : (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p =
      (vertexHeight K p) ⁻¹' Ioi (0 : ℝ) := by
    ext x
    exact (vertexHeight_pos_iff K p x).symm
  rw [he]
  exact isOpen_Ioi.preimage (vertexHeight K p).continuous


theorem isOpen_puncturedVertexOpenStar [Finite K.faces] :
    IsOpen ((Subtype.val : K.space → E) ⁻¹' puncturedVertexOpenStar K p) :=
  (isOpen_vertexOpenStar K p).inter
    ((isClosed_singleton.preimage continuous_subtype_val).isOpen_compl)

theorem isEmpty_puncturedVertexOpenStar_iff [Finite K.faces] (hp : {p} ∈ K.faces) :
    IsEmpty (puncturedVertexOpenStar K p) ↔ IsEmpty (geometricLink K {p}).space := by
  constructor
  · intro h
    exact ⟨fun y ↦ h.false (vertexStarCone K p hp (y, ⟨1 / 2, by constructor <;> norm_num⟩))⟩
  · intro h
    exact ⟨fun x ↦ h.false (vertexStarCoordinates K p hp x).1⟩

end DifferentialGeometry.Topology.SimplicialComplex
