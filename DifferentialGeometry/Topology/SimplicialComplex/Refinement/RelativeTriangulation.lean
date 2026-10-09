import DifferentialGeometry.Topology.SimplicialComplex.Expansion.PrincipalFaces
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricCoverage
import DifferentialGeometry.Topology.SimplicialComplex.Stellar.StellarEdgeWeights
import Mathlib.Analysis.Convex.Join

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry
open scoped BigOperators

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

def hasSupportingCone (B : SimplicialComplex ℝ E) (c : E) : Prop :=
  ∀ s ∈ B.faces, ∃ A : E →ᵃ[ℝ] ℝ, A c = 1 ∧
    (∀ x ∈ convexHull ℝ (s : Set E), A x = 0) ∧ (∀ x ∈ B.space, 0 ≤ A x)

omit [DecidableEq E] in
private theorem affine_apply_combo (A : E →ᵃ[ℝ] ℝ) (c x : E)
    {a b : ℝ} (hab : a + b = 1) :
    A (a • c + b • x) = a * A c + b * A x := by
  classical
  have ha : a = 1 - b := by linarith
  subst a
  simpa only [AffineMap.lineMap_apply_module, smul_eq_mul] using A.apply_lineMap c x b

omit [DecidableEq E] in
private theorem mem_hull_insert_coordinates {s : Finset E} (hs : s.Nonempty) (c x : E)
    (hx : x ∈ convexHull ℝ (insert c s : Set E)) :
    ∃ y ∈ convexHull ℝ (s : Set E), ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • c + b • y = x := by
  classical
  rw [convexHull_insert (show (s : Set E).Nonempty from hs), convexJoin_singleton_left] at hx
  obtain ⟨y, hy, a, b, ha, hb, hab, he⟩ := mem_iUnion₂.mp hx
  exact ⟨y, hy, a, b, ha, hb, hab, he⟩

namespace hasSupportingCone

variable {B : SimplicialComplex ℝ E} {c : E} (h : hasSupportingCone B c)
include h

omit [DecidableEq E] in
theorem not_mem_space : c ∉ B.space := by
  classical
  intro hc
  obtain ⟨s, hs, hcs⟩ := SimplicialComplex.mem_space_iff.mp hc
  obtain ⟨A, hAc, hAs, -⟩ := h s hs
  have := hAs c hcs
  rw [hAc] at this
  norm_num at this

omit [DecidableEq E] in
theorem not_mem_face {s : Finset E} (hs : s ∈ B.faces) : c ∉ s := by
  classical
  exact fun hc => h.not_mem_space (B.subset_space hs hc)

omit [DecidableEq E] in
private theorem radial_unique {x y : E} (hx : x ∈ B.space) (hy : y ∈ B.space)
    {a b a' b' : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (_ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' + b' = 1)
    (he : a • c + b • x = a' • c + b' • y) :
    a = a' ∧ b = b' ∧ (b = 0 ∨ x = y) := by
  classical
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨t, ht, hyt⟩ := SimplicialComplex.mem_space_iff.mp hy
  obtain ⟨A, hAc, hAs, hApos⟩ := h s hs
  obtain ⟨D, hDc, hDt, hDpos⟩ := h t ht
  have hAe := congrArg A he
  have hDe := congrArg D he
  rw [affine_apply_combo A c x hab, affine_apply_combo A c y hab', hAc, hAs x hxs] at hAe
  rw [affine_apply_combo D c x hab, affine_apply_combo D c y hab', hDc, hDt y hyt] at hDe
  have haa : a = a' := by nlinarith [mul_nonneg hb (hDpos x hx), mul_nonneg hb' (hApos y hy)]
  have hbb : b = b' := by linarith
  refine ⟨haa, hbb, ?_⟩
  by_cases hb0 : b = 0
  · exact Or.inl hb0
  · right
    rw [← haa, ← hbb] at he
    exact (smul_right_injective E hb0) (add_left_cancel he)

omit [DecidableEq E] in
theorem hull_insert_inter_space {s : Finset E} (hs : s ∈ B.faces) :
    convexHull ℝ (insert c s : Set E) ∩ B.space = convexHull ℝ (s : Set E) := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hx, hxB⟩
    obtain ⟨y, hy, a, b, ha, hb, hab, he⟩ :=
      mem_hull_insert_coordinates (B.nonempty_of_mem_faces hs) c x hx
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxB
    obtain ⟨A, hAc, hAt, hApos⟩ := h t ht
    have hAe := congrArg A he
    rw [affine_apply_combo A c y hab, hAc, hAt x hxt] at hAe
    have ha0 : a = 0 := by nlinarith [mul_nonneg hb (hApos y (B.convexHull_subset_space hs hy))]
    have hb1 : b = 1 := by linarith
    have he' : y = x := by simpa [ha0, hb1] using he
    exact he' ▸ hy
  · intro x hx
    exact ⟨convexHull_mono (by simp) hx, B.convexHull_subset_space hs hx⟩

omit [DecidableEq E] in
theorem hull_insert_inter_hull_insert {s t : Finset E} (hs : s ∈ B.faces)
    (ht : t ∈ B.faces) :
    convexHull ℝ (insert c s : Set E) ∩ convexHull ℝ (insert c t : Set E) =
      convexHull ℝ (insert c ((s : Set E) ∩ (t : Set E))) := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hx, hx'⟩
    obtain ⟨y, hy, a, b, ha, hb, hab, he⟩ :=
      mem_hull_insert_coordinates (B.nonempty_of_mem_faces hs) c x hx
    obtain ⟨z, hz, a', b', ha', hb', hab', he'⟩ :=
      mem_hull_insert_coordinates (B.nonempty_of_mem_faces ht) c x hx'
    obtain ⟨haa, hbb, hb0 | hyz⟩ := h.radial_unique
      (B.convexHull_subset_space hs hy) (B.convexHull_subset_space ht hz)
      ha hb hab ha' hb' hab' (he.trans he'.symm)
    · have ha1 : a = 1 := by linarith
      have hxc : x = c := by simpa [ha1, hb0] using he.symm
      rw [hxc]
      exact subset_convexHull ℝ _ (mem_insert _ _)
    · have hyi := B.inter_subset_convexHull hs ht ⟨hy, hyz ▸ hz⟩
      rw [← he]
      exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ (mem_insert _ _))
        (convexHull_mono (subset_insert _ _) hyi) ha hb hab
  · intro x hx
    exact ⟨convexHull_mono (insert_subset_insert inter_subset_left) hx,
      convexHull_mono (insert_subset_insert inter_subset_right) hx⟩

theorem independent_insert {s : Finset E} (hs : s ∈ B.faces) :
    AffineIndependent ℝ ((↑) : ↥(insert c s : Finset E) → E) := by
  let i : (insert c s : Finset E) := ⟨c, Finset.mem_insert_self _ _⟩
  let e : {z : (insert c s : Finset E) // z ≠ i} ↪ s :=
    { toFun := fun z => ⟨z.val.val, (Finset.mem_insert.mp z.val.property).resolve_left
        (fun he => z.property (Subtype.ext he))⟩
      inj' := fun x y he => Subtype.ext (Subtype.ext (show x.val.val = y.val.val from congrArg (fun z : s => z.val) he)) }
  have hind : AffineIndependent ℝ (fun z : {z : (insert c s : Finset E) // z ≠ i} => z.val.val) :=
    (B.indep hs).comp_embedding e
  apply hind.affineIndependent_of_notMem_span
  obtain ⟨A, hAc, hAs, -⟩ := h s hs
  intro hc
  have hzero : EqOn A (AffineMap.const ℝ E (0 : ℝ))
      (Subtype.val '' {z : (insert c s : Finset E) | z ≠ i}) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hAs z.val (subset_convexHull ℝ _
      ((Finset.mem_insert.mp z.property).resolve_left (fun he => hz (Subtype.ext he))))
  have he := AffineMap.eqOn_affineSpan hzero hc
  change A c = 0 at he
  rw [hAc] at he
  norm_num at he

def complex : SimplicialComplex ℝ E where
  faces := B.faces ∪ {s | s = {c}} ∪ {s | ∃ t ∈ B.faces, s = insert c t}
  isRelLowerSet_faces := by
    rintro s ((hs | rfl) | ⟨t, ht, rfl⟩)
    · exact ⟨B.nonempty_of_mem_faces hs, fun u hus hu => Or.inl (Or.inl (B.down_closed hs hus hu))⟩
    · refine ⟨Finset.singleton_nonempty _, fun u hus hu => Or.inl (Or.inr ?_)⟩
      exact Finset.eq_singleton_iff_unique_mem.mpr ⟨by obtain ⟨y, hy⟩ := hu; simpa [Finset.mem_singleton.mp (hus hy)] using hy,
        fun y hy => Finset.mem_singleton.mp (hus hy)⟩
    · refine ⟨Finset.insert_nonempty _ _, ?_⟩
      intro u hus hu
      by_cases hcu : c ∈ u
      · by_cases he : u.erase c = ∅
        · exact Or.inl (Or.inr (by simpa [he] using (Finset.insert_erase hcu).symm))
        · refine Or.inr ⟨u.erase c, B.down_closed ht ?_
            (Finset.nonempty_iff_ne_empty.mpr he), (Finset.insert_erase hcu).symm⟩
          intro x hx
          exact (Finset.mem_insert.mp (hus (Finset.mem_of_mem_erase hx))).resolve_left
            (Finset.ne_of_mem_erase hx)
      · refine Or.inl (Or.inl (B.down_closed ht ?_ hu))
        intro x hx
        exact (Finset.mem_insert.mp (hus hx)).resolve_left (fun he => hcu (he ▸ hx))
  indep := by
    rintro s ((hs | rfl) | ⟨t, ht, rfl⟩)
    · exact B.indep hs
    · exact affineIndependent_of_subsingleton ℝ _
    · exact h.independent_insert ht
  inter_subset_convexHull := by
    rintro s t ((hs | rfl) | ⟨s, hs, rfl⟩) ((ht | rfl) | ⟨t, ht, rfl⟩) x hx
    · exact B.inter_subset_convexHull hs ht hx
    · have he : x = c := by simpa using hx.2
      exact (h.not_mem_space (he ▸ B.convexHull_subset_space hs hx.1)).elim
    · have hxt : x ∈ convexHull ℝ (t : Set E) := by
        apply (h.hull_insert_inter_space ht).subset
        exact ⟨by simpa only [Finset.coe_insert] using hx.2, B.convexHull_subset_space hs hx.1⟩
      exact convexHull_mono (by intro y hy; exact ⟨hy.1, Finset.mem_insert_of_mem hy.2⟩)
        (B.inter_subset_convexHull hs ht ⟨hx.1, hxt⟩)
    · have he : x = c := by simpa using hx.1
      exact (h.not_mem_space (he ▸ B.convexHull_subset_space ht hx.2)).elim
    · simpa using hx.1
    · have he : x = c := by simpa using hx.1
      rw [he]
      exact subset_convexHull ℝ _ ⟨by simp, by simp⟩
    · have hxs : x ∈ convexHull ℝ (s : Set E) := by
        apply (h.hull_insert_inter_space hs).subset
        exact ⟨by simpa only [Finset.coe_insert] using hx.1, B.convexHull_subset_space ht hx.2⟩
      exact convexHull_mono (by intro y hy; exact ⟨Finset.mem_insert_of_mem hy.1, hy.2⟩)
        (B.inter_subset_convexHull hs ht ⟨hxs, hx.2⟩)
    · have he : x = c := by simpa using hx.2
      rw [he]
      exact subset_convexHull ℝ _ ⟨by simp, by simp⟩
    · have hm := (h.hull_insert_inter_hull_insert hs ht).subset
        (by simpa only [Finset.coe_insert] using hx)
      exact convexHull_mono (by
        intro y hy
        rcases hy with rfl | hy
        · exact ⟨by simp, by simp⟩
        · exact ⟨Finset.mem_insert_of_mem hy.1, Finset.mem_insert_of_mem hy.2⟩) hm

theorem old_faces_subset : B.faces ⊆ h.complex.faces := fun _ hs => Or.inl (Or.inl hs)

theorem finite_faces (hB : B.faces.Finite) : h.complex.faces.Finite := by
  have hi : {s | ∃ t ∈ B.faces, s = insert c t} = (fun t => insert c t) '' B.faces := by
    ext s
    simp only [mem_ofPred_eq, mem_image]
    constructor <;> rintro ⟨t, ht, he⟩ <;> exact ⟨t, ht, he.symm⟩
  change (B.faces ∪ {s | s = {c}} ∪ {s | ∃ t ∈ B.faces, s = insert c t}).Finite
  rw [hi]
  exact (hB.union (finite_singleton _)).union (hB.image _)

theorem hull_face_inter_space {s : Finset E} (hs : s ∈ h.complex.faces) :
    ∃ t ⊆ s, (t ∈ B.faces ∨ t = ∅) ∧
      convexHull ℝ (s : Set E) ∩ B.space = convexHull ℝ (t : Set E) := by
  rcases hs with (hs | rfl) | ⟨t, ht, rfl⟩
  · exact ⟨s, subset_rfl, Or.inl hs, inter_eq_left.mpr (B.convexHull_subset_space hs)⟩
  · refine ⟨∅, Finset.empty_subset _, Or.inr rfl, ?_⟩
    simp only [Finset.coe_singleton, convexHull_singleton, Finset.coe_empty, convexHull_empty]
    exact disjoint_iff_inter_eq_empty.mp (disjoint_singleton_left.mpr h.not_mem_space)
  · exact ⟨t, Finset.subset_insert _ _, Or.inl ht,
      by simpa only [Finset.coe_insert] using h.hull_insert_inter_space ht⟩

end hasSupportingCone

theorem exists_centroid_facet_support (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) {i : E} (hi : i ∈ V) :
    ∃ A : E →ᵃ[ℝ] ℝ, A (V.centroid ℝ id) = 1 ∧
      (∀ x ∈ convexHull ℝ (V.erase i : Set E), A x = 0) ∧
      (∀ x ∈ convexHull ℝ (V : Set E), 0 ≤ A x) := by
  obtain ⟨A, hA⟩ := exists_affineMap_of_affineIndependent hV
    (fun x => if x = i then (V.card : ℝ) else 0)
  have hcard : (V.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne'
  refine ⟨A, ?_, ?_, ?_⟩
  · rw [Finset.centroid_def, Finset.map_affineCombination _ _ _
      (V.sum_centroidWeights_eq_one_of_nonempty ℝ ⟨i, hi⟩),
      Finset.affineCombination_eq_linear_combination _ _ _
        (V.sum_centroidWeights_eq_one_of_nonempty ℝ ⟨i, hi⟩)]
    calc
      (∑ x ∈ V, V.centroidWeights ℝ x • A (id x)) =
          ∑ x ∈ V, (V.card : ℝ)⁻¹ * (if x = i then (V.card : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [id_eq, hA x hx]
        rfl
      _ = 1 := by simp [mul_ite, hi, hcard]
  · intro x hx
    apply convexHull_min _ ((convex_singleton (0 : ℝ)).affine_preimage A) hx
    intro v hv
    change A v = 0
    rw [hA v (Finset.mem_of_mem_erase hv)]
    simp [Finset.ne_of_mem_erase hv]
  · intro x hx
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage A) hx
    intro v hv
    change 0 ≤ A v
    rw [hA v hv]
    split_ifs <;> positivity

theorem hasSupportingCone_centroid (B : SimplicialComplex ℝ E) (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E))
    (hparents : ∀ s ∈ B.faces, ∃ i ∈ V,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V.erase i : Set E)) :
    hasSupportingCone B (V.centroid ℝ id) := by
  intro s hs
  obtain ⟨i, hi, hsi⟩ := hparents s hs
  obtain ⟨A, hAc, hA0, hApos⟩ := exists_centroid_facet_support V hV hi
  refine ⟨A, hAc, fun x hx => hA0 x (hsi hx), ?_⟩
  intro x hx
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨j, hj, htj⟩ := hparents t ht
  exact hApos x (convexHull_mono (Finset.erase_subset _ _) (htj hxt))

def boundaryConeComplex (B : SimplicialComplex ℝ E) (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E))
    (hparents : ∀ s ∈ B.faces, ∃ i ∈ V,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V.erase i : Set E)) :
    SimplicialComplex ℝ E := (hasSupportingCone_centroid B V hV hparents).complex

theorem exists_centroid_boundary_segment (V : Finset E) (hVne : V.Nonempty) {x : E}
    (hx : x ∈ convexHull ℝ (V : Set E)) :
    x = V.centroid ℝ id ∨ ∃ y ∈ finiteSimplexBoundary V, ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • V.centroid ℝ id + b • y = x := by
  obtain ⟨w, hw, hsum, hpoint⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨i, hi, hmin⟩ := V.exists_min_image w hVne
  let c := w i
  let a : ℝ := (V.card : ℝ) * c
  have hc : 0 ≤ c := hw i hi
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hc
  have ha1 : a ≤ 1 := by
    calc
      a = ∑ j ∈ V, c := by simp [a]
      _ ≤ ∑ j ∈ V, w j := Finset.sum_le_sum (fun j hj => hmin j hj)
      _ = 1 := hsum
  have hcard : (V.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hVne).ne'
  have hcent : a • V.centroid ℝ id = ∑ j ∈ V, c • j := by
    rw [centroid_eq_card_inv_smul_sum V hVne id, smul_smul, ← Finset.smul_sum]
    congr 1
    dsimp [a]
    field_simp
  have hres : ∑ j ∈ V, (w j - c) = 1 - a := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul]
  have hsplit : x = a • V.centroid ℝ id + ∑ j ∈ V, (w j - c) • j := by
    rw [← hpoint, hcent, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← add_smul]
    congr 1
    ring
  by_cases hae : a = 1
  · left
    have hzero : ∀ j ∈ V, w j - c = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sub_nonneg.mpr (hmin j hj))).mp
        (by simpa [hae] using hres)
    rw [hsplit, hae, one_smul]
    have hz : ∑ j ∈ V, (w j - c) • j = 0 := Finset.sum_eq_zero
      (fun j hj => by rw [hzero j hj, zero_smul])
    rw [hz, add_zero]
  · right
    have hpos : 0 < 1 - a := sub_pos.mpr (lt_of_le_of_ne ha1 hae)
    let z : E → ℝ := fun j => (w j - c) / (1 - a)
    have hz : ∀ j ∈ V.erase i, 0 ≤ z j := fun j hj =>
      div_nonneg (sub_nonneg.mpr (hmin j (Finset.mem_of_mem_erase hj))) hpos.le
    have hzsum : ∑ j ∈ V.erase i, z j = 1 := by
      dsimp [z]
      rw [← Finset.sum_div, Finset.sum_erase_eq_sub hi, hres]
      simp only [c, sub_self, sub_zero]
      exact div_self hpos.ne'
    let y : E := ∑ j ∈ V.erase i, z j • j
    have hy : y ∈ convexHull ℝ (V.erase i : Set E) :=
      Finset.mem_convexHull'.mpr ⟨z, hz, hzsum, rfl⟩
    refine ⟨y, mem_iUnion₂.mpr ⟨i, hi, hy⟩, a, 1 - a, ha, hpos.le, by ring, ?_⟩
    have hresvec : (1 - a) • y = ∑ j ∈ V, (w j - c) • j := by
      rw [Finset.smul_sum]
      simp_rw [smul_smul]
      have hterm (j : E) : (1 - a) * z j = w j - c := by
        dsimp [z]
        field_simp
      simp_rw [hterm]
      rw [Finset.sum_erase_eq_sub hi]
      simp [c]
    rw [hresvec, ← hsplit]

namespace boundaryConeComplex

variable (B : SimplicialComplex ℝ E) (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E))
    (hparents : ∀ s ∈ B.faces, ∃ i ∈ V,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V.erase i : Set E))
theorem finite_faces (hB : B.faces.Finite) :
    (boundaryConeComplex B V hV hparents).faces.Finite :=
  (hasSupportingCone_centroid B V hV hparents).finite_faces hB
theorem old_faces_subset : B.faces ⊆ (boundaryConeComplex B V hV hparents).faces :=
  (hasSupportingCone_centroid B V hV hparents).old_faces_subset
theorem space (hVne : V.Nonempty) (hBspace : B.space = finiteSimplexBoundary V) :
    (boundaryConeComplex B V hV hparents).space = convexHull ℝ (V : Set E) := by
  let C := boundaryConeComplex B V hV hparents
  have hBsub : B.space ⊆ convexHull ℝ (V : Set E) := by
    intro x hx
    rw [hBspace] at hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact convexHull_mono (Finset.erase_subset _ _) hxi
  have hc : V.centroid ℝ id ∈ convexHull ℝ (V : Set E) := V.centroid_mem_convexHull hVne
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, (hs | rfl) | ⟨t, ht, rfl⟩, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    · exact hBsub (B.convexHull_subset_space hs hxs)
    · have he : x = V.centroid ℝ id := by simpa using hxs
      exact he.symm ▸ hc
    · apply convexHull_min _ (convex_convexHull ℝ (V : Set E)) hxs
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hc
      · exact hBsub (B.subset_space ht hy)
  · intro x hx
    rcases exists_centroid_boundary_segment V hVne hx with rfl | ⟨y, hy, a, b, ha, hb, hab, he⟩
    · exact C.subset_space (Or.inl (Or.inr rfl)) (Finset.mem_singleton_self _)
    · obtain ⟨s, hs, hys⟩ := SimplicialComplex.mem_space_iff.mp (hBspace.symm ▸ hy)
      apply C.convexHull_subset_space (Or.inr ⟨s, hs, rfl⟩)
      rw [← he]
      exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))
        (convexHull_mono (Finset.subset_insert _ _) hys) ha hb hab
theorem face_card_le (hVne : V.Nonempty) (hBspace : B.space = finiteSimplexBoundary V) :
    ∀ s ∈ (boundaryConeComplex B V hV hparents).faces, s.card ≤ V.card := by
  intro s hs
  apply ((boundaryConeComplex B V hV hparents).indep hs).card_le_card_of_subset_affineSpan
  intro x hx
  apply convexHull_subset_affineSpan
  rw [← space B V hV hparents hVne hBspace]
  exact (boundaryConeComplex B V hV hparents).subset_space hs hx
theorem hull_face_inter_boundary (hBspace : B.space = finiteSimplexBoundary V)
    {s : Finset E} (hs : s ∈ (boundaryConeComplex B V hV hparents).faces) :
    ∃ t ⊆ s, (t ∈ B.faces ∨ t = ∅) ∧
      convexHull ℝ (s : Set E) ∩ finiteSimplexBoundary V = convexHull ℝ (t : Set E) := by
  rw [← hBspace]
  exact (hasSupportingCone_centroid B V hV hparents).hull_face_inter_space hs

end boundaryConeComplex

theorem exists_cone_triangulation_of_boundary (B : SimplicialComplex ℝ E)
    (hB : B.faces.Finite) (V : Finset E) (hVne : V.Nonempty)
    (hV : AffineIndependent ℝ ((↑) : V → E))
    (hparents : ∀ s ∈ B.faces, ∃ i ∈ V,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V.erase i : Set E))
    (hBspace : B.space = finiteSimplexBoundary V) :
    ∃ C : SimplicialComplex ℝ E, C.faces.Finite ∧ C.space = convexHull ℝ (V : Set E) ∧
      (∀ s ∈ C.faces, s.card ≤ V.card) ∧
      (∀ s ∈ C.faces, ∃ t ⊆ s, (t ∈ B.faces ∨ t = ∅) ∧
        convexHull ℝ (s : Set E) ∩ finiteSimplexBoundary V = convexHull ℝ (t : Set E)) :=
  ⟨boundaryConeComplex B V hV hparents, boundaryConeComplex.finite_faces B V hV hparents hB,
    boundaryConeComplex.space B V hV hparents hVne hBspace,
    boundaryConeComplex.face_card_le B V hV hparents hVne hBspace,
    fun _ hs => boundaryConeComplex.hull_face_inter_boundary B V hV hparents hBspace hs⟩

end
end DifferentialGeometry.Topology.Engulfing
