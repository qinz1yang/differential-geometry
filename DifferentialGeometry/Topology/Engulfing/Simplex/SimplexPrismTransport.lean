import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexPrism
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology
open scoped BigOperators

noncomputable section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def simplexAffineBasis (v : ι → E) (hv : AffineIndependent ℝ v) :
    AffineBasis ι ℝ (affineSpan ℝ (range v)) where
  toFun i := ⟨v i, mem_affineSpan ℝ (mem_range_self i)⟩
  ind' := hv.of_comp (affineSpan ℝ (range v)).subtype
  tot' := by
    convert affineSpan_coe_preimage_eq_top (k := ℝ) (range v) using 1
    congr 1
    ext x
    change (∃ i, (⟨v i, _⟩ : affineSpan ℝ (range v)) = x) ↔ ∃ i, v i = x.val
    exact ⟨fun ⟨i, hi⟩ => ⟨i, congrArg Subtype.val hi⟩,
      fun ⟨i, hi⟩ => ⟨i, Subtype.ext hi⟩⟩

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] in
@[simp] theorem simplexAffineBasis_coe (v : ι → E) (hv : AffineIndependent ℝ v) (i : ι) :
    ((simplexAffineBasis v hv i : affineSpan ℝ (range v)) : E) = v i := rfl

def simplexPoint (v : ι → E) (w : ι → ℝ) : E := ∑ i, w i • v i

omit [DecidableEq ι] [Nonempty ι] [FiniteDimensional ℝ E] in
theorem continuous_simplexPoint (v : ι → E) : Continuous (simplexPoint v) := by
  unfold simplexPoint
  fun_prop

omit [DecidableEq ι] [Nonempty ι] [FiniteDimensional ℝ E] in
theorem simplexPoint_mem_affineSpan (v : ι → E) {w : ι → ℝ}
    (hw : ∑ i, w i = 1) : simplexPoint v w ∈ affineSpan ℝ (range v) := by
  rw [simplexPoint, ← Finset.affineCombination_eq_linear_combination _ _ _ hw]
  exact affineCombination_mem_affineSpan hw v

def simplexBarycentricHomeomorph (v : ι → E) (hv : AffineIndependent ℝ v) :
    affineSpan ℝ (range v) ≃ₜ barycentricHyperplane ι where
  toFun x := ⟨fun i => (simplexAffineBasis v hv).coord i x,
    (simplexAffineBasis v hv).sum_coord_apply_eq_one x⟩
  invFun w := ⟨simplexPoint v w, simplexPoint_mem_affineSpan v w.property⟩
  left_inv x := by
    apply Subtype.ext
    have h := congrArg Subtype.val ((simplexAffineBasis v hv).affineCombination_coord_eq_self x)
    have hm := Finset.univ.map_affineCombination (simplexAffineBasis v hv)
      (fun i => (simplexAffineBasis v hv).coord i x)
      ((simplexAffineBasis v hv).sum_coord_apply_eq_one x) (affineSpan ℝ (range v)).subtype
    rw [Finset.affineCombination_eq_linear_combination _ _ _
      ((simplexAffineBasis v hv).sum_coord_apply_eq_one x)] at hm
    exact hm.symm.trans h
  right_inv w := by
    apply Subtype.ext
    funext i
    have h := (simplexAffineBasis v hv).coord_apply_combination_of_mem
      (Finset.mem_univ i) w.property
    convert h using 2
    apply Subtype.ext
    have hm := Finset.univ.map_affineCombination (simplexAffineBasis v hv)
      w.val w.property (affineSpan ℝ (range v)).subtype
    rw [Finset.affineCombination_eq_linear_combination _ _ _ w.property] at hm
    exact hm.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i => ((simplexAffineBasis v hv).coord i).continuous_of_finiteDimensional)
  continuous_invFun := (continuous_simplexPoint v).comp continuous_subtype_val |>.subtype_mk _

def affineSubspaceProductHomeomorph (S : AffineSubspace ℝ E) (p : S) :
    E ≃ₜ S.directionᗮ × S :=
  letI : Nonempty S := ⟨p⟩
  (Homeomorph.subRight (p : E)).trans
    (((S.directionᗮ.prodEquivOfIsCompl S.direction S.direction.isCompl_orthogonal.symm).toContinuousLinearEquiv).toHomeomorph.symm.trans
      ((Homeomorph.refl _).prodCongr
        (AffineEquiv.toContinuousAffineEquiv (AffineEquiv.vaddConst ℝ p)).toHomeomorph))

theorem affineSubspaceProductHomeomorph_symm_apply (S : AffineSubspace ℝ E) (p : S)
    (z : S.directionᗮ × S) :
    (affineSubspaceProductHomeomorph S p).symm z = (z.1 : E) + (z.2 : E) := by
  change (z.1.val + (z.2.val - p.val)) + p.val = _
  abel

theorem affineSubspaceProductHomeomorph_apply_mem (S : AffineSubspace ℝ E) (p x : S) :
    affineSubspaceProductHomeomorph S p x = (0, x) := by
  apply (affineSubspaceProductHomeomorph S p).symm.injective
  rw [Homeomorph.symm_apply_apply, affineSubspaceProductHomeomorph_symm_apply]
  simp

abbrev simplexTransverse (v : ι → E) := (affineSpan ℝ (range v)).directionᗮ

def SimplexSplit.ambientPrismCoordinates (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) : E ≃ₜ simplexTransverse v × (s.horizontal × ℝ) :=
  (affineSubspaceProductHomeomorph (affineSpan ℝ (range v))
    (simplexAffineBasis v hv (Classical.choice inferInstance))).trans
    ((Homeomorph.refl _).prodCongr ((simplexBarycentricHomeomorph v hv).trans s.prismCoordinates))

theorem SimplexSplit.ambientPrismCoordinates_symm_apply (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (p : simplexTransverse v × (s.horizontal × ℝ)) :
    (s.ambientPrismCoordinates v hv).symm p =
      (p.1 : E) + simplexPoint v (s.fiberPoint p.2.1 p.2.2) :=
  affineSubspaceProductHomeomorph_symm_apply _ _ _

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
theorem simplexPoint_injective_on_hyperplane (v : ι → E) (hv : AffineIndependent ℝ v) :
    InjOn (simplexPoint v) (barycentricHyperplane ι) := by
  intro x hx y hy hxy
  have h : (simplexBarycentricHomeomorph v hv).symm ⟨x, hx⟩ =
      (simplexBarycentricHomeomorph v hv).symm ⟨y, hy⟩ := Subtype.ext hxy
  exact congrArg Subtype.val ((simplexBarycentricHomeomorph v hv).symm.injective h)

omit [Nonempty ι] [DecidableEq ι] in
private theorem convex_standardBarycentricSimplex :
    Convex ℝ (standardBarycentricSimplex ι) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

omit [Nonempty ι] [FiniteDimensional ℝ E] in
omit [DecidableEq ι] in
theorem simplexPoint_image_simplex (v : ι → E) :
    simplexPoint v '' standardBarycentricSimplex ι = convexHull ℝ (range v) := by
  classical
  apply Subset.antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have h := Finset.univ.centerMass_mem_convexHull (fun i _ => hw.1 i)
      (by rw [hw.2]; norm_num) (fun i _ => (mem_range_self i : v i ∈ range v))
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw.2] at h
    exact h
  · apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, ⟨?_, by simp⟩, ?_⟩
      · intro j
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · simp [simplexPoint]
    · exact convex_standardBarycentricSimplex.linear_image (Fintype.linearCombination ℝ v)

omit [FiniteDimensional ℝ E] in
omit [DecidableEq ι] in
theorem simplexPoint_mem_convexHull_iff (v : ι → E) (hv : AffineIndependent ℝ v)
    {w : ι → ℝ} (hw : ∑ i, w i = 1) :
    simplexPoint v w ∈ convexHull ℝ (range v) ↔ w ∈ standardBarycentricSimplex ι := by
  classical
  rw [← simplexPoint_image_simplex v]
  constructor
  · rintro ⟨z, hz, he⟩
    have he' := simplexPoint_injective_on_hyperplane v hv hz.2 hw he
    exact he' ▸ hz
  · intro h
    exact mem_image_of_mem _ h

theorem SimplexSplit.ambientPrismCoordinates_simplex_iff (s : SimplexSplit ι)
    (v : ι → E) (hv : AffineIndependent ℝ v) (x : E) :
    x ∈ convexHull ℝ (range v) ↔
      (s.ambientPrismCoordinates v hv x).1 = 0 ∧
      (s.ambientPrismCoordinates v hv x).2.2 ∈
        Icc (s.lower (s.ambientPrismCoordinates v hv x).2.1)
          (s.upper (s.ambientPrismCoordinates v hv x).2.1) := by
  let e := s.ambientPrismCoordinates v hv
  have hspan : convexHull ℝ (range v) ⊆ affineSpan ℝ (range v) :=
    convexHull_subset_affineSpan _
  constructor
  · intro hx
    let y : affineSpan ℝ (range v) := ⟨x, hspan hx⟩
    have he : e x = (0, s.prismCoordinates (simplexBarycentricHomeomorph v hv y)) := by
      have hy := affineSubspaceProductHomeomorph_apply_mem (affineSpan ℝ (range v))
        (simplexAffineBasis v hv (Classical.choice inferInstance)) y
      change ((Homeomorph.refl _).prodCongr _)
        (affineSubspaceProductHomeomorph (affineSpan ℝ (range v)) _ (x : E)) = _
      rw [hy]
      rfl
    rw [he]
    refine ⟨rfl, (s.prismCoordinates_simplex_iff _).mp ?_⟩
    apply (simplexPoint_mem_convexHull_iff v hv
      (simplexBarycentricHomeomorph v hv y).property).mp
    have hh := congrArg Subtype.val ((simplexBarycentricHomeomorph v hv).symm_apply_apply y)
    change simplexPoint v _ = x at hh
    rwa [hh]
  · rintro ⟨hzero, ht⟩
    have hh := s.ambientPrismCoordinates_symm_apply v hv (e x)
    rw [e.symm_apply_apply, hzero] at hh
    simp only [Submodule.coe_zero, zero_add] at hh
    rw [hh]
    exact (simplexPoint_mem_convexHull_iff v hv (s.sum_fiberPoint _ _ |>.trans
      (e x).2.1.property.1)).mpr ((s.fiberPoint_mem_simplex_iff _ _).mpr
        ⟨(e x).2.1.property.1, ht⟩)

def barycentricFace (J : Finset ι) : Set (ι → ℝ) :=
  {w | w ∈ standardBarycentricSimplex ι ∧ ∀ i ∉ J, w i = 0}

omit [Nonempty ι] in
theorem barycentricFace_eq_convexHull (J : Finset ι) :
    barycentricFace J = convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (J : Set ι)) := by
  apply Subset.antisymm
  · rintro w ⟨hw, hw0⟩
    have hsum : ∑ i ∈ J, w i = 1 := by
      rw [← hw.2]
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hw0 i hi)
    have h := J.centerMass_mem_convexHull (fun i _ => hw.1 i) (by rw [hsum]; norm_num)
      (fun i hi => mem_image_of_mem (fun i : ι => Pi.single i (1 : ℝ)) hi)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum] at h
    have he : (∑ i ∈ J, w i • Pi.single i (1 : ℝ)) = w := by
      rw [Finset.sum_subset (Finset.subset_univ J)
        (fun i _ hi => by rw [hw0 i hi, zero_smul])]
      ext i
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rwa [he] at h
  · apply convexHull_min
    · rintro w ⟨i, hi, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro j
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · simp
      · intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hj hi
        simp [hji]
    · intro x hx y hy a b ha hb hab
      refine ⟨convex_standardBarycentricSimplex hx.1 hy.1 ha hb hab, ?_⟩
      intro i hi
      simp [Pi.add_apply, Pi.smul_apply, hx.2 i hi, hy.2 i hi]

omit [Nonempty ι] [FiniteDimensional ℝ E] in
omit [DecidableEq ι] in
theorem simplexPoint_image_face (v : ι → E) (J : Finset ι) :
    simplexPoint v '' barycentricFace J = convexHull ℝ (v '' (J : Set ι)) := by
  classical
  rw [barycentricFace_eq_convexHull]
  change (Fintype.linearCombination ℝ v) '' _ = _
  rw [LinearMap.image_convexHull, ← image_comp]
  congr 2
  funext i
  simp [Fintype.linearCombination_apply]

omit [FiniteDimensional ℝ E] in
omit [DecidableEq ι] in
theorem simplexPoint_mem_face_iff (v : ι → E) (hv : AffineIndependent ℝ v)
    {w : ι → ℝ} (hw : ∑ i, w i = 1) (J : Finset ι) :
    simplexPoint v w ∈ convexHull ℝ (v '' (J : Set ι)) ↔ w ∈ barycentricFace J := by
  classical
  rw [← simplexPoint_image_face v J]
  constructor
  · rintro ⟨z, hz, he⟩
    have he' := simplexPoint_injective_on_hyperplane v hv hz.1.2 hw he
    exact he' ▸ hz
  · intro h
    exact mem_image_of_mem _ h

def simplexFacet (v : ι → E) (i : ι) : Set E :=
  convexHull ℝ (v '' ({i}ᶜ : Set ι))

omit [FiniteDimensional ℝ E] in
omit [DecidableEq ι] in
theorem simplexPoint_mem_facet_iff (v : ι → E) (hv : AffineIndependent ℝ v)
    {w : ι → ℝ} (hw : w ∈ standardBarycentricSimplex ι) (i : ι) :
    simplexPoint v w ∈ simplexFacet v i ↔ w i = 0 := by
  classical
  have h := simplexPoint_mem_face_iff v hv hw.2 (Finset.univ.erase i)
  simpa [simplexFacet, barycentricFace, hw, compl_eq_univ_sdiff] using h

theorem SimplexSplit.ambientPrismCoordinates_lower_graph_iff (s : SimplexSplit ι)
    (v : ι → E) (hv : AffineIndependent ℝ v) {x : E}
    (hx : x ∈ convexHull ℝ (range v)) :
    (s.ambientPrismCoordinates v hv x).2.2 =
      s.lower (s.ambientPrismCoordinates v hv x).2.1 ↔
      ∃ i ∈ s.right, x ∈ simplexFacet v i := by
  let e := s.ambientPrismCoordinates v hv
  obtain ⟨hzero, ht⟩ := (s.ambientPrismCoordinates_simplex_iff v hv x).mp hx
  have hh := s.ambientPrismCoordinates_symm_apply v hv (e x)
  rw [e.symm_apply_apply, hzero] at hh
  simp only [Submodule.coe_zero, zero_add] at hh
  have hw := (s.fiberPoint_mem_simplex_iff (e x).2.1 (e x).2.2).mpr
    ⟨(e x).2.1.property.1, ht⟩
  rw [s.eq_lower_iff_coordinate_zero ht]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  have hi := simplexPoint_mem_facet_iff v hv hw i
  rw [← hh] at hi
  exact hi.symm

theorem SimplexSplit.ambientPrismCoordinates_upper_graph_iff (s : SimplexSplit ι)
    (v : ι → E) (hv : AffineIndependent ℝ v) {x : E}
    (hx : x ∈ convexHull ℝ (range v)) :
    (s.ambientPrismCoordinates v hv x).2.2 =
      s.upper (s.ambientPrismCoordinates v hv x).2.1 ↔
      ∃ i ∈ s.left, x ∈ simplexFacet v i := by
  let e := s.ambientPrismCoordinates v hv
  obtain ⟨hzero, ht⟩ := (s.ambientPrismCoordinates_simplex_iff v hv x).mp hx
  have hh := s.ambientPrismCoordinates_symm_apply v hv (e x)
  rw [e.symm_apply_apply, hzero] at hh
  simp only [Submodule.coe_zero, zero_add] at hh
  have hw := (s.fiberPoint_mem_simplex_iff (e x).2.1 (e x).2.2).mpr
    ⟨(e x).2.1.property.1, ht⟩
  rw [s.eq_upper_iff_coordinate_zero ht]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  have hi := simplexPoint_mem_facet_iff v hv hw i
  rw [← hh] at hi
  exact hi.symm

def SimplexSplit.ambientPrismHomeomorph (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) : E ≃ₜ (simplexTransverse v × s.horizontal) × ℝ :=
  (s.ambientPrismCoordinates v hv).trans (Homeomorph.prodAssoc _ _ _).symm

theorem SimplexSplit.ambientPrismHomeomorph_symm_apply (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (p : (simplexTransverse v × s.horizontal) × ℝ) :
    (s.ambientPrismHomeomorph v hv).symm p =
      (p.1.1 : E) + simplexPoint v (s.fiberPoint p.1.2 p.2) :=
  s.ambientPrismCoordinates_symm_apply v hv (p.1.1, p.1.2, p.2)

theorem SimplexSplit.ambientPrismHomeomorph_simplex_iff (s : SimplexSplit ι)
    (v : ι → E) (hv : AffineIndependent ℝ v) (x : E) :
    x ∈ convexHull ℝ (range v) ↔
      (s.ambientPrismHomeomorph v hv x).1.1 = 0 ∧
      (s.ambientPrismHomeomorph v hv x).2 ∈
        Icc (s.lower (s.ambientPrismHomeomorph v hv x).1.2)
          (s.upper (s.ambientPrismHomeomorph v hv x).1.2) :=
  s.ambientPrismCoordinates_simplex_iff v hv x

theorem SimplexSplit.ambientPrismHomeomorph_image_simplex (s : SimplexSplit ι)
    (v : ι → E) (hv : AffineIndependent ℝ v) :
    s.ambientPrismHomeomorph v hv '' convexHull ℝ (range v) =
      {p | p.1.1 = 0 ∧ p.2 ∈ Icc (s.lower p.1.2) (s.upper p.1.2)} := by
  let e := s.ambientPrismHomeomorph v hv
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (s.ambientPrismHomeomorph_simplex_iff v hv x).mp hx
  · intro hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    apply (s.ambientPrismHomeomorph_simplex_iff v hv _).mpr
    simpa only [← show e = s.ambientPrismHomeomorph v hv from rfl,
      e.apply_symm_apply, mem_ofPred_eq] using hp

theorem SimplexSplit.ambientPrismHomeomorph_lower_graph_iff (s : SimplexSplit ι)
    (v : ι → E) (hv : AffineIndependent ℝ v) {x : E}
    (hx : x ∈ convexHull ℝ (range v)) :
    (s.ambientPrismHomeomorph v hv x).2 =
      s.lower (s.ambientPrismHomeomorph v hv x).1.2 ↔
      ∃ i ∈ s.right, x ∈ simplexFacet v i :=
  s.ambientPrismCoordinates_lower_graph_iff v hv hx

theorem SimplexSplit.ambientPrismHomeomorph_upper_graph_iff (s : SimplexSplit ι)
    (v : ι → E) (hv : AffineIndependent ℝ v) {x : E}
    (hx : x ∈ convexHull ℝ (range v)) :
    (s.ambientPrismHomeomorph v hv x).2 =
      s.upper (s.ambientPrismHomeomorph v hv x).1.2 ↔
      ∃ i ∈ s.left, x ∈ simplexFacet v i :=
  s.ambientPrismCoordinates_upper_graph_iff v hv hx

end

end DifferentialGeometry.Topology.Engulfing
