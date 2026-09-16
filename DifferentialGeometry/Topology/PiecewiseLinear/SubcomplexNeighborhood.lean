import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra

open Set Topology unitInterval

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def subcomplexInclusion {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces) :
    C(L.space, K.space) :=
  (SimplicialComplex.geometricInclusion (K := L) (L := K) hL).hom

theorem subcomplexBarycentricMass_eq_one
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) {x : E} (hx : x ∈ L.space) :
    subcomplexBarycentricMass K L x = 1 := by
  classical
  obtain ⟨e, he, hxe⟩ := L.mem_space_iff.mp hx
  have hf : e.filter (· ∈ L.vertices) = e := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact L.down_closed he (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  rw [subcomplexBarycentricMass_eq_sum_filter K L (hL he) hxe, hf, sum_weights hxe]

theorem subcomplexBarycentricMass_combo
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) {x y : E}
    (hx : x ∈ convexHull ℝ (e : Set E)) (hy : y ∈ convexHull ℝ (e : Set E))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    subcomplexBarycentricMass K L (a • x + b • y) =
      a * subcomplexBarycentricMass K L x + b * subcomplexBarycentricMass K L y := by
  classical
  rw [subcomplexBarycentricMass_eq_sum_filter K L he
      ((convex_convexHull ℝ _) hx hy ha hb hab),
    subcomplexBarycentricMass_eq_sum_filter K L he hx,
    subcomplexBarycentricMass_eq_sum_filter K L he hy,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v hv =>
    weights_combo (K.indep he) hx hy ha hb hab v (Finset.mem_filter.mp hv).1

theorem subcomplexBarycentricMass_pos_iff
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) {x : E} (hx : x ∈ convexHull ℝ (e : Set E)) :
    0 < subcomplexBarycentricMass K L x ↔
      ∃ v ∈ e, v ∈ L.vertices ∧ 0 < weights e x v := by
  classical
  rw [subcomplexBarycentricMass_eq_sum_filter K L he hx,
    Finset.sum_pos_iff_of_nonneg (fun v hv => weights_nonneg hx (Finset.mem_filter.mp hv).1)]
  simp only [Finset.mem_filter, and_assoc]

open Classical in
def subcomplexOpenNeighborhood (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Set K.space :=
  {x | 0 < subcomplexBarycentricMass (barycentricSubdivision K) (barycentricSubdivision L) x}

theorem isOpen_subcomplexOpenNeighborhood [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    IsOpen (subcomplexOpenNeighborhood K L) := by
  classical
  have hc := continuousOn_subcomplexBarycentricMass
    (barycentricSubdivision K) (barycentricSubdivision L)
  rw [(barycentricSubdivision_isSubdivision K).space_eq] at hc
  exact isOpen_lt continuous_const (continuousOn_iff_continuous_domRestrict.mp hc)

theorem mem_subcomplexOpenNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (x : K.space) (hx : (x : E) ∈ L.space) :
    x ∈ subcomplexOpenNeighborhood K L := by
  classical
  change 0 < subcomplexBarycentricMass (barycentricSubdivision K) (barycentricSubdivision L) x
  rw [subcomplexBarycentricMass_eq_one (barycentricSubdivision_faces_subset hL)
    (by rwa [(barycentricSubdivision_isSubdivision L).space_eq])]
  exact zero_lt_one

open Classical in
theorem subcomplexBarycentricProjection_mem_of_mass_pos
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) {x : E} (hx : x ∈ K.space)
    (hm : 0 < subcomplexBarycentricMass (barycentricSubdivision K) (barycentricSubdivision L) x) :
    subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x ∈
      L.space := by
  classical
  have hx' : x ∈ (barycentricSubdivision K).space := by
    rwa [(barycentricSubdivision_isSubdivision K).space_eq]
  obtain ⟨e, he, hxe⟩ := (barycentricSubdivision K).mem_space_iff.mp hx'
  have hp := subcomplexBarycentricProjection_mem_convexHull_filter
    (barycentricSubdivision K) (barycentricSubdivision L) he hxe hm
  have hf : (e.filter (· ∈ (barycentricSubdivision L).vertices)).Nonempty := by
    obtain ⟨v, hv, hvL, _⟩ := (subcomplexBarycentricMass_pos_iff _ _ he hxe).mp hm
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvL⟩⟩
  have hpL := (barycentricSubdivision L).convexHull_subset_space
    (barycentricSubdivision_filter_mem hL he hf) hp
  rwa [(barycentricSubdivision_isSubdivision L).space_eq] at hpL

open Classical in
theorem subcomplexBarycentricHomotopy_mem_openNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) {x : K.space} (hx : x ∈ subcomplexOpenNeighborhood K L) (t : I) :
    ∃ hy : subcomplexBarycentricHomotopy (barycentricSubdivision K)
        (barycentricSubdivision L) t x ∈ K.space,
      ⟨subcomplexBarycentricHomotopy (barycentricSubdivision K)
        (barycentricSubdivision L) t x, hy⟩ ∈ subcomplexOpenNeighborhood K L := by
  classical
  have hxK : (x : E) ∈ (barycentricSubdivision K).space := by
    rw [(barycentricSubdivision_isSubdivision K).space_eq]
    exact x.2
  obtain ⟨e, he, hxe⟩ := (barycentricSubdivision K).mem_space_iff.mp hxK
  have hp := subcomplexBarycentricProjection_mem_convexHull_filter
    (barycentricSubdivision K) (barycentricSubdivision L) he hxe hx
  have hpe := convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hp
  have ht : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  have hsum : (1 - (t : ℝ)) + (t : ℝ) = 1 := sub_add_cancel _ _
  have hye := (convex_convexHull ℝ _) hxe hpe ht t.2.1 hsum
  have hy := (barycentricSubdivision K).convexHull_subset_space he hye
  rw [(barycentricSubdivision_isSubdivision K).space_eq] at hy
  refine ⟨hy, ?_⟩
  change 0 < subcomplexBarycentricMass (barycentricSubdivision K) (barycentricSubdivision L)
    ((1 - (t : ℝ)) • (x : E) + (t : ℝ) •
      subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x)
  rw [subcomplexBarycentricMass_combo _ _ he hxe hpe ht t.2.1 hsum,
    subcomplexBarycentricMass_eq_one (barycentricSubdivision_faces_subset hL)
      (x := subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x)
      (by rw [(barycentricSubdivision_isSubdivision L).space_eq]
          exact subcomplexBarycentricProjection_mem_of_mass_pos hL x.2 hx), mul_one]
  by_cases ht0 : (t : ℝ) = 0
  · rw [ht0]
    simpa only [sub_zero, one_mul, add_zero] using
      (show 0 < subcomplexBarycentricMass (barycentricSubdivision K)
        (barycentricSubdivision L) x from hx)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ht (le_of_lt hx)) (lt_of_le_of_ne t.2.1 (Ne.symm ht0))

open Classical in
noncomputable def subcomplexOpenNeighborhoodInclusion
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) : C(L.space, subcomplexOpenNeighborhood K L) where
  toFun x := ⟨⟨x, space_mono_of_faces_subset hL x.2⟩,
    mem_subcomplexOpenNeighborhood hL _ x.2⟩
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

open Classical in
theorem continuous_subcomplexBarycentricProjection_openNeighborhood
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Continuous (fun x : subcomplexOpenNeighborhood K L =>
      subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x.1) := by
  have hm := continuousOn_subcomplexBarycentricMass
    (barycentricSubdivision K) (barycentricSubdivision L)
  have hv := continuousOn_subcomplexBarycentricMoment
    (barycentricSubdivision K) (barycentricSubdivision L)
  rw [(barycentricSubdivision_isSubdivision K).space_eq] at hm hv
  have hm' : Continuous (fun x : subcomplexOpenNeighborhood K L =>
      subcomplexBarycentricMass (barycentricSubdivision K) (barycentricSubdivision L) x.1) :=
    (continuousOn_iff_continuous_domRestrict.mp hm).comp continuous_subtype_val
  have hv' : Continuous (fun x : subcomplexOpenNeighborhood K L =>
      subcomplexBarycentricMoment (barycentricSubdivision K) (barycentricSubdivision L) x.1) :=
    (continuousOn_iff_continuous_domRestrict.mp hv).comp continuous_subtype_val
  exact (hm'.inv₀ fun x => ne_of_gt x.2).smul hv'

open Classical in
noncomputable def subcomplexOpenNeighborhoodRetraction
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) : C(subcomplexOpenNeighborhood K L, L.space) where
  toFun x := ⟨subcomplexBarycentricProjection (barycentricSubdivision K)
    (barycentricSubdivision L) x.1, subcomplexBarycentricProjection_mem_of_mass_pos hL x.1.2 x.2⟩
  continuous_toFun := (continuous_subcomplexBarycentricProjection_openNeighborhood K L).subtype_mk _

open Classical in
noncomputable def subcomplexOpenNeighborhoodHomotopy
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) :
    ContinuousMap.Homotopy (ContinuousMap.id (subcomplexOpenNeighborhood K L))
      ((subcomplexOpenNeighborhoodInclusion hL).comp (subcomplexOpenNeighborhoodRetraction hL)) where
  toFun z := ⟨⟨subcomplexBarycentricHomotopy (barycentricSubdivision K)
    (barycentricSubdivision L) z.1 z.2.1,
    (subcomplexBarycentricHomotopy_mem_openNeighborhood hL z.2.2 z.1).choose⟩,
    (subcomplexBarycentricHomotopy_mem_openNeighborhood hL z.2.2 z.1).choose_spec⟩
  continuous_toFun := by
    have ht : Continuous (fun z : I × subcomplexOpenNeighborhood K L => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun z : I × subcomplexOpenNeighborhood K L => (z.2.1 : E)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have hp : Continuous (fun z : I × subcomplexOpenNeighborhood K L =>
        subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) z.2.1) :=
      (continuous_subcomplexBarycentricProjection_openNeighborhood K L).comp continuous_snd
    exact (((continuous_const.sub ht).smul hx |>.add (ht.smul hp)).subtype_mk _).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [subcomplexBarycentricHomotopy]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [subcomplexBarycentricHomotopy, subcomplexOpenNeighborhoodRetraction,
      subcomplexOpenNeighborhoodInclusion]

theorem subcomplexOpenNeighborhoodRetraction_comp_inclusion
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) :
    (subcomplexOpenNeighborhoodRetraction hL).comp (subcomplexOpenNeighborhoodInclusion hL) =
      ContinuousMap.id L.space := by
  ext x
  exact subcomplexBarycentricProjection_eq_self_on_subcomplex hL x.2

theorem subcomplexOpenNeighborhoodHomotopy_fixed_on
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (t : I) (x : L.space) :
    subcomplexOpenNeighborhoodHomotopy hL (t, subcomplexOpenNeighborhoodInclusion hL x) =
      subcomplexOpenNeighborhoodInclusion hL x := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  change (1 - (t : ℝ)) • (x : E) + (t : ℝ) •
    subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x = x
  rw [subcomplexBarycentricProjection_eq_self_on_subcomplex hL x.2,
    ← add_smul, sub_add_cancel, one_smul]

noncomputable def subcomplexOpenNeighborhoodHomotopyEquiv
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) :
    ContinuousMap.HomotopyEquiv (subcomplexOpenNeighborhood K L) L.space where
  toFun := subcomplexOpenNeighborhoodRetraction hL
  invFun := subcomplexOpenNeighborhoodInclusion hL
  left_inv := ⟨(subcomplexOpenNeighborhoodHomotopy hL).symm⟩
  right_inv := by
    rw [subcomplexOpenNeighborhoodRetraction_comp_inclusion hL]

noncomputable def subcomplexOpenNeighborhoodStrongDeformationRetract
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) :
    DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract
      {x : subcomplexOpenNeighborhood K L | (x.1 : E) ∈ L.space} where
  retraction := {
    toFun x := ⟨subcomplexOpenNeighborhoodInclusion hL (subcomplexOpenNeighborhoodRetraction hL x),
      (subcomplexOpenNeighborhoodRetraction hL x).2⟩
    continuous_toFun := ((subcomplexOpenNeighborhoodInclusion hL).continuous.comp
      (subcomplexOpenNeighborhoodRetraction hL).continuous).subtype_mk _
  }
  homotopy := {
    toHomotopy := subcomplexOpenNeighborhoodHomotopy hL
    prop' := by
      classical
      intro t x hx
      apply Subtype.ext
      apply Subtype.ext
      change (1 - (t : ℝ)) • (x.1 : E) + (t : ℝ) •
        subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x.1 = x.1
      rw [subcomplexBarycentricProjection_eq_self_on_subcomplex hL hx,
        ← add_smul, sub_add_cancel, one_smul]
  }

theorem subcomplexOpenNeighborhood_mono
    {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hLM : L.faces ⊆ M.faces) :
    subcomplexOpenNeighborhood K L ⊆ subcomplexOpenNeighborhood K M := by
  classical
  intro x hx
  have hxK : (x : E) ∈ (barycentricSubdivision K).space := by
    rw [(barycentricSubdivision_isSubdivision K).space_eq]
    exact x.2
  obtain ⟨e, he, hxe⟩ := (barycentricSubdivision K).mem_space_iff.mp hxK
  obtain ⟨v, hv, hvL, hvpos⟩ := (subcomplexBarycentricMass_pos_iff _ _ he hxe).mp hx
  exact (subcomplexBarycentricMass_pos_iff _ _ he hxe).mpr
    ⟨v, hv, barycentricSubdivision_faces_subset hLM hvL, hvpos⟩

theorem subcomplexOpenNeighborhood_inter
    {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces) :
    subcomplexOpenNeighborhood K (intersectionComplex L M) =
      subcomplexOpenNeighborhood K L ∩ subcomplexOpenNeighborhood K M := by
  classical
  apply Set.Subset.antisymm
  · exact fun _ hx => ⟨subcomplexOpenNeighborhood_mono
      (L := intersectionComplex L M) (M := L) (fun _ hs => hs.1) hx,
      subcomplexOpenNeighborhood_mono
        (L := intersectionComplex L M) (M := M) (fun _ hs => hs.2) hx⟩
  · rintro x ⟨hxL, hxM⟩
    have hxK : (x : E) ∈ (barycentricSubdivision K).space := by
      rw [(barycentricSubdivision_isSubdivision K).space_eq]
      exact x.2
    obtain ⟨e, he, hxe⟩ := (barycentricSubdivision K).mem_space_iff.mp hxK
    obtain ⟨v, hv, hvL, hvpos⟩ := (subcomplexBarycentricMass_pos_iff _ _ he hxe).mp hxL
    obtain ⟨w, hw, hwM, hwpos⟩ := (subcomplexBarycentricMass_pos_iff _ _ he hxe).mp hxM
    obtain ⟨d, hd, hdne, hde⟩ := he
    have he : e ∈ (barycentricSubdivision K).faces := ⟨d, hd, hdne, hde⟩
    obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp (hde ▸ hv)
    obtain ⟨t, ht, htw⟩ := Finset.mem_image.mp (hde ▸ hw)
    have hsL : s ∈ L.faces := by
      obtain ⟨s', hs', hs'v⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision L hvL
      have hss' := injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K)
        (hd.mem_faces hs) (hL hs') (hsv.trans hs'v.symm)
      exact hss' ▸ hs'
    have htM : t ∈ M.faces := by
      obtain ⟨t', ht', ht'w⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision M hwM
      have htt' := injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K)
        (hd.mem_faces ht) (hM ht') (htw.trans ht'w.symm)
      exact htt' ▸ ht'
    apply (subcomplexBarycentricMass_pos_iff _ _ he hxe).mpr
    rcases hd.subset_or_subset hs ht with hst | hts
    · refine ⟨v, hv, ?_, hvpos⟩
      rw [← hsv]
      exact singleton_centroid_mem_barycentricSubdivision (intersectionComplex L M)
        ⟨hsL, M.down_closed htM hst (L.nonempty_of_mem_faces hsL)⟩
    · refine ⟨w, hw, ?_, hwpos⟩
      rw [← htw]
      exact singleton_centroid_mem_barycentricSubdivision (intersectionComplex L M)
        ⟨L.down_closed hsL hts (M.nonempty_of_mem_faces htM), htM⟩

theorem subcomplexOpenNeighborhood_union
    {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces)
    (hcover : K.faces ⊆ L.faces ∪ M.faces) :
    subcomplexOpenNeighborhood K L ∪ subcomplexOpenNeighborhood K M = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨e, he, hxe⟩ := K.mem_space_iff.mp x.2
  rcases hcover he with heL | heM
  · exact Or.inl (mem_subcomplexOpenNeighborhood hL x (L.convexHull_subset_space heL hxe))
  · exact Or.inr (mem_subcomplexOpenNeighborhood hM x (M.convexHull_subset_space heM hxe))

noncomputable def subcomplexOpenNeighborhoodInterInclusion
    {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces) :
    C((intersectionComplex L M).space,
      (subcomplexOpenNeighborhood K L ∩ subcomplexOpenNeighborhood K M : Set K.space)) where
  toFun x := ⟨⟨x, space_mono_of_faces_subset
    (L := intersectionComplex L M) (fun _ hs => hL hs.1) x.2⟩,
    mem_subcomplexOpenNeighborhood hL _ (space_mono_of_faces_subset
      (K := L) (L := intersectionComplex L M) (fun _ hs => hs.1) x.2),
    mem_subcomplexOpenNeighborhood hM _ (space_mono_of_faces_subset
      (K := M) (L := intersectionComplex L M) (fun _ hs => hs.2) x.2)⟩
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

noncomputable def subcomplexOpenNeighborhoodInterHomotopyEquiv
    [FiniteDimensional ℝ E] {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces) :
    ContinuousMap.HomotopyEquiv
      (subcomplexOpenNeighborhood K L ∩ subcomplexOpenNeighborhood K M : Set K.space)
      (intersectionComplex L M).space :=
  (Homeomorph.setCongr (subcomplexOpenNeighborhood_inter hL hM).symm).toHomotopyEquiv.trans
    (subcomplexOpenNeighborhoodHomotopyEquiv
      (K := K) (L := intersectionComplex L M) (fun _ hs => hL hs.1))

theorem subcomplexOpenNeighborhoodInterHomotopyEquiv_invFun
    [FiniteDimensional ℝ E] {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces) :
    (subcomplexOpenNeighborhoodInterHomotopyEquiv hL hM).invFun =
      subcomplexOpenNeighborhoodInterInclusion hL hM := by
  ext x
  rfl

end DifferentialGeometry.Topology.PiecewiseLinear
