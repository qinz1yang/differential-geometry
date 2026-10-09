import DifferentialGeometry.Topology.SimplicialComplex.Stellar.HyperplaneCut

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq E] in
theorem convexHull_inter_affine_zero_of_nonneg (V : Finset E) (f : E →ᵃ[ℝ] ℝ)
    (hV : ∀ v ∈ V, 0 ≤ f v) :
    convexHull ℝ (V : Set E) ∩ {x | f x = 0} =
      convexHull ℝ ((V.filter (fun v => f v = 0) : Finset E) : Set E) := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hx, hfx⟩
    change f x = 0 at hfx
    obtain ⟨w, hwV, hw, hm, hp⟩ := (mem_convexHull_iff_weights V x).mp hx
    have hsum : ∑ v ∈ w.support, w v * f v = 0 := by
      simpa only [Finsupp.sum, smul_eq_mul, hp, hfx] using (affineMap_weightPoint f hm).symm
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v hv => mul_nonneg (hw v) (hV v (hwV hv)))).mp hsum
    have hs : w.support ⊆ V.filter (fun v => f v = 0) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨hwV hv,
        (mul_eq_zero.mp (hterms v hv)).resolve_left (Finsupp.mem_support_iff.mp hv)⟩
    exact (mem_convexHull_iff_weights _ x).mpr ⟨w, hs, hw, hm, hp⟩
  · intro x hx
    refine ⟨convexHull_mono (Finset.filter_subset _ _) hx, ?_⟩
    have hzero : Convex ℝ {x | f x = 0} := (convex_singleton (0 : ℝ)).affine_preimage f
    exact convexHull_min (fun v hv => (Finset.mem_filter.mp hv).2) hzero hx

omit [DecidableEq E] in
theorem convexHull_inter_affine_zero_of_nonpos (V : Finset E) (f : E →ᵃ[ℝ] ℝ)
    (hV : ∀ v ∈ V, f v ≤ 0) :
    convexHull ℝ (V : Set E) ∩ {x | f x = 0} =
      convexHull ℝ ((V.filter (fun v => f v = 0) : Finset E) : Set E) := by
  classical
  simpa using convexHull_inter_affine_zero_of_nonneg V (-f) (fun v hv => neg_nonneg.mpr (hV v hv))

def vertexRestriction (K : SimplicialComplex ℝ E) (S : Set E) : SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ (s : Set E) ⊆ S}
  isRelLowerSet_faces := fun _ hs => ⟨K.nonempty_of_mem_faces hs.1,
    fun _ hts ht => ⟨K.down_closed hs.1 hts ht, fun _ hx => hs.2 (hts hx)⟩⟩
  indep := fun hs => K.indep hs.1
  inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1

omit [DecidableEq E] in
theorem vertexRestriction_refines (K : SimplicialComplex ℝ E) (S : Set E) :
    simplicialRefines (vertexRestriction K S) K := by
  classical
  exact fun s hs => ⟨s, hs.1, subset_rfl⟩

omit [DecidableEq E] in
theorem vertexRestriction_finite_faces (K : SimplicialComplex ℝ E) (S : Set E)
    (hK : K.faces.Finite) : (vertexRestriction K S).faces.Finite := by
  classical
  exact hK.subset (fun _ hs => hs.1)

omit [DecidableEq E] in
theorem vertexRestriction_space_subset (K : SimplicialComplex ℝ E) (S : Set E)
    (hS : Convex ℝ S) : (vertexRestriction K S).space ⊆ K.space ∩ S := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact ⟨K.convexHull_subset_space hs.1 hxs, convexHull_min hs.2 hS hxs⟩

omit [DecidableEq E] in
theorem vertexRestriction_inter (K : SimplicialComplex ℝ E) (S T : Set E) :
    vertexRestriction (vertexRestriction K S) T = vertexRestriction K (S ∩ T) := by
  classical
  ext s
  change ((s ∈ K.faces ∧ (s : Set E) ⊆ S) ∧ (s : Set E) ⊆ T) ↔
    (s ∈ K.faces ∧ (s : Set E) ⊆ S ∩ T)
  simp only [subset_inter_iff]
  tauto

omit [DecidableEq E] in
@[simp] theorem vertexRestriction_univ (K : SimplicialComplex ℝ E) :
    vertexRestriction K univ = K := by
  classical
  ext s
  change (s ∈ K.faces ∧ (s : Set E) ⊆ univ) ↔ s ∈ K.faces
  simp

omit [DecidableEq E] in
theorem vertexRestriction_space_of_face_inter (K : SimplicialComplex ℝ E) (S : Set E)
    [DecidablePred (fun x => x ∈ S)]
    (hS : Convex ℝ S)
    (hface : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ∩ S =
      convexHull ℝ ((s.filter (fun x => x ∈ S) : Finset E) : Set E)) :
    (vertexRestriction K S).space = K.space ∩ S := by
  classical
  apply (vertexRestriction_space_subset K S hS).antisymm
  rintro x ⟨hx, hxS⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  have hxf : x ∈ convexHull ℝ ((s.filter (fun x => x ∈ S) : Finset E) : Set E) := by
    rw [← hface s hs]
    exact ⟨hxs, hxS⟩
  have hfne : (s.filter (fun x => x ∈ S)).Nonempty := by
    exact_mod_cast (convexHull_nonempty_iff.mp ⟨x, hxf⟩)
  exact (vertexRestriction K S).convexHull_subset_space
    ⟨K.down_closed hs (Finset.filter_subset _ _) hfne,
      fun v hv => (Finset.mem_filter.mp hv).2⟩ hxf

omit [DecidableEq E] in
theorem respectsAffineHyperplane.neg {K : SimplicialComplex ℝ E} {f : E →ᵃ[ℝ] ℝ}
    (h : respectsAffineHyperplane K f) : respectsAffineHyperplane K (-f) := by
  classical
  intro s hs
  rcases h s hs with hle | hge
  · exact Or.inr (fun x hx => by
      change 0 ≤ -f x
      exact neg_nonneg.mpr (show f x ≤ 0 from hle hx))
  · exact Or.inl (fun x hx => by
      change -f x ≤ 0
      exact neg_nonpos.mpr (show 0 ≤ f x from hge hx))

omit [DecidableEq E] in
theorem respectsAffineHyperplane.vertexRestriction_zero {K : SimplicialComplex ℝ E}
    {f : E →ᵃ[ℝ] ℝ} (h : respectsAffineHyperplane K f) :
    (vertexRestriction K {x | f x = 0}).space = K.space ∩ {x | f x = 0} := by
  classical
  apply vertexRestriction_space_of_face_inter K _ ((convex_singleton (0 : ℝ)).affine_preimage f)
  intro s hs
  rcases h s hs with hle | hge
  · exact convexHull_inter_affine_zero_of_nonpos s f
      (fun v hv => hle (subset_convexHull ℝ _ hv))
  · exact convexHull_inter_affine_zero_of_nonneg s f
      (fun v hv => hge (subset_convexHull ℝ _ hv))

omit [DecidableEq E] in
theorem respectsAffineHyperplane.vertexRestriction_le {K : SimplicialComplex ℝ E}
    {f : E →ᵃ[ℝ] ℝ} (h : respectsAffineHyperplane K f) :
    (vertexRestriction K {x | f x ≤ 0}).space = K.space ∩ {x | f x ≤ 0} := by
  classical
  apply vertexRestriction_space_of_face_inter K _ ((convex_Iic (0 : ℝ)).affine_preimage f)
  intro s hs
  change convexHull ℝ (s : Set E) ∩ {x | f x ≤ 0} =
    convexHull ℝ ((s.filter (fun x => f x ≤ 0) : Finset E) : Set E)
  rcases h s hs with hle | hge
  · have hf : s.filter (fun x => f x ≤ 0) = s := Finset.filter_eq_self.mpr
      (fun x hx => hle (subset_convexHull ℝ _ hx))
    rw [hf, inter_eq_left.mpr hle]
  · have heq : convexHull ℝ (s : Set E) ∩ {x | f x ≤ 0} =
        convexHull ℝ (s : Set E) ∩ {x | f x = 0} := by
      ext x
      exact and_congr_right (fun hx => ⟨fun hh => le_antisymm hh (hge hx),
        fun hh => hh.le⟩)
    rw [heq, convexHull_inter_affine_zero_of_nonneg s f
      (fun v hv => hge (subset_convexHull ℝ _ hv))]
    congr 2
    apply Finset.filter_congr
    intro x hx
    exact ⟨fun he => he.le, fun he => le_antisymm he (hge (subset_convexHull ℝ _ hx))⟩

omit [DecidableEq E] in
theorem respectsAffineHyperplane.vertexRestriction_ge {K : SimplicialComplex ℝ E}
    {f : E →ᵃ[ℝ] ℝ} (h : respectsAffineHyperplane K f) :
    (vertexRestriction K {x | 0 ≤ f x}).space = K.space ∩ {x | 0 ≤ f x} := by
  classical
  simpa using h.neg.vertexRestriction_le

omit [DecidableEq E] in
theorem vertexRestriction_finite_halfspaces {ι : Type*} (K : SimplicialComplex ℝ E)
    (I : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ)
    (hcut : ∀ i ∈ I, respectsAffineHyperplane K (f i)) :
    (vertexRestriction K {x | ∀ i ∈ I, 0 ≤ f i x}).space =
      K.space ∩ {x | ∀ i ∈ I, 0 ≤ f i x} := by
  classical
  induction I using Finset.induction_on generalizing K with
  | empty => simp
  | @insert i I hi ih =>
    have hset : {x | ∀ j ∈ insert i I, 0 ≤ f j x} =
        {x | 0 ≤ f i x} ∩ {x | ∀ j ∈ I, 0 ≤ f j x} := by
      ext x
      simp
    rw [hset, ← vertexRestriction_inter]
    rw [ih (vertexRestriction K {x | 0 ≤ f i x}) (fun j hj =>
      (hcut j (Finset.mem_insert_of_mem hj)).refines (vertexRestriction_refines _ _)),
      (hcut i (Finset.mem_insert_self _ _)).vertexRestriction_ge, inter_assoc]

omit [DecidableEq E] in
theorem exists_subdivision_with_halfspace_subcomplexes {ι : Type*}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (J : Finset ι)
    (F : ι → Finset (E →ᵃ[ℝ] ℝ)) {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ n + 1) ∧
      ∀ j ∈ J, (vertexRestriction L {x | ∀ f ∈ F j, 0 ≤ f x}).space =
        K.space ∩ {x | ∀ f ∈ F j, 0 ≤ f x} := by
  classical
  let I := J.biUnion F
  obtain ⟨L, hL, hspace, href, hcut, hdim⟩ :=
    exists_subdivision_respects_affineHyperplanes K hK I id hd
  refine ⟨L, hL, hspace, href, hdim, ?_⟩
  intro j hj
  simpa only [id_eq, hspace] using vertexRestriction_finite_halfspaces L (F j) id
    (fun f hf => hcut f (Finset.mem_biUnion.mpr ⟨j, hj, hf⟩))

end DifferentialGeometry.Topology.Engulfing
