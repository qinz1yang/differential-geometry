import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiber
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lt_height_iff_of_affine_on_faces
    (R : Geometry.SimplicialComplex ℝ E) (a b : E →ᵃ[ℝ] ℝ) (r t : ℝ) {h : E → E}
    (hfaces : ∀ s ∈ R.faces, ∃ c : E →ᵃ[ℝ] E, EqOn h c (convexHull ℝ (s : Set E)))
    (hside : ∀ s ∈ R.faces, convexHull ℝ (s : Set E) ⊆ {x | a x ≤ r} ∨
      convexHull ℝ (s : Set E) ⊆ {x | r ≤ a x})
    (hverts : ∀ v ∈ R.vertices, (a v ≤ r → b (h v) ≤ t) ∧
      (r ≤ a v → t ≤ b (h v)) ∧ (a v = r ↔ b (h v) = t))
    {x : E} (hx : x ∈ R.space) : a x < r ↔ b (h x) < t := by
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex R hx
  obtain ⟨c, hc⟩ := hfaces s hs
  have hvs : ∀ v ∈ s, v ∈ R.vertices := fun v hv =>
    R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hcvert : ∀ v ∈ s, c v = h v := fun v hv =>
    (hc (subset_convexHull ℝ _ hv)).symm
  have heq := eq_height_iff_of_affine_on_faces R a b r t hfaces hside hverts hx
  rcases hside s hs with hle | hge
  · have hax : a x ≤ r := hle (openSimplex_subset_convexHull s hxs)
    have hbx : b (h x) ≤ t := by
      rw [hc (openSimplex_subset_convexHull s hxs)]
      change (b.comp c) x ≤ t
      exact convexHull_min (fun v hv => by
          change b (c v) ≤ t
          rw [hcvert v hv]
          exact (hverts v (hvs v hv)).1 (hle (subset_convexHull ℝ _ hv)))
        ((convex_Iic t).affine_preimage (b.comp c))
        (openSimplex_subset_convexHull s hxs)
    constructor
    · intro hlt
      exact lt_of_le_of_ne hbx fun hbt => hlt.ne (heq.mpr hbt)
    · intro hlt
      exact lt_of_le_of_ne hax fun har => hlt.ne (heq.mp har)
  · have hax : r ≤ a x := hge (openSimplex_subset_convexHull s hxs)
    have hbx : t ≤ b (h x) := by
      rw [hc (openSimplex_subset_convexHull s hxs)]
      change t ≤ (b.comp c) x
      exact convexHull_min (fun v hv => by
          change t ≤ b (c v)
          rw [hcvert v hv]
          exact (hverts v (hvs v hv)).2.1 (hge (subset_convexHull ℝ _ hv)))
        ((convex_Ici t).affine_preimage (b.comp c))
        (openSimplex_subset_convexHull s hxs)
    exact iff_of_false (not_lt_of_ge hax) (not_lt_of_ge hbx)

theorem height_lt_iff_of_affine_on_faces
    (R : Geometry.SimplicialComplex ℝ E) (a b : E →ᵃ[ℝ] ℝ) (r t : ℝ) {h : E → E}
    (hfaces : ∀ s ∈ R.faces, ∃ c : E →ᵃ[ℝ] E, EqOn h c (convexHull ℝ (s : Set E)))
    (hside : ∀ s ∈ R.faces, convexHull ℝ (s : Set E) ⊆ {x | a x ≤ r} ∨
      convexHull ℝ (s : Set E) ⊆ {x | r ≤ a x})
    (hverts : ∀ v ∈ R.vertices, (a v ≤ r → b (h v) ≤ t) ∧
      (r ≤ a v → t ≤ b (h v)) ∧ (a v = r ↔ b (h v) = t))
    {x : E} (hx : x ∈ R.space) : r < a x ↔ t < b (h x) := by
  simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using
    lt_height_iff_of_affine_on_faces R (-a) (-b) (-r) (-t) hfaces (by
      intro s hs
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_le_neg_iff] using (hside s hs).symm) (by
      intro v hv
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_le_neg_iff, neg_inj] using
        ⟨(hverts v hv).2.1, (hverts v hv).1, (hverts v hv).2.2⟩) hx

theorem isPLHomeomorphOn_simplicialMap_radialProj_of_radial [FiniteDimensional ℝ E]
    (p : E) (L L' : Geometry.SimplicialComplex ℝ E) [Finite L'.faces]
    (hrayL : IsRadiallyInjective p L.space) (hL' : IsConeBase p L')
    (hadapt : ∀ σ ∈ L'.faces, ∃ τ ∈ L.faces, ∀ w ∈ σ,
      ∃ s : ℝ, 0 < s ∧ p + s • (w - p) ∈ convexHull ℝ (τ : Set E))
    (hsurj : ∀ x ∈ L.space, ∃ s : ℝ, 0 < s ∧ p + s • (x - p) ∈ L'.space) :
    IsPLHomeomorphOn (simplicialMap L' (radialProj p L.space)) L'.space L.space := by
  classical
  have h := isPLHomeomorphOn_simplicialImage L' (radialProj p L.space)
    (fun σ hσ => affineIndependent_image_radialProj p L' hL' L.space hσ)
    (injOn_simplicialMap_radialProj p L' hL' L.space)
  rwa [simplicialImage_space,
    image_simplicialMap_radialProj_eq p L L' hrayL hL' hadapt hsurj] at h

theorem isPLHomeomorphOn_simplicialMap_radialProj_geometricLink_of_isSubdivision
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K' K : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (h : IsSubdivision K' K) {p : E} (hp : {p} ∈ K.faces) :
    IsPLHomeomorphOn
      (simplicialMap (SimplicialComplex.geometricLink K' {p})
        (radialProj p (SimplicialComplex.geometricLink K {p}).space))
      (SimplicialComplex.geometricLink K' {p}).space
      (SimplicialComplex.geometricLink K {p}).space := by
  have hp' : {p} ∈ K'.faces := h.singleton_mem hp
  apply isPLHomeomorphOn_simplicialMap_radialProj_of_radial p
    (SimplicialComplex.geometricLink K {p})
    (SimplicialComplex.geometricLink K' {p})
    (isRadiallyInjective_geometricLink K) (isConeBase_geometricLink K')
  · intro σ hσ
    obtain ⟨hσne, hpσ, hins⟩ :=
      (SimplicialComplex.mem_geometricLink_singleton K' p σ).mp hσ
    obtain ⟨t, ht, hsub⟩ := h.exists_face_subset hins
    have hpt : p ∈ t := mem_of_mem_convexHull_of_singleton_mem K hp ht
      (hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self p σ))))
    refine ⟨t.erase p, ?_, fun w hw => ?_⟩
    · refine (SimplicialComplex.mem_geometricLink_singleton K p _).mpr
        ⟨?_, Finset.notMem_erase p t, by rwa [Finset.insert_erase hpt]⟩
      obtain ⟨w, hw⟩ := hσne
      have hwt : w ∈ convexHull ℝ (t : Set E) :=
        hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hw)))
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty, Finset.erase_eq_empty_iff] at hne
      rcases hne with h0 | h0
      · exact (K.nonempty_of_mem_faces ht).ne_empty h0
      · rw [h0, Finset.coe_singleton, convexHull_singleton] at hwt
        exact hpσ (hwt ▸ hw)
    · have hwt : w ∈ convexHull ℝ ((insert p (t.erase p) : Finset E) : Set E) := by
        rw [Finset.insert_erase hpt]
        exact hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hw)))
      exact exists_ray_mem_convexHull_of_mem_convexHull_insert hwt
        (ne_of_mem_of_not_mem hw hpσ)
  · intro x hx
    have hxp : x ≠ p := ne_of_mem_of_not_mem hx (notMem_geometricLink_space K)
    refine exists_ray_mem_geometricLink_space K' hp' (fun t ht0 ht1 => ?_) hxp
    rw [h.space_eq]
    exact mem_convexHull_insert_of_mem_geometricLink_space K hx ht0.le ht1

theorem exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_preserving_height_sign
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K' K : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (h : IsSubdivision K' K) {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hside : ∀ s ∈ K'.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x}) :
    ∃ f : E → E,
      IsPLHomeomorphOn f (SimplicialComplex.geometricLink K' {p}).space
        (SimplicialComplex.geometricLink K {p}).space ∧
      f '' ((SimplicialComplex.geometricLink K' {p}).space ∩ {x | ℓ x = ℓ p}) =
        (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p} ∧
      f '' ((SimplicialComplex.geometricLink K' {p}).space ∩ {x | ℓ x < ℓ p}) =
        (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x < ℓ p} ∧
      f '' ((SimplicialComplex.geometricLink K' {p}).space ∩ {x | ℓ p < ℓ x}) =
        (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ p < ℓ x} := by
  let L' := SimplicialComplex.geometricLink K' {p}
  let L := SimplicialComplex.geometricLink K {p}
  let f : E → E := simplicialMap L' (radialProj p L.space)
  have hf : IsPLHomeomorphOn f L'.space L.space :=
    isPLHomeomorphOn_simplicialMap_radialProj_geometricLink_of_isSubdivision h hp
  have hfaces : ∀ s ∈ L'.faces, ∃ c : E →ᵃ[ℝ] E,
      EqOn f c (convexHull ℝ (s : Set E)) :=
    fun s hs => exists_affineMap_eqOn_simplicialMap L' (radialProj p L.space) hs
  have hside' : ∀ s ∈ L'.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x} :=
    fun s hs => hside s (geometricLink_faces_subset K' {p} hs)
  have hverts : ∀ v ∈ L'.vertices, (ℓ v ≤ ℓ p → ℓ (f v) ≤ ℓ p) ∧
      (ℓ p ≤ ℓ v → ℓ p ≤ ℓ (f v)) ∧ (ℓ v = ℓ p ↔ ℓ (f v) = ℓ p) := by
    intro v hv
    have hfv : f v = radialProj p L.space v := simplicialMap_vertex L' _ hv
    have hdiff : ℓ (f v) - ℓ p = radialRatio p L.space v * (ℓ v - ℓ p) := by
      rw [hfv, ← map_sub, radialProj_sub, map_smul, smul_eq_mul, map_sub]
    have hratio := radialRatio_pos p L.space v
    refine ⟨fun hle => ?_, fun hge => ?_, ?_⟩
    · rw [← sub_nonpos]
      rw [hdiff]
      exact mul_nonpos_of_nonneg_of_nonpos hratio.le (sub_nonpos.mpr hle)
    · rw [← sub_nonneg]
      rw [hdiff]
      exact mul_nonneg hratio.le (sub_nonneg.mpr hge)
    · constructor
      · intro heq
        apply sub_eq_zero.mp
        rw [hdiff, heq, sub_self, mul_zero]
      · intro heq
        have hzero : radialRatio p L.space v * (ℓ v - ℓ p) = 0 := by
          rw [← hdiff, heq, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hratio.ne')
  have heq : ∀ x ∈ L'.space, ℓ x = ℓ p ↔ ℓ (f x) = ℓ p := fun x hx =>
    eq_height_iff_of_affine_on_faces L' ℓ.toAffineMap ℓ.toAffineMap (ℓ p) (ℓ p)
      hfaces hside' hverts hx
  have hlt : ∀ x ∈ L'.space, ℓ x < ℓ p ↔ ℓ (f x) < ℓ p := fun x hx =>
    lt_height_iff_of_affine_on_faces L' ℓ.toAffineMap ℓ.toAffineMap (ℓ p) (ℓ p)
      hfaces hside' hverts hx
  have hgt : ∀ x ∈ L'.space, ℓ p < ℓ x ↔ ℓ p < ℓ (f x) := fun x hx =>
    height_lt_iff_of_affine_on_faces L' ℓ.toAffineMap ℓ.toAffineMap (ℓ p) (ℓ p)
      hfaces hside' hverts hx
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro y ⟨x, ⟨hx, hxeq⟩, rfl⟩
      exact ⟨hf.bijOn.mapsTo hx, (heq x hx).mp hxeq⟩
    · rintro y ⟨hy, hyeq⟩
      obtain ⟨x, hx, rfl⟩ := hf.bijOn.surjOn hy
      exact ⟨x, ⟨hx, (heq x hx).mpr hyeq⟩, rfl⟩
  · apply Subset.antisymm
    · rintro y ⟨x, ⟨hx, hxlt⟩, rfl⟩
      exact ⟨hf.bijOn.mapsTo hx, (hlt x hx).mp hxlt⟩
    · rintro y ⟨hy, hylt⟩
      obtain ⟨x, hx, rfl⟩ := hf.bijOn.surjOn hy
      exact ⟨x, ⟨hx, (hlt x hx).mpr hylt⟩, rfl⟩
  · apply Subset.antisymm
    · rintro y ⟨x, ⟨hx, hxgt⟩, rfl⟩
      exact ⟨hf.bijOn.mapsTo hx, (hgt x hx).mp hxgt⟩
    · rintro y ⟨hy, hygt⟩
      obtain ⟨x, hx, rfl⟩ := hf.bijOn.surjOn hy
      exact ⟨x, ⟨hx, (hgt x hx).mpr hygt⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
