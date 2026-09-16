import DifferentialGeometry.Topology.PiecewiseLinear.ConvexBoundaryLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem injOn_linearMap_convexHull_of_card_eq_two
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : Finset E) (hcard : F.card = 2) (f : E →ₗ[ℝ] ℝ)
    (hfinj : InjOn f (F : Set E)) : InjOn f (convexHull ℝ (F : Set E)) := by
  classical
  obtain ⟨r, s, hrs, rfl⟩ := Finset.card_eq_two.mp hcard
  intro x hx y hy hxy
  rw [Finset.coe_pair, convexHull_pair, segment_eq_image_lineMap] at hx hy
  obtain ⟨u, -, rfl⟩ := hx
  obtain ⟨v, -, rfl⟩ := hy
  have hfrs : f r ≠ f s := fun h => hrs (hfinj (by simp) (by simp) h)
  have huv : u = v := by
    have hsum : u * (f s - f r) + f r = v * (f s - f r) + f r := by
      simpa only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul] using hxy
    exact mul_right_cancel₀ (sub_ne_zero.mpr hfrs.symm) (add_right_cancel hsum)
  rw [huv]

theorem exists_linearMap_supporting_simplex_facet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    {a : E} (ha : a ∈ T) (hcard : 2 ≤ T.card) :
    ∃ r ∈ T.erase a, ∃ m : E →ₗ[ℝ] ℝ,
      (∀ x ∈ convexHull ℝ (T : Set E), m r ≤ m x) ∧
      ∀ x ∈ convexHull ℝ (T : Set E),
        m x = m r ↔ x ∈ convexHull ℝ ((T.erase a : Finset E) : Set E) := by
  classical
  let F := T.erase a
  have hFne : F.Nonempty := by
    apply Finset.card_pos.mp
    rw [show F.card = T.card - 1 by simp only [F, Finset.card_erase_of_mem ha]]
    omega
  obtain ⟨r, hr⟩ := hFne
  let S := vectorSpan ℝ (F : Set E)
  let d := a - r
  have hinsert : insert a F = T := Finset.insert_erase ha
  let i : T := ⟨a, ha⟩
  have himage : ((↑) : T → E) '' (Set.univ \ ({i} : Set T)) = (F : Set E) := by
    ext x
    constructor
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩
      apply Finset.mem_coe.mpr
      apply Finset.mem_erase.mpr
      refine ⟨?_, y.property⟩
      intro hay
      apply hy
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact hay
    · intro hx
      obtain ⟨hxa, hxT⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hx)
      refine ⟨⟨x, hxT⟩, ⟨Set.mem_univ _, ?_⟩, rfl⟩
      intro hxi
      apply hxa
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hxi)
  have haSpan : a ∉ affineSpan ℝ (F : Set E) := by
    rw [← himage]
    exact hT.notMem_affineSpan_sdiff i Set.univ
  have hdS : d ∉ S := by
    intro hd
    apply haSpan
    have hd' : d ∈ (affineSpan ℝ (F : Set E)).direction := by
      simpa only [S, direction_affineSpan] using hd
    have hr' : r ∈ affineSpan ℝ (F : Set E) := subset_affineSpan ℝ _ hr
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hd' hr'
    simpa only [d, vadd_eq_add, sub_add_cancel] using hmem
  obtain ⟨k, hkd, hSk⟩ := S.exists_le_ker_of_notMem hdS
  let m : E →ₗ[ℝ] ℝ := (k d)⁻¹ • k
  have hmd : m d = 1 := by
    simp only [m, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hkd]
  have hSm : S ≤ LinearMap.ker m := by
    intro x hx
    rw [LinearMap.mem_ker]
    simp only [m, LinearMap.smul_apply, smul_eq_mul]
    rw [show k x = 0 from LinearMap.mem_ker.mp (hSk hx), mul_zero]
  have hconstant (x : E) (hx : x ∈ convexHull ℝ (F : Set E)) : m x = m r := by
    have hxS : x - r ∈ S := by
      change x - r ∈ vectorSpan ℝ (F : Set E)
      have h := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
        (k := ℝ) (s := (F : Set E))
        (convexHull_subset_affineSpan (F : Set E) hx)
        (subset_affineSpan ℝ (F : Set E) hr)
      simpa only [vsub_eq_sub] using h
    have hz := hSm hxS
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hz
    exact hz
  have hma : m a = m r + 1 := by
    have h := hmd
    simp only [d, map_sub] at h
    linarith
  have hmain : ∀ x ∈ convexHull ℝ (T : Set E),
      m r ≤ m x ∧ (m x = m r ↔ x ∈ convexHull ℝ (F : Set E)) := by
    intro x hx
    have hx' : x ∈ convexHull ℝ ((insert a F : Finset E) : Set E) := by
      rwa [hinsert]
    rcases exists_combo_of_mem_convexHull_insert (Finset.notMem_erase a T) hx' with hxa |
      ⟨z, hz, s, hs, hs1, rfl⟩
    · subst x
      refine ⟨by linarith, ?_⟩
      constructor
      · intro h
        linarith
      · intro h
        exact (haSpan (convexHull_subset_affineSpan (F : Set E) h)).elim
    · have hmz := hconstant z hz
      have hmx : m (a + s • (z - a)) = m r + (1 - s) := by
        rw [map_add, map_smul, map_sub, hmz, hma, smul_eq_mul]
        ring
      refine ⟨by linarith, ?_⟩
      constructor
      · intro heq
        have hsone : s = 1 := by linarith
        simpa only [hsone, one_smul, add_sub_cancel] using hz
      · intro hxF
        exact hconstant _ hxF
  exact ⟨r, hr, m, fun x hx => (hmain x hx).1, fun x hx => (hmain x hx).2⟩

theorem geometricLink_section_subsingleton_of_simplex_facet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 3) {a q : E} (ha : a ∈ T)
    (hq : q ∈ convexHull ℝ ((T.erase a : Finset E) : Set E))
    (M : Geometry.SimplicialComplex ℝ E)
    (hspace : M.space = convexHull ℝ (T : Set E))
    (f : E →L[ℝ] ℝ) (hfinj : InjOn f (T : Set E)) :
    ((SimplicialComplex.geometricLink M {q}).space ∩ {x | f x = f q}).Subsingleton := by
  have hface : convexHull ℝ ((T.erase a : Finset E) : Set E) ⊆
      convexHull ℝ (T : Set E) := convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset a T))
  have hqT := hface hq
  have hFcard : (T.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  obtain ⟨r, -, m, hsupport, heq⟩ :=
    exists_linearMap_supporting_simplex_facet T hT ha (by omega)
  have hmrq : m q = m r := (heq q hqT).mpr hq
  have hfinjF : InjOn f.toLinearMap ((T.erase a : Finset E) : Set E) := by
    intro x hx y hy hxy
    apply hfinj (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy)
    simpa only [ContinuousLinearMap.coe_coe] using hxy
  have hsegment := injOn_linearMap_convexHull_of_card_eq_two
    (T.erase a) hFcard f.toLinearMap hfinjF
  apply geometricLink_section_subsingleton_of_supporting_fiber
    T hT hcard hqT M hspace f hfinj m
  · intro x hx
    rw [hmrq]
    exact hsupport x hx
  · intro x hx hfx hmx
    have hxF := (heq x hx).mp (hmx.trans hmrq)
    apply hsegment hxF hq
    simpa only [ContinuousLinearMap.coe_coe] using hfx

end DifferentialGeometry.Topology.PiecewiseLinear
