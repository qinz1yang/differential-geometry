import DifferentialGeometry.Topology.PiecewiseLinear.RetainedDiskLink

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem mem_faces_of_mem_openSimplex_mem_space_of_faces_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hxs : x ∈ openSimplex s)
    (hxL : x ∈ L.space) : s ∈ L.faces := by
  classical
  obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
  exact L.down_closed ht
    (face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hLK ht) hxs hxt)
    (K.nonempty_of_mem_faces hs)

theorem map_le_of_mem_geometricLink_space_of_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [dE : DecidableEq E]
    (M : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) {q v : E}
    (hlocal : ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q)
    (hv : v ∈ (SimplicialComplex.geometricLink M {q}).space) : ℓ v ≤ ℓ q := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let r : ℝ → E := fun t => q + t • (v - q)
  have hr : Filter.Tendsto r (𝓝 0) (𝓝 q) := by
    have hc : Continuous r := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [r, zero_smul, add_zero] using hc.tendsto 0
  have hev : ∀ᶠ t in 𝓝[>] 0, r t ∈ M.space → ℓ (r t) ≤ ℓ q :=
    (hr.mono_left nhdsWithin_le_nhds).eventually hlocal
  obtain ⟨t, ht, ht01⟩ := (hev.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have htM : r t ∈ M.space := by
    exact mem_convexHull_insert_of_mem_geometricLink_space M hv ht01.1.le ht01.2.le
  have hle := ht htM
  have hmap : ℓ (r t) = ℓ q + t * (ℓ v - ℓ q) := by
    simp only [r, map_add, map_smul, map_sub, smul_eq_mul]
  rw [hmap] at hle
  nlinarith

theorem geometricLink_boundaryComplex_space_eq_pair_of_isPLBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsPLBall 2 M.space) {q a b : E}
    (hqB : {q} ∈ (boundaryComplex 2 M).faces)
    (ha : {a} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces)
    (hb : {b} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces)
    (hab : a ≠ b) :
    (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).space = {a, b} := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hman : IsCombinatorialManifoldWithBoundary 2 M :=
    hM.isCombinatorialManifoldWithBoundary
  have hlinkBall : IsPLBall 1 (SimplicialComplex.geometricLink M {q}).space := by
    have h := ((hman.mem_boundaryComplex_faces_iff M).mp hqB).2.2
    simpa only [Finset.card_singleton, Nat.reduceSub] using h
  have hsphere : IsPLSphere 0
      (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).space := by
    rw [geometricLink_boundaryComplex (n := 1) M q]
    exact isPLSphere_boundaryComplex_space_of_isPLBall
      (SimplicialComplex.geometricLink M {q}) hlinkBall
  obtain ⟨c, d, hcd, hspace⟩ := isPLSphere_zero_iff.mp hsphere
  have haS : a ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).space :=
    (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).convexHull_subset_space
      ha (subset_convexHull ℝ _ (by simp))
  have hbS : b ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).space :=
    (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).convexHull_subset_space
      hb (subset_convexHull ℝ _ (by simp))
  have hsub : ({a, b} : Set E) ⊆
      (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).space := by
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ haS
    · exact hx ▸ hbS
  have hcard :
      (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).space.encard = 2 := by
    rw [hspace, encard_pair hcd]
  exact (((Set.finite_singleton b).insert a).eq_of_subset_of_encard_le hsub (by
    rw [hcard, encard_pair hab])).symm

theorem mem_geometricLink_boundaryComplex_of_height_eq_of_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [dE : DecidableEq E]
    (M : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) {q v : E}
    (hlocal : ∀ᶠ x in 𝓝 q,
      x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q)
    (hv : v ∈ (SimplicialComplex.geometricLink M {q}).vertices)
    (hvq : ℓ v = ℓ q) :
    {v} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  obtain ⟨hne, hqv, hface⟩ :=
    (SimplicialComplex.mem_geometricLink_singleton M q {v}).mp hv
  let r : ℝ → E := fun t => q + t • (v - q)
  have hr : Filter.Tendsto r (𝓝 0) (𝓝 q) := by
    have hc : Continuous r := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [r, zero_smul, add_zero] using hc.tendsto 0
  have hev : ∀ᶠ t in 𝓝[>] 0,
      r t ∈ (boundaryComplex 2 M).space ↔ r t ∈ M.space ∧ ℓ (r t) = ℓ q :=
    (hr.mono_left nhdsWithin_le_nhds).eventually hlocal
  obtain ⟨t, ht, ht01⟩ := (hev.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have hqne : q ≠ v := by simpa only [Finset.mem_singleton] using hqv
  have herase : (insert q ({v} : Finset E)).erase v = {q} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxv, hxq | hxv'⟩
      · exact hxq
      · exact (hxv hxv').elim
    · intro hxq
      exact ⟨fun hxv => hqne (hxq.symm.trans hxv), Or.inl hxq⟩
  have hqopen : q ∈ openSimplex ((insert q ({v} : Finset E)).erase v) := by
    rw [herase]
    exact mem_openSimplex_singleton q
  have hropen : r t ∈ openSimplex (insert q {v}) := by
    apply openSegment_subset_openSimplex_of_mem_openSimplex_erase
      (M.indep hface) (by simp) hqopen
    simpa only [r, AffineMap.lineMap_apply_module', add_comm] using
      lineMap_mem_openSegment ℝ q v ht01
  have hrM : r t ∈ M.space :=
    M.convexHull_subset_space hface (openSimplex_subset_convexHull _ hropen)
  have hrlevel : ℓ (r t) = ℓ q := by
    simp only [r, map_add, map_smul, map_sub, hvq, sub_self, smul_eq_mul, mul_zero,
      add_zero]
  have hrB : r t ∈ (boundaryComplex 2 M).space := ht.mpr ⟨hrM, hrlevel⟩
  have hBface : insert q {v} ∈ (boundaryComplex 2 M).faces :=
    mem_faces_of_mem_openSimplex_mem_space_of_faces_subset M (boundaryComplex 2 M)
      (boundaryComplex_faces_subset 2 M) hface hropen hrB
  exact (SimplicialComplex.mem_geometricLink_singleton (boundaryComplex 2 M) q {v}).mpr
    ⟨hne, hqv, hBface⟩

theorem geometricLink_vertices_lt_of_halfSpace_boundary_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsPLBall 2 M.space) (ℓ : E →L[ℝ] ℝ) {q a b : E}
    (hqB : {q} ∈ (boundaryComplex 2 M).faces)
    (ha : {a} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces)
    (hb : {b} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces)
    (hab : a ≠ b)
    (hhalf : ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q)
    (hboundary : ∀ᶠ x in 𝓝 q,
      x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q) :
    ∀ v ∈ (SimplicialComplex.geometricLink M {q}).vertices,
      v ≠ a → v ≠ b → ℓ v < ℓ q := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hpair := geometricLink_boundaryComplex_space_eq_pair_of_isPLBall
    M hM hqB ha hb hab
  intro v hv hva hvb
  have hvspace : v ∈ (SimplicialComplex.geometricLink M {q}).space :=
    (SimplicialComplex.geometricLink M {q}).convexHull_subset_space hv
      (subset_convexHull ℝ _ (by simp))
  have hle := map_le_of_mem_geometricLink_space_of_eventually M ℓ hhalf hvspace
  apply lt_of_le_of_ne hle
  intro heq
  have hvB := mem_geometricLink_boundaryComplex_of_height_eq_of_eventually
    M ℓ hboundary hv heq
  have hvBspace : v ∈
      (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).space :=
    (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).convexHull_subset_space
      hvB (subset_convexHull ℝ _ (by simp))
  rw [hpair] at hvBspace
  rcases hvBspace with h | h
  · exact hva h
  · exact hvb h

theorem eventually_geometricLink_section_subsingleton_of_halfSpace_boundary_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsPLBall 2 M.space) (ℓ : E →L[ℝ] ℝ) {q a b : E}
    (hqB : {q} ∈ (boundaryComplex 2 M).faces)
    (ha : {a} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces)
    (hb : {b} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces)
    (hab : a ≠ b) (hq : q ∈ openSegment ℝ a b)
    (hhalf : ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q)
    (hboundary : ∀ᶠ x in 𝓝 q,
      x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      InjOn f (insert q (SimplicialComplex.geometricLink M {q}).vertices) →
        ((SimplicialComplex.geometricLink M {q}).space ∩
          {x | f x = f q}).Subsingleton := by
  apply eventually_geometricLink_section_subsingleton_of_boundary_segment
    M hM ℓ hqB ha hb hab hq
  exact geometricLink_vertices_lt_of_halfSpace_boundary_germ
    M hM ℓ hqB ha hb hab hhalf hboundary

end DifferentialGeometry.Topology.PiecewiseLinear
