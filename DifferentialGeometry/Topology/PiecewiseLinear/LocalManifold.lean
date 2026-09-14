import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
def IsLocallyCombinatorialManifoldWithBoundary (n : ℕ) (K : Geometry.SimplicialComplex ℝ E)
    (A : Set E) : Prop :=
  ∀ v, {v} ∈ K.faces →
    (∃ s ∈ K.faces, v ∈ s ∧ (convexHull ℝ (s : Set E) ∩ A).Nonempty) →
      IsPLSphere n (SimplicialComplex.geometricLink K {v}).space ∨
        IsPLBall n (SimplicialComplex.geometricLink K {v}).space

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isLocally {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} (h : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (A : Set E) : IsLocallyCombinatorialManifoldWithBoundary n K A :=
  fun v hv _ => h v hv

open Classical in
theorem IsLocallyCombinatorialManifoldWithBoundary.mono {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} {A B : Set E}
    (h : IsLocallyCombinatorialManifoldWithBoundary n K A) (hBA : B ⊆ A) :
    IsLocallyCombinatorialManifoldWithBoundary n K B := by
  rintro v hv ⟨s, hs, hvs, x, hxs, hxB⟩
  exact h v hv ⟨s, hs, hvs, x, hxs, hBA hxB⟩

open Classical in
theorem card_le_of_vertex_geometricLink [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {v : E}
    (h : IsPLSphere n (SimplicialComplex.geometricLink K {v}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K {v}).space)
    {s : Finset E} (hs : s ∈ K.faces) (hv : v ∈ s) : s.card ≤ n + 2 := by
  have hcard := Finset.card_erase_of_mem hv
  rcases (s.erase v).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty] at hcard
    omega
  · have hmem : s.erase v ∈ (SimplicialComplex.geometricLink K {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
        ⟨hne, Finset.notMem_erase v s, by rwa [Finset.insert_erase hv]⟩
    have hle := card_le_of_isPLBall_or_isPLSphere
      (SimplicialComplex.geometricLink K {v}) h.symm hmem
    omega

open Classical in
theorem isPLSphere_or_isPLBall_geometricLink_of_vertex [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {v : E}
    (h : IsPLSphere n (SimplicialComplex.geometricLink K {v}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K {v}).space)
    {s : Finset E} (hs : s ∈ K.faces) (hv : v ∈ s) {k : ℕ}
    (hcard : s.card = k + 1) (hk : k ≤ n) :
    IsPLSphere (n - k) (SimplicialComplex.geometricLink K s).space ∨
      IsPLBall (n - k) (SimplicialComplex.geometricLink K s).space := by
  cases k with
  | zero =>
    obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hcard
    have hvw := Finset.mem_singleton.mp hv
    subst w
    simpa only [Nat.sub_zero] using h
  | succ k =>
    obtain ⟨s', hvs', rfl⟩ : ∃ s', v ∉ s' ∧ s = insert v s' :=
      ⟨s.erase v, Finset.notMem_erase v s, (Finset.insert_erase hv).symm⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hcard' : s'.card = k + 1 := by
      rw [Finset.card_insert_of_notMem hvs'] at hcard
      omega
    have hsL : s' ∈ (SimplicialComplex.geometricLink K {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton K v s').mpr
        ⟨Finset.card_pos.mp (by omega), hvs', hs⟩
    rw [geometricLink_insert K hvs', show m + 1 - (k + 1) = m - k by omega]
    rcases h with hL | hL
    · exact Or.inl (isPLSphere_geometricLink_faces_of_isPLSphere _ hL hsL hcard' (by omega))
    · exact isPLSphere_or_isPLBall_geometricLink_faces_of_isPLBall _ hL hsL hcard' (by omega)

open Classical in
theorem IsLocallyCombinatorialManifoldWithBoundary.card_le [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {A : Set E}
    (h : IsLocallyCombinatorialManifoldWithBoundary n K A) {s : Finset E} (hs : s ∈ K.faces)
    (hsA : (convexHull ℝ (s : Set E) ∩ A).Nonempty) : s.card ≤ n + 2 := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hvK := K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  exact card_le_of_vertex_geometricLink K (h v hvK ⟨s, hs, hv, hsA⟩) hs hv

open Classical in
theorem IsLocallyCombinatorialManifoldWithBoundary.isPLSphere_or_isPLBall_geometricLink
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {A : Set E} (h : IsLocallyCombinatorialManifoldWithBoundary n K A)
    {s : Finset E} (hs : s ∈ K.faces) (hsA : (convexHull ℝ (s : Set E) ∩ A).Nonempty)
    {k : ℕ} (hcard : s.card = k + 1) (hk : k ≤ n) :
    IsPLSphere (n - k) (SimplicialComplex.geometricLink K s).space ∨
      IsPLBall (n - k) (SimplicialComplex.geometricLink K s).space := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hvK := K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  exact isPLSphere_or_isPLBall_geometricLink_of_vertex K (h v hvK ⟨s, hs, hv, hsA⟩) hs hv hcard hk

open Classical in
theorem starAvoiding_eq_simplexBoundary_of_card_le_cofaces {m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) {t : Finset E} (ht : t ∈ K.faces)
    (hcard : t.card = m + 2) (hK : ∀ u ∈ K.faces, t ⊆ u → u.card ≤ m + 2) :
    starAvoiding K t = simplexBoundary t (K.indep ht) := by
  ext s
  rw [mem_starAvoiding_faces_iff, mem_simplexBoundary_faces_iff]
  constructor
  · rintro ⟨hs, hst, hts⟩
    have hle := hK _ hst Finset.subset_union_right
    have hsub : t = s ∪ t := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    refine ⟨fun w hw => ?_, K.nonempty_of_mem_faces hs, fun hst' => hts ?_⟩
    · rw [hsub]
      exact Finset.mem_union_left t hw
    · subst hst'
      exact Finset.Subset.refl _
  · rintro ⟨hst, hne, hst'⟩
    exact ⟨K.down_closed ht hst hne, by rwa [Finset.union_eq_right.mpr hst],
      fun hh => hst' (Finset.Subset.antisymm hst hh)⟩

open Classical in
theorem isPLSphere_geometricLink_of_card_le_cofaces [FiniteDimensional ℝ E] {m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {t : Finset E} (ht : t ∈ K.faces)
    (hcard : t.card = m + 2) (hK : ∀ u ∈ K.faces, t ⊆ u → u.card ≤ m + 2)
    {x : E} (hx : x ∈ openSimplex t) {K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (hK' : IsSubdivision K' K) (hx' : {x} ∈ K'.faces) :
    IsPLSphere m (SimplicialComplex.geometricLink K' {x}).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_starAvoiding K ht hx hK' hx'
  rw [starAvoiding_eq_simplexBoundary_of_card_le_cofaces K ht hcard hK,
    simplexBoundary_space t (K.indep ht) (by omega)] at hf
  exact (isPLSphere_biUnion_erase t (K.indep ht) hcard).of_isPLHomeomorphOn hf.symm

open Classical in
theorem isPLSphere_or_isPLBall_geometricLink_of_mem_openSimplex [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {t : Finset E} (ht : t ∈ K.faces)
    {v : E} (hv : v ∈ t)
    (h : IsPLSphere n (SimplicialComplex.geometricLink K {v}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K {v}).space)
    {x : E} (hx : x ∈ openSimplex t) {K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (hK' : IsSubdivision K' K) (hx' : {x} ∈ K'.faces) :
    IsPLSphere n (SimplicialComplex.geometricLink K' {x}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K' {x}).space := by
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 :=
    ⟨t.card - 1, by have := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht); omega⟩
  have hcardle := card_le_of_vertex_geometricLink K h ht hv
  by_cases hkn : k ≤ n
  · rcases isPLSphere_or_isPLBall_geometricLink_of_vertex K h ht hv hk hkn with hsph | hball
    · refine Or.inl ?_
      have hres := isPLSphere_geometricLink_of_isPLSphere_geometricLink K ht hx hK' hx' hk hsph
      rwa [show k + (n - k) = n by omega] at hres
    · refine Or.inr ?_
      have hres := isPLBall_geometricLink_of_isPLBall_geometricLink K ht hx hK' hx' hk hball
      rwa [show k + (n - k) = n by omega] at hres
  · exact Or.inl (isPLSphere_geometricLink_of_card_le_cofaces K ht (by omega)
      (fun u hu htu => card_le_of_vertex_geometricLink K h hu (htu hv)) hx hK' hx')

open Classical in
theorem IsLocallyCombinatorialManifoldWithBoundary.of_isSubdivision [FiniteDimensional ℝ E]
    {n : ℕ} {K K' : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite K'.faces] {A : Set E}
    (h : IsLocallyCombinatorialManifoldWithBoundary n K A) (hK' : IsSubdivision K' K) :
    IsLocallyCombinatorialManifoldWithBoundary n K' A := by
  rintro x hx' ⟨s, hs, hxs, y, hys, hyA⟩
  obtain ⟨u, hu, hsu⟩ := hK'.exists_face_subset hs
  have hxu : x ∈ convexHull ℝ (u : Set E) := hsu (subset_convexHull ℝ _ hxs)
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex K (K.convexHull_subset_space hu hxu)
  have htu := face_subset_of_mem_openSimplex_of_mem_convexHull K ht hu hxt hxu
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
  have hvK := K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  exact isPLSphere_or_isPLBall_geometricLink_of_mem_openSimplex K ht hv
    (h v hvK ⟨u, hu, htu hv, y, hsu hys, hyA⟩) hxt hK' hx'

open Classical in
theorem IsLocallyCombinatorialManifoldWithBoundary.upperLink_faces_eq_empty_of_card
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {A : Set E} (h : IsLocallyCombinatorialManifoldWithBoundary n K A) {e : Finset E}
    (heA : (convexHull ℝ (e : Set E) ∩ A).Nonempty) (hcard : e.card = n + 2) :
    (upperLink K e).faces = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro u ⟨d, hd, hne, hgt, -⟩
  obtain ⟨s, hs⟩ := hne
  obtain ⟨x, hxe, hxA⟩ := heA
  have h1 := Finset.card_lt_card (hgt s hs)
  have h2 := h.card_le (hd.mem_faces hs)
    ⟨x, convexHull_mono (Finset.coe_subset.mpr (hgt s hs).subset) hxe, hxA⟩
  omega

open Classical in
theorem IsLocallyCombinatorialManifoldWithBoundary.isPLBall_geometricLink_derivedNeighborhood_of_lower
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ E)
    (h : IsLocallyCombinatorialManifoldWithBoundary n K L.space) {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e)
    {k : ℕ} (hcard : e.card = k + 2)
    (hlower : IsPLBall k (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id}).space) :
    IsPLBall n (SimplicialComplex.geometricLink (derivedNeighborhood K L)
      {e.centroid ℝ id}).space := by
  have hK' := h.of_isSubdivision (barycentricSubdivision_isSubdivision K)
  have heL : (convexHull ℝ (e : Set E) ∩ L.space).Nonempty := by
    obtain ⟨σ, hσ, hσe⟩ := hef
    exact ⟨σ.centroid ℝ id, subset_convexHull ℝ _ hσe,
      L.convexHull_subset_space hσ (σ.centroid_mem_convexHull (L.nonempty_of_mem_faces hσ))⟩
  have hfinU := (upperLink_faces_finite (barycentricSubdivision K) e).to_subtype
  have hfinF := (faceNeighborhood_faces_finite e ((barycentricSubdivision K).indep he)
    (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)).to_subtype
  rw [geometricLink_derivedNeighborhood_eq K L he hef]
  have hcardle : e.card ≤ n + 2 := hK'.card_le he heL
  rcases Nat.lt_or_ge k n with hkn | hkn
  · have hfinJ := (internalJoin_faces_finite (secondDerived K) _ _
      (geometricLink_faceNeighborhood_faces_subset_secondDerived K L he)
      (upperLink_faces_subset _ _) (union_mem_secondDerived_of_lower_upper K L he hef)).to_subtype
    have hfinJ' := (joinComplex_faces_finite (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id})
      (upperLink (barycentricSubdivision K) e)).to_subtype
    have hiso := (isGlueIso_internalJoin (secondDerived K) _ _
      (geometricLink_faceNeighborhood_faces_subset_secondDerived K L he)
      (upperLink_faces_subset _ _) (union_mem_secondDerived_of_lower_upper K L he hef)
      (disjoint_lower_upper K L he hef)).isPLHomeomorphOn
    obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_upperLink (barycentricSubdivision K) he
    have hupper := hK'.isPLSphere_or_isPLBall_geometricLink he heL
      (show e.card = (k + 1) + 1 by omega) (by omega)
    have hjoin : IsPLBall n (joinComplex (SimplicialComplex.geometricLink
        (faceNeighborhood e ((barycentricSubdivision K).indep he)
          (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id})
        (upperLink (barycentricSubdivision K) e)).space := by
      have hdim : k + (n - (k + 1)) + 1 = n := by omega
      rcases hupper with hs | hb
      · have := isPLBall_joinComplex_of_isPLBall_of_isPLSphere hlower (hs.of_isPLHomeomorphOn hg.symm)
        rwa [hdim] at this
      · have := isPLBall_joinComplex_of_isPLBall_of_isPLBall hlower (hb.of_isPLHomeomorphOn hg.symm)
        rwa [hdim] at this
    exact hjoin.of_isPLHomeomorphOn hiso.symm
  · have hk : k = n := by omega
    subst hk
    have hempty := hK'.upperLink_faces_eq_empty_of_card heL hcard
    have heq := internalJoin_eq_left_of_faces_eq_empty (secondDerived K)
      (geometricLink_faceNeighborhood_faces_subset_secondDerived K L he)
      (upperLink_faces_subset _ _) (union_mem_secondDerived_of_lower_upper K L he hef) hempty
    rw [heq]
    exact hlower

open Classical in
theorem IsLocallyCombinatorialManifoldWithBoundary.derivedNeighborhood [FiniteDimensional ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ E)
    (h : IsLocallyCombinatorialManifoldWithBoundary n K L.space) :
    IsCombinatorialManifoldWithBoundary (n + 1) (PiecewiseLinear.derivedNeighborhood K L) := by
  intro v hv
  have hvK'' : {v} ∈ (secondDerived K).faces := derivedNeighborhood_faces_subset K L hv
  obtain ⟨e, he, rfl⟩ :=
    exists_eq_centroid_of_singleton_mem_barycentricSubdivision (barycentricSubdivision K) hvK''
  have hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e :=
    (singleton_centroid_mem_derivedNeighborhood_iff K L he).mp hv
  by_cases hsub : ∀ w ∈ e, ∃ σ ∈ L.faces, σ.centroid ℝ id = w
  · rw [geometricLink_derivedNeighborhood_eq_of_subset K L he hsub]
    have hK' := h.of_isSubdivision (barycentricSubdivision_isSubdivision K)
    obtain ⟨σ, hσ, hσe⟩ := hef
    have hσK' := (barycentricSubdivision K).down_closed he (Finset.singleton_subset_iff.mpr hσe)
      (Finset.singleton_nonempty _)
    exact isPLSphere_or_isPLBall_geometricLink_of_mem_openSimplex (barycentricSubdivision K) he hσe
      (hK' _ hσK' ⟨e, he, hσe, σ.centroid ℝ id, subset_convexHull ℝ _ hσe,
        L.convexHull_subset_space hσ (σ.centroid_mem_convexHull (L.nonempty_of_mem_faces hσ))⟩)
      (centroid_mem_openSimplex ((barycentricSubdivision K).nonempty_of_mem_faces he))
      (barycentricSubdivision_isSubdivision (barycentricSubdivision K))
      (singleton_centroid_mem_barycentricSubdivision _ he)
  · obtain ⟨w, hw⟩ := not_forall.mp hsub
    obtain ⟨hwe, hwL⟩ := Classical.not_imp.mp hw
    have hfT : (e.filter fun x => ∃ σ ∈ L.faces, σ.centroid ℝ id = x) ⊆ e :=
      Finset.filter_subset _ _
    have hfne : (e.filter fun x => ∃ σ ∈ L.faces, σ.centroid ℝ id = x).Nonempty := by
      obtain ⟨σ, hσ, hσe⟩ := hef
      exact ⟨_, Finset.mem_filter.mpr ⟨hσe, σ, hσ, rfl⟩⟩
    have hfe : (e.filter fun x => ∃ σ ∈ L.faces, σ.centroid ℝ id = x) ≠ e := by
      intro heq
      have hwf : w ∈ e.filter fun x => ∃ σ ∈ L.faces, σ.centroid ℝ id = x := by
        rw [heq]
        exact hwe
      exact hwL (Finset.mem_filter.mp hwf).2
    obtain ⟨k, hk⟩ : ∃ k, e.card = k + 2 := by
      refine ⟨e.card - 2, ?_⟩
      have h1 := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hfT, hfe⟩)
      have h2 := Finset.card_pos.mpr hfne
      omega
    exact Or.inr (h.isPLBall_geometricLink_derivedNeighborhood_of_lower L he hef hk
      (isPLBall_geometricLink_faceNeighborhood_centroid ((barycentricSubdivision K).indep he)
        hfT hfne hfe hk))

end DifferentialGeometry.Topology.PiecewiseLinear
