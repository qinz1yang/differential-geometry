import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodLink
import DifferentialGeometry.Topology.PiecewiseLinear.FaceNeighborhoodLink
import DifferentialGeometry.Topology.PiecewiseLinear.JoinBall
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem singleton_centroid_mem_barycentricSubdivision [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {e : Finset E} (he : e ∈ K.faces) :
    {e.centroid ℝ id} ∈ (barycentricSubdivision K).faces :=
  ⟨{e}, ⟨fun s hs => (Finset.mem_singleton.mp hs).symm ▸ he, fun s hs t ht =>
    Or.inl ((Finset.mem_singleton.mp hs).trans (Finset.mem_singleton.mp ht).symm ▸
      Finset.Subset.refl _)⟩, Finset.singleton_nonempty e, by rw [Finset.image_singleton]⟩

open Classical in
theorem upperLink_faces_eq_empty_of_card [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (h : IsCombinatorialManifoldWithBoundary (n + 1) K) {e : Finset E} (hcard : e.card = n + 2) :
    (upperLink K e).faces = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro u ⟨d, hd, hne, hgt, -⟩
  obtain ⟨s, hs⟩ := hne
  have h1 := Finset.card_lt_card (hgt s hs)
  have h2 := h.card_le K (hd.mem_faces hs)
  omega

open Classical in
theorem isPLSphere_or_isPLBall_geometricLink_derivedNeighborhood_of_subset
    [FiniteDimensional ℝ E] {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (h : IsCombinatorialManifoldWithBoundary (n + 1) K) {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces)
    (hsub : ∀ v ∈ e, ∃ σ ∈ L.faces, σ.centroid ℝ id = v) :
    IsPLSphere n (SimplicialComplex.geometricLink (derivedNeighborhood K L)
      {e.centroid ℝ id}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink (derivedNeighborhood K L)
        {e.centroid ℝ id}).space := by
  rw [geometricLink_derivedNeighborhood_eq_of_subset K L he hsub]
  exact h.secondDerived _ (singleton_centroid_mem_barycentricSubdivision _ he)

open Classical in
theorem isPLBall_geometricLink_derivedNeighborhood_of_lower [FiniteDimensional ℝ E] {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (h : IsCombinatorialManifoldWithBoundary (n + 1) K) {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e)
    {k : ℕ} (hcard : e.card = k + 2)
    (hlower : IsPLBall k (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id}).space) :
    IsPLBall n (SimplicialComplex.geometricLink (derivedNeighborhood K L)
      {e.centroid ℝ id}).space := by
  have hK' : IsCombinatorialManifoldWithBoundary (n + 1) (barycentricSubdivision K) :=
    h.barycentricSubdivision
  have hfinU := (upperLink_faces_finite (barycentricSubdivision K) e).to_subtype
  have hfinF := (faceNeighborhood_faces_finite e ((barycentricSubdivision K).indep he)
    (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)).to_subtype
  rw [geometricLink_derivedNeighborhood_eq K L he hef]
  have hcardle : e.card ≤ n + 2 := hK'.card_le _ he
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
    have hupper := hK'.isPLSphere_or_isPLBall_geometricLink _ he
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
    have hempty := upperLink_faces_eq_empty_of_card _ hK' hcard
    have heq := internalJoin_eq_left_of_faces_eq_empty (secondDerived K)
      (geometricLink_faceNeighborhood_faces_subset_secondDerived K L he)
      (upperLink_faces_subset _ _) (union_mem_secondDerived_of_lower_upper K L he hef) hempty
    rw [heq]
    exact hlower

open Classical in
theorem IsCombinatorialManifoldWithBoundary.derivedNeighborhood [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (h : IsCombinatorialManifoldWithBoundary (n + 1) K) (L : Geometry.SimplicialComplex ℝ E) :
    IsCombinatorialManifoldWithBoundary (n + 1)
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L) := by
  intro v hv
  have hvK'' : {v} ∈ (PiecewiseLinear.secondDerived K).faces := derivedNeighborhood_faces_subset K L hv
  obtain ⟨e, he, rfl⟩ :=
    exists_eq_centroid_of_singleton_mem_barycentricSubdivision (PiecewiseLinear.barycentricSubdivision K) hvK''
  have hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e :=
    (singleton_centroid_mem_derivedNeighborhood_iff K L he).mp hv
  by_cases hsub : ∀ w ∈ e, ∃ σ ∈ L.faces, σ.centroid ℝ id = w
  · exact isPLSphere_or_isPLBall_geometricLink_derivedNeighborhood_of_subset K L h he hsub
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
    exact Or.inr (isPLBall_geometricLink_derivedNeighborhood_of_lower K L h he hef hk
      (isPLBall_geometricLink_faceNeighborhood_centroid ((PiecewiseLinear.barycentricSubdivision K).indep he)
        hfT hfne hfe hk))

end DifferentialGeometry.Topology.PiecewiseLinear
