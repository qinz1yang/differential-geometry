import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryLinkDirections

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_geometricLink_pair_openSegment_of_opposite_rays
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hG : IsCombinatorialManifold 1 G) {q d : E} (hq : {q} ∈ G.faces) (hd : d ≠ 0)
    (hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < t → q + t • d ∈ G.space)
    (hneg : ∀ᶠ t : ℝ in 𝓝 0, 0 < t → q + t • (-d) ∈ G.space) :
    ∃ a b : E, a ≠ b ∧
      {a} ∈ (SimplicialComplex.geometricLink G {q}).faces ∧
      {b} ∈ (SimplicialComplex.geometricLink G {q}).faces ∧
      q ∈ openSegment ℝ a b := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  obtain ⟨c, hc, haL⟩ :=
    exists_ray_mem_geometricLink_space_of_eventually G hq hd hpos
  obtain ⟨e, he, hbL⟩ := exists_ray_mem_geometricLink_space_of_eventually G hq
    (neg_ne_zero.mpr hd) hneg
  let a := q + c • d
  let b := q + e • (-d)
  have hcard : ∀ s ∈ G.faces, s.card ≤ 2 := by
    intro s hs
    simpa only [Nat.reduceAdd] using hG.card_le G hs
  have haN : a ≠ q ∧ {q, a} ∈ G.faces := by
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard q] at haL
    exact haL
  have hbN : b ≠ q ∧ {q, b} ∈ G.faces := by
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard q] at hbL
    exact hbL
  have haF : {a} ∈ (SimplicialComplex.geometricLink G {q}).faces := by
    apply (SimplicialComplex.mem_geometricLink_singleton G q {a}).mpr
    exact ⟨Finset.singleton_nonempty a, by simpa using haN.1.symm, haN.2⟩
  have hbF : {b} ∈ (SimplicialComplex.geometricLink G {q}).faces := by
    apply (SimplicialComplex.mem_geometricLink_singleton G q {b}).mpr
    exact ⟨Finset.singleton_nonempty b, by simpa using hbN.1.symm, hbN.2⟩
  have hab : a ≠ b := by
    intro hab'
    have hvec : c • d = e • (-d) := by
      change q + c • d = q + e • (-d) at hab'
      exact add_left_cancel hab'
    have hzero : (c + e) • d = 0 := by
      rw [add_smul, hvec, smul_neg, neg_add_cancel]
    exact (ne_of_gt (add_pos hc he)) ((smul_eq_zero.mp hzero).resolve_right hd)
  let t := c / (c + e)
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hc (add_pos hc he)
    · rw [div_lt_one (add_pos hc he)]
      linarith
  have hcoeff : c - t * (e + c) = 0 := by
    dsimp only [t]
    rw [add_comm e c, div_mul_cancel₀ c (ne_of_gt (add_pos hc he)), sub_self]
  have hline : AffineMap.lineMap a b t = q := by
    rw [AffineMap.lineMap_apply_module']
    calc
      t • (b - a) + a = q + (c - t * (e + c)) • d := by
        dsimp only [a, b]
        module
      _ = q := by rw [hcoeff, zero_smul, add_zero]
  refine ⟨a, b, hab, haF, hbF, ?_⟩
  rw [← hline]
  exact lineMap_mem_openSegment ℝ a b ht

theorem exists_geometricLink_pair_openSegment_of_openSimplex_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hG : IsCombinatorialManifold 1 G) {q : E} (hq : {q} ∈ G.faces)
    {s : Finset E} (hscard : s.card = 2) (hqs : q ∈ openSimplex s)
    (hsG : convexHull ℝ (s : Set E) ⊆ G.space) :
    ∃ a b : E, a ≠ b ∧
      {a} ∈ (SimplicialComplex.geometricLink G {q}).faces ∧
      {b} ∈ (SimplicialComplex.geometricLink G {q}).faces ∧
      q ∈ openSegment ℝ a b := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hscard
  let d := u - v
  have hd : d ≠ 0 := sub_ne_zero.mpr huv
  have hdspan : d ∈ vectorSpan ℝ (({u, v} : Finset E) : Set E) := by
    exact vsub_mem_vectorSpan ℝ (by simp) (by simp)
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < t → q + t • d ∈ G.space := by
    filter_upwards [eventually_mem_openSimplex_of_mem_vectorSpan hqs hdspan] with t ht
    intro _
    exact hsG (openSimplex_subset_convexHull _ ht)
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, 0 < t → q + t • (-d) ∈ G.space := by
    filter_upwards [eventually_mem_openSimplex_of_mem_vectorSpan hqs
      (Submodule.neg_mem _ hdspan)] with t ht
    intro _
    exact hsG (openSimplex_subset_convexHull _ ht)
  exact exists_geometricLink_pair_openSegment_of_opposite_rays G hG hq hd hpos hneg

end DifferentialGeometry.Topology.PiecewiseLinear
