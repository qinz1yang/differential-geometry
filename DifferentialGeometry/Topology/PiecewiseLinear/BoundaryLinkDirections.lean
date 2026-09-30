import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryLinkGerm

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_geometricLink_pair_openSegment_of_eventually_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hG : IsCombinatorialManifold 1 G) {q d : E} (hq : {q} ∈ G.faces) (hd : d ≠ 0)
    (hlocal : ∀ᶠ x in 𝓝 q,
      x ∈ G.space ↔ x - q ∈ Submodule.span ℝ ({d} : Set E)) :
    ∃ a b : E, a ≠ b ∧
      {a} ∈ (SimplicialComplex.geometricLink G {q}).faces ∧
      {b} ∈ (SimplicialComplex.geometricLink G {q}).faces ∧
      q ∈ openSegment ℝ a b := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let P := Submodule.span ℝ ({d} : Set E)
  have hdP : d ∈ P := Submodule.subset_span (by simp)
  have hray (e : E) (he : e ∈ P) :
      ∀ᶠ t : ℝ in 𝓝 0, 0 < t → q + t • e ∈ G.space := by
    have hc : Continuous (fun t : ℝ => q + t • e) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have htend : Filter.Tendsto (fun t : ℝ => q + t • e) (𝓝 0) (𝓝 q) := by
      simpa only [zero_smul, add_zero] using hc.tendsto 0
    filter_upwards [htend.eventually hlocal] with t ht
    intro _
    apply ht.mpr
    simpa only [add_sub_cancel_left] using P.smul_mem t he
  obtain ⟨c, hc, haL⟩ :=
    exists_ray_mem_geometricLink_space_of_eventually G hq hd (hray d hdP)
  obtain ⟨e, he, hbL⟩ := exists_ray_mem_geometricLink_space_of_eventually G hq
    (neg_ne_zero.mpr hd) (hray (-d) (P.neg_mem hdP))
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

end DifferentialGeometry.Topology.PiecewiseLinear
