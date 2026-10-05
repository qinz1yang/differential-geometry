import DifferentialGeometry.Topology.PiecewiseLinear.AffineOrientation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem linearMap_mul_neg_of_distinct_cofaces
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} {x a b : E}
    (hx : x ∈ openSimplex s) (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (haK : insert a s ∈ K.faces) (hbK : insert b s ∈ K.faces)
    (ℓ : E →ₗ[ℝ] ℝ) (hspan : vectorSpan ℝ (s : Set E) = LinearMap.ker ℓ) :
    ℓ (a - x) * ℓ (b - x) < 0 := by
  obtain ⟨m, hm, hma, hmb⟩ := exists_linearMap_separating_cofaces K hx ha hb hab haK hbK
  have hane : ℓ (a - x) ≠ 0 := by
    intro ha0
    have hmem : a - x ∈ vectorSpan ℝ (s : Set E) := by
      rw [hspan]
      exact ha0
    have hm0 : m (a - x) = 0 := hm hmem
    linarith
  have hdir : (b - x) - (ℓ (b - x) / ℓ (a - x)) • (a - x) ∈
      vectorSpan ℝ (s : Set E) := by
    rw [hspan, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul,
      div_mul_cancel₀ _ hane, sub_self]
  have hm0 : m ((b - x) - (ℓ (b - x) / ℓ (a - x)) • (a - x)) = 0 := hm hdir
  rw [map_sub, map_smul, smul_eq_mul, hma, mul_one, sub_eq_zero] at hm0
  have hratio : ℓ (b - x) / ℓ (a - x) < 0 := by rwa [← hm0]
  rcases div_neg_iff.mp hratio with ⟨hbpos, haneg⟩ | ⟨hbneg, hapos⟩
  · exact mul_neg_of_neg_of_pos haneg hbpos
  · exact mul_neg_of_pos_of_neg hapos hbneg

open Classical in
theorem affineMap_mul_neg_of_distinct_cofaces
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {a b : E} (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (haK : insert a s ∈ K.faces) (hbK : insert b s ∈ K.faces)
    (ℓ : E →ᵃ[ℝ] ℝ) (hzero : EqOn ℓ (fun _ => 0) (s : Set E))
    (hspan : vectorSpan ℝ (s : Set E) = LinearMap.ker ℓ.linear) :
    ℓ a * ℓ b < 0 := by
  let x := s.centroid ℝ id
  have hx : x ∈ openSimplex s := centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
  have hxspan : x ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan _ (openSimplex_subset_convexHull s hx)
  have hxzero : ℓ x = 0 :=
    AffineMap.eqOn_affineSpan (g := AffineMap.const ℝ E 0) hzero hxspan
  have hlinear : ∀ z : E, ℓ.linear (z - x) = ℓ z := by
    intro z
    simpa only [vsub_eq_sub, hxzero, sub_zero] using ℓ.linearMap_vsub z x
  simpa only [hlinear] using
    linearMap_mul_neg_of_distinct_cofaces K hx ha hb hab haK hbK ℓ.linear hspan

open Classical in
theorem affineMap_mul_neg_of_distinct_cofaces_of_card_eq_finrank [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = Module.finrank ℝ E)
    {a b : E} (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (haK : insert a s ∈ K.faces) (hbK : insert b s ∈ K.faces)
    (ℓ : E →ᵃ[ℝ] ℝ) (hℓ : ℓ.linear ≠ 0) (hzero : EqOn ℓ (fun _ => 0) (s : Set E)) :
    ℓ a * ℓ b < 0 := by
  have hle : vectorSpan ℝ (s : Set E) ≤ LinearMap.ker ℓ.linear := by
    intro v hv
    exact AffineMap.linear_eqOn_vectorSpan (g := AffineMap.const ℝ E 0) hzero hv
  have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext v; simp
  have hc : Fintype.card s = Module.finrank ℝ (LinearMap.ker ℓ.linear) + 1 := by
    rw [Fintype.card_coe, hcard, Module.Dual.finrank_ker_add_one_of_ne_zero hℓ]
  have hspan : vectorSpan ℝ (s : Set E) = LinearMap.ker ℓ.linear := by
    simpa only [hrange] using
      (K.indep hs).vectorSpan_eq_of_le_of_card_eq_finrank_add_one
        (show vectorSpan ℝ (Set.range ((↑) : s → E)) ≤ LinearMap.ker ℓ.linear by
          simpa only [hrange] using hle) hc
  exact affineMap_mul_neg_of_distinct_cofaces K hs ha hb hab haK hbK ℓ hzero hspan

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_cofaces_pos_neg [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hdim : Module.finrank ℝ E = n + 1) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = n + 1) (hsB : s ∉ (boundaryComplex (n + 1) K).faces)
    (ℓ : E →ᵃ[ℝ] ℝ) (hℓ : ℓ.linear ≠ 0) (hzero : EqOn ℓ (fun _ => 0) (s : Set E)) :
    ∃ a b, {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b} ∧ 0 < ℓ a ∧ ℓ b < 0 := by
  obtain ⟨a, b, hab, hpair⟩ := hK.codimension_one_cofaces_of_notMem_boundary K hs hcard hsB
  have ha : a ∉ s ∧ insert a s ∈ K.faces := by
    change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    exact Set.mem_insert a {b}
  have hb : b ∉ s ∧ insert b s ∈ K.faces := by
    change b ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hmul := affineMap_mul_neg_of_distinct_cofaces_of_card_eq_finrank K hs
    (hcard.trans hdim.symm) ha.1 hb.1 hab ha.2 hb.2 ℓ hℓ hzero
  rcases mul_neg_iff.mp hmul with ⟨hapos, hbneg⟩ | ⟨haneg, hbpos⟩
  · exact ⟨a, b, hpair, hapos, hbneg⟩
  · exact ⟨b, a, hpair.trans (Set.pair_comm a b), hbpos, haneg⟩

end DifferentialGeometry.Topology.PiecewiseLinear
