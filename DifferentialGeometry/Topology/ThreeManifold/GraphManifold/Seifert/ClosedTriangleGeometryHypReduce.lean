import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypMoves
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatReduce

/-!
# Reduction of a hyperbolic closed triangle fold to the doubled triangle

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3; the
hyperbolic analogue of B3's `ClosedTriangleGeometryFlatReduce`, both rows at once). Every point `y`
of the fold domain is related by the local composite relation to a point over a vertex `v₁`, `v₂`,
`0`, or over the triangle minus its vertices, or over the mirrored triangle minus its vertices
(`exists_foldRel_reduced`): in a vertex disc a power of the screw of the vertex turns the Möbius
coordinate into the window `[a, a + 2θ)` (`exists_rot_window`), which is the triangle sector and
the adjacent mirrored sector (`mem_triangle_of_discOne`, …: on the unit disc the side functions
are positive multiples of the imaginary parts of the rotated coordinates); on the mirrored disc
about `v̄₁` the inverse of `S₃` moves to the disc about `v₁`; a wall patch point outside the
triangle reflects into the open triangle, and the matching side pairing (`S₃` for wall 1, `S₂⁻¹`
for wall 2) moves it into the mirrored open triangle.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open TwoConeFold

section Signs

variable {σ : CompactShape} (hσ : σ.curv = .hyperbolic)
include hσ

theorem wallSide_one_nonneg_of {z : ℂ} (hz : ‖z‖ < 1) (h : 0 ≤ (σ.rotOne z).im) :
    0 ≤ σ.wallSide 1 z := by
  have e := HypFold.rotOne_im_mul_normSq hσ hz
  have hp := HypFold.normSq_pos_of_ne (HypFold.one_sub_conj_vertexOne_mul_ne_zero hσ hz)
  have ht := one_sub_sideTan_sq_pos (HypFold.sideOneThree_pos hσ) (HypFold.sideOneThree_lt_one hσ)
  by_contra hn
  rw [not_le] at hn
  nlinarith [mul_neg_of_pos_of_neg ht hn]

theorem wallSide_two_nonneg_of_rotTwo {z : ℂ} (_hz : ‖z‖ < 1) (h : 0 ≤ (σ.rotTwo z).im) :
    0 ≤ σ.wallSide 2 z := by
  rw [HypFold.wallSide_two_eq_rotTwo hσ]
  exact mul_nonneg h (normSq_nonneg _)

theorem wallSide_zero_nonneg_of_rotTwo {z : ℂ} (hz : ‖z‖ < 1)
    (h : (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im ≤ 0) : 0 ≤ σ.wallSide 0 z := by
  have e := HypFold.rotTwo_rot_im_mul_normSq hσ z
  have hp := HypFold.normSq_pos_of_ne (HypFold.one_sub_vertexTwo_mul_ne_zero hσ hz)
  have ht := one_sub_sideTan_sq_pos (HypFold.sideTwoThree_pos hσ) (HypFold.sideTwoThree_lt_one hσ)
  by_contra hn
  rw [not_le] at hn
  nlinarith [mul_neg_of_pos_of_neg ht hn]

theorem wallSide_two_nonneg_of_rotOne {z : ℂ} (hz : ‖z‖ < 1)
    (h : (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im ≤ 0) : 0 ≤ σ.wallSide 2 z := by
  have e := HypFold.rotOne_rot_im_mul_normSq hσ hz
  have hs0 := HypFold.sideOneTwo_pos hσ
  have hs1 := HypFold.sideOneTwo_lt_one hσ
  have ht := one_sub_sideTan_sq_pos hs0 hs1
  apply wallSide_two_nonneg_of_rotTwo hσ hz
  by_contra hn
  rw [not_le] at hn
  have hN := normSq_nonneg (1 - (HypFold.sideOneTwo σ : ℂ) * σ.rotTwo z)
  nlinarith [mul_neg_of_pos_of_neg ht hn]

omit hσ in
theorem wallSide_one_nonneg_of_three {z : ℂ} (h : (exp (-((σ.θ₃ : ℂ) * I)) * z).im ≤ 0) :
    0 ≤ σ.wallSide 1 z := by
  have := HypFold.wallSide_one_eq_neg_im (σ := σ) z
  linarith

theorem mem_plane_of_norm {z : ℂ} (hz : ‖z‖ < 1) : z ∈ σ.plane := by
  rw [CompactShape.plane_hyp hσ, mem_ball_zero_iff]; exact hz

end Signs

section SectorsT

variable {σ : CompactShape} (hσ : σ.curv = .hyperbolic) {D : σ.FoldData}
include hσ

theorem mem_triangle_of_discOne {z : ℂ} (hd : z ∈ discOne D) (h0 : 0 ≤ arg (σ.rotOne z))
    (h1 : arg (σ.rotOne z) ≤ σ.θ₁) : z ∈ σ.triangle := by
  have hρ := rhoZero_pos (σ := σ)
  refine ⟨mem_plane_of_norm hσ hd.1, fun i => ?_⟩
  fin_cases i
  · have := wallSide_zero_of_mem_discOne hσ hd
    change 0 ≤ σ.wallSide 0 z
    linarith
  · exact wallSide_one_nonneg_of hσ hd.1 (arg_nonneg_iff.mp h0)
  · exact wallSide_two_nonneg_of_rotOne hσ hd.1
      (im_rot_nonpos_of_arg_le σ.θ₁_pos σ.θ₁_le h0 h1)

theorem mem_triangle_of_discTwo {z : ℂ} (hd : z ∈ discTwo D) (h0 : 0 ≤ arg (σ.rotTwo z))
    (h1 : arg (σ.rotTwo z) ≤ σ.θ₂) : z ∈ σ.triangle := by
  have hρ := rhoZero_pos (σ := σ)
  refine ⟨mem_plane_of_norm hσ hd.1, fun i => ?_⟩
  fin_cases i
  · exact wallSide_zero_nonneg_of_rotTwo hσ hd.1
      (im_rot_nonpos_of_arg_le σ.θ₂_pos σ.θ₂_le h0 h1)
  · have := wallSide_one_of_mem_discTwo hσ hd
    change 0 ≤ σ.wallSide 1 z
    linarith
  · exact wallSide_two_nonneg_of_rotTwo hσ hd.1 (arg_nonneg_iff.mp h0)

theorem mem_triangle_of_discThree {z : ℂ} (hd : z ∈ discThree D) (h0 : 0 ≤ arg z)
    (h1 : arg z ≤ σ.θ₃) : z ∈ σ.triangle := by
  have hρ := rhoZero_pos (σ := σ)
  refine ⟨mem_plane_of_norm hσ (norm_lt_one_of_mem_discThree D hd), fun i => ?_⟩
  fin_cases i
  · exact arg_nonneg_iff.mp h0
  · exact wallSide_one_nonneg_of_three (im_rot_nonpos_of_arg_le σ.θ₃_pos σ.θ₃_le h0 h1)
  · have := wallSide_two_of_mem_discThree hσ hd
    change 0 ≤ σ.wallSide 2 z
    linarith

theorem refl_one_mem_triangle {z : ℂ} (hd : z ∈ discOne D) (h0 : -σ.θ₁ ≤ arg (σ.rotOne z))
    (h1 : arg (σ.rotOne z) < 0) : σ.refl 1 z ∈ σ.triangle := by
  have ha := arg_conj_of_neg h1
  apply mem_triangle_of_discOne hσ (refl_one_mem_discOne hσ hd)
  · rw [HypFold.rotOne_refl_one hσ, ha]; linarith
  · rw [HypFold.rotOne_refl_one hσ, ha]; linarith

theorem conj_mem_triangle_of_discTwo {z : ℂ} (hd : z ∈ discTwo D)
    (h0 : σ.θ₂ < arg (σ.rotTwo z)) (h1 : arg (σ.rotTwo z) < 2 * σ.θ₂) :
    conj z ∈ σ.triangle := by
  have hθ := σ.θ₂_pos
  have hθ' := σ.θ₂_le
  have hw : σ.rotTwo z ≠ 0 := by
    intro h; rw [h, arg_zero] at h0; linarith
  have hcw : conj (σ.rotTwo z) ≠ 0 := (map_ne_zero _).2 hw
  have hneg : arg (conj (σ.rotTwo z)) = -arg (σ.rotTwo z) := by
    rw [arg_conj, ite_eq_right_iff.mpr (fun h' => absurd h' (by linarith))]
  have hr : σ.rotTwo (conj z) = exp ((2 * σ.θ₂ : ℝ) * I) * conj (σ.rotTwo z) := by
    have := HypFold.rotTwo_refl_zero hσ z
    change σ.rotTwo (conj z) = _ at this
    rw [this]
    congr 2
    push_cast
    ring
  have harg : arg (σ.rotTwo (conj z)) = 2 * σ.θ₂ - arg (σ.rotTwo z) := by
    rw [hr, arg_exp_mul' hcw (by rw [hneg]; linarith) (by rw [hneg]; linarith), hneg]
    ring
  apply mem_triangle_of_discTwo hσ (conj_mem_discTwo hσ hd)
  · rw [harg]; linarith
  · rw [harg]; linarith

theorem conj_mem_triangle_of_discThree {z : ℂ} (hd : z ∈ discThree D)
    (h0 : -σ.θ₃ ≤ arg z) (h1 : arg z < 0) : conj z ∈ σ.triangle := by
  have ha := arg_conj_of_neg h1
  apply mem_triangle_of_discThree hσ (conj_mem_discThree hd)
  · rw [ha]; linarith
  · rw [ha]; linarith

omit hσ in
theorem zero_mem_discThree : (0 : ℂ) ∈ discThree D := by
  change ‖(0 : ℂ)‖ < _; rw [norm_zero]; exact radThree_pos D

theorem ne_vertices_of_discOne {z : ℂ} (hd : z ∈ discOne D) (h : σ.rotOne z ≠ 0) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨fun h0 => ?_, fun h1 => h (by rw [h1, rotOne_vertexOne hσ]), fun h2 => ?_⟩
  · exact disjoint_left.mp (disjoint_discOne_discThree hσ) hd (h0 ▸ zero_mem_discThree)
  · exact disjoint_left.mp (disjoint_discOne_discTwo hσ) hd (h2 ▸ mem_discTwo_vertexTwo hσ)

theorem ne_vertices_of_discTwo {z : ℂ} (hd : z ∈ discTwo D) (h : σ.rotTwo z ≠ 0) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => h (by rw [h2, rotTwo_vertexTwo hσ])⟩
  · exact disjoint_left.mp (disjoint_discTwo_discThree hσ) hd (h0 ▸ zero_mem_discThree)
  · exact disjoint_left.mp (disjoint_discOne_discTwo hσ) (h1 ▸ mem_discOne_vertexOne hσ) hd

theorem ne_vertices_of_discThree {z : ℂ} (hd : z ∈ discThree D) (h : z ≠ 0) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨h, fun h1 => ?_, fun h2 => ?_⟩
  · exact disjoint_left.mp (disjoint_discOne_discThree hσ) (h1 ▸ mem_discOne_vertexOne hσ) hd
  · exact disjoint_left.mp (disjoint_discTwo_discThree hσ) (h2 ▸ mem_discTwo_vertexTwo hσ) hd

omit hσ in
theorem ne_vertices_of_intT {z : ℂ} (h : z ∈ intT σ) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := σ.ne_of_mem_openTriangle h

theorem ne_zero_of_main {z : ℂ} (hm : z ∈ mainSet D) : z ≠ 0 := by
  have hk := kap_pos D hσ
  rintro rfl
  rcases hm with ((h | h) | h) | h
  · exact ne_zero_of_mem_intT h rfl
  · have := h.2.1; rw [HypFold.wallSide_one_zero] at this; linarith
  · have := h.2.1; rw [σ.wallSide_zero_eq, zero_im] at this; linarith
  · have := h.2.1; rw [σ.wallSide_zero_eq, zero_im] at this; linarith

end SectorsT

def reducedSet (K : HypDatum) : Set ModelCoordinates :=
  {y | hb y = K.σ.vertexOne ∨ hb y = K.σ.vertexTwo ∨ hb y = 0 ∨
    (hb y ∈ K.σ.triangle ∧ hb y ≠ 0 ∧ hb y ≠ K.σ.vertexOne ∧ hb y ≠ K.σ.vertexTwo) ∨
    (conj (hb y) ∈ K.σ.triangle ∧ conj (hb y) ≠ 0 ∧ conj (hb y) ≠ K.σ.vertexOne ∧
      conj (hb y) ≠ K.σ.vertexTwo)}

section Iterate

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (K : HypDatum)

theorem discOne_subset_domain {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) :
    x ∈ hypDomain K := by
  change hb x ∈ hypBase K
  simp only [hypBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inr hd)))

theorem discTwo_subset_domain {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) :
    x ∈ hypDomain K := by
  change hb x ∈ hypBase K
  simp only [hypBase, mem_union]
  exact Or.inl (Or.inr hd)

theorem discThree_subset_domain {x : ModelCoordinates} (hd : hb x ∈ discThree K.D) :
    x ∈ hypDomain K := by
  change hb x ∈ hypBase K
  simp only [hypBase, mem_union]
  exact Or.inr hd

theorem iterate_screwOne {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) (k : ℕ) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x (K.screwOne^[k] x) ∧
      hb (K.screwOne^[k] x) ∈ discOne K.D ∧
      K.σ.rotOne (hb (K.screwOne^[k] x)) =
        (Circle.exp (-2 * Real.pi / K.σ.p₁) : ℂ) ^ k * K.σ.rotOne (hb x) := by
  induction k with
  | zero => exact ⟨FoldRel.refl (hypDomain K).isOpen (discOne_subset_domain K hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwOne C hc h3 K hd'), K.screwOne_mem_discOne hd', ?_⟩
    rw [K.rotOne_screwOne, hrot, pow_succ]
    ring

theorem iterate_screwTwo {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) (k : ℕ) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x (K.screwTwo^[k] x) ∧
      hb (K.screwTwo^[k] x) ∈ discTwo K.D ∧
      K.σ.rotTwo (hb (K.screwTwo^[k] x)) =
        (Circle.exp (-2 * Real.pi / K.σ.p₂) : ℂ) ^ k * K.σ.rotTwo (hb x) := by
  induction k with
  | zero => exact ⟨FoldRel.refl (hypDomain K).isOpen (discTwo_subset_domain K hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwTwo C hc h3 K hd'), K.screwTwo_mem_discTwo hd', ?_⟩
    rw [K.rotTwo_screwTwo, hrot, pow_succ]
    ring

theorem iterate_screwThree {x : ModelCoordinates} (hd : hb x ∈ discThree K.D) (k : ℕ) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x (K.screwThree^[k] x) ∧
      hb (K.screwThree^[k] x) ∈ discThree K.D ∧
      hb (K.screwThree^[k] x) = (Circle.exp (-2 * Real.pi / K.σ.p₃) : ℂ) ^ k * hb x := by
  induction k with
  | zero => exact ⟨FoldRel.refl (hypDomain K).isOpen (discThree_subset_domain K hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwThree C hc h3 K hd'), K.screwThree_mem_discThree hd', ?_⟩
    rw [K.hb_screwThree, hrot, pow_succ]
    ring

theorem exists_reduced_discOne {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) :
    ∃ y, FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x y ∧
      y ∈ reducedSet K := by
  by_cases h : K.σ.rotOne (hb x) = 0
  · refine ⟨x, FoldRel.refl (hypDomain K).isOpen (discOne_subset_domain K hd), Or.inl ?_⟩
    by_contra hne
    exact rotOne_ne_zero K.hσ hd.1 hne h
  have hθ := K.σ.θ₁_pos
  have hθ' := K.σ.θ₁_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := -K.σ.θ₁) K.p₁_pos (HypFold.θ₁_mul K.σ)
    (by linarith) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwOne C hc h3 K hd k
  rw [← hrot] at hk1 hk2
  have hne : K.σ.rotOne (hb (K.screwOne^[k] x)) ≠ 0 := by
    rw [hrot]; exact circle_pow_mul_ne_zero _ _ h
  by_cases hs : 0 ≤ arg (K.σ.rotOne (hb (K.screwOne^[k] x)))
  · obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discOne K.hσ hd' hne
    exact ⟨_, hr, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨mem_triangle_of_discOne K.hσ hd' hs (by linarith), n0, n1, n2⟩)))⟩
  · push Not at hs
    refine ⟨K.screwThree (K.screwOne^[k] x),
      hr.trans (foldRel_screwThree_discOne C hc h3 K hd'), ?_⟩
    have hT := refl_one_mem_triangle K.hσ hd' hk1 hs
    have hd'' := refl_one_mem_discOne K.hσ hd'
    have hne' : K.σ.rotOne (K.σ.refl 1 (hb (K.screwOne^[k] x))) ≠ 0 := by
      rw [HypFold.rotOne_refl_one K.hσ, map_ne_zero]; exact hne
    obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discOne K.hσ hd'' hne'
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [K.conj_hb_screwThree]
    exact ⟨hT, n0, n1, n2⟩

theorem exists_reduced_discTwo {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) :
    ∃ y, FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x y ∧
      y ∈ reducedSet K := by
  by_cases h : K.σ.rotTwo (hb x) = 0
  · refine ⟨x, FoldRel.refl (hypDomain K).isOpen (discTwo_subset_domain K hd),
      Or.inr (Or.inl ?_)⟩
    by_contra hne
    exact rotTwo_ne_zero K.hσ hd.1 hne h
  have hθ := K.σ.θ₂_pos
  have hθ' := K.σ.θ₂_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := 0) K.p₂_pos (HypFold.θ₂_mul K.σ)
    (by linarith [Real.pi_pos]) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwTwo C hc h3 K hd k
  rw [← hrot] at hk1 hk2
  have hne : K.σ.rotTwo (hb (K.screwTwo^[k] x)) ≠ 0 := by
    rw [hrot]; exact circle_pow_mul_ne_zero _ _ h
  refine ⟨_, hr, ?_⟩
  by_cases hs : arg (K.σ.rotTwo (hb (K.screwTwo^[k] x))) ≤ K.σ.θ₂
  · obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discTwo K.hσ hd' hne
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨mem_triangle_of_discTwo K.hσ hd' hk1 hs, n0, n1, n2⟩)))
  · push Not at hs
    have hT := conj_mem_triangle_of_discTwo K.hσ hd' hs (by linarith)
    have hd'' := conj_mem_discTwo K.hσ hd'
    have hne' : K.σ.rotTwo (conj (hb (K.screwTwo^[k] x))) ≠ 0 := by
      have := HypFold.rotTwo_refl_zero K.hσ (hb (K.screwTwo^[k] x))
      change K.σ.rotTwo (conj _) = _ at this
      rw [this]
      exact mul_ne_zero (Complex.exp_ne_zero _) ((map_ne_zero _).2 hne)
    obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discTwo K.hσ hd'' hne'
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hT, n0, n1, n2⟩)))

theorem exists_reduced_discThree {x : ModelCoordinates} (hd : hb x ∈ discThree K.D) :
    ∃ y, FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x y ∧
      y ∈ reducedSet K := by
  by_cases h : hb x = 0
  · exact ⟨x, FoldRel.refl (hypDomain K).isOpen (discThree_subset_domain K hd),
      Or.inr (Or.inr (Or.inl h))⟩
  have hθ := K.σ.θ₃_pos
  have hθ' := K.σ.θ₃_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := -K.σ.θ₃) K.p₃_pos (HypFold.θ₃_mul K.σ)
    (by linarith) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwThree C hc h3 K hd k
  rw [← hrot] at hk1 hk2
  have hne : hb (K.screwThree^[k] x) ≠ 0 := by
    rw [hrot]; exact circle_pow_mul_ne_zero _ _ h
  refine ⟨_, hr, ?_⟩
  by_cases hs : 0 ≤ arg (hb (K.screwThree^[k] x))
  · obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discThree K.hσ hd' hne
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨mem_triangle_of_discThree K.hσ hd' hs (by linarith), n0, n1, n2⟩)))
  · push Not at hs
    have hT := conj_mem_triangle_of_discThree K.hσ hd' hk1 hs
    obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discThree K.hσ (conj_mem_discThree hd')
      ((map_ne_zero _).2 hne)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hT, n0, n1, n2⟩)))

end Iterate

section Reduce

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (hχ : d.orbChi < 0) (D : (C.closedHypShape hc h3 hχ).FoldData)

set_option hygiene false in
local notation "𝒦" => hypDatum C hc h3 hχ D

theorem hb_screwThree_symm (K : HypDatum) (x : ModelCoordinates) :
    hb (K.screwThree.symm x) = K.σ.refl 1 (conj (hb x)) := by
  rw [HypDatum.screwThree_symm, HypDatum.hb_rotThreeInv]

theorem hb_screwTwo_eq (K : HypDatum) (x : ModelCoordinates) :
    hb (K.screwTwo x) = K.σ.refl 2 (conj (hb x)) := by
  have h := K.hb_screwTwo_symm (K.screwTwo x)
  rw [Diffeomorph.symm_apply_apply] at h
  rw [h, Complex.conj_conj]
  exact (HypFold.refl_refl K.hσ 2 (norm_hypDisc_lt_one _)).symm

theorem exists_foldRel_reduced {y : ModelCoordinates} (hy : y ∈ hypDomain (𝒦)) :
    ∃ y₀, FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) y y₀ ∧
      y₀ ∈ reducedSet (𝒦) := by
  have hN := (hypDomain (𝒦)).isOpen
  have hσ := (𝒦).hσ
  change hb y ∈ hypBase (𝒦) at hy
  simp only [hypBase, mem_union, mem_ofPred_eq] at hy
  rcases hy with ((((hm | hm) | hd) | hd) | hd) | hd
  · by_cases hT : hb y ∈ (𝒦).σ.triangle
    · obtain ⟨n1, n2⟩ := HypDatum.mainSet_ne_vertex hσ hm
      exact ⟨y, FoldRel.refl hN (by
        change hb y ∈ hypBase (𝒦); exact main_subset_hypBase _ hm),
        Or.inr (Or.inr (Or.inr (Or.inl ⟨hT, ne_zero_of_main hσ hm, n1, n2⟩)))⟩
    rcases hm with ((h | h) | h) | h
    · exact absurd (intT_subset_triangle h) hT
    · have hi := refl_mem_intT_of_patchZero hσ h hT
      exact ⟨y, FoldRel.refl hN (by
          change hb y ∈ hypBase (𝒦); exact main_subset_hypBase _ (Or.inl (Or.inl
            (Or.inr h)))),
        Or.inr (Or.inr (Or.inr (Or.inr ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩)))⟩
    · have hi := refl_mem_intT_of_patchOne hσ h hT
      refine ⟨(𝒦).screwThree y, foldRel_screwThree_patchOne C hc h3 hχ D h, ?_⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      rw [HypDatum.conj_hb_screwThree]
      exact ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩
    · have hi := refl_mem_intT_of_patchTwo hσ h hT
      refine ⟨(𝒦).screwTwo.symm y, foldRel_screwTwoInv_patchTwo C hc h3 hχ D h, ?_⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      rw [HypDatum.hb_screwTwo_symm, Complex.conj_conj]
      exact ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩
  · by_cases hT : conj (hb y) ∈ (𝒦).σ.triangle
    · obtain ⟨n1, n2⟩ := HypDatum.mainSet_ne_vertex hσ hm
      exact ⟨y, FoldRel.refl hN (by
        change hb y ∈ hypBase (𝒦); exact conjMain_subset_hypBase _ hm),
        Or.inr (Or.inr (Or.inr (Or.inr ⟨hT, ne_zero_of_main hσ hm, n1, n2⟩)))⟩
    rcases hm with ((h | h) | h) | h
    · exact absurd (intT_subset_triangle h) hT
    · have hi := refl_mem_intT_of_patchZero hσ h hT
      change conj (conj (hb y)) ∈ _ at hi
      rw [Complex.conj_conj] at hi
      exact ⟨y, FoldRel.refl hN (by
          change hb y ∈ hypBase (𝒦); exact main_subset_hypBase _ (Or.inl (Or.inl
            (Or.inl hi)))),
        Or.inr (Or.inr (Or.inr (Or.inl ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩)))⟩
    · have hi := refl_mem_intT_of_patchOne hσ h hT
      have hp : hb ((𝒦).screwThree.symm y) ∈ patchOne (𝒦).D := by
        rw [hb_screwThree_symm]; exact refl_mem_patchOne hσ h
      have hr := foldRel_screwThree_patchOne C hc h3 hχ D hp
      rw [Diffeomorph.apply_symm_apply] at hr
      refine ⟨(𝒦).screwThree.symm y, hr.symm, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      rw [hb_screwThree_symm]
      exact ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩
    · have hi := refl_mem_intT_of_patchTwo hσ h hT
      have hp : hb ((𝒦).screwTwo y) ∈ patchTwo (𝒦).D := by
        rw [hb_screwTwo_eq]; exact refl_mem_patchTwo hσ h
      have hr := foldRel_screwTwoInv_patchTwo C hc h3 hχ D hp
      rw [Diffeomorph.symm_apply_apply] at hr
      refine ⟨(𝒦).screwTwo y, hr.symm, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      rw [hb_screwTwo_eq]
      exact ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩
  · exact exists_reduced_discOne C hc h3 _ hd
  · have hd' : hb ((𝒦).screwThree.symm y) ∈ discOne (𝒦).D := by
      rw [hb_screwThree_symm]
      exact refl_one_mem_discOne hσ ((mem_discOneMirror_iff _).1 hd)
    have hr := foldRel_screwThree_discOne C hc h3 _ hd'
    rw [Diffeomorph.apply_symm_apply] at hr
    obtain ⟨y₀, hr₀, hy₀⟩ := exists_reduced_discOne C hc h3 _ hd'
    exact ⟨y₀, hr.symm.trans hr₀, hy₀⟩
  · exact exists_reduced_discTwo C hc h3 _ hd
  · exact exists_reduced_discThree C hc h3 _ hd

end Reduce

end Hyp

end ClosedTriangle

end GC.Seifert
