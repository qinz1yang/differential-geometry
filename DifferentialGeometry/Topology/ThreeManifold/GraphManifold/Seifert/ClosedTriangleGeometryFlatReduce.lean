import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatMoves

/-!
# Reduction of a flat closed triangle fold to the doubled triangle

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§3 step 2, with review 27). Every point `y` of the fold domain is related by the local composite
relation to a point over a vertex `v₁`, `v₂`, `0`, or over the triangle minus its vertices, or over
the mirrored triangle minus its vertices (`exists_foldRel_reduced`):
* in a vertex disc a power of the screw of the vertex turns the disc coordinate into the window
  `[a, a + 2θ)` (`exists_rot_window`), which is the triangle sector and the adjacent mirrored
  sector (for `v₁` the adjacent sector `r₁ T` is moved to the mirror by `S₃`);
* on the mirrored disc about `v̄₁` the inverse of `S₃` moves to the disc about `v₁`;
* a wall patch point outside the triangle reflects into the open triangle, and the matching side
  pairing (`S₃` for wall 1, `S₂⁻¹` for wall 2) moves it into the mirrored open triangle.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

section Angles

theorem im_nonpos_of_arg_nonpos {x : ℂ} (h : arg x ≤ 0) : x.im ≤ 0 := by
  rcases h.lt_or_eq with h | h
  · exact (arg_neg_iff.mp h).le
  · exact (arg_eq_zero_iff.mp h).2.le

theorem arg_exp_mul' {θ : ℝ} {w : ℂ} (hw : w ≠ 0) (h1 : -Real.pi < θ + arg w)
    (h2 : θ + arg w ≤ Real.pi) : arg (exp (θ * I) * w) = θ + arg w :=
  arg_exp_mul_of_mem hw h1 h2

theorem arg_real_mul_exp {r β : ℝ} (hr : 0 < r) (h1 : -Real.pi < β) (h2 : β ≤ Real.pi) :
    arg ((r : ℂ) * exp (β * I)) = β := by
  rw [arg_real_mul _ hr, exp_mul_I, arg_cos_add_sin_mul_I ⟨h1, h2⟩]

theorem exists_rot_window {θ a : ℝ} {p : ℕ} (hp : 0 < p) (hθ : θ * p = Real.pi)
    (ha : -Real.pi < a) (ha2 : a + 2 * θ ≤ Real.pi) {w : ℂ} (hw : w ≠ 0) :
    ∃ k : ℕ, a ≤ arg ((Circle.exp (-2 * Real.pi / p) : ℂ) ^ k * w) ∧
      arg ((Circle.exp (-2 * Real.pi / p) : ℂ) ^ k * w) < a + 2 * θ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hθp : θ = Real.pi / p := by rw [← hθ, mul_div_cancel_right₀ _ hp0]
  have hθ0 : 0 < θ := by rw [hθp]; exact div_pos Real.pi_pos (by exact_mod_cast hp)
  set n : ℤ := ⌊(arg w - a) / (2 * θ)⌋ with hn
  set β : ℝ := arg w - 2 * n * θ with hβ
  have hfl := Int.floor_le ((arg w - a) / (2 * θ))
  have hlt := Int.lt_floor_add_one ((arg w - a) / (2 * θ))
  rw [← hn] at hfl hlt
  have h2θ : 0 < 2 * θ := by linarith
  have hb1 : a ≤ β := by
    rw [le_div_iff₀ h2θ] at hfl
    rw [hβ]; nlinarith
  have hb2 : β < a + 2 * θ := by
    rw [div_lt_iff₀ h2θ] at hlt
    rw [hβ]; nlinarith
  refine ⟨(n % p).toNat, ?_⟩
  have hmod : ((n % p).toNat : ℤ) = n % p := Int.toNat_of_nonneg (Int.emod_nonneg _
    (by exact_mod_cast hp.ne'))
  have hdecomp : n = n % p + p * (n / p) := by
    have := Int.mul_ediv_add_emod n p
    linarith
  have hkey : ((Circle.exp (-2 * Real.pi / p) : ℂ) ^ (n % p).toNat * w) =
      (‖w‖ : ℂ) * exp (β * I) := by
    rw [← Circle.coe_pow, ← zpow_natCast, circle_exp_pow, Circle.coe_exp]
    conv_lhs => rw [← norm_mul_exp_arg_mul_I w]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 1
    have hj : (((n % p).toNat : ℤ) : ℝ) * (-2 * Real.pi / p) + arg w =
        β + ((n / p : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hmod, hβ, hθp]
      have : ((n : ℤ) : ℝ) = ((n % p : ℤ) : ℝ) + p * ((n / p : ℤ) : ℝ) := by
        conv_lhs => rw [hdecomp]
        push_cast
        ring
      rw [this]
      field_simp
      ring
    rw [← add_mul, ← ofReal_add, hj, ofReal_add, add_mul, Complex.exp_add]
    rw [show (((((n / p : ℤ) : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) * I =
      ((n / p : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring, Complex.exp_int_mul_two_pi_mul_I,
      mul_one]
  rw [hkey, arg_real_mul_exp (norm_pos_iff.mpr hw) (by linarith) (by linarith)]
  exact ⟨hb1, hb2⟩

theorem im_rot_nonpos_of_arg_le {w : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2)
    (h0 : 0 ≤ arg w) (h1 : arg w ≤ θ) : (exp (-((θ : ℂ) * I)) * w).im ≤ 0 := by
  by_cases hw : w = 0
  · rw [hw, mul_zero, zero_im]
  have hexp : exp (-((θ : ℂ) * I)) = exp (((-θ : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  rw [hexp]
  apply im_nonpos_of_arg_nonpos
  rw [arg_exp_mul' hw (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  linarith

end Angles

section SectorsT

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

theorem mem_triangle_of_discOne {z : ℂ} (hd : z ∈ discOne D) (h0 : 0 ≤ arg (σ.rotOne z))
    (h1 : arg (σ.rotOne z) ≤ σ.θ₁) : z ∈ σ.triangle := by
  have hρ := rhoZero_pos (σ := σ)
  intro i
  fin_cases i
  · have := wallSide_zero_of_mem_discOne D hd
    change 0 ≤ σ.wallSide 0 z
    linarith
  · change 0 ≤ σ.wallSide 1 z
    rw [σ.wallSide_one_eq_im_rotOne]
    exact arg_nonneg_iff.mp h0
  · change 0 ≤ σ.wallSide 2 z
    rw [σ.wallSide_two_eq_rotOne]
    linarith [im_rot_nonpos_of_arg_le σ.θ₁_pos σ.θ₁_le h0 h1]

theorem mem_triangle_of_discTwo {z : ℂ} (hd : z ∈ discTwo D) (h0 : 0 ≤ arg (σ.rotTwo z))
    (h1 : arg (σ.rotTwo z) ≤ σ.θ₂) : z ∈ σ.triangle := by
  have hρ := rhoZero_pos (σ := σ)
  intro i
  fin_cases i
  · change 0 ≤ σ.wallSide 0 z
    rw [σ.wallSide_zero_eq_rotTwo]
    linarith [im_rot_nonpos_of_arg_le σ.θ₂_pos σ.θ₂_le h0 h1]
  · have := wallSide_one_of_mem_discTwo D hd
    change 0 ≤ σ.wallSide 1 z
    linarith
  · exact arg_nonneg_iff.mp h0

theorem mem_triangle_of_discThree {z : ℂ} (hd : z ∈ discThree D) (h0 : 0 ≤ arg z)
    (h1 : arg z ≤ σ.θ₃) : z ∈ σ.triangle := by
  have hρ := rhoZero_pos (σ := σ)
  intro i
  fin_cases i
  · exact arg_nonneg_iff.mp h0
  · change 0 ≤ σ.wallSide 1 z
    rw [σ.wallSide_one_eq_rotThree]
    linarith [im_rot_nonpos_of_arg_le σ.θ₃_pos σ.θ₃_le h0 h1]
  · have := wallSide_two_of_mem_discThree D hd
    change 0 ≤ σ.wallSide 2 z
    linarith

theorem arg_conj_of_neg {w : ℂ} (h : arg w < 0) : arg (conj w) = -arg w := by
  rw [arg_conj, ite_eq_right_iff.mpr (fun h' => absurd h' (by linarith [Real.pi_pos]))]

theorem refl_one_mem_triangle {z : ℂ} (hd : z ∈ discOne D) (h0 : -σ.θ₁ ≤ arg (σ.rotOne z))
    (h1 : arg (σ.rotOne z) < 0) : σ.refl 1 z ∈ σ.triangle := by
  have ha := arg_conj_of_neg h1
  apply mem_triangle_of_discOne D (refl_one_mem_discOne D hd)
  · rw [σ.rotOne_refl_one, ha]; linarith
  · rw [σ.rotOne_refl_one, ha]; linarith

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
    have := σ.rotTwo_refl_zero z
    change σ.rotTwo (conj z) = _ at this
    rw [this]
    congr 2
    push_cast
    ring
  have harg : arg (σ.rotTwo (conj z)) = 2 * σ.θ₂ - arg (σ.rotTwo z) := by
    rw [hr, arg_exp_mul' hcw (by rw [hneg]; linarith) (by rw [hneg]; linarith), hneg]
    ring
  apply mem_triangle_of_discTwo D (conj_mem_discTwo D hd)
  · rw [harg]; linarith
  · rw [harg]; linarith

theorem conj_mem_triangle_of_discThree {z : ℂ} (hd : z ∈ discThree D)
    (h0 : -σ.θ₃ ≤ arg z) (h1 : arg z < 0) : conj z ∈ σ.triangle := by
  have ha := arg_conj_of_neg h1
  apply mem_triangle_of_discThree D (conj_mem_discThree D hd)
  · rw [ha]; linarith
  · rw [ha]; linarith

theorem ne_vertices_of_discOne {z : ℂ} (hd : z ∈ discOne D) (h : σ.rotOne z ≠ 0) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨fun h0 => ?_, fun h1 => h (by rw [h1, σ.rotOne_vertexOne]), fun h2 => ?_⟩
  · apply disjoint_left.mp (disjoint_discOne_discThree D) hd
    change ‖z‖ < _; rw [h0, norm_zero]; exact radThree_pos D
  · apply disjoint_left.mp (disjoint_discOne_discTwo D) hd
    change ‖z - σ.vertexTwo‖ < _; rw [h2, sub_self, norm_zero]; exact radTwo_pos D

theorem ne_vertices_of_discTwo {z : ℂ} (hd : z ∈ discTwo D) (h : σ.rotTwo z ≠ 0) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => h (by rw [h2, σ.rotTwo_vertexTwo])⟩
  · apply disjoint_left.mp (disjoint_discTwo_discThree D) hd
    change ‖z‖ < _; rw [h0, norm_zero]; exact radThree_pos D
  · apply disjoint_left.mp (disjoint_discOne_discTwo D) _ hd
    change ‖z - σ.vertexOne‖ < _; rw [h1, sub_self, norm_zero]; exact radOne_pos D

theorem ne_vertices_of_discThree {z : ℂ} (hd : z ∈ discThree D) (h : z ≠ 0) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨h, fun h1 => ?_, fun h2 => ?_⟩
  · apply disjoint_left.mp (disjoint_discOne_discThree D) _ hd
    change ‖z - σ.vertexOne‖ < _; rw [h1, sub_self, norm_zero]; exact radOne_pos D
  · apply disjoint_left.mp (disjoint_discTwo_discThree D) _ hd
    change ‖z - σ.vertexTwo‖ < _; rw [h2, sub_self, norm_zero]; exact radTwo_pos D

theorem ne_vertices_of_intT {z : ℂ} (h : z ∈ intT σ) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo :=
  ⟨ne_zero_of_mem_intT h, ne_vertexOne_of_mem_intT h, ne_vertexTwo_of_mem_intT h⟩

theorem ne_zero_of_main {z : ℂ} (hm : z ∈ mainSet D) : z ≠ 0 := by
  have hk := kap_pos D
  rintro rfl
  rcases hm with ((h | h) | h) | h
  · exact ne_zero_of_mem_intT h rfl
  · have := h.2.1; rw [σ.wallSide_one_zero] at this; linarith
  · have := h.2.1; rw [σ.wallSide_zero_zero] at this; linarith
  · have := h.2.1; rw [σ.wallSide_zero_zero] at this; linarith

end SectorsT

def reducedSet (K : FlatDatum) : Set ModelCoordinates :=
  {y | planeOf y = K.σ.vertexOne ∨ planeOf y = K.σ.vertexTwo ∨ planeOf y = 0 ∨
    (planeOf y ∈ K.σ.triangle ∧ planeOf y ≠ 0 ∧ planeOf y ≠ K.σ.vertexOne ∧
      planeOf y ≠ K.σ.vertexTwo) ∨
    (conj (planeOf y) ∈ K.σ.triangle ∧ conj (planeOf y) ≠ 0 ∧ conj (planeOf y) ≠ K.σ.vertexOne ∧
      conj (planeOf y) ≠ K.σ.vertexTwo)}

section Iterate

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (K : FlatDatum)

theorem discOne_subset_domain {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) :
    x ∈ flatDomain K := by
  change planeOf x ∈ flatBase K
  simp only [flatBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inr hd)))

theorem discTwo_subset_domain {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) :
    x ∈ flatDomain K := by
  change planeOf x ∈ flatBase K
  simp only [flatBase, mem_union]
  exact Or.inl (Or.inr hd)

theorem discThree_subset_domain {x : ModelCoordinates} (hd : planeOf x ∈ discThree K.D) :
    x ∈ flatDomain K := by
  change planeOf x ∈ flatBase K
  simp only [flatBase, mem_union]
  exact Or.inr hd

theorem iterate_screwOne {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) (k : ℕ) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x (K.screwOne^[k] x) ∧
      planeOf (K.screwOne^[k] x) ∈ discOne K.D ∧
      K.σ.rotOne (planeOf (K.screwOne^[k] x)) =
        (Circle.exp (-2 * Real.pi / K.σ.p₁) : ℂ) ^ k * K.σ.rotOne (planeOf x) := by
  induction k with
  | zero => exact ⟨FoldRel.refl (flatDomain K).isOpen (discOne_subset_domain K hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwOne C hc h3 K hd'), K.screwOne_mem_discOne hd', ?_⟩
    rw [K.rotOne_screwOne, hrot, pow_succ]
    ring

theorem iterate_screwTwo {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) (k : ℕ) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x (K.screwTwo^[k] x) ∧
      planeOf (K.screwTwo^[k] x) ∈ discTwo K.D ∧
      K.σ.rotTwo (planeOf (K.screwTwo^[k] x)) =
        (Circle.exp (-2 * Real.pi / K.σ.p₂) : ℂ) ^ k * K.σ.rotTwo (planeOf x) := by
  induction k with
  | zero => exact ⟨FoldRel.refl (flatDomain K).isOpen (discTwo_subset_domain K hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwTwo C hc h3 K hd'), K.screwTwo_mem_discTwo hd', ?_⟩
    rw [K.rotTwo_screwTwo, hrot, pow_succ]
    ring

theorem iterate_screwThree {x : ModelCoordinates} (hd : planeOf x ∈ discThree K.D) (k : ℕ) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x (K.screwThree^[k] x) ∧
      planeOf (K.screwThree^[k] x) ∈ discThree K.D ∧
      planeOf (K.screwThree^[k] x) =
        (Circle.exp (-2 * Real.pi / K.σ.p₃) : ℂ) ^ k * planeOf x := by
  induction k with
  | zero => exact ⟨FoldRel.refl (flatDomain K).isOpen (discThree_subset_domain K hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwThree C hc h3 K hd'), K.screwThree_mem_discThree hd', ?_⟩
    rw [K.planeOf_screwThree, hrot, pow_succ]
    ring

theorem rotOne_eq_zero_iff (σ : EuclidShape) {z : ℂ} : σ.rotOne z = 0 ↔ z = σ.vertexOne := by
  constructor
  · intro h
    rw [EuclidShape.rotOne, neg_eq_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (Complex.exp_ne_zero _)
    · exact sub_eq_zero.mp h
  · rintro rfl; exact σ.rotOne_vertexOne

theorem rotTwo_eq_zero_iff (σ : EuclidShape) {z : ℂ} : σ.rotTwo z = 0 ↔ z = σ.vertexTwo := by
  constructor
  · intro h
    rw [EuclidShape.rotTwo, neg_eq_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (Complex.exp_ne_zero _)
    · exact sub_eq_zero.mp h
  · rintro rfl; exact σ.rotTwo_vertexTwo

theorem circle_pow_mul_ne_zero (a : ℝ) (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (Circle.exp a : ℂ) ^ k * w ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (Circle.coe_ne_zero _)) hw

theorem exists_reduced_discOne {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) :
    ∃ y, FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x y ∧
      y ∈ reducedSet K := by
  by_cases h : K.σ.rotOne (planeOf x) = 0
  · exact ⟨x, FoldRel.refl (flatDomain K).isOpen (discOne_subset_domain K hd),
      Or.inl ((rotOne_eq_zero_iff K.σ).1 h)⟩
  have hθ := K.σ.θ₁_pos
  have hθ' := K.σ.θ₁_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := -K.σ.θ₁) K.p₁_pos K.σ.θ₁_mul
    (by linarith) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwOne C hc h3 K hd k
  rw [← hrot] at hk1 hk2
  have hne : K.σ.rotOne (planeOf (K.screwOne^[k] x)) ≠ 0 := by
    rw [hrot]; exact circle_pow_mul_ne_zero _ _ h
  by_cases hs : 0 ≤ arg (K.σ.rotOne (planeOf (K.screwOne^[k] x)))
  · obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discOne K.D hd' hne
    exact ⟨_, hr, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨mem_triangle_of_discOne K.D hd' hs (by linarith), n0, n1, n2⟩)))⟩
  · push Not at hs
    refine ⟨K.screwThree (K.screwOne^[k] x),
      hr.trans (foldRel_screwThree_discOne C hc h3 K hd'), ?_⟩
    have hT := refl_one_mem_triangle K.D hd' hk1 hs
    have hd'' := refl_one_mem_discOne K.D hd'
    have hne' : K.σ.rotOne (K.σ.refl 1 (planeOf (K.screwOne^[k] x))) ≠ 0 := by
      rw [K.σ.rotOne_refl_one, map_ne_zero]; exact hne
    obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discOne K.D hd'' hne'
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [K.conj_planeOf_screwThree]
    exact ⟨hT, n0, n1, n2⟩

theorem exists_reduced_discTwo {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) :
    ∃ y, FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x y ∧
      y ∈ reducedSet K := by
  by_cases h : K.σ.rotTwo (planeOf x) = 0
  · exact ⟨x, FoldRel.refl (flatDomain K).isOpen (discTwo_subset_domain K hd),
      Or.inr (Or.inl ((rotTwo_eq_zero_iff K.σ).1 h))⟩
  have hθ := K.σ.θ₂_pos
  have hθ' := K.σ.θ₂_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := 0) K.p₂_pos K.σ.θ₂_mul
    (by linarith [Real.pi_pos]) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwTwo C hc h3 K hd k
  rw [← hrot] at hk1 hk2
  have hne : K.σ.rotTwo (planeOf (K.screwTwo^[k] x)) ≠ 0 := by
    rw [hrot]; exact circle_pow_mul_ne_zero _ _ h
  refine ⟨_, hr, ?_⟩
  by_cases hs : arg (K.σ.rotTwo (planeOf (K.screwTwo^[k] x))) ≤ K.σ.θ₂
  · obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discTwo K.D hd' hne
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨mem_triangle_of_discTwo K.D hd' hk1 hs, n0, n1, n2⟩)))
  · push Not at hs
    have hT := conj_mem_triangle_of_discTwo K.D hd' hs (by linarith)
    have hd'' := conj_mem_discTwo K.D hd'
    have hne' : K.σ.rotTwo (conj (planeOf (K.screwTwo^[k] x))) ≠ 0 := by
      have := K.σ.rotTwo_refl_zero (planeOf (K.screwTwo^[k] x))
      change K.σ.rotTwo (conj _) = _ at this
      rw [this]
      exact mul_ne_zero (Complex.exp_ne_zero _) ((map_ne_zero _).2 hne)
    obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discTwo K.D hd'' hne'
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hT, n0, n1, n2⟩)))

theorem exists_reduced_discThree {x : ModelCoordinates} (hd : planeOf x ∈ discThree K.D) :
    ∃ y, FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x y ∧
      y ∈ reducedSet K := by
  by_cases h : planeOf x = 0
  · exact ⟨x, FoldRel.refl (flatDomain K).isOpen (discThree_subset_domain K hd),
      Or.inr (Or.inr (Or.inl h))⟩
  have hθ := K.σ.θ₃_pos
  have hθ' := K.σ.θ₃_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := -K.σ.θ₃) K.p₃_pos K.σ.θ₃_mul
    (by linarith) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwThree C hc h3 K hd k
  rw [← hrot] at hk1 hk2
  have hne : planeOf (K.screwThree^[k] x) ≠ 0 := by
    rw [hrot]; exact circle_pow_mul_ne_zero _ _ h
  refine ⟨_, hr, ?_⟩
  by_cases hs : 0 ≤ arg (planeOf (K.screwThree^[k] x))
  · obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discThree K.D hd' hne
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨mem_triangle_of_discThree K.D hd' hs (by linarith), n0, n1, n2⟩)))
  · push Not at hs
    have hT := conj_mem_triangle_of_discThree K.D hd' hk1 hs
    obtain ⟨n0, n1, n2⟩ := ne_vertices_of_discThree K.D (conj_mem_discThree K.D hd')
      ((map_ne_zero _).2 hne)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hT, n0, n1, n2⟩)))

end Iterate

section Reduce

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (h0 : d.orbChi = 0) (D : (C.closedEuclidShape hc h3 h0).toCompactShape.FoldData)

set_option hygiene false in
local notation "𝒦" => flatDatum C hc h3 h0 D

theorem planeOf_screwThree_symm (K : FlatDatum) (x : ModelCoordinates) :
    planeOf (K.screwThree.symm x) = K.σ.refl 1 (conj (planeOf x)) := by
  rw [FlatDatum.screwThree_symm, FlatDatum.rotThreeInv, planeOf_ofPlane]

theorem planeOf_screwTwo_symm (K : FlatDatum) (x : ModelCoordinates) :
    planeOf (K.screwTwo.symm x) = conj (K.σ.refl 2 (planeOf x)) := by
  rw [FlatDatum.screwTwo_symm, FlatDatum.rotTwoInv, planeOf_ofPlane]

theorem planeOf_screwTwo_eq (K : FlatDatum) (x : ModelCoordinates) :
    planeOf (K.screwTwo x) = K.σ.refl 2 (conj (planeOf x)) := by
  have h := planeOf_screwTwo_symm K (K.screwTwo x)
  rw [Diffeomorph.symm_apply_apply] at h
  rw [h, Complex.conj_conj, K.σ.refl_refl]

theorem exists_foldRel_reduced {y : ModelCoordinates} (hy : y ∈ flatDomain (𝒦)) :
    ∃ y₀, FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) y y₀ ∧
      y₀ ∈ reducedSet (𝒦) := by
  have hN := (flatDomain (𝒦)).isOpen
  change planeOf y ∈ flatBase (𝒦) at hy
  simp only [flatBase, mem_union, mem_ofPred_eq] at hy
  rcases hy with ((((hm | hm) | hd) | hd) | hd) | hd
  · by_cases hT : planeOf y ∈ (𝒦).σ.triangle
    · obtain ⟨n1, n2⟩ := FlatDatum.mainSet_ne_vertex hm
      exact ⟨y, FoldRel.refl hN (by
        change planeOf y ∈ flatBase (𝒦); exact main_subset_flatBase _ hm),
        Or.inr (Or.inr (Or.inr (Or.inl ⟨hT, ne_zero_of_main _ hm, n1, n2⟩)))⟩
    rcases hm with ((h | h) | h) | h
    · exact absurd (intT_subset_triangle h) hT
    · have hi := refl_mem_intT_of_patchZero _ h hT
      exact ⟨y, FoldRel.refl hN (by
          change planeOf y ∈ flatBase (𝒦); exact main_subset_flatBase _ (Or.inl (Or.inl
            (Or.inr h)))),
        Or.inr (Or.inr (Or.inr (Or.inr ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩)))⟩
    · have hi := refl_mem_intT_of_patchOne _ h hT
      refine ⟨(𝒦).screwThree y, foldRel_screwThree_patchOne C hc h3 h0 D h, ?_⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      rw [FlatDatum.conj_planeOf_screwThree]
      exact ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩
    · have hi := refl_mem_intT_of_patchTwo _ h hT
      refine ⟨(𝒦).screwTwo.symm y, foldRel_screwTwoInv_patchTwo C hc h3 h0 D h, ?_⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      rw [planeOf_screwTwo_symm, Complex.conj_conj]
      exact ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩
  · by_cases hT : conj (planeOf y) ∈ (𝒦).σ.triangle
    · obtain ⟨n1, n2⟩ := FlatDatum.mainSet_ne_vertex hm
      exact ⟨y, FoldRel.refl hN (by
        change planeOf y ∈ flatBase (𝒦); exact conjMain_subset_flatBase _ hm),
        Or.inr (Or.inr (Or.inr (Or.inr ⟨hT, ne_zero_of_main _ hm, n1, n2⟩)))⟩
    rcases hm with ((h | h) | h) | h
    · exact absurd (intT_subset_triangle h) hT
    · have hi := refl_mem_intT_of_patchZero _ h hT
      change conj (conj (planeOf y)) ∈ _ at hi
      rw [Complex.conj_conj] at hi
      exact ⟨y, FoldRel.refl hN (by
          change planeOf y ∈ flatBase (𝒦); exact main_subset_flatBase _ (Or.inl (Or.inl
            (Or.inl hi)))),
        Or.inr (Or.inr (Or.inr (Or.inl ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩)))⟩
    · have hi := refl_mem_intT_of_patchOne _ h hT
      have hp : planeOf ((𝒦).screwThree.symm y) ∈ patchOne (𝒦).D := by
        rw [planeOf_screwThree_symm]; exact refl_mem_patchOne _ h
      have hr := foldRel_screwThree_patchOne C hc h3 h0 D hp
      rw [Diffeomorph.apply_symm_apply] at hr
      refine ⟨(𝒦).screwThree.symm y, hr.symm, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      rw [planeOf_screwThree_symm]
      exact ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩
    · have hi := refl_mem_intT_of_patchTwo _ h hT
      have hp : planeOf ((𝒦).screwTwo y) ∈ patchTwo (𝒦).D := by
        rw [planeOf_screwTwo_eq]; exact refl_mem_patchTwo _ h
      have hr := foldRel_screwTwoInv_patchTwo C hc h3 h0 D hp
      rw [Diffeomorph.symm_apply_apply] at hr
      refine ⟨(𝒦).screwTwo y, hr.symm, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      rw [planeOf_screwTwo_eq]
      exact ⟨intT_subset_triangle hi, ne_vertices_of_intT hi⟩
  · exact exists_reduced_discOne C hc h3 _ hd
  · have hd' : planeOf ((𝒦).screwThree.symm y) ∈ discOne (𝒦).D := by
      rw [planeOf_screwThree_symm]
      exact refl_one_mem_discOne _ ((mem_discOneMirror_iff _).1 hd)
    have hr := foldRel_screwThree_discOne C hc h3 _ hd'
    rw [Diffeomorph.apply_symm_apply] at hr
    obtain ⟨y₀, hr₀, hy₀⟩ := exists_reduced_discOne C hc h3 _ hd'
    exact ⟨y₀, hr.symm.trans hr₀, hy₀⟩
  · exact exists_reduced_discTwo C hc h3 _ hd
  · exact exists_reduced_discThree C hc h3 _ hd

end Reduce

end ClosedTriangle

end GC.Seifert
