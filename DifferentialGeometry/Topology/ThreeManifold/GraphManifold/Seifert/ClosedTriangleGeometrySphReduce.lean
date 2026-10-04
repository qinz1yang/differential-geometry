import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphRel
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphSurj
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatReduce

/-!
# Reduction of a spherical closed triangle fold to the doubled triangle

Lane B3d3, for B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`,
§6, with review 32 §7.1; the spherical analogue of `ClosedTriangleGeometryHypReduce`). On the
round sphere every point `hopfParam y` of the fold domain is related by the local composite
relation of `sphMap (sphFoldMap L C hc h3)` to `hopfParam y₀` with `y₀` over a vertex `v₁`, `v₂`,
`0`, over the triangle minus its vertices, or over the mirrored triangle minus its vertices
(`exists_foldRel_reduced`). Every step uses a generator of `SphRel` on the open piece where it is
valid: in a vertex disc a power of the screw of the vertex turns the rotated coordinate into the
window `[a, a + 2θ)` (`exists_reduced_discOne`, `…Two`, `…Three`), which is the closed sector
(`SphLayout.disc*_sector`) or its mirror; the lower half of the window about `v₁` is carried to
the mirror disc by the screw about `0`. The mirror disc about `v̄₁` (the repeated vertex `c₃ B₁`)
is moved back to the disc about `v₁` by `S₃⁻¹` (the inverse screw about `0`, read through
`foldRel_screwThree_discOne`). A wall patch point outside the triangle reflects into the open
triangle: over patch `0` the point is already on the mirror side, over patch `1` the screw about
`0` and over patch `2` the inverse screw about `v₂` move it there. The mirrored patch points are
handled by the inverse moves, which exist on `S³` only: `S₃⁻¹` is a global screw, and
`hopfParam (screwChart v θ s (screwChart v (-θ) (-s) y)) = hopfParam y` is the group identity
`screwSph v θ s * screwSph v (-θ) (-s) = 1` (`hopfParam_screwChart_neg`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

open TwoConeFold

def sphReducedSet (K : SphDatum) : Set ModelCoordinates :=
  {y | planeOf y = K.σ.vertexOne ∨ planeOf y = K.σ.vertexTwo ∨ planeOf y = 0 ∨
    (planeOf y ∈ K.σ.triangle ∧ planeOf y ≠ 0 ∧ planeOf y ≠ K.σ.vertexOne ∧
      planeOf y ≠ K.σ.vertexTwo) ∨
    (conj (planeOf y) ∈ K.σ.triangle ∧ conj (planeOf y) ≠ 0 ∧
      conj (planeOf y) ≠ K.σ.vertexOne ∧ conj (planeOf y) ≠ K.σ.vertexTwo)}

section Group

theorem screwSph_mul_neg (v : ℂ) (θ s : ℝ) : screwSph v θ s * screwSph v (-θ) (-s) = 1 := by
  have h0 : fibreLiftS3 0 = 1 := by
    apply Prod.ext
    · rfl
    · simp [fibreLiftS3]
  simp only [screwSph, mul_assoc]
  rw [← mul_assoc (recentreInvS3 v) (recentreS3 v), recentreInvS3_mul_recentreS3, one_mul,
    ← mul_assoc (screwLiftS3 0 θ s), screwLiftS3_mul, add_neg_cancel, add_neg_cancel,
    screwLiftS3_zero, h0, one_mul, recentreS3_mul_recentreInvS3]

theorem hopfParam_screwChart_neg {v : ℂ} {θ s : ℝ} {y : ModelCoordinates}
    (h1 : 1 + conj v * planeOf y ≠ 0)
    (h2 : 1 - conj v * planeOf (screwDiffeomorph (-θ) (-s) (centred v y)) ≠ 0)
    (h3 : 1 + conj v * planeOf (screwChart v (-θ) (-s) y) ≠ 0)
    (h4 : 1 - conj v * planeOf (screwDiffeomorph θ s (centred v (screwChart v (-θ) (-s) y))) ≠
      0) :
    hopfParam (screwChart v θ s (screwChart v (-θ) (-s) y)) = hopfParam y := by
  rw [← s3Diffeo_screwSph h3 h4, ← s3Diffeo_screwSph h1 h2, ← s3Diffeo_mul_apply,
    screwSph_mul_neg]
  exact Equiv.ext_iff.mp (map_one s3Perm) _

end Group

section Reduce

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)
  (D : (C.closedSphShape hc h3 hχ).FoldData) (L : SphLayout (sphDatum C hc h3 hχ D))

set_option hygiene false in
local notation "𝒦" => sphDatum C hc h3 hχ D

set_option hygiene false in
local notation "ℛ" => FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L))
  (sphMap (sphFoldMap L C hc h3))

theorem foldRel_refl_base {y : ModelCoordinates} (hy : planeOf y ∈ sphBase L) :
    (ℛ) (hopfParam y) (hopfParam y) :=
  FoldRel.refl (sphDomain (sphBase L) (isOpen_sphBase L)).isOpen
    (hopfParam_mem_sphDomain (isOpen_sphBase L) hy)

theorem eq_vertexOne_of_rotOne {z : ℂ} (hd : z ∈ L.discOne) (h : (𝒦).σ.rotOne z = 0) :
    z = (𝒦).σ.vertexOne := by
  by_contra hne
  exact rotOne_ne_zero L hd hne h

theorem eq_vertexTwo_of_rotTwo {z : ℂ} (hd : z ∈ L.discTwo) (h : (𝒦).σ.rotTwo z = 0) :
    z = (𝒦).σ.vertexTwo := by
  by_contra hne
  exact rotTwo_ne_zero L hd hne h

theorem ne_vertices_of_discOne {z : ℂ} (hd : z ∈ L.discOne) (h : (𝒦).σ.rotOne z ≠ 0) :
    z ≠ 0 ∧ z ≠ (𝒦).σ.vertexOne ∧ z ≠ (𝒦).σ.vertexTwo := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact disjoint_left.mp L.disjoint_one_three hd (zero_mem_discThree C hc h3 hχ D L)
  · rintro rfl
    exact h (rotOne_vertexOne C hc h3 hχ D)
  · rintro rfl
    exact disjoint_left.mp L.disjoint_one_two hd (vertexTwo_mem_discTwo C hc h3 hχ D L)

theorem ne_vertices_of_discTwo {z : ℂ} (hd : z ∈ L.discTwo) (h : (𝒦).σ.rotTwo z ≠ 0) :
    z ≠ 0 ∧ z ≠ (𝒦).σ.vertexOne ∧ z ≠ (𝒦).σ.vertexTwo := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact disjoint_left.mp L.disjoint_two_three hd (zero_mem_discThree C hc h3 hχ D L)
  · rintro rfl
    exact disjoint_left.mp L.disjoint_one_two (vertexOne_mem_discOne C hc h3 hχ D L) hd
  · rintro rfl
    exact h (rotTwo_vertexTwo C hc h3 hχ D)

theorem ne_vertices_of_discThree {z : ℂ} (hd : z ∈ L.discThree) (h : z ≠ 0) :
    z ≠ 0 ∧ z ≠ (𝒦).σ.vertexOne ∧ z ≠ (𝒦).σ.vertexTwo := by
  refine ⟨h, ?_, ?_⟩
  · rintro rfl
    exact disjoint_left.mp L.disjoint_one_three (vertexOne_mem_discOne C hc h3 hχ D L) hd
  · rintro rfl
    exact disjoint_left.mp L.disjoint_two_three (vertexTwo_mem_discTwo C hc h3 hχ D L) hd

theorem rotOne_screwChart_one {y : ModelCoordinates} (hy : planeOf y ∈ L.discOne) :
    (𝒦).σ.rotOne (planeOf (screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁)
      (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁) y)) =
        (Circle.exp (-2 * Real.pi / (𝒦).σ.p₁) : ℂ) * (𝒦).σ.rotOne (planeOf y) := by
  have hden := L.discOne_den _ hy (-2 * Real.pi / (𝒦).σ.p₁)
  have hy' : 1 - conj (𝒦).σ.vertexOne * planeOf (screwDiffeomorph (-2 * Real.pi / (𝒦).σ.p₁)
      (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁) (centred (𝒦).σ.vertexOne y)) ≠ 0 := by
    rw [planeOf_screwDiffeomorph, planeOf_centred]
    exact hden
  have hx' := (screwChart_mem_discOne C hc h3 hχ D L hy).1
  rw [rotOne_eq_of_sph (𝒦).hσ, rotOne_eq_of_sph (𝒦).hσ, disc_screwChart hy.1 hy' hx',
    Circle.coe_exp]
  ring

theorem rotTwo_screwChart_two {y : ModelCoordinates} (hy : planeOf y ∈ L.discTwo) :
    (𝒦).σ.rotTwo (planeOf (screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂)
      (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) y)) =
        (Circle.exp (-2 * Real.pi / (𝒦).σ.p₂) : ℂ) * (𝒦).σ.rotTwo (planeOf y) := by
  have hden := L.discTwo_den _ hy (-2 * Real.pi / (𝒦).σ.p₂)
  have hy' : 1 - conj (𝒦).σ.vertexTwo * planeOf (screwDiffeomorph (-2 * Real.pi / (𝒦).σ.p₂)
      (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) (centred (𝒦).σ.vertexTwo y)) ≠ 0 := by
    rw [planeOf_screwDiffeomorph, planeOf_centred]
    exact hden
  have hx' := (screwChart_mem_discTwo C hc h3 hχ D L hy).1
  rw [rotTwo_eq_of_sph (𝒦).hσ, rotTwo_eq_of_sph (𝒦).hσ, disc_screwChart hy.1 hy' hx',
    Circle.coe_exp]
  ring

theorem iterate_screwOne {x : ModelCoordinates} (hd : planeOf x ∈ L.discOne) (k : ℕ) :
    (ℛ) (hopfParam x) (hopfParam ((screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁)
        (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))^[k] x)) ∧
      planeOf ((screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁)
        (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))^[k] x) ∈ L.discOne ∧
      (𝒦).σ.rotOne (planeOf ((screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁)
        (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))^[k] x)) =
        (Circle.exp (-2 * Real.pi / (𝒦).σ.p₁) : ℂ) ^ k * (𝒦).σ.rotOne (planeOf x) := by
  induction k with
  | zero =>
    exact ⟨foldRel_refl_base C hc h3 hχ D L (disc_mem_base_one C hc h3 hχ D L hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwOne C hc h3 hχ D L hd'),
      screwChart_mem_discOne C hc h3 hχ D L hd', ?_⟩
    rw [rotOne_screwChart_one C hc h3 hχ D L hd', hrot, pow_succ]
    ring

theorem iterate_screwTwo {x : ModelCoordinates} (hd : planeOf x ∈ L.discTwo) (k : ℕ) :
    (ℛ) (hopfParam x) (hopfParam ((screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂)
        (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂))^[k] x)) ∧
      planeOf ((screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂)
        (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂))^[k] x) ∈ L.discTwo ∧
      (𝒦).σ.rotTwo (planeOf ((screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂)
        (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂))^[k] x)) =
        (Circle.exp (-2 * Real.pi / (𝒦).σ.p₂) : ℂ) ^ k * (𝒦).σ.rotTwo (planeOf x) := by
  induction k with
  | zero =>
    exact ⟨foldRel_refl_base C hc h3 hχ D L (disc_mem_base_two C hc h3 hχ D L hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwTwo C hc h3 hχ D L hd'),
      screwChart_mem_discTwo C hc h3 hχ D L hd', ?_⟩
    rw [rotTwo_screwChart_two C hc h3 hχ D L hd', hrot, pow_succ]
    ring

theorem iterate_screwThree {x : ModelCoordinates} (hd : planeOf x ∈ L.discThree) (k : ℕ) :
    (ℛ) (hopfParam x)
        (hopfParam ((screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift)^[k] x)) ∧
      planeOf ((screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift)^[k] x) ∈
        L.discThree ∧
      planeOf ((screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift)^[k] x) =
        (Circle.exp (-2 * Real.pi / (𝒦).σ.p₃) : ℂ) ^ k * planeOf x := by
  induction k with
  | zero =>
    exact ⟨foldRel_refl_base C hc h3 hχ D L (disc_mem_base_three C hc h3 hχ D L hd), hd,
      by simp⟩
  | succ k ih =>
    obtain ⟨hr, hd', hrot⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hr.trans (foldRel_screwThree C hc h3 hχ D L hd'),
      screwZero_mem_discThree C hc h3 hχ D L hd', ?_⟩
    rw [(𝒦).planeOf_screwZero, hrot, pow_succ]
    ring

theorem exists_reduced_discOne {x : ModelCoordinates} (hd : planeOf x ∈ L.discOne) :
    ∃ y, (ℛ) (hopfParam x) (hopfParam y) ∧ y ∈ sphReducedSet (𝒦) := by
  by_cases h : (𝒦).σ.rotOne (planeOf x) = 0
  · exact ⟨x, foldRel_refl_base C hc h3 hχ D L (disc_mem_base_one C hc h3 hχ D L hd),
      Or.inl (eq_vertexOne_of_rotOne C hc h3 hχ D L hd h)⟩
  have hθ := (𝒦).σ.θ₁_pos
  have hθ' := (𝒦).σ.θ₁_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := -(𝒦).σ.θ₁) (𝒦).p₁_pos (𝒦).θ₁_mul
    (by linarith [Real.pi_pos]) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwOne C hc h3 hχ D L hd k
  rw [← hrot] at hk1 hk2
  have hne : (𝒦).σ.rotOne (planeOf ((screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁)
      (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))^[k] x)) ≠ 0 := by
    rw [hrot]
    exact circle_pow_mul_ne_zero _ _ h
  by_cases hs : 0 ≤ arg ((𝒦).σ.rotOne (planeOf ((screwChart (𝒦).σ.vertexOne
      (-2 * Real.pi / (𝒦).σ.p₁) (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))^[k] x)))
  · exact ⟨_, hr, Or.inr (Or.inr (Or.inr (Or.inl ⟨L.discOne_sector _ hd' hs (by linarith),
      ne_vertices_of_discOne C hc h3 hχ D L hd' hne⟩)))⟩
  · push Not at hs
    refine ⟨_, hr.trans (foldRel_screwThree_discOne C hc h3 hχ D L hd'), ?_⟩
    have hd'' := L.refl_one_mem_discOne hd'
    have hrr := rotOne_refl_one_sph (𝒦).hσ (planeOf ((screwChart (𝒦).σ.vertexOne
      (-2 * Real.pi / (𝒦).σ.p₁) (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))^[k] x))
    have ha := arg_conj_of_neg hs
    have hne' : (𝒦).σ.rotOne ((𝒦).σ.refl 1 (planeOf ((screwChart (𝒦).σ.vertexOne
        (-2 * Real.pi / (𝒦).σ.p₁) (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))^[k] x))) ≠ 0 := by
      rw [hrr, map_ne_zero]
      exact hne
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [(𝒦).conj_planeOf_screwZero]
    exact ⟨L.discOne_sector _ hd'' (by rw [hrr, ha]; linarith) (by rw [hrr, ha]; linarith),
      ne_vertices_of_discOne C hc h3 hχ D L hd'' hne'⟩

theorem exists_reduced_discTwo {x : ModelCoordinates} (hd : planeOf x ∈ L.discTwo) :
    ∃ y, (ℛ) (hopfParam x) (hopfParam y) ∧ y ∈ sphReducedSet (𝒦) := by
  by_cases h : (𝒦).σ.rotTwo (planeOf x) = 0
  · exact ⟨x, foldRel_refl_base C hc h3 hχ D L (disc_mem_base_two C hc h3 hχ D L hd),
      Or.inr (Or.inl (eq_vertexTwo_of_rotTwo C hc h3 hχ D L hd h))⟩
  have hθ := (𝒦).σ.θ₂_pos
  have hθ' := (𝒦).σ.θ₂_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := 0) (𝒦).p₂_pos (𝒦).θ₂_mul
    (by linarith [Real.pi_pos]) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwTwo C hc h3 hχ D L hd k
  rw [← hrot] at hk1 hk2
  set z := planeOf ((screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂)
    (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂))^[k] x) with hz
  have hne : (𝒦).σ.rotTwo z ≠ 0 := by
    rw [hrot]
    exact circle_pow_mul_ne_zero _ _ h
  refine ⟨_, hr, ?_⟩
  by_cases hs : arg ((𝒦).σ.rotTwo z) ≤ (𝒦).σ.θ₂
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨L.discTwo_sector _ hd' hk1 hs,
      ne_vertices_of_discTwo C hc h3 hχ D L hd' hne⟩)))
  · push Not at hs
    have hcw : conj ((𝒦).σ.rotTwo z) ≠ 0 := (map_ne_zero _).2 hne
    have hneg : arg (conj ((𝒦).σ.rotTwo z)) = -arg ((𝒦).σ.rotTwo z) := by
      rw [arg_conj, ite_eq_right_iff.mpr (fun h' => absurd h' (by linarith))]
    have hr' : (𝒦).σ.rotTwo (conj z) =
        exp ((2 * (𝒦).σ.θ₂ : ℝ) * I) * conj ((𝒦).σ.rotTwo z) := by
      rw [rotTwo_conj_sph (𝒦).hσ]
      congr 2
      push_cast
      ring
    have harg : arg ((𝒦).σ.rotTwo (conj z)) = 2 * (𝒦).σ.θ₂ - arg ((𝒦).σ.rotTwo z) := by
      rw [hr', arg_exp_mul' hcw (by rw [hneg]; linarith) (by rw [hneg]; linarith), hneg]
      ring
    have hd'' := L.conj_mem_discTwo hd'
    have hne' : (𝒦).σ.rotTwo (conj z) ≠ 0 := by
      rw [hr']
      exact mul_ne_zero (Complex.exp_ne_zero _) hcw
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨L.discTwo_sector _ hd''
      (by rw [harg]; linarith) (by rw [harg]; linarith),
      ne_vertices_of_discTwo C hc h3 hχ D L hd'' hne'⟩)))

theorem exists_reduced_discThree {x : ModelCoordinates} (hd : planeOf x ∈ L.discThree) :
    ∃ y, (ℛ) (hopfParam x) (hopfParam y) ∧ y ∈ sphReducedSet (𝒦) := by
  by_cases h : planeOf x = 0
  · exact ⟨x, foldRel_refl_base C hc h3 hχ D L (disc_mem_base_three C hc h3 hχ D L hd),
      Or.inr (Or.inr (Or.inl h))⟩
  have hθ := (𝒦).σ.θ₃_pos
  have hθ' := (𝒦).σ.θ₃_le
  obtain ⟨k, hk1, hk2⟩ := exists_rot_window (a := -(𝒦).σ.θ₃) (𝒦).p₃_pos (𝒦).θ₃_mul
    (by linarith [Real.pi_pos]) (by linarith) h
  obtain ⟨hr, hd', hrot⟩ := iterate_screwThree C hc h3 hχ D L hd k
  rw [← hrot] at hk1 hk2
  set z := planeOf ((screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift)^[k] x) with hz
  have hne : z ≠ 0 := by
    rw [hrot]
    exact circle_pow_mul_ne_zero _ _ h
  refine ⟨_, hr, ?_⟩
  by_cases hs : 0 ≤ arg z
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨L.discThree_sector _ hd' hs (by linarith),
      ne_vertices_of_discThree C hc h3 hχ D L hd' hne⟩)))
  · push Not at hs
    have ha := arg_conj_of_neg hs
    have hd'' := L.conj_mem_discThree hd'
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨L.discThree_sector _ hd''
      (by rw [ha]; linarith) (by rw [ha]; linarith),
      ne_vertices_of_discThree C hc h3 hχ D L hd'' ((map_ne_zero _).2 hne)⟩)))

theorem refl_one_refl_one (z : ℂ) : (𝒦).σ.refl 1 ((𝒦).σ.refl 1 z) = z := by
  change exp (2 * ((𝒦).σ.θ₃ : ℂ) * I) * conj (exp (2 * ((𝒦).σ.θ₃ : ℂ) * I) * conj z) = z
  rw [map_mul, conj_conj, ← exp_conj, ← mul_assoc, ← exp_add]
  simp only [map_mul, map_ofNat, conj_ofReal, conj_I]
  ring_nf
  rw [exp_zero, one_mul]

theorem screwZero_neg (y : ModelCoordinates) :
    screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift
      (screwDiffeomorph (-(𝒦).screwZeroAngle) (-(𝒦).screwZeroShift) y) = y :=
  screwDiffeomorph_screwDiffeomorph _ _ y

theorem planeOf_screwZero_neg (y : ModelCoordinates) :
    planeOf (screwDiffeomorph (-(𝒦).screwZeroAngle) (-(𝒦).screwZeroShift) y) =
      (𝒦).σ.refl 1 (conj (planeOf y)) := by
  have h := (𝒦).conj_planeOf_screwZero
    (screwDiffeomorph (-(𝒦).screwZeroAngle) (-(𝒦).screwZeroShift) y)
  rw [screwZero_neg C hc h3 hχ D] at h
  rw [h, refl_one_refl_one C hc h3 hχ D]

theorem exists_reduced_discOneMirror {y : ModelCoordinates} (hd : planeOf y ∈ L.discOneMirror) :
    ∃ y₀, (ℛ) (hopfParam y) (hopfParam y₀) ∧ y₀ ∈ sphReducedSet (𝒦) := by
  have hd' : planeOf (screwDiffeomorph (-(𝒦).screwZeroAngle) (-(𝒦).screwZeroShift) y) ∈
      L.discOne := by
    rw [planeOf_screwZero_neg C hc h3 hχ D]
    exact L.refl_one_mem_discOne hd
  have hr := foldRel_screwThree_discOne C hc h3 hχ D L hd'
  rw [screwZero_neg C hc h3 hχ D] at hr
  obtain ⟨y₀, hr₀, hy₀⟩ := exists_reduced_discOne C hc h3 hχ D L hd'
  exact ⟨y₀, hr.symm.trans hr₀, hy₀⟩

theorem exists_reduced_main {y : ModelCoordinates} (hm : planeOf y ∈ L.mainSet) :
    ∃ y₀, (ℛ) (hopfParam y) (hopfParam y₀) ∧ y₀ ∈ sphReducedSet (𝒦) := by
  have hb := main_mem_base C hc h3 hχ D L hm
  by_cases hT : planeOf y ∈ (𝒦).σ.triangle
  · exact ⟨y, foldRel_refl_base C hc h3 hχ D L hb,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨hT, L.main_ne _ hm⟩)))⟩
  have hO : ∀ {w : ℂ}, w ∈ (𝒦).σ.openTriangle →
      w ∈ (𝒦).σ.triangle ∧ w ≠ 0 ∧ w ≠ (𝒦).σ.vertexOne ∧ w ≠ (𝒦).σ.vertexTwo :=
    fun hw => ⟨(𝒦).σ.openTriangle_subset hw, L.main_ne _ (Or.inl (Or.inl (Or.inl hw)))⟩
  rcases hm with ((h | h) | h) | h
  · exact absurd ((𝒦).σ.openTriangle_subset h) hT
  · exact ⟨y, foldRel_refl_base C hc h3 hχ D L hb,
      Or.inr (Or.inr (Or.inr (Or.inr (hO (L.patchZero_out _ h hT)))))⟩
  · refine ⟨_, foldRel_screwThree_patchOne C hc h3 hχ D L h,
      Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    rw [(𝒦).conj_planeOf_screwZero]
    exact hO (L.patchOne_out _ h hT)
  · refine ⟨_, foldRel_screwTwoInv_patchTwo C hc h3 hχ D L h,
      Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    rw [screwTwoInv_mem_conjMain C hc h3 hχ D]
    exact hO (L.patchTwo_out _ h hT)

theorem conj_den_neg {v : ℂ} (hv : conj v = v) (θ : ℝ) (z : ℂ) :
    conj (1 - conj v * (exp (((-θ : ℝ) : ℂ) * I) * discV v z)) =
      1 - conj v * (exp ((θ : ℂ) * I) * discV v (conj z)) := by
  rw [discV_conj_of_real hv, map_sub, map_one, map_mul, map_mul, ← exp_conj, hv]
  congr 4
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast
  ring

theorem planeOf_screwChart_neg_two (y : ModelCoordinates) :
    planeOf (screwChart (𝒦).σ.vertexTwo (-(2 * Real.pi / (𝒦).σ.p₂))
      (-((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂)) y) = (𝒦).σ.refl 2 (conj (planeOf y)) := by
  have hv := conj_vertexTwo_sph (𝒦).σ
  have hE : conj (exp (((2 * Real.pi / (𝒦).σ.p₂ : ℝ) : ℂ) * I)) =
      exp (((-(2 * Real.pi / (𝒦).σ.p₂) : ℝ) : ℂ) * I) := by
    rw [← exp_conj]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  rw [← conj_conj ((𝒦).σ.refl 2 _), (𝒦).conj_refl_two_sph, SphDatum.planeOf_screwChart,
    discV_conj_of_real hv]
  simp only [map_div₀, map_add, map_sub, map_one, map_mul, conj_conj, hv, hE]

theorem exists_reduced_conjMain {y : ModelCoordinates} (hm : conj (planeOf y) ∈ L.mainSet) :
    ∃ y₀, (ℛ) (hopfParam y) (hopfParam y₀) ∧ y₀ ∈ sphReducedSet (𝒦) := by
  have hb := conjMain_mem_base C hc h3 hχ D L hm
  by_cases hT : conj (planeOf y) ∈ (𝒦).σ.triangle
  · exact ⟨y, foldRel_refl_base C hc h3 hχ D L hb,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨hT, L.main_ne _ hm⟩)))⟩
  have hO : ∀ {w : ℂ}, w ∈ (𝒦).σ.openTriangle →
      w ∈ (𝒦).σ.triangle ∧ w ≠ 0 ∧ w ≠ (𝒦).σ.vertexOne ∧ w ≠ (𝒦).σ.vertexTwo :=
    fun hw => ⟨(𝒦).σ.openTriangle_subset hw, L.main_ne _ (Or.inl (Or.inl (Or.inl hw)))⟩
  have hwm := hm
  rcases hm with ((h | h) | h) | h
  · exact absurd ((𝒦).σ.openTriangle_subset h) hT
  · have hi := L.patchZero_out _ h hT
    rw [conj_conj] at hi
    exact ⟨y, foldRel_refl_base C hc h3 hχ D L hb, Or.inr (Or.inr (Or.inr (Or.inl (hO hi))))⟩
  · have hp := planeOf_screwZero_neg C hc h3 hχ D y
    have hp1 : planeOf (screwDiffeomorph (-(𝒦).screwZeroAngle) (-(𝒦).screwZeroShift) y) ∈
        L.patchOne := by
      rw [hp]
      exact (L.patchOne_spec _ h).2.2
    have hr := foldRel_screwThree_patchOne C hc h3 hχ D L hp1
    rw [screwZero_neg C hc h3 hχ D] at hr
    refine ⟨_, hr.symm, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
    rw [hp]
    exact hO (L.patchOne_out _ h hT)
  · have hv := conj_vertexTwo_sph (𝒦).σ
    have hp := planeOf_screwChart_neg_two C hc h3 hχ D y
    have hrp := (L.patchTwo_spec _ h).2.2.2.2
    have hp2 : planeOf (screwChart (𝒦).σ.vertexTwo (-(2 * Real.pi / (𝒦).σ.p₂))
        (-((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂)) y) ∈ L.patchTwo := by
      rw [hp]
      exact hrp
    have h1 : 1 + conj (𝒦).σ.vertexTwo * planeOf y ≠ 0 := by
      have e : 1 + conj (𝒦).σ.vertexTwo * planeOf y =
          conj (1 + conj (𝒦).σ.vertexTwo * conj (planeOf y)) := by
        simp only [map_add, map_one, map_mul, conj_conj, hv]
      rw [e, map_ne_zero]
      exact slitPlane_ne_zero (L.main_slit _ hwm).2
    have h2 : 1 - conj (𝒦).σ.vertexTwo * planeOf (screwDiffeomorph (-(2 * Real.pi / (𝒦).σ.p₂))
        (-((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂)) (centred (𝒦).σ.vertexTwo y)) ≠ 0 := by
      rw [planeOf_screwDiffeomorph, planeOf_centred]
      intro h0
      apply den_patchTwo C hc h3 hχ D L h
      have := congrArg conj h0
      rw [conj_den_neg hv, map_zero] at this
      exact this
    have h3' : 1 + conj (𝒦).σ.vertexTwo * planeOf (screwChart (𝒦).σ.vertexTwo
        (-(2 * Real.pi / (𝒦).σ.p₂)) (-((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂)) y) ≠ 0 :=
      slitPlane_ne_zero (L.main_slit _ (Or.inr hp2)).2
    have h4 : 1 - conj (𝒦).σ.vertexTwo * planeOf (screwDiffeomorph (2 * Real.pi / (𝒦).σ.p₂)
        ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) (centred (𝒦).σ.vertexTwo (screwChart (𝒦).σ.vertexTwo
          (-(2 * Real.pi / (𝒦).σ.p₂)) (-((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂)) y))) ≠ 0 := by
      rw [planeOf_screwDiffeomorph, planeOf_centred]
      exact den_patchTwo C hc h3 hχ D L hp2
    have hr := foldRel_screwTwoInv_patchTwo C hc h3 hχ D L hp2
    rw [hopfParam_screwChart_neg h1 h2 h3' h4] at hr
    refine ⟨_, hr.symm, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
    rw [hp]
    exact hO (L.patchTwo_out _ h hT)

theorem exists_foldRel_reduced {y : ModelCoordinates} (hy : planeOf y ∈ sphBase L) :
    ∃ y₀, FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L))
      (sphMap (sphFoldMap L C hc h3)) (hopfParam y) (hopfParam y₀) ∧
        y₀ ∈ sphReducedSet (sphDatum C hc h3 hχ D) := by
  simp only [sphBase, mem_union, mem_ofPred_eq] at hy
  rcases hy with ((((hm | hm) | hd) | hd) | hd) | hd
  · exact exists_reduced_main C hc h3 hχ D L hm
  · exact exists_reduced_conjMain C hc h3 hχ D L hm
  · exact exists_reduced_discOne C hc h3 hχ D L hd
  · exact exists_reduced_discOneMirror C hc h3 hχ D L hd
  · exact exists_reduced_discTwo C hc h3 hχ D L hd
  · exact exists_reduced_discThree C hc h3 hχ D L hd

end Reduce

end Sph

end ClosedTriangle

end GC.Seifert
