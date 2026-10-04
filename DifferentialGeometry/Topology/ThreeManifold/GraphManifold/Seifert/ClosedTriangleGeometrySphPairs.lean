import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphRel
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphSurj
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphReduce
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphTriangle
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatPairs

/-!
# Same-image pairs of a spherical closed triangle fold

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §6, with
DB3 §3 steps 1, 3, 4 and review 32 §7.1). Two reduced points (over a vertex, over the triangle
minus its vertices, or over its mirror) with the same image under the fold are related by the
local composite relation of the round sphere (`foldRel_of_reduced`):
* over a vertex: the image is a core circle, the tube coordinates agree, and with the Bézout
  column a power of the screw of the vertex (which fixes the vertex fibre and shifts it by
  `-ℓ q/p`, `screwChart_vertex`) followed by a deck translation moves one to the other
  (`foldRel_vertex_fibre`); the lifted relations carry `s3Period` powers, which disappear on the
  sphere;
* over the triangle or its mirror: `P` is injective, so the base lifts agree; `f` is injective on
  the triangle and real exactly on the walls, so the base points agree, or they are a wall-1 pair
  (`S₃`), a wall-2 pair (`S₂⁻¹`, or `S₃ S₁` near `v₁`), or the same point of wall 0; then the fibre
  coordinates differ by a deck translation.
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

theorem screwChart_vertex {v : ℂ} {θ s : ℝ} {y : ModelCoordinates} (hy : planeOf y = v) :
    planeOf (screwChart v θ s y) = v ∧ screwChart v θ s y 2 = y 2 + s := by
  have hpos : (0 : ℝ) < 1 + normSq v := by have := normSq_nonneg v; linarith
  have harg : arg (1 + conj v * v) = 0 := by
    rw [mul_comm, mul_conj, show (1 : ℂ) + (normSq v : ℂ) = ((1 + normSq v : ℝ) : ℂ) by
      push_cast; ring]
    exact arg_ofReal_of_nonneg hpos.le
  have hc : centred v y = ofPlane 0 (y 2) := by
    rw [centred, hy, sub_self, zero_div, harg, add_zero]
  have hp : planeOf (screwDiffeomorph θ s (ofPlane 0 (y 2))) = 0 := by
    rw [planeOf_screwDiffeomorph, planeOf_ofPlane, mul_zero]
  have h2 : screwDiffeomorph θ s (ofPlane 0 (y 2)) 2 = y 2 + s := by
    rw [screwDiffeomorph_two, ofPlane_apply_two]
  refine ⟨?_, ?_⟩
  · rw [screwChart, hc, uncentred, planeOf_ofPlane, hp, zero_add, mul_zero, sub_zero, div_one]
  · rw [screwChart, hc, uncentred, ofPlane_apply_two, hp, mul_zero, sub_zero, arg_one, add_zero,
      h2]

theorem screwZero_vertex {θ s : ℝ} {y : ModelCoordinates} (hy : planeOf y = 0) :
    planeOf (screwDiffeomorph θ s y) = 0 ∧ screwDiffeomorph θ s y 2 = y 2 + s :=
  ⟨by rw [planeOf_screwDiffeomorph, hy, mul_zero], screwDiffeomorph_two θ s y⟩

section VertexFibre

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)
  (D : (C.closedSphShape hc h3 hχ).FoldData) (L : SphLayout (sphDatum C hc h3 hχ D))

set_option hygiene false in
local notation "𝒦" => sphDatum C hc h3 hχ D

set_option hygiene false in
local notation "𝒢" => sphFoldMap L C hc h3

set_option hygiene false in
local notation "ℛ" => FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L))
  (sphMap (sphFoldMap L C hc h3))

theorem eq_shift_of {y y' : ModelCoordinates} (hp : planeOf y' = planeOf y) {n : ℤ}
    (h2 : y' 2 / (𝒦).ℓ = y 2 / (𝒦).ℓ + n) :
    y' = y + GC.Geometry.fibreShift (n * (𝒦).ℓ) := by
  apply modelCoordinates_ext
  · rw [SphDatum.planeOf_add_fibreShift', hp]
  · have hℓ := (𝒦).ℓ_ne
    have : (y + GC.Geometry.fibreShift (n * (𝒦).ℓ)) 2 = y 2 + n * (𝒦).ℓ := by
      simp [GC.Geometry.fibreShift]
    rw [this]
    field_simp at h2
    linarith

theorem foldRel_vertex_fibre (σ : ModelCoordinates → ModelCoordinates) (v : ℂ)
    {p : ℕ} (hp : 0 < p) {q a b : ℤ} (hb : (p : ℤ) * b - a * q = 1)
    (hvb : v ∈ sphBase L)
    (hS : ∀ y : ModelCoordinates, planeOf y = v →
      ℛ (hopfParam y) (hopfParam (σ y)) ∧ planeOf (σ y) = v ∧ σ y 2 = y 2 - (𝒦).ℓ * q / p)
    {y y' : ModelCoordinates} (hy : planeOf y = v) (hy' : planeOf y' = v) (n : ℤ)
    (h2 : y' 2 / (𝒦).ℓ = y 2 / (𝒦).ℓ + n / p) :
    ℛ (hopfParam y) (hopfParam y') := by
  have hN : IsOpen ((sphDomain (sphBase L) (isOpen_sphBase L) : Set RoundThree)) :=
    (sphDomain (sphBase L) (isOpen_sphBase L)).isOpen
  have hit : ∀ k : ℕ, ℛ (hopfParam y) (hopfParam (σ^[k] y)) ∧ planeOf (σ^[k] y) = v ∧
      (σ^[k] y) 2 = y 2 - k * ((𝒦).ℓ * q / p) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, hy, by simp⟩
      exact FoldRel.refl hN ⟨y, show planeOf y ∈ sphBase L by rw [hy]; exact hvb, rfl⟩
    | succ k ih =>
      obtain ⟨hr, hv, h2k⟩ := ih
      obtain ⟨hr', hv', h2'⟩ := hS _ hv
      rw [Function.iterate_succ_apply']
      refine ⟨hr.trans hr', hv', ?_⟩
      rw [h2', h2k]
      push_cast
      ring
  set r := (n * a) % (p : ℤ) with hr
  set Q := (n * a) / (p : ℤ) with hQ
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have hdiv : n * a = p * Q + r := by
    have := Int.mul_ediv_add_emod (n * a) p
    linarith
  obtain ⟨hrel, hv, h2k⟩ := hit r.toNat
  have hcast : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hr0
  have hy'eq : y' = σ^[r.toNat] y + GC.Geometry.fibreShift ((n * b - Q * q : ℤ) * (𝒦).ℓ) := by
    apply eq_shift_of C hc h3 hχ D (by rw [hv, hy'])
    rw [h2k, hcast, h2]
    have hℓ := (𝒦).ℓ_ne
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hb' : (p : ℝ) * b - a * q = 1 := by exact_mod_cast hb
    have hdiv' : (n : ℝ) * a = p * Q + r := by exact_mod_cast hdiv
    have key : (n : ℝ) = -(r : ℝ) * q + p * (n * b - Q * q) := by
      linear_combination (-(n : ℝ)) * hb' - (q : ℝ) * hdiv'
    have e1 : (y 2 - (r : ℝ) * ((𝒦).ℓ * q / p)) / (𝒦).ℓ = y 2 / (𝒦).ℓ - (r : ℝ) * q / p := by
      field_simp
    have e2 : (n : ℝ) / p = -(r : ℝ) * q / p + (n * b - Q * q) := by
      field_simp
      linear_combination key
    rw [e1]
    push_cast
    linear_combination e2
  rw [hy'eq]
  have hb' : planeOf (σ^[r.toNat] y) ∈ sphBase L := by rw [hv]; exact hvb
  exact hrel.trans (foldRel_deck C hc h3 hχ D L _ hb')

theorem tubeOne_snd_eq {x x' : ModelCoordinates}
    (hx : planeOf x = (𝒦).σ.vertexOne) (hx' : planeOf x' = (𝒦).σ.vertexOne)
    (h : (𝒦).tubeOne x = (𝒦).tubeOne x') :
    ∃ n : ℤ, x' 2 / (𝒦).ℓ = x 2 / (𝒦).ℓ + n / (𝒦).σ.p₁ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : ((𝒦).σ.p₁ : ℝ) ≠ 0 := by exact_mod_cast (𝒦).p₁_pos.ne'
  simp only [SphDatum.sOne, hx, hx'] at hn
  field_simp
  linear_combination hn

theorem tubeTwo_snd_eq {x x' : ModelCoordinates}
    (hx : planeOf x = (𝒦).σ.vertexTwo) (hx' : planeOf x' = (𝒦).σ.vertexTwo)
    (h : (𝒦).tubeTwo x = (𝒦).tubeTwo x') :
    ∃ n : ℤ, x' 2 / (𝒦).ℓ = x 2 / (𝒦).ℓ + n / (𝒦).σ.p₂ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : ((𝒦).σ.p₂ : ℝ) ≠ 0 := by exact_mod_cast (𝒦).p₂_pos.ne'
  simp only [SphDatum.sTwo, hx, hx'] at hn
  field_simp
  linear_combination hn

theorem tubeThree_snd_eq {x x' : ModelCoordinates} (h : (𝒦).tubeThree x = (𝒦).tubeThree x') :
    ∃ n : ℤ, x' 2 / (𝒦).ℓ = x 2 / (𝒦).ℓ + n / (𝒦).σ.p₃ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : ((𝒦).σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast (𝒦).p₃_pos.ne'
  simp only [SphDatum.sThree] at hn
  field_simp
  linear_combination hn

theorem foldRel_vertexOne {x x' : ModelCoordinates} (hx : planeOf x = (𝒦).σ.vertexOne)
    (hx' : planeOf x' = (𝒦).σ.vertexOne) (h : (𝒢) x = (𝒢) x') :
    ℛ (hopfParam x) (hopfParam x') := by
  have hd := vertexOne_mem_discOne C hc h3 hχ D L
  rw [sphFoldMap_of_discOne L C hc h3 (hx ▸ hd), sphFoldMap_of_discOne L C hc h3 (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeOne_fst L (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeOne_fst L (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeOne_snd_eq C hc h3 hχ D hx hx' ht
  refine foldRel_vertex_fibre C hc h3 hχ D L
    (screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁) (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))
    (𝒦).σ.vertexOne (𝒦).p₁_pos (𝒦).bez₁ (disc_mem_base_one C hc h3 hχ D L hd) ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := screwChart_vertex (θ := -2 * Real.pi / (𝒦).σ.p₁)
    (s := -(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁) hy
  refine ⟨foldRel_screwOne C hc h3 hχ D L (hy ▸ hd), h1, ?_⟩
  rw [h2]
  ring

theorem foldRel_vertexTwo {x x' : ModelCoordinates} (hx : planeOf x = (𝒦).σ.vertexTwo)
    (hx' : planeOf x' = (𝒦).σ.vertexTwo) (h : (𝒢) x = (𝒢) x') :
    ℛ (hopfParam x) (hopfParam x') := by
  have hd := vertexTwo_mem_discTwo C hc h3 hχ D L
  rw [sphFoldMap_of_discTwo L C hc h3 (hx ▸ hd), sphFoldMap_of_discTwo L C hc h3 (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeTwo_fst L (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeTwo_fst L (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeTwo_snd_eq C hc h3 hχ D hx hx' ht
  refine foldRel_vertex_fibre C hc h3 hχ D L
    (screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂) (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂))
    (𝒦).σ.vertexTwo (𝒦).p₂_pos (𝒦).bez₂ (disc_mem_base_two C hc h3 hχ D L hd) ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := screwChart_vertex (θ := -2 * Real.pi / (𝒦).σ.p₂)
    (s := -(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) hy
  refine ⟨foldRel_screwTwo C hc h3 hχ D L (hy ▸ hd), h1, ?_⟩
  rw [h2]
  ring

theorem foldRel_vertexThree {x x' : ModelCoordinates} (hx : planeOf x = 0)
    (hx' : planeOf x' = 0) (h : (𝒢) x = (𝒢) x') :
    ℛ (hopfParam x) (hopfParam x') := by
  have hd := zero_mem_discThree C hc h3 hχ D L
  rw [sphFoldMap_of_discThree L C hc h3 (hx ▸ hd),
    sphFoldMap_of_discThree L C hc h3 (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeThree_fst L (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeThree_fst L (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeThree_snd_eq C hc h3 hχ D ht
  refine foldRel_vertex_fibre C hc h3 hχ D L
    (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift) 0 (𝒦).p₃_pos (𝒦).bez₃
    (disc_mem_base_three C hc h3 hχ D L hd) ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := screwZero_vertex (θ := (𝒦).screwZeroAngle) (s := (𝒦).screwZeroShift) hy
  refine ⟨foldRel_screwThree C hc h3 hχ D L (hy ▸ hd), h1, ?_⟩
  rw [h2, SphDatum.screwZeroShift]
  ring

theorem sphFoldMap_vertex_core {x : ModelCoordinates}
    (hx : planeOf x = (𝒦).σ.vertexOne ∨ planeOf x = (𝒦).σ.vertexTwo ∨ planeOf x = 0) :
    ∃ j : Fin 3, ∃ w : Circle, (𝒢) x = C.tubeMap (C.closedHoleEquiv hc h3 j) (0, w) ∧
      planeOf x = (if j = 1 then (𝒦).σ.vertexOne else if j = 2 then (𝒦).σ.vertexTwo else 0) := by
  rcases hx with hx | hx | hx
  · refine ⟨1, ((𝒦).tubeOne x).2, ?_, by simp [hx]⟩
    rw [sphFoldMap_of_discOne L C hc h3 (hx ▸ vertexOne_mem_discOne C hc h3 hχ D L)]
    congr 1
    refine Prod.ext ?_ rfl
    change (𝒦).σ.rotOne (planeOf x) * _ = 0
    rw [hx, rotOne_vertexOne C hc h3 hχ D, zero_mul]
  · refine ⟨2, ((𝒦).tubeTwo x).2, ?_, by simp [hx]⟩
    rw [sphFoldMap_of_discTwo L C hc h3 (hx ▸ vertexTwo_mem_discTwo C hc h3 hχ D L)]
    congr 1
    refine Prod.ext ?_ rfl
    change (𝒦).σ.rotTwo (planeOf x) * _ = 0
    rw [hx, rotTwo_vertexTwo C hc h3 hχ D, zero_mul]
  · refine ⟨0, ((𝒦).tubeThree x).2, ?_, by simp [hx]⟩
    rw [sphFoldMap_of_discThree L C hc h3 (hx ▸ zero_mem_discThree C hc h3 hχ D L)]
    congr 1
    refine Prod.ext ?_ rfl
    change _ * planeOf x * _ = 0
    rw [hx, mul_zero, zero_mul]

theorem liftP_mem_closedDomain_of_T {x : ModelCoordinates} (hT : planeOf x ∈ (𝒦).σ.triangle)
    (h0 : planeOf x ≠ 0) (h1 : planeOf x ≠ (𝒦).σ.vertexOne)
    (h2 : planeOf x ≠ (𝒦).σ.vertexTwo) : (𝒦).liftP x ∈ closedDomain := by
  refine ⟨(SphLayout.norm_f_lt_of_triangle hT h0), fun h => h1 ?_, fun h => h2 ?_⟩
  · exact (𝒦).D.eq_of_f_eq ⟨hT, h0⟩ (𝒦).σ.vertexOne_mem_diff (h.trans (𝒦).D.f_vertexOne.symm)
  · exact (𝒦).D.eq_of_f_eq ⟨hT, h0⟩ (𝒦).σ.vertexTwo_mem_diff (h.trans (𝒦).D.f_vertexTwo.symm)

theorem liftM_fst (x : ModelCoordinates) :
    ((𝒦).liftM x).1 = conj ((𝒦).D.f (conj (planeOf x))) := by
  change conj ((𝒦).D.f (planeOf (reflectMap (𝒦).c₀ x))) = _
  rw [planeOf_reflectMap]

theorem liftM_mem_closedDomain_of_T {x : ModelCoordinates}
    (hT : conj (planeOf x) ∈ (𝒦).σ.triangle) (h0 : conj (planeOf x) ≠ 0)
    (h1 : conj (planeOf x) ≠ (𝒦).σ.vertexOne) (h2 : conj (planeOf x) ≠ (𝒦).σ.vertexTwo) :
    (𝒦).liftM x ∈ closedDomain := by
  have hP := liftP_mem_closedDomain_of_T C hc h3 hχ D (x := reflectMap (𝒦).c₀ x)
    (by rw [planeOf_reflectMap]; exact hT) (by rw [planeOf_reflectMap]; exact h0)
    (by rw [planeOf_reflectMap]; exact h1) (by rw [planeOf_reflectMap]; exact h2)
  obtain ⟨a, b, c⟩ := hP
  change ‖conj ((𝒦).liftP (reflectMap (𝒦).c₀ x)).1‖ < 7 / 2 ∧
    conj ((𝒦).liftP (reflectMap (𝒦).c₀ x)).1 ≠ 3 / 2 ∧
      conj ((𝒦).liftP (reflectMap (𝒦).c₀ x)).1 ≠ -(3 / 2)
  rw [Complex.norm_conj]
  refine ⟨a, fun h => b ?_, fun h => c ?_⟩
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this

theorem foldRel_of_liftP_eq {x x' : ModelCoordinates} (hx : planeOf x ∈ sphBase L)
    (hT : planeOf x ∈ (𝒦).σ.triangle) (h0 : planeOf x ≠ 0)
    (hT' : planeOf x' ∈ (𝒦).σ.triangle) (h0' : planeOf x' ≠ 0) (h : (𝒦).liftP x = (𝒦).liftP x') :
    ℛ (hopfParam x) (hopfParam x') := by
  have hz : planeOf x' = planeOf x :=
    ((𝒦).D.eq_of_f_eq ⟨hT, h0⟩ ⟨hT', h0'⟩ (congrArg Prod.fst h)).symm
  have h2 := congrArg Prod.snd h
  change eC (x 2 / (𝒦).ℓ) * (𝒦).psiC (planeOf x) =
    eC (x' 2 / (𝒦).ℓ) * (𝒦).psiC (planeOf x') at h2
  rw [hz] at h2
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (mul_right_cancel h2)
  rw [eq_shift_of C hc h3 hχ D hz hn]
  exact foldRel_deck C hc h3 hχ D L n hx

theorem foldRel_of_liftM_eq {x x' : ModelCoordinates} (hx : planeOf x ∈ sphBase L)
    (hT : conj (planeOf x) ∈ (𝒦).σ.triangle) (h0 : conj (planeOf x) ≠ 0)
    (hT' : conj (planeOf x') ∈ (𝒦).σ.triangle) (h0' : conj (planeOf x') ≠ 0)
    (h : (𝒦).liftM x = (𝒦).liftM x') : ℛ (hopfParam x) (hopfParam x') := by
  have h' : (𝒦).liftP (reflectMap (𝒦).c₀ x) = (𝒦).liftP (reflectMap (𝒦).c₀ x') := by
    have := congrArg conjPair h
    simpa only [SphDatum.liftM, conjPair_conjPair] using this
  have hz : conj (planeOf x') = conj (planeOf x) := by
    have := ((𝒦).D.eq_of_f_eq ⟨hT, h0⟩ ⟨hT', h0'⟩ (by
      have := congrArg Prod.fst h'
      simpa only [SphDatum.liftP, planeOf_reflectMap] using this)).symm
    exact this
  have hz' : planeOf x' = planeOf x := by simpa using congrArg conj hz
  have h2 := congrArg Prod.snd h'
  change eC (reflectMap (𝒦).c₀ x 2 / (𝒦).ℓ) * (𝒦).psiC (planeOf (reflectMap (𝒦).c₀ x)) =
    eC (reflectMap (𝒦).c₀ x' 2 / (𝒦).ℓ) * (𝒦).psiC (planeOf (reflectMap (𝒦).c₀ x')) at h2
  rw [planeOf_reflectMap, planeOf_reflectMap, hz] at h2
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (mul_right_cancel h2)
  rw [reflectMap_two, reflectMap_two] at hn
  have hn' : x' 2 / (𝒦).ℓ = x 2 / (𝒦).ℓ + ((-n : ℤ) : ℝ) := by
    have hℓ := (𝒦).ℓ_ne
    push_cast
    field_simp at hn ⊢
    linarith
  rw [eq_shift_of C hc h3 hχ D hz' hn']
  exact foldRel_deck C hc h3 hχ D L _ hx

end VertexFibre

section Final

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)
  (D : (C.closedSphShape hc h3 hχ).FoldData) (L : SphLayout (sphDatum C hc h3 hχ D))

set_option hygiene false in
local notation "𝒦" => sphDatum C hc h3 hχ D

set_option hygiene false in
local notation "𝒢" => sphFoldMap L C hc h3

set_option hygiene false in
local notation "ℛ" => FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L))
  (sphMap (sphFoldMap L C hc h3))

theorem map_eq_of_foldRel {x x₁ : ModelCoordinates} (hr : ℛ (hopfParam x) (hopfParam x₁)) :
    (𝒢) x₁ = (𝒢) x := by
  have := hr.map_eq
  rwa [sphMap_hopfParam (hper_sph C hc h3 hχ D L),
    sphMap_hopfParam (hper_sph C hc h3 hχ D L)] at this

theorem foldRel_TT {x x' : ModelCoordinates} (hT : planeOf x ∈ (𝒦).σ.triangle)
    (h0' : planeOf x ≠ 0) (h1 : planeOf x ≠ (𝒦).σ.vertexOne) (h2 : planeOf x ≠ (𝒦).σ.vertexTwo)
    (hT' : planeOf x' ∈ (𝒦).σ.triangle) (h0'' : planeOf x' ≠ 0)
    (h1' : planeOf x' ≠ (𝒦).σ.vertexOne) (h2' : planeOf x' ≠ (𝒦).σ.vertexTwo)
    (h : (𝒢) x = (𝒢) x') : ℛ (hopfParam x) (hopfParam x') := by
  obtain ⟨hF, hx⟩ := sphFoldMap_of_triangle C hc h3 hχ D L hT h0' h1 h2
  obtain ⟨hF', -⟩ := sphFoldMap_of_triangle C hc h3 hχ D L hT' h0'' h1' h2'
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftP_mem_closedDomain_of_T C hc h3 hχ D hT h0' h1 h2)
    (liftP_mem_closedDomain_of_T C hc h3 hχ D hT' h0'' h1' h2') h
  exact foldRel_of_liftP_eq C hc h3 hχ D L hx hT h0' hT' h0'' hL

theorem foldRel_CC {x x' : ModelCoordinates} (hT : conj (planeOf x) ∈ (𝒦).σ.triangle)
    (h0' : conj (planeOf x) ≠ 0) (h1 : conj (planeOf x) ≠ (𝒦).σ.vertexOne)
    (h2 : conj (planeOf x) ≠ (𝒦).σ.vertexTwo)
    (hT' : conj (planeOf x') ∈ (𝒦).σ.triangle) (h0'' : conj (planeOf x') ≠ 0)
    (h1' : conj (planeOf x') ≠ (𝒦).σ.vertexOne) (h2' : conj (planeOf x') ≠ (𝒦).σ.vertexTwo)
    (h : (𝒢) x = (𝒢) x') : ℛ (hopfParam x) (hopfParam x') := by
  obtain ⟨hF, hx⟩ := sphFoldMap_of_conjTriangle C hc h3 hχ D L hT h0' h1 h2
  obtain ⟨hF', -⟩ := sphFoldMap_of_conjTriangle C hc h3 hχ D L hT' h0'' h1' h2'
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftM_mem_closedDomain_of_T C hc h3 hχ D hT h0' h1 h2)
    (liftM_mem_closedDomain_of_T C hc h3 hχ D hT' h0'' h1' h2') h
  exact foldRel_of_liftM_eq C hc h3 hχ D L hx hT h0' hT' h0'' hL

theorem rotOne_injOn {z w : ℂ} (hz : 1 + conj (𝒦).σ.vertexOne * z ≠ 0)
    (hw : 1 + conj (𝒦).σ.vertexOne * w ≠ 0) (h : (𝒦).σ.rotOne z = (𝒦).σ.rotOne w) :
    z = w := by
  rw [rotOne_eq_of_sph (𝒦).hσ, rotOne_eq_of_sph (𝒦).hσ] at h
  have hμ : -exp (-(((𝒦).σ.θ₃ : ℂ) * I)) ≠ 0 := neg_ne_zero.2 (exp_ne_zero _)
  have hd := mul_left_cancel₀ hμ h
  unfold discV at hd
  rw [div_eq_div_iff hz hw] at hd
  have hv : (1 + conj (𝒦).σ.vertexOne * (𝒦).σ.vertexOne) ≠ 0 := by
    rw [mul_comm, mul_conj]
    have : (0 : ℝ) < 1 + normSq (𝒦).σ.vertexOne := by
      have := normSq_nonneg (𝒦).σ.vertexOne; linarith
    exact_mod_cast this.ne'
  have : (z - w) * (1 + conj (𝒦).σ.vertexOne * (𝒦).σ.vertexOne) = 0 := by
    linear_combination hd
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv)

theorem conj_rotOne_of_wallTwo {z : ℂ} (hT : z ∈ (𝒦).σ.triangle) (hw : (𝒦).σ.wallSide 2 z = 0) :
    conj ((𝒦).σ.rotOne z) = (Circle.exp (-2 * Real.pi / (𝒦).σ.p₁) : ℂ) * (𝒦).σ.rotOne z := by
  have hs := (𝒦).hσ
  have h1 := CompactShape.one_add_conj_vertexOne_ne_sph hs hT
  have h2' := CompactShape.one_add_vertexTwo_ne_sph hs hT
  have h2 : 1 + conj (𝒦).σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  have key := CompactShape.wallSide_two_eq_rotOne_sph hs h1 h2
  have hR2 : ((𝒦).σ.rotTwo z).im = 0 := by
    have e := (𝒦).σ.wallSide_two_eq z
    rw [hw] at e
    have hN : Complex.normSq (1 - (𝒦).σ.eps * conj (𝒦).σ.vertexTwo * z) ≠ 0 := by
      rw [SphLayout.eps_eq, conj_vertexTwo_sph]
      push_cast
      rw [show (1 : ℂ) - -1 * (𝒦).σ.vertexTwo * z = 1 + (𝒦).σ.vertexTwo * z by ring]
      exact (normSq_pos.2 h2').ne'
    rcases mul_eq_zero.1 e.symm with h | h
    · exact h
    · exact absurd h hN
  have hsec := (CompactShape.sector_two_sph hs hT).2
  have hR2re : 0 ≤ ((𝒦).σ.rotTwo z).re := by
    have hreal : (𝒦).σ.rotTwo z = (((𝒦).σ.rotTwo z).re : ℂ) :=
      Complex.ext (by simp) (by simp [hR2])
    rw [hreal] at hsec
    have hsin := (𝒦).σ.sin_θ₂_pos
    simp only [mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, conj_ofReal, ofReal_re,
      ofReal_im, mul_zero] at hsec
    nlinarith
  have ht : 0 ≤ (𝒦).σ.sphTOneTwo := by
    unfold CompactShape.sphTOneTwo CompactShape.sideTan
    rw [hs]
    exact Real.sqrt_nonneg _
  have hN : Complex.normSq (1 + (𝒦).σ.sphTOneTwo * (𝒦).σ.rotTwo z) ≠ 0 := by
    apply (normSq_pos.2 _).ne'
    intro h0
    have := congrArg Complex.re h0
    simp only [add_re, one_re, re_ofReal_mul, zero_re] at this
    nlinarith
  rw [hR2, mul_zero] at key
  have hIm : (exp (((𝒦).σ.θ₁ : ℂ) * I) * conj ((𝒦).σ.rotOne z)).im = 0 :=
    (mul_eq_zero.1 key).resolve_right hN
  set R := (𝒦).σ.rotOne z
  set E := exp (((𝒦).σ.θ₁ : ℂ) * I)
  have hreal : conj (E * conj R) = E * conj R := Complex.conj_eq_iff_im.2 hIm
  have hcE : conj E = exp (-(((𝒦).σ.θ₁ : ℂ) * I)) := by
    rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]
  rw [map_mul, conj_conj, hcE] at hreal
  have hEE : E * exp (-(((𝒦).σ.θ₁ : ℂ) * I)) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hω : (Circle.exp (-2 * Real.pi / (𝒦).σ.p₁) : ℂ) =
      exp (-(((𝒦).σ.θ₁ : ℂ) * I)) * exp (-(((𝒦).σ.θ₁ : ℂ) * I)) := by
    rw [Circle.coe_exp, ← exp_add, CompactShape.θ₁]
    congr 1
    push_cast
    ring
  rw [hω]
  linear_combination (exp (-(((𝒦).σ.θ₁ : ℂ) * I))) * hreal.symm - conj R * hEE

theorem foldRel_TC {x x' : ModelCoordinates} (hT : planeOf x ∈ (𝒦).σ.triangle)
    (h0' : planeOf x ≠ 0) (h1 : planeOf x ≠ (𝒦).σ.vertexOne) (h2 : planeOf x ≠ (𝒦).σ.vertexTwo)
    (hT' : conj (planeOf x') ∈ (𝒦).σ.triangle) (h0'' : conj (planeOf x') ≠ 0)
    (h1' : conj (planeOf x') ≠ (𝒦).σ.vertexOne) (h2' : conj (planeOf x') ≠ (𝒦).σ.vertexTwo)
    (h : (𝒢) x = (𝒢) x') : ℛ (hopfParam x) (hopfParam x') := by
  obtain ⟨hF, hx⟩ := sphFoldMap_of_triangle C hc h3 hχ D L hT h0' h1 h2
  obtain ⟨hF', -⟩ := sphFoldMap_of_conjTriangle C hc h3 hχ D L hT' h0'' h1' h2'
  have h₀ := h
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftP_mem_closedDomain_of_T C hc h3 hχ D hT h0' h1 h2)
    (liftM_mem_closedDomain_of_T C hc h3 hχ D hT' h0'' h1' h2') h
  set z := planeOf x with hz
  set w := conj (planeOf x') with hw
  have hf : (𝒦).D.f z = conj ((𝒦).D.f w) := by
    have := congrArg Prod.fst hL
    rw [liftM_fst] at this
    exact this
  have a1 := ((𝒦).D.bijOn_f.mapsTo ⟨hT, h0'⟩).2
  have a2 := ((𝒦).D.bijOn_f.mapsTo ⟨hT', h0''⟩).2
  have him : ((𝒦).D.f z).im = 0 := by
    have := congrArg Complex.im hf
    rw [conj_im] at this
    linarith
  have himw : ((𝒦).D.f w).im = 0 := by
    have := congrArg Complex.im hf
    rw [conj_im] at this
    linarith
  have hzw : z = w := (𝒦).D.eq_of_f_eq ⟨hT, h0'⟩ ⟨hT', h0''⟩
    (hf.trans (Complex.conj_eq_iff_im.mpr himw))
  have hx'z : conj (planeOf x') = z := hzw.symm
  obtain ⟨i, hwi⟩ := (𝒦).D.wall_of_im_f_eq_zero hT h0' him
  have finish : ∀ x₁ : ModelCoordinates, ℛ (hopfParam x) (hopfParam x₁) →
      conj (planeOf x₁) = z → ℛ (hopfParam x) (hopfParam x') := by
    intro x₁ hr hp
    refine hr.trans (foldRel_CC C hc h3 hχ D L (hp ▸ hT) (hp ▸ h0') (hp ▸ h1) (hp ▸ h2) hT' h0''
      h1' h2' ?_)
    rw [map_eq_of_foldRel C hc h3 hχ D L hr]
    exact h₀
  have hcov := L.cover ⟨hT, h0'⟩
  simp only [mem_union] at hcov
  fin_cases i
  · change (𝒦).σ.wallSide 0 z = 0 at hwi
    have hcz : conj z = z := Complex.conj_eq_iff_im.mpr hwi
    have hpx' : planeOf x' = z := by
      have := congrArg conj hx'z
      rwa [Complex.conj_conj, hcz] at this
    have hV : planeOf x' ∈ (𝒦).D.V 0 := by
      rw [hpx']; exact (𝒦).D.foldWall_diff_subset_V 0 ⟨⟨hT, hwi⟩, h0'⟩
    have hre : ((𝒦).D.f (planeOf x')).re < -(3 / 2) := by
      rw [hpx']; exact ((𝒦).D.re_f_wallZero ⟨hT, hwi⟩ h0' h2).2
    have hsl : 1 + conj (𝒦).σ.vertexTwo * planeOf x' ∈ slitPlane := by
      obtain ⟨r, hr0, -, hrz⟩ := (𝒦).σ.eq_real_of_wallZero hT hwi
      rw [hpx', hrz, conj_vertexTwo_sph, CompactShape.vertexTwo_eq_real]
      refine mem_slitPlane_iff.2 (Or.inl ?_)
      simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      have := (𝒦).σ.sideTanTwo_pos
      positivity
    rw [(𝒦).liftM_eq_liftP hV hre hsl] at hL
    exact foldRel_of_liftP_eq C hc h3 hχ D L hx hT h0' (hpx' ▸ hT) (hpx' ▸ h0') hL
  · change (𝒦).σ.wallSide 1 z = 0 at hwi
    have hr1 : (𝒦).σ.refl 1 z = z := (𝒦).σ.refl_eq_self (i := 1) (mem_univ _) hwi
    have hS3 : conj (planeOf (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift x)) = z := by
      rw [(𝒦).conj_planeOf_screwZero, ← hz, hr1]
    have hre := ((𝒦).D.re_f_wallOne ⟨hT, hwi⟩ h0' h1).1
    rcases hcov with ((hm | hd) | hd) | hd
    · rcases hm with ((hm | hm) | hm) | hm
      · exact absurd hwi (hm.2 1).ne'
      · have := (L.patchZero_spec _ hm).2.1; linarith
      · exact finish _ (foldRel_screwThree_patchOne C hc h3 hχ D L hm) hS3
      · have := (L.patchTwo_spec _ hm).2.2.1; linarith
    · exact finish _ (foldRel_screwThree_discOne C hc h3 hχ D L hd) hS3
    · have hf2 := (L.f_of_mem_discTwo hd).2
      have := L.re_apexTwo_lt hd
      rw [← hf2] at this
      linarith
    · exact finish _ (foldRel_screwThree C hc h3 hχ D L hd) hS3
  · change (𝒦).σ.wallSide 2 z = 0 at hwi
    have hV2 : z ∈ (𝒦).D.V 2 := (𝒦).D.foldWall_diff_subset_V 2 ⟨⟨hT, hwi⟩, h0'⟩
    have hr2 : (𝒦).σ.refl 2 z = z :=
      (𝒦).σ.refl_eq_self ((𝒦).D.V_subset_reflChart 2 hV2) hwi
    obtain ⟨hre1, hre2⟩ := (𝒦).D.re_f_wallTwo ⟨hT, hwi⟩ h1 h2
    have hS2 : conj (planeOf (screwChart (𝒦).σ.vertexTwo (2 * Real.pi / (𝒦).σ.p₂)
        ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) x)) = z := by
      rw [screwTwoInv_mem_conjMain C hc h3 hχ D x, ← hz, hr2]
    rcases hcov with ((hm | hd) | hd) | hd
    · rcases hm with ((hm | hm) | hm) | hm
      · exact absurd hwi (hm.2 2).ne'
      · have := (L.patchZero_spec _ hm).2.1; linarith
      · have := (L.patchOne_spec _ hm).2.1; linarith
      · exact finish _ (foldRel_screwTwoInv_patchTwo C hc h3 hχ D L hm) hS2
    · have hd1 := screwChart_mem_discOne C hc h3 hχ D L hd
      refine finish _ ((foldRel_screwOne C hc h3 hχ D L hd).trans
        (foldRel_screwThree_discOne C hc h3 hχ D L hd1)) ?_
      rw [(𝒦).conj_planeOf_screwZero]
      have hp1 : planeOf (screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁)
          (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁) x) = (𝒦).σ.refl 1 z := by
        apply rotOne_injOn C hc h3 hχ D hd1.1 (L.refl_one_mem_discOne hd).1
        rw [rotOne_screwChart_one C hc h3 hχ D L hd, rotOne_refl_one_sph (𝒦).hσ,
          conj_rotOne_of_wallTwo C hc h3 hχ D hT hwi]
      rw [hp1, refl_one_refl_one C hc h3 hχ D]
    · have hx1 : planeOf (screwChart (𝒦).σ.vertexTwo (2 * Real.pi / (𝒦).σ.p₂)
          ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) x) ∈ L.discTwo := by
        have := L.conj_mem_discTwo hd
        rw [← hS2, conj_conj] at this
        exact this
      have hr := foldRel_screwTwo C hc h3 hχ D L hx1
      have e1 : (2 * Real.pi / (𝒦).σ.p₂ : ℝ) = -(-2 * Real.pi / (𝒦).σ.p₂) := by ring
      have e2 : ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂ : ℝ) = -(-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) := by ring
      have hback : hopfParam (screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂)
          (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) (screwChart (𝒦).σ.vertexTwo (2 * Real.pi / (𝒦).σ.p₂)
            ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) x)) = hopfParam x := by
        have hden1 := L.discTwo_den _ hd (2 * Real.pi / (𝒦).σ.p₂)
        have hden2 := L.discTwo_den _ hx1 (-2 * Real.pi / (𝒦).σ.p₂)
        rw [e1, e2] at hx1 hden2 ⊢
        rw [e1] at hden1
        refine hopfParam_screwChart_neg hd.1 ?_ hx1.1 ?_
        · rw [planeOf_screwDiffeomorph, planeOf_centred]; exact hden1
        · rw [planeOf_screwDiffeomorph, planeOf_centred]; exact hden2
      rw [hback] at hr
      exact finish _ hr.symm hS2
    · have hn3 := L.norm_f_of_discThree hd h0'
      have hreal : (𝒦).D.f z = (((𝒦).D.f z).re : ℂ) :=
        Complex.ext (by simp) (by simp [him])
      rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hn3
      have := abs_lt.2 ⟨hre1, hre2⟩
      linarith

theorem sphFoldMap_regular {x : ModelCoordinates}
    (hx : (planeOf x ∈ (𝒦).σ.triangle ∧ planeOf x ≠ 0 ∧ planeOf x ≠ (𝒦).σ.vertexOne ∧
      planeOf x ≠ (𝒦).σ.vertexTwo) ∨
      (conj (planeOf x) ∈ (𝒦).σ.triangle ∧ conj (planeOf x) ≠ 0 ∧
        conj (planeOf x) ≠ (𝒦).σ.vertexOne ∧ conj (planeOf x) ≠ (𝒦).σ.vertexTwo)) :
    ∃ Y ∈ closedDomain, (𝒢) x = C.closedChart hc h3 Y := by
  rcases hx with ⟨a, b, c, e⟩ | ⟨a, b, c, e⟩
  · exact ⟨_, liftP_mem_closedDomain_of_T C hc h3 hχ D a b c e,
      (sphFoldMap_of_triangle C hc h3 hχ D L a b c e).1⟩
  · exact ⟨_, liftM_mem_closedDomain_of_T C hc h3 hχ D a b c e,
      (sphFoldMap_of_conjTriangle C hc h3 hχ D L a b c e).1⟩

theorem foldRel_of_reduced {x x' : ModelCoordinates} (hx : x ∈ sphReducedSet (𝒦))
    (hx' : x' ∈ sphReducedSet (𝒦)) (h : (𝒢) x = (𝒢) x') :
    ℛ (hopfParam x) (hopfParam x') := by
  have hcore : ∀ {y : ModelCoordinates}, y ∈ sphReducedSet (𝒦) →
      (planeOf y = (𝒦).σ.vertexOne ∨ planeOf y = (𝒦).σ.vertexTwo ∨ planeOf y = 0) ∨
      ((planeOf y ∈ (𝒦).σ.triangle ∧ planeOf y ≠ 0 ∧ planeOf y ≠ (𝒦).σ.vertexOne ∧
        planeOf y ≠ (𝒦).σ.vertexTwo) ∨
      (conj (planeOf y) ∈ (𝒦).σ.triangle ∧ conj (planeOf y) ≠ 0 ∧
        conj (planeOf y) ≠ (𝒦).σ.vertexOne ∧ conj (planeOf y) ≠ (𝒦).σ.vertexTwo)) := by
    intro y hy
    rcases hy with hy | hy | hy | hy | hy
    · exact Or.inl (Or.inl hy)
    · exact Or.inl (Or.inr (Or.inl hy))
    · exact Or.inl (Or.inr (Or.inr hy))
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)
  rcases hcore hx with hv | hr <;> rcases hcore hx' with hv' | hr'
  · obtain ⟨j, w, hF, hp⟩ := sphFoldMap_vertex_core C hc h3 hχ D L hv
    obtain ⟨j', w', hF', hp'⟩ := sphFoldMap_vertex_core C hc h3 hχ D L hv'
    have h₁ := h
    rw [hF, hF'] at h₁
    have h00 : ‖((0 : ℂ), w).1‖ < 1 + C.ε := by
      change ‖(0 : ℂ)‖ < _; rw [norm_zero]; linarith [C.ε_pos]
    have h00' : ‖((0 : ℂ), w').1‖ < 1 + C.ε := by
      change ‖(0 : ℂ)‖ < _; rw [norm_zero]; linarith [C.ε_pos]
    have hjj := (C.closedHoleEquiv hc h3).injective
      ((C.tubeMap_eq_iff_of_core h00 h00').1 h₁).1
    subst hjj
    have hpp : planeOf x = planeOf x' := hp.trans hp'.symm
    rcases hv with hv | hv | hv
    · exact foldRel_vertexOne C hc h3 hχ D L hv (hpp ▸ hv) h
    · exact foldRel_vertexTwo C hc h3 hχ D L hv (hpp ▸ hv) h
    · exact foldRel_vertexThree C hc h3 hχ D L hv (hpp ▸ hv) h
  · obtain ⟨j, w, hF, -⟩ := sphFoldMap_vertex_core C hc h3 hχ D L hv
    obtain ⟨Y, hY, hF'⟩ := sphFoldMap_regular C hc h3 hχ D L hr'
    rw [hF, hF'] at h
    exact absurd h.symm (C.closedChart_ne_tubeMap_zero hc h3 hY _ w)
  · obtain ⟨j, w, hF', -⟩ := sphFoldMap_vertex_core C hc h3 hχ D L hv'
    obtain ⟨Y, hY, hF⟩ := sphFoldMap_regular C hc h3 hχ D L hr
    rw [hF, hF'] at h
    exact absurd h (C.closedChart_ne_tubeMap_zero hc h3 hY _ w)
  · rcases hr with ⟨a, b, c, e⟩ | ⟨a, b, c, e⟩ <;>
      rcases hr' with ⟨a', b', c', e'⟩ | ⟨a', b', c', e'⟩
    · exact foldRel_TT C hc h3 hχ D L a b c e a' b' c' e' h
    · exact foldRel_TC C hc h3 hχ D L a b c e a' b' c' e' h
    · exact (foldRel_TC C hc h3 hχ D L a' b' c' e' a b c e h.symm).symm
    · exact foldRel_CC C hc h3 hχ D L a b c e a' b' c' e' h

theorem foldRel_of_sphFoldMap_eq {y y' : ModelCoordinates} (hy : planeOf y ∈ sphBase L)
    (hy' : planeOf y' ∈ sphBase L) (h : (𝒢) y = (𝒢) y') : ℛ (hopfParam y) (hopfParam y') := by
  obtain ⟨y₀, r, hy₀⟩ := exists_foldRel_reduced C hc h3 hχ D L hy
  obtain ⟨y₀', r', hy₀'⟩ := exists_foldRel_reduced C hc h3 hχ D L hy'
  have h₀ : (𝒢) y₀ = (𝒢) y₀' := by
    rw [map_eq_of_foldRel C hc h3 hχ D L r, map_eq_of_foldRel C hc h3 hχ D L r', h]
  exact r.trans ((foldRel_of_reduced C hc h3 hχ D L hy₀ hy₀' h₀).trans r'.symm)

end Final

end Sph

end ClosedTriangle

end GC.Seifert
