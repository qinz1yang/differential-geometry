import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphFold

/-!
# The generator moves of a spherical closed triangle fold on the round sphere

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §2, §3, §6,
with review 32 §7.1). For the fold `G = sphFoldMap` on the Hopf chart and its descent
`sphMap G` to the round three-sphere, every generator is a global isometry `s3Diffeo γ` of the
sphere read in the chart by an explicit local map `σ` preserving `G` on an open piece; by
`foldRel_sphMap` it relates `hopfParam x` to `hopfParam (σ x)`:
* the deck translations `h^n` (`γ = fibreLiftS3 (n ℓ)`, `σ = + n ℓ` in the fibre) on all of the
  domain (`foldRel_deck`);
* the screws about `v₁`, `v₂` (`γ = screwSph vⱼ (-2π/pⱼ) (-ℓ qⱼ/pⱼ)`, `σ = screwChart`) on their
  discs (`foldRel_screwOne`, `foldRel_screwTwo`), and the screw about `0`
  (`γ = screwLiftS3 0 (-2π/p₃) (-ℓ q₃/p₃)`, `σ = screwDiffeomorph`) on its disc, on the disc of
  `v₁` (onto the mirror disc, where `G = G ∘ S₃⁻¹`) and on the wall-1 patch (`foldRel_screwThree`,
  `foldRel_screwThree_discOne`, `foldRel_screwThree_patchOne`);
* the inverse screw about `v₂` (`γ = screwSph v₂ (2π/p₂) (ℓ q₂/p₂)`) on the wall-2 patch
  (`foldRel_screwTwoInv_patchTwo`), where the real closing identity is obtained from the layout's
  continuity window, the identity modulo `2π` (`psiS_wallTwo_angle`) and the excess formula
  (`closing_wallTwo`).
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

theorem one_add_conj_mul_planeOf_screwChart {v : ℂ} {θ s : ℝ} {x : ModelCoordinates}
    (hd : 1 - conj v * (exp (θ * I) * discV v (planeOf x)) ≠ 0) :
    1 + conj v * planeOf (screwChart v θ s x) ≠ 0 := by
  rw [SphDatum.planeOf_screwChart]
  have hv : (1 + conj v * v) ≠ 0 := by
    rw [mul_comm, mul_conj]
    have : (0 : ℝ) < 1 + normSq v := by have := normSq_nonneg v; linarith
    exact_mod_cast this.ne'
  have e : 1 + conj v * ((exp (θ * I) * discV v (planeOf x) + v) /
      (1 - conj v * (exp (θ * I) * discV v (planeOf x)))) =
        (1 + conj v * v) / (1 - conj v * (exp (θ * I) * discV v (planeOf x))) := by
    rw [eq_div_iff hd, add_mul, mul_assoc (conj v), div_mul_cancel₀ _ hd]
    ring
  rw [e]
  exact div_ne_zero hv hd

theorem screwDiffeomorph_screwDiffeomorph (a b : ℝ) (y : ModelCoordinates) :
    screwDiffeomorph a b (screwDiffeomorph (-a) (-b) y) = y := by
  apply modelCoordinates_ext
  · rw [planeOf_screwDiffeomorph, planeOf_screwDiffeomorph, ← mul_assoc, ← exp_add]
    push_cast
    ring_nf
    rw [exp_zero, one_mul]
  · rw [screwDiffeomorph_two, screwDiffeomorph_two]
    ring

section Rel

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)
  (D : (C.closedSphShape hc h3 hχ).FoldData) (L : SphLayout (sphDatum C hc h3 hχ D))

set_option hygiene false in
local notation "𝒦" => sphDatum C hc h3 hχ D

set_option hygiene false in
local notation "𝒢" => sphFoldMap L C hc h3

theorem hper_sph : ∀ (x : ModelCoordinates) (m : ℤ),
    (𝒢) (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = (𝒢) x :=
  sphFoldMap_period C hc h3 hχ D L

theorem isOpen_preimage_planeOf {S : Set ℂ} (hS : IsOpen S) : IsOpen (planeOf ⁻¹' S) :=
  hS.preimage contDiff_planeOf.continuous

theorem foldRel_deck (n : ℤ) {x : ModelCoordinates} (hx : planeOf x ∈ sphBase L) :
    FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L)) (sphMap (𝒢))
      (hopfParam x) (hopfParam (x + GC.Geometry.fibreShift (n * (𝒦).ℓ))) := by
  have hpl : ∀ y : ModelCoordinates, planeOf (y + GC.Geometry.fibreShift (n * (𝒦).ℓ)) =
      planeOf y := fun y => SphDatum.planeOf_add_fibreShift' y _
  refine foldRel_sphMap (hper_sph C hc h3 hχ D L) (isOpen_sphBase L) (fibreLiftS3 (n * (𝒦).ℓ))
    (fun y => y + GC.Geometry.fibreShift (n * (𝒦).ℓ))
    (isOpen_preimage_planeOf (isOpen_sphBase L)) hx (fun y hy => hy)
    (fun y hy => by rw [hpl]; exact hy) (fun y _ => (hopfParam_add_fibreShift y _).symm)
    (fun y _ => ?_)
  refine sphFoldMap_shift C hc h3 hχ D L n (hpl y) ?_
  have h2 : (y + GC.Geometry.fibreShift (n * (𝒦).ℓ)) 2 = y 2 + n * (𝒦).ℓ := by
    simp [GC.Geometry.fibreShift]
  rw [h2, add_div, mul_div_cancel_right₀ _ (𝒦).ℓ_ne]

theorem disc_mem_base_one {z : ℂ} (hz : z ∈ L.discOne) : z ∈ sphBase L := by
  simp only [sphBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inr hz)))

theorem disc_mem_base_mirror {z : ℂ} (hz : z ∈ L.discOneMirror) : z ∈ sphBase L := by
  simp only [sphBase, mem_union]
  exact Or.inl (Or.inl (Or.inr hz))

theorem disc_mem_base_two {z : ℂ} (hz : z ∈ L.discTwo) : z ∈ sphBase L := by
  simp only [sphBase, mem_union]
  exact Or.inl (Or.inr hz)

theorem disc_mem_base_three {z : ℂ} (hz : z ∈ L.discThree) : z ∈ sphBase L := by
  simp only [sphBase, mem_union]
  exact Or.inr hz

theorem main_mem_base {z : ℂ} (hz : z ∈ L.mainSet) : z ∈ sphBase L := by
  simp only [sphBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hz))))

theorem conjMain_mem_base {z : ℂ} (hz : conj z ∈ L.mainSet) : z ∈ sphBase L := by
  simp only [sphBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hz))))

theorem screwChart_mem_discOne {y : ModelCoordinates} (hy : planeOf y ∈ L.discOne) :
    planeOf (screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁)
      (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁) y) ∈ L.discOne := by
  have hden := L.discOne_den _ hy (-2 * Real.pi / (𝒦).σ.p₁)
  have hx' := one_add_conj_mul_planeOf_screwChart (s := -(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁) hden
  have hy' : 1 - conj (𝒦).σ.vertexOne * planeOf (screwDiffeomorph (-2 * Real.pi / (𝒦).σ.p₁)
      (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁) (centred (𝒦).σ.vertexOne y)) ≠ 0 := by
    rw [planeOf_screwDiffeomorph, planeOf_centred]
    exact hden
  refine ⟨hx', ?_⟩
  rw [SphLayout.norm_rotOne, disc_screwChart hy.1 hy' hx', norm_mul,
    show ((-2 * Real.pi / (𝒦).σ.p₁ : ℝ) : ℂ) * I = ((-2 * Real.pi / (𝒦).σ.p₁ : ℝ) : ℂ) * I
      from rfl, norm_exp_ofReal_mul_I, one_mul, ← SphLayout.norm_rotOne]
  exact hy.2

theorem foldRel_screwOne {x : ModelCoordinates} (hd : planeOf x ∈ L.discOne) :
    FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L)) (sphMap (𝒢))
      (hopfParam x) (hopfParam (screwChart (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁)
        (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁) x)) := by
  refine foldRel_sphMap (hper_sph C hc h3 hχ D L) (isOpen_sphBase L)
    (screwSph (𝒦).σ.vertexOne (-2 * Real.pi / (𝒦).σ.p₁) (-(𝒦).ℓ * (𝒦).q₁ / (𝒦).σ.p₁))
    _ (isOpen_preimage_planeOf L.isOpen_discOne) hd
    (fun y hy => disc_mem_base_one C hc h3 hχ D L hy)
    (fun y hy => disc_mem_base_one C hc h3 hχ D L (screwChart_mem_discOne C hc h3 hχ D L hy))
    (fun y hy => ?_) (fun y hy => ?_)
  · have hden := L.discOne_den _ hy (-2 * Real.pi / (𝒦).σ.p₁)
    refine s3Diffeo_screwSph hy.1 ?_
    rw [planeOf_screwDiffeomorph, planeOf_centred]
    exact hden
  · have hy' := screwChart_mem_discOne C hc h3 hχ D L hy
    have hden := L.discOne_den _ hy (-2 * Real.pi / (𝒦).σ.p₁)
    rw [sphFoldMap_of_discOne L C hc h3 hy', sphFoldMap_of_discOne L C hc h3 hy,
      (𝒦).tubeOne_screwChart hy.1 (by rw [planeOf_screwDiffeomorph, planeOf_centred]; exact hden)
        hy'.1]

theorem screwChart_mem_discTwo {y : ModelCoordinates} (hy : planeOf y ∈ L.discTwo) :
    planeOf (screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂)
      (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) y) ∈ L.discTwo := by
  have hden := L.discTwo_den _ hy (-2 * Real.pi / (𝒦).σ.p₂)
  have hx' := one_add_conj_mul_planeOf_screwChart (s := -(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) hden
  have hy' : 1 - conj (𝒦).σ.vertexTwo * planeOf (screwDiffeomorph (-2 * Real.pi / (𝒦).σ.p₂)
      (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) (centred (𝒦).σ.vertexTwo y)) ≠ 0 := by
    rw [planeOf_screwDiffeomorph, planeOf_centred]
    exact hden
  refine ⟨hx', ?_⟩
  rw [SphLayout.norm_rotTwo, disc_screwChart hy.1 hy' hx', norm_mul, norm_exp_ofReal_mul_I,
    one_mul, ← SphLayout.norm_rotTwo]
  exact hy.2

theorem foldRel_screwTwo {x : ModelCoordinates} (hd : planeOf x ∈ L.discTwo) :
    FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L)) (sphMap (𝒢))
      (hopfParam x) (hopfParam (screwChart (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂)
        (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) x)) := by
  refine foldRel_sphMap (hper_sph C hc h3 hχ D L) (isOpen_sphBase L)
    (screwSph (𝒦).σ.vertexTwo (-2 * Real.pi / (𝒦).σ.p₂) (-(𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂))
    _ (isOpen_preimage_planeOf L.isOpen_discTwo) hd
    (fun y hy => disc_mem_base_two C hc h3 hχ D L hy)
    (fun y hy => disc_mem_base_two C hc h3 hχ D L (screwChart_mem_discTwo C hc h3 hχ D L hy))
    (fun y hy => ?_) (fun y hy => ?_)
  · have hden := L.discTwo_den _ hy (-2 * Real.pi / (𝒦).σ.p₂)
    refine s3Diffeo_screwSph hy.1 ?_
    rw [planeOf_screwDiffeomorph, planeOf_centred]
    exact hden
  · have hy' := screwChart_mem_discTwo C hc h3 hχ D L hy
    have hden := L.discTwo_den _ hy (-2 * Real.pi / (𝒦).σ.p₂)
    rw [sphFoldMap_of_discTwo L C hc h3 hy', sphFoldMap_of_discTwo L C hc h3 hy,
      (𝒦).tubeTwo_screwChart hy.1 (by rw [planeOf_screwDiffeomorph, planeOf_centred]; exact hden)
        hy'.1]

theorem hσ_screwZero (y : ModelCoordinates) :
    s3Diffeo (screwLiftS3 0 (𝒦).screwZeroAngle (𝒦).screwZeroShift) (hopfParam y) =
      hopfParam (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift y) :=
  (hopfParam_screwDiffeomorph _ _ y).symm

theorem screwZero_mem_discThree {y : ModelCoordinates} (hy : planeOf y ∈ L.discThree) :
    planeOf (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift y) ∈ L.discThree := by
  change ‖_‖ < _
  rw [(𝒦).planeOf_screwZero, norm_mul, Circle.norm_coe, one_mul]
  exact hy

theorem foldRel_screwThree {x : ModelCoordinates} (hd : planeOf x ∈ L.discThree) :
    FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L)) (sphMap (𝒢))
      (hopfParam x) (hopfParam (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift x)) :=
  foldRel_sphMap (hper_sph C hc h3 hχ D L) (isOpen_sphBase L)
    (screwLiftS3 0 (𝒦).screwZeroAngle (𝒦).screwZeroShift) _
    (isOpen_preimage_planeOf L.isOpen_discThree) hd
    (fun y hy => disc_mem_base_three C hc h3 hχ D L hy)
    (fun y hy => disc_mem_base_three C hc h3 hχ D L (screwZero_mem_discThree C hc h3 hχ D L hy))
    (fun y _ => hσ_screwZero C hc h3 hχ D y) (fun y hy => by
      rw [sphFoldMap_of_discThree L C hc h3 (screwZero_mem_discThree C hc h3 hχ D L hy),
        sphFoldMap_of_discThree L C hc h3 hy, (𝒦).tubeThree_screwZero])

theorem rotThreeInv_screwZero (y : ModelCoordinates) :
    (𝒦).rotThreeInv (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift y) = y := by
  rw [rotThreeInv_eq_screw]
  have e1 : (𝒦).screwZeroAngle = -(2 * Real.pi / (𝒦).σ.p₃) := by
    simp only [SphDatum.screwZeroAngle]; ring
  have e2 : (𝒦).screwZeroShift = -((𝒦).ℓ * (𝒦).k₃) := by
    simp only [SphDatum.screwZeroShift, SphDatum.k₃]; ring
  rw [e1, e2, screwDiffeomorph_screwDiffeomorph]

theorem screwZero_mem_discOneMirror {y : ModelCoordinates} (hy : planeOf y ∈ L.discOne) :
    planeOf (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift y) ∈ L.discOneMirror := by
  change conj _ ∈ L.discOne
  rw [(𝒦).conj_planeOf_screwZero]
  exact L.refl_one_mem_discOne hy

theorem foldRel_screwThree_discOne {x : ModelCoordinates} (hd : planeOf x ∈ L.discOne) :
    FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L)) (sphMap (𝒢))
      (hopfParam x) (hopfParam (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift x)) :=
  foldRel_sphMap (hper_sph C hc h3 hχ D L) (isOpen_sphBase L)
    (screwLiftS3 0 (𝒦).screwZeroAngle (𝒦).screwZeroShift) _
    (isOpen_preimage_planeOf L.isOpen_discOne) hd
    (fun y hy => disc_mem_base_one C hc h3 hχ D L hy)
    (fun y hy => disc_mem_base_mirror C hc h3 hχ D L
      (screwZero_mem_discOneMirror C hc h3 hχ D L hy))
    (fun y _ => hσ_screwZero C hc h3 hχ D y) (fun y hy => by
      rw [sphFoldMap_of_discOneMirror L C hc h3 (screwZero_mem_discOneMirror C hc h3 hχ D L hy),
        sphFoldMap_of_discOne L C hc h3 hy, rotThreeInv_screwZero])

theorem foldRel_screwThree_patchOne {x : ModelCoordinates} (hp : planeOf x ∈ L.patchOne) :
    FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L)) (sphMap (𝒢))
      (hopfParam x) (hopfParam (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift x)) := by
  have hmain : ∀ {z : ℂ}, z ∈ L.patchOne → z ∈ L.mainSet := fun h => Or.inl (Or.inr h)
  have hconj : ∀ {y : ModelCoordinates}, planeOf y ∈ L.patchOne →
      conj (planeOf (screwDiffeomorph (𝒦).screwZeroAngle (𝒦).screwZeroShift y)) ∈
        L.mainSet := fun hy => by
    rw [(𝒦).conj_planeOf_screwZero]
    exact hmain (L.patchOne_spec _ hy).2.2
  exact foldRel_sphMap (hper_sph C hc h3 hχ D L) (isOpen_sphBase L)
    (screwLiftS3 0 (𝒦).screwZeroAngle (𝒦).screwZeroShift) _
    (isOpen_preimage_planeOf L.isOpen_patchOne) hp
    (fun y hy => main_mem_base C hc h3 hχ D L (hmain hy))
    (fun y hy => conjMain_mem_base C hc h3 hχ D L (hconj hy))
    (fun y _ => hσ_screwZero C hc h3 hχ D y) (fun y hy => by
      obtain ⟨hV, hre, -⟩ := L.patchOne_spec _ hy
      rw [sphFoldMap_of_conjMain C hc h3 hχ D L (hconj hy),
        sphFoldMap_of_main C hc h3 hχ D L (hmain hy),
        (𝒦).liftM_screwZero hV hre (L.main_slit _ (hmain hy)).1])

theorem reflA_eq_refl_two (z : ℂ) :
    reflA ((𝒦).σ.sideTan (𝒦).σ.θ₂ (𝒦).σ.θ₃ (𝒦).σ.θ₁) (exp (-(2 * ((𝒦).σ.θ₂ : ℂ) * I))) z =
      (𝒦).σ.refl 2 z := by
  have he : (𝒦).σ.eps = -1 := SphLayout.eps_eq
  change _ = (𝒦).σ.discInv (𝒦).σ.vertexTwo ((𝒦).σ.reflTwoAux z)
  unfold reflA discInvA discA CompactShape.discInv CompactShape.reflTwoAux CompactShape.disc
  rw [he, CompactShape.vertexTwo, conj_ofReal]
  push_cast
  ring_nf

theorem one_add_vertexTwo_mul_vertexOne_re_pos :
    0 < (1 + (𝒦).σ.vertexTwo * (𝒦).σ.vertexOne).re := by
  have h2 := (𝒦).σ.sideTanTwo_pos
  have h1 := (𝒦).σ.sideTanOne_pos
  have hcos := (𝒦).σ.cos_θ₃_nonneg
  rw [CompactShape.vertexTwo_eq_real, CompactShape.vertexOne_eq_ray]
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im, zero_mul, sub_zero]
  have : 0 ≤ (𝒦).σ.sideTanTwo * ((𝒦).σ.sideTanOne * Real.cos (𝒦).σ.θ₃) := by positivity
  nlinarith

theorem closing_wallTwo {z : ℂ} (hp : z ∈ L.patchTwo) :
    psiS (𝒦).σ.vertexOne z + psiS (𝒦).σ.vertexOne ((𝒦).σ.refl 2 z) -
      psiS (𝒦).σ.vertexTwo z - psiS (𝒦).σ.vertexTwo ((𝒦).σ.refl 2 z) =
        (𝒦).ℓ * (𝒦).phase.e := by
  set a := (𝒦).σ.sideTan (𝒦).σ.θ₂ (𝒦).σ.θ₃ (𝒦).σ.θ₁ with ha
  have hv2 : (𝒦).σ.vertexTwo = (a : ℂ) := rfl
  obtain ⟨hV, -, -, -, hrp⟩ := L.patchTwo_spec z hp
  have hm : z ∈ L.mainSet := Or.inr hp
  have hm' : (𝒦).σ.refl 2 z ∈ L.mainSet := Or.inr hrp
  have hrefl := reflA_eq_refl_two C hc h3 hχ D z
  have hw₁ : exp (-(2 * ((𝒦).σ.θ₂ : ℂ) * I)) * conj (discA a (𝒦).σ.vertexOne) =
      discA a (𝒦).σ.vertexOne := by
    have h := L.rotTwo_vertexOne_real
    simp only [discV, hv2, conj_ofReal] at h
    exact h
  have hz : 1 + (a : ℂ) * z ≠ 0 := by
    have := slitPlane_ne_zero (L.main_slit z hm).2
    rwa [hv2, conj_ofReal] at this
  have hb : 1 + (a : ℂ) * (𝒦).σ.vertexOne ≠ 0 := by
    intro h
    have := one_add_vertexTwo_mul_vertexOne_re_pos C hc h3 hχ D
    rw [hv2, h, zero_re] at this
    exact lt_irrefl _ this
  have hd : 1 - a * (exp (-(2 * ((𝒦).σ.θ₂ : ℂ) * I)) * conj (discA a z)) ≠ 0 := by
    have h := ((𝒦).D.V_subset_reflChart 2 hV).2
    have he : (𝒦).σ.eps = -1 := SphLayout.eps_eq
    unfold CompactShape.reflTwoAux CompactShape.disc at h
    rw [he, hv2, conj_ofReal] at h
    push_cast at h
    rw [show (1 : ℂ) - -1 * ↑a * z = 1 + ↑a * z by ring] at h
    unfold discA
    intro h0
    apply h
    linear_combination h0
  have h1 : 1 + conj (𝒦).σ.vertexOne * z ≠ 0 := slitPlane_ne_zero (L.main_slit z hm).1
  have h1' : 1 + conj (𝒦).σ.vertexOne * reflA a (exp (-(2 * ((𝒦).σ.θ₂ : ℂ) * I))) z ≠ 0 := by
    rw [hrefl]
    exact slitPlane_ne_zero (L.main_slit _ hm').1
  have hang := psiS_wallTwo_angle hw₁ hz hb hd h1 h1'
  rw [hrefl] at hang
  have hwin := L.patchTwo_window z hp
  rw [hv2] at hwin ⊢
  have hex := two_mul_arg_one_add_vertexTwo_mul_vertexOne (𝒦).σ (𝒦).hσ
  rw [hv2] at hex
  have heq := eq_of_coe_angle_eq hang (by linarith [Real.pi_pos, abs_nonneg (psiS
    (𝒦).σ.vertexOne z + psiS (𝒦).σ.vertexOne ((𝒦).σ.refl 2 z) - psiS (↑a) z -
      psiS (↑a) ((𝒦).σ.refl 2 z) - 2 * arg (1 + ↑a * (𝒦).σ.vertexOne))])
  rw [heq, hex, (𝒦).closing_phase]

theorem screwTwoInv_mem_conjMain (y : ModelCoordinates) :
    conj (planeOf (screwChart (𝒦).σ.vertexTwo (2 * Real.pi / (𝒦).σ.p₂)
      ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) y)) = (𝒦).σ.refl 2 (planeOf y) := by
  rw [SphDatum.planeOf_screwChart, ← (𝒦).conj_refl_two_sph, conj_conj]

theorem den_patchTwo {z : ℂ} (hp : z ∈ L.patchTwo) :
    1 - conj (𝒦).σ.vertexTwo * (exp (((2 * Real.pi / (𝒦).σ.p₂ : ℝ) : ℂ) * I) *
      discV (𝒦).σ.vertexTwo z) ≠ 0 := by
  obtain ⟨hV, -⟩ := L.patchTwo_spec z hp
  have h := ((𝒦).D.V_subset_reflChart 2 hV).2
  have he : (𝒦).σ.eps = -1 := SphLayout.eps_eq
  unfold CompactShape.reflTwoAux at h
  rw [he, disc_of_sph (𝒦).hσ] at h
  intro h0
  apply h
  have hce : conj (exp (((2 * Real.pi / (𝒦).σ.p₂ : ℝ) : ℂ) * I)) =
      exp (-(2 * ((𝒦).σ.θ₂ : ℂ) * I)) := by
    rw [← exp_conj, CompactShape.θ₂]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  have := congrArg conj h0
  simp only [map_sub, map_one, map_mul, map_zero, conj_vertexTwo_sph, hce] at this
  rw [conj_vertexTwo_sph] at h ⊢
  push_cast at this ⊢
  linear_combination this

theorem foldRel_screwTwoInv_patchTwo {x : ModelCoordinates} (hp : planeOf x ∈ L.patchTwo) :
    FoldRel sphericalModelMetric (sphDomain (sphBase L) (isOpen_sphBase L)) (sphMap (𝒢))
      (hopfParam x) (hopfParam (screwChart (𝒦).σ.vertexTwo (2 * Real.pi / (𝒦).σ.p₂)
        ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) x)) := by
  have hmain : ∀ {z : ℂ}, z ∈ L.patchTwo → z ∈ L.mainSet := fun h => Or.inr h
  have hconj : ∀ {y : ModelCoordinates}, planeOf y ∈ L.patchTwo →
      conj (planeOf (screwChart (𝒦).σ.vertexTwo (2 * Real.pi / (𝒦).σ.p₂)
        ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) y)) ∈ L.mainSet := fun {y} hy => by
    rw [screwTwoInv_mem_conjMain C hc h3 hχ D y]
    exact hmain (L.patchTwo_spec _ hy).2.2.2.2
  have hy0 : ∀ {y : ModelCoordinates}, planeOf y ∈ L.patchTwo →
      1 - conj (𝒦).σ.vertexTwo * planeOf (screwDiffeomorph (2 * Real.pi / (𝒦).σ.p₂)
        ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) (centred (𝒦).σ.vertexTwo y)) ≠ 0 := fun hy => by
    rw [planeOf_screwDiffeomorph, planeOf_centred]
    exact den_patchTwo C hc h3 hχ D L hy
  exact foldRel_sphMap (hper_sph C hc h3 hχ D L) (isOpen_sphBase L)
    (screwSph (𝒦).σ.vertexTwo (2 * Real.pi / (𝒦).σ.p₂) ((𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂)) _
    (isOpen_preimage_planeOf L.isOpen_patchTwo) hp
    (fun y hy => main_mem_base C hc h3 hχ D L (hmain hy))
    (fun y hy => conjMain_mem_base C hc h3 hχ D L (hconj hy))
    (fun y hy => s3Diffeo_screwSph (slitPlane_ne_zero (L.main_slit _ (hmain hy)).2) (hy0 hy))
    (fun y hy => by
      obtain ⟨hV, h1, h2, hn, hr⟩ := L.patchTwo_spec _ hy
      have hx' := one_add_conj_mul_planeOf_screwChart
        (s := (𝒦).ℓ * (𝒦).q₂ / (𝒦).σ.p₂) (den_patchTwo C hc h3 hχ D L hy)
      rw [sphFoldMap_of_conjMain C hc h3 hχ D L (hconj hy),
        sphFoldMap_of_main C hc h3 hχ D L (hmain hy),
        (𝒦).liftM_screwTwoInv hV h1 h2 hn.le (slitPlane_ne_zero (L.main_slit _ (hmain hy)).2)
          (hy0 hy) hx' (L.main_slit _ (hmain hr)).2 (closing_wallTwo C hc h3 hχ D L hy)])

end Rel

end Sph

end ClosedTriangle

end GC.Seifert
