import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryStable

/-!
# The generator moves of the two-cone fold preserve the fold locally

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.3,
with review 21 §4.7). For the fold `F = foldMap` on its domain `N = foldDomain` and the model
metric,
the relation `FoldRel` holds between a point and its image under each generator move, on an open
piece where the move preserves `F`: the deck translations everywhere (`foldRel_moveTrans`), the side
pairing `γ₁ = ρ₀ρ₁` on `patchOne` and on the cone disc about `v₁` (`foldRel_gammaOne_patch`,
`foldRel_gammaOne_disc`), `γ₂ = ρ₀ρ₂` on `patchTwo` (`foldRel_gammaTwo`), and the screws
`S₁ = ρ₁ρ₂`, `S₂ = ρ₂ρ₀` on the cone discs (`foldRel_screwOne`, `foldRel_screwTwo`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

theorem point_ext {p p' : ModelCoordinates} (hz : zOf p = zOf p') (h2 : p 2 = p' 2) : p = p' := by
  have hl : logPoint p = logPoint p' := UpperHalfPlane.ext hz
  rw [← logCoords_logPoint p, ← logCoords_logPoint p', hl, h2]

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (m₁ m₂ : Fin d.fillingCount) (hk : d.k = 3)
  (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)
  {σ : ConeShape} (D : σ.FoldData)
  (hθ₁ : σ.θ₁ * (chartNumbers C m₁ m₂).p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * (chartNumbers C m₁ m₂).p₂ = Real.pi)
  (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ))

def gammaOne : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  (rhoOne σ).trans (rhoZero (chartNumbers C m₁ m₂).c₀)

def gammaTwo : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  (rhoTwo σ (chartNumbers C m₁ m₂).k₁).trans (rhoZero (chartNumbers C m₁ m₂).c₀)

def screwOne : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  (rhoTwo σ (chartNumbers C m₁ m₂).k₁).trans (rhoOne σ)

def screwTwo : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  (rhoZero (chartNumbers C m₁ m₂).c₀).trans (rhoTwo σ (chartNumbers C m₁ m₂).k₁)

theorem foldMap_congr {p p' : ModelCoordinates} (hz : zOf p' = zOf p) (k : ℤ)
    (h2 : p' 2 = p 2 + k) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ p' = foldMap C m₁ m₂ hk D hθ₁ hθ₂ p := by
  unfold foldMap
  rw [hz, liftT_congr D _ hz k h2, liftS_congr D _ hz k h2, tubeOne_congr D _ hz k h2,
    tubeOneS_congr D _ hz k h2, tubeTwo_congr D _ hz k h2]

theorem foldRel_moveTrans {y : ModelCoordinates} (hy : y ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂)
    (k : ℤ) :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y (moveTrans k y) := by
  refine ⟨moveTrans k, pullbackMetric_moveTrans k, rfl, foldDomain C m₁ m₂ D hθ₁ hθ₂, hy,
    subset_rfl, fun z hz => ?_, fun z _ => ?_⟩
  · change zOf (moveTrans k z) ∈ baseDomain D hθ₁ hθ₂
    rw [zOf_moveTrans]; exact hz
  · exact foldMap_congr C m₁ m₂ hk D hθ₁ hθ₂ (zOf_moveTrans k z) k (moveTrans_two k z)

theorem zOf_gammaOne (p : ModelCoordinates) :
    zOf (gammaOne C m₁ m₂ (σ := σ) p) = σ.refl 0 (σ.refl 1 (zOf p)) := by
  change zOf (rhoZero _ (rhoOne σ p)) = _
  rw [zOf_rhoZero, zOf_rhoOne]

theorem flip_gammaOne (p : ModelCoordinates) :
    flipMap (chartNumbers C m₁ m₂).c₀ (gammaOne C m₁ m₂ (σ := σ) p) = rhoOne σ p :=
  flipMap_flipMap _ _

theorem zOf_gammaTwo (p : ModelCoordinates) (hp' : 0 < (zOf p).im) :
    zOf (gammaTwo C m₁ m₂ (σ := σ) p) = σ.refl 0 (σ.refl 2 (zOf p)) := by
  change zOf (rhoZero _ (rhoTwo σ _ p)) = _
  rw [zOf_rhoZero, zOf_rhoTwo σ _ p hp']

theorem flip_gammaTwo (p : ModelCoordinates) :
    flipMap (chartNumbers C m₁ m₂).c₀ (gammaTwo C m₁ m₂ (σ := σ) p) =
      rhoTwo σ (chartNumbers C m₁ m₂).k₁ p :=
  flipMap_flipMap _ _

theorem mem_mirrorSet_refl {S : Set ℂ} {w : ℂ} (hw : w ∈ S) (him : 0 < w.im) :
    σ.refl 0 w ∈ mirrorSet σ S :=
  ⟨σ.refl_im_pos him 0, by rw [σ.refl_refl him 0]; exact hw⟩

include hj hp hc₁ hc₂ in
theorem foldRel_gammaOne_patch {y : ModelCoordinates} (hy : zOf y ∈ patchOne D hθ₁) :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y (gammaOne C m₁ m₂ (σ := σ) y) := by
  have hopen : IsOpen (zOf ⁻¹' patchOne D hθ₁) :=
    (isOpen_patchOne D hθ₁).preimage contDiff_zOf.continuous
  have hmir : ∀ z ∈ zOf ⁻¹' patchOne D hθ₁,
      zOf (gammaOne C m₁ m₂ (σ := σ) z) ∈ mirrorSet σ (mainSet D hθ₁ hθ₂) := fun z hz => by
    rw [zOf_gammaOne]
    exact mem_mirrorSet_refl (Or.inl (Or.inr (refl_one_mem_patchOne D hθ₁ hz)))
      (σ.refl_im_pos hz.1 1)
  refine ⟨gammaOne C m₁ m₂ (σ := σ), pullbackMetric_trans_iso (pullbackMetric_rhoOne σ)
    (pullbackMetric_rhoZero _), rfl, ⟨_, hopen⟩, hy,
    fun z hz => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hz))))),
    fun z hz => Or.inl (Or.inl (Or.inl (Or.inr (hmir z hz)))), fun z hz => ?_⟩
  rw [foldMap_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (hmir z hz),
    foldMap_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inl (Or.inr hz))]
  congr 1
  unfold liftS
  rw [flip_gammaOne, liftT_rhoOne D _ hz.2.1 hz.2.2.2.2.2.2.1, conjPair_conjPair]

theorem foldRel_gammaOne_disc {y : ModelCoordinates} (hy : zOf y ∈ discOne D hθ₁) :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y (gammaOne C m₁ m₂ (σ := σ) y) := by
  have hopen : IsOpen (zOf ⁻¹' discOne D hθ₁) :=
    (isOpen_discOne D hθ₁).preimage contDiff_zOf.continuous
  have hmir : ∀ z ∈ zOf ⁻¹' discOne D hθ₁,
      zOf (gammaOne C m₁ m₂ (σ := σ) z) ∈ mirrorSet σ (discOne D hθ₁) := fun z hz => by
    rw [zOf_gammaOne]
    exact mem_mirrorSet_refl (refl_one_mem_discOne D hθ₁ hz) (σ.refl_im_pos hz.1 1)
  refine ⟨gammaOne C m₁ m₂ (σ := σ), pullbackMetric_trans_iso (pullbackMetric_rhoOne σ)
    (pullbackMetric_rhoZero _), rfl, ⟨_, hopen⟩, hy,
    fun z hz => Or.inl (Or.inl (Or.inr hz)),
    fun z hz => Or.inl (Or.inr (hmir z hz)), fun z hz => ?_⟩
  rw [foldMap_of_mirrorDiscOne C m₁ m₂ hk D hθ₁ hθ₂ (hmir z hz),
    foldMap_of_discOne C m₁ m₂ hk D hθ₁ hθ₂ hz]
  congr 1
  unfold tubeOneS
  have hspec := radiusOne_spec D hθ₁ hz.1 hz.2
  rw [flip_gammaOne, tubeOne_rhoOne D _ hspec.2.2.2.1
    (by linarith [re_f_of_mem_discOne D hθ₁ hz (n := chartNumbers C m₁ m₂)]),
    conjPair_conjPair]

include hj hp hc₁ hc₂ in
theorem foldRel_gammaTwo {y : ModelCoordinates} (hy : zOf y ∈ patchTwo D hθ₁ hθ₂) :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y (gammaTwo C m₁ m₂ (σ := σ) y) := by
  have hopen : IsOpen (zOf ⁻¹' patchTwo D hθ₁ hθ₂) :=
    (isOpen_patchTwo D hθ₁ hθ₂).preimage contDiff_zOf.continuous
  have hmir : ∀ z ∈ zOf ⁻¹' patchTwo D hθ₁ hθ₂,
      zOf (gammaTwo C m₁ m₂ (σ := σ) z) ∈ mirrorSet σ (mainSet D hθ₁ hθ₂) := fun z hz => by
    rw [zOf_gammaTwo C m₁ m₂ (σ := σ) z hz.1]
    exact mem_mirrorSet_refl (Or.inr (refl_two_mem_patchTwo D hθ₁ hθ₂ hz))
      (σ.refl_im_pos hz.1 2)
  refine ⟨gammaTwo C m₁ m₂ (σ := σ), pullbackMetric_trans_iso (pullbackMetric_rhoTwo σ _)
    (pullbackMetric_rhoZero _), rfl, ⟨_, hopen⟩, hy,
    fun z hz => Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hz)))),
    fun z hz => Or.inl (Or.inl (Or.inl (Or.inr (hmir z hz)))), fun z hz => ?_⟩
  rw [foldMap_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (hmir z hz),
    foldMap_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inr hz)]
  congr 1
  unfold liftS
  rw [flip_gammaTwo, liftT_rhoTwo D _ hz.2.1 hz.2.2.2.2.2.2.1 hz.2.2.2.2.2.2.2.1,
    conjPair_conjPair]

include hp in
theorem foldRel_screwOne {y : ModelCoordinates} (hy : zOf y ∈ discOne D hθ₁) :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y (screwOne C m₁ m₂ (σ := σ) y) := by
  have hopen : IsOpen (zOf ⁻¹' discOne D hθ₁) :=
    (isOpen_discOne D hθ₁).preimage contDiff_zOf.continuous
  have hz' : ∀ z ∈ zOf ⁻¹' discOne D hθ₁, zOf (screwOne C m₁ m₂ (σ := σ) z) ∈ discOne D hθ₁ :=
    fun z hz => by
      change zOf (rhoOne σ (rhoTwo σ (chartNumbers C m₁ m₂).k₁ z)) ∈ discOne D hθ₁
      rw [zOf_rhoOne, zOf_rhoTwo σ _ z hz.1]
      exact rot_mem_discOne D hθ₁ hz
  refine ⟨screwOne C m₁ m₂ (σ := σ), pullbackMetric_trans_iso (pullbackMetric_rhoTwo σ _)
    (pullbackMetric_rhoOne σ), rfl, ⟨_, hopen⟩, hy,
    fun z hz => Or.inl (Or.inl (Or.inr hz)),
    fun z hz => Or.inl (Or.inl (Or.inr (hz' z hz))), fun z hz => ?_⟩
  rw [foldMap_of_discOne C m₁ m₂ hk D hθ₁ hθ₂ (hz' z hz),
    foldMap_of_discOne C m₁ m₂ hk D hθ₁ hθ₂ hz]
  congr 1
  exact tubeOne_screw D hθ₁ (chartNumbers_bezout₁ C m₁ m₂ hp) hz (hz' z hz)

include hp in
theorem foldRel_screwTwo {y : ModelCoordinates} (hy : zOf y ∈ discTwo D hθ₂) :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y (screwTwo C m₁ m₂ (σ := σ) y) := by
  have hopen : IsOpen (zOf ⁻¹' discTwo D hθ₂) :=
    (isOpen_discTwo D hθ₂).preimage contDiff_zOf.continuous
  have hz' : ∀ z ∈ zOf ⁻¹' discTwo D hθ₂, zOf (screwTwo C m₁ m₂ (σ := σ) z) ∈ discTwo D hθ₂ :=
    fun z hz => by
      change zOf (rhoTwo σ (chartNumbers C m₁ m₂).k₁ (rhoZero (chartNumbers C m₁ m₂).c₀ z)) ∈
        discTwo D hθ₂
      rw [zOf_rhoTwo σ _ _ (by rw [zOf_rhoZero]; exact σ.refl_im_pos hz.1 0), zOf_rhoZero]
      exact rot_mem_discTwo D hθ₂ hz
  refine ⟨screwTwo C m₁ m₂ (σ := σ), pullbackMetric_trans_iso (pullbackMetric_rhoZero _)
    (pullbackMetric_rhoTwo σ _), rfl, ⟨_, hopen⟩, hy,
    fun z hz => Or.inr hz, fun z hz => Or.inr (hz' z hz), fun z hz => ?_⟩
  rw [foldMap_of_discTwo C m₁ m₂ hk D hθ₁ hθ₂ (hz' z hz),
    foldMap_of_discTwo C m₁ m₂ hk D hθ₁ hθ₂ hz]
  congr 1
  exact tubeTwo_screw D hθ₂ (chartNumbers_bezout₂ C m₁ m₂ hp) hz (hz' z hz)

end Fold

end TwoConeFold

end GC.Seifert
