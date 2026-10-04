import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryPieces

/-!
# The reflections of the two-cone fold and the local relation of same-image pairs

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §2,
§3.3, with review 21 §4.3, §4.7). The wall lifts `ρ₀ = (σ₀ z, c₀ - s)`, `ρ₁ = (σ₁ z, -s)`,
`ρ₂ = (σ₂ z, k₁ - s)` and the fibre translations `(z, s + t)` are isometries of the model metric
`.hyperbolicProduct` (a flip followed by a Möbius map in the log chart, `pullbackMetric_rho*`);
their products are the side pairings `γᵢ = ρ₀ρᵢ`, the screws `S₁ = ρ₁ρ₂`, `S₂ = ρ₂ρ₀` and the
deck translations. `FoldRel g N F y y'` says that `y` and `y'` are related by an ambient isometry
preserving `F` on an open neighbourhood of `y` inside `N` that it maps into `N` — exactly the
conclusion required by `metricFiberCompatible_of_foldPairs`. Following review 21 §4.7 it is an
equivalence relation on `N` (`FoldRel.refl`, `FoldRel.symm`, `FoldRel.trans`), so the same-image
analysis only needs generator moves, not an exhaustive list of words.
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold UpperHalfPlane

namespace GC.Seifert

namespace TwoConeFold

section Rel

variable {M : Type*} (g : SmoothRiemannianMetric (𝓡 3) ModelCoordinates)
  (N : Set ModelCoordinates) (F : ModelCoordinates → M)

def FoldRel (y y' : ModelCoordinates) : Prop :=
  ∃ γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates,
    Diffeomorph.pullbackMetric g γ = g ∧ γ y = y' ∧
      ∃ U : TopologicalSpace.Opens ModelCoordinates, y ∈ U ∧ (U : Set ModelCoordinates) ⊆ N ∧
        MapsTo γ (U : Set ModelCoordinates) N ∧ ∀ z ∈ U, F (γ z) = F z

variable {g N F}

theorem FoldRel.refl' {y : ModelCoordinates} (hN : IsOpen N) (hy : y ∈ N) : FoldRel g N F y y := by
  refine ⟨Diffeomorph.refl (𝓡 3) ModelCoordinates ∞, ?_, rfl, ⟨N, hN⟩, hy, subset_rfl,
    fun z hz => hz, fun z _ => rfl⟩
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change g.inner x (mfderiv (𝓡 3) (𝓡 3) id x v) (mfderiv (𝓡 3) (𝓡 3) id x w) = _
  rw [mfderiv_id]
  rfl

theorem pullbackMetric_symm_iso {γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates}
    (h : Diffeomorph.pullbackMetric g γ = g) : Diffeomorph.pullbackMetric g γ.symm = g := by
  conv_lhs => rw [← h]
  rw [Diffeomorph.pullbackMetric_trans, Diffeomorph.symm_trans_self]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change g.inner x (mfderiv (𝓡 3) (𝓡 3) id x v) (mfderiv (𝓡 3) (𝓡 3) id x w) = _
  rw [mfderiv_id]
  rfl

theorem pullbackMetric_trans_iso {γ δ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates}
    (hγ : Diffeomorph.pullbackMetric g γ = g) (hδ : Diffeomorph.pullbackMetric g δ = g) :
    Diffeomorph.pullbackMetric g (γ.trans δ) = g := by
  rw [← Diffeomorph.pullbackMetric_trans, hδ, hγ]

theorem FoldRel.symm {y y' : ModelCoordinates} (h : FoldRel g N F y y') : FoldRel g N F y' y := by
  obtain ⟨γ, hγ, hyy, U, hyU, hUN, hmaps, hF⟩ := h
  refine ⟨γ.symm, pullbackMetric_symm_iso hγ, by rw [← hyy, γ.symm_apply_apply],
    ⟨γ '' U, γ.toHomeomorph.isOpenMap _ U.isOpen⟩, ⟨y, hyU, hyy⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hmaps hz
  · rintro _ ⟨z, hz, rfl⟩
    rw [γ.symm_apply_apply]
    exact hUN hz
  · rintro _ ⟨z, hz, rfl⟩
    rw [γ.symm_apply_apply]
    exact (hF z hz).symm

theorem FoldRel.trans {y y' y'' : ModelCoordinates} (h : FoldRel g N F y y')
    (h' : FoldRel g N F y' y'') : FoldRel g N F y y'' := by
  obtain ⟨γ, hγ, hyy, U, hyU, hUN, hmaps, hF⟩ := h
  obtain ⟨δ, hδ, hyy', V, hyV, hVN, hmaps', hF'⟩ := h'
  refine ⟨γ.trans δ, pullbackMetric_trans_iso hγ hδ, by
      change δ (γ y) = y''; rw [hyy, hyy'],
    ⟨U ∩ γ ⁻¹' V, U.isOpen.inter (V.isOpen.preimage γ.continuous)⟩,
    ⟨hyU, by change γ y ∈ V; rw [hyy]; exact hyV⟩, fun z hz => hUN hz.1,
    fun z hz => hmaps' hz.2, fun z hz => ?_⟩
  change F (δ (γ z)) = F z
  rw [hF' _ hz.2, hF z hz.1]

end Rel

section Moves

open ConeShape

variable (σ : ConeShape)

def glOfDet' (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A hA.ne'

theorem glOfDet'_det_pos (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) :
    0 < (glOfDet' A hA).det.val := by
  simpa [glOfDet', Matrix.GeneralLinearGroup.mkOfDetNeZero] using hA

theorem coe_glOfDet'_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) (z : ℍ) :
    ((glOfDet' A hA • z : ℍ) : ℂ) = (A 0 0 * (z : ℂ) + A 0 1) / (A 1 0 * z + A 1 1) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (glOfDet'_det_pos A hA)]
  rfl

def transMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, t; 0, 1]

theorem transMatrix_det (t : ℝ) : 0 < (transMatrix t).det := by
  simp [transMatrix, Matrix.det_fin_two]

def circleMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![σ.centre, σ.centre ^ 2 - 1 / 16; 1, σ.centre]

theorem circleMatrix_det : 0 < (circleMatrix σ).det := by
  simp [circleMatrix, Matrix.det_fin_two]
  nlinarith

def moveTrans (t : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  pairingDiffeo (glOfDet' (transMatrix 0) (transMatrix_det 0))
    (glOfDet'_det_pos _ (transMatrix_det 0)) t

def rhoZero (c : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates := foldFlip c

def rhoOne : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  (foldFlip 0).trans (pairingDiffeo (glOfDet' (transMatrix (2 * σ.width))
    (transMatrix_det _)) (glOfDet'_det_pos _ (transMatrix_det _)) 0)

def rhoTwo (c : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  (foldFlip c).trans (pairingDiffeo (glOfDet' (circleMatrix σ) (circleMatrix_det σ))
    (glOfDet'_det_pos _ (circleMatrix_det σ)) 0)

theorem zOf_mobiusLogMap (g' : GL (Fin 2) ℝ) (t : ℝ) (p : ModelCoordinates) :
    zOf (mobiusLogMap g' t p) = ((g' • logPoint p : ℍ) : ℂ) := by
  rw [zOf, mobiusLogMap, logPoint_logCoords]

theorem mobiusLogMap_two' (g' : GL (Fin 2) ℝ) (t : ℝ) (p : ModelCoordinates) :
    mobiusLogMap g' t p 2 = p 2 + t :=
  logCoords_two _ _

theorem zOf_moveTrans (t : ℝ) (p : ModelCoordinates) : zOf (moveTrans t p) = zOf p := by
  change zOf (mobiusLogMap _ t p) = _
  rw [zOf_mobiusLogMap, coe_glOfDet'_smul]
  simp [transMatrix, zOf]

theorem moveTrans_two (t : ℝ) (p : ModelCoordinates) : moveTrans t p 2 = p 2 + t :=
  mobiusLogMap_two' _ _ _

theorem zOf_rhoZero (c : ℝ) (p : ModelCoordinates) : zOf (rhoZero c p) = σ.refl 0 (zOf p) := by
  change zOf (flipMap c p) = _
  rw [coe_logPoint_flipMap]
  rfl

theorem rhoZero_two (c : ℝ) (p : ModelCoordinates) : rhoZero c p 2 = c - p 2 := flipMap_two c p

theorem zOf_rhoOne (p : ModelCoordinates) : zOf (rhoOne σ p) = σ.refl 1 (zOf p) := by
  change zOf (mobiusLogMap _ 0 (flipMap 0 p)) = _
  rw [zOf_mobiusLogMap, coe_glOfDet'_smul]
  change _ = 2 * (σ.width : ℂ) - conj (zOf p)
  have h := coe_logPoint_flipMap 0 p
  rw [zOf] at h
  simp only [transMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [h]
  push_cast
  ring

theorem rhoOne_two (p : ModelCoordinates) : rhoOne σ p 2 = -p 2 := by
  change mobiusLogMap _ 0 (flipMap 0 p) 2 = _
  rw [mobiusLogMap_two', flipMap_two]
  ring

theorem zOf_rhoTwo (c : ℝ) (p : ModelCoordinates) (hp : 0 < (zOf p).im) :
    zOf (rhoTwo σ c p) = σ.refl 2 (zOf p) := by
  change zOf (mobiusLogMap _ 0 (flipMap c p)) = _
  rw [zOf_mobiusLogMap, coe_glOfDet'_smul]
  have h := coe_logPoint_flipMap c p
  rw [zOf] at h
  simp only [circleMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [h]
  change _ = (σ.centre : ℂ) + 1 / 16 / (conj (zOf p) - σ.centre)
  have hne : conj (zOf p) - σ.centre ≠ 0 := σ.conj_centre_ne hp
  have hne' : (σ.centre : ℂ) - conj (zOf p) ≠ 0 := by
    intro h0; apply hne; linear_combination -h0
  rw [show ((1 : ℝ) : ℂ) * -conj (zOf p) + (σ.centre : ℂ) =
    (σ.centre : ℂ) - conj (zOf p) by push_cast; ring]
  rw [div_eq_iff hne']
  push_cast
  field_simp
  ring

theorem rhoTwo_two (c : ℝ) (p : ModelCoordinates) : rhoTwo σ c p 2 = c - p 2 := by
  change mobiusLogMap _ 0 (flipMap c p) 2 = _
  rw [mobiusLogMap_two', flipMap_two]
  ring

theorem pullbackMetric_moveTrans (t : ℝ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (moveTrans t) =
      coordinateModelMetric .hyperbolicProduct :=
  pullbackMetric_pairingDiffeo _ _ _

theorem pullbackMetric_rhoZero (c : ℝ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (rhoZero c) =
      coordinateModelMetric .hyperbolicProduct :=
  pullbackMetric_foldFlip c

theorem pullbackMetric_rhoOne :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (rhoOne σ) =
      coordinateModelMetric .hyperbolicProduct :=
  pullbackMetric_trans_iso (pullbackMetric_foldFlip 0) (pullbackMetric_pairingDiffeo _ _ _)

theorem pullbackMetric_rhoTwo (c : ℝ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (rhoTwo σ c) =
      coordinateModelMetric .hyperbolicProduct :=
  pullbackMetric_trans_iso (pullbackMetric_foldFlip c) (pullbackMetric_pairingDiffeo _ _ _)

end Moves

end TwoConeFold

end GC.Seifert
