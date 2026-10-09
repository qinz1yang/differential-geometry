import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitSite
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSphere

/-!
# The split tube of a mixed stage

Lane MS, tier MS2 (design `handoffs/20261004-design-ms-mixed-split.md` §1.2). The Seifert instance
of the split charts of lane N2c (`Seifert/MoveSplitCappedSphere.lean`, section `Instance`) for a
split seam `j` on side `b` of a mixed stage `σ` with linear matching: standard product structures
of the solid torus and of the host over the round disc and the round pants that agree with the
actual piece collars on a sub-collar (`SplitData`, chosen once as `splitData`), the charts
`solidMap`, `hostMap` (for any split datum `S`, so that an elementary
presentation can pass its own), the seam chart `seamMap` read from the solid side, the host side
`hostSide`, and `splitCharts : SplitTube.SplitCharts Q.Carrier`. The resulting one-tube system is
`splitSeamTube`. Only the torus presentation and the two non-frozen pieces `V`, `H` are read; the
texts are those of N2c with the elementary presentation replaced by the mixed stage.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (sideHeight sideHeight_not sideHeight_neg clampDisc
  clampPants clampDisc_val clampPants_val discCollar_eq pantsCollar_eq
  isLocalDiffeomorphAt_clampDisc isLocalDiffeomorphAt_clampPants)

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool}

section SplitData

structure SplitData (h : σ.IsSplitSeam j b) where
  δ : ℝ
  hδ : 0 < δ
  ΘV : ((discPlanarBase.{u} 1).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
    (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1), σ.toTorus.cutCarrier.model⟯
      σ.toTorus.components.piece (σ.seamPiece j b)
  ΘH : (pantsPlanarBase.{u}.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
    pantsPlanarBase.{u}.surface.kind).prod (𝓡 1), σ.toTorus.cutCarrier.model⟯
      σ.toTorus.components.piece (σ.hostPiece j b)
  hV : ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
    σ.toTorus.pieceCollar (σ.seamPiece j b)
      (σ.standardPort (σ.seamPiece j b) (σ.seamPiece_not_frozen h) h.2.1 l) p =
      ΘV ((discPlanarBase.{u} 1).collar l (p.1.1, p.2), p.1.2)
  hH : ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
    σ.toTorus.pieceCollar (σ.hostPiece j b)
      (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 l) p =
      ΘH (pantsPlanarBase.{u}.collar l (p.1.1, p.2), p.1.2)

theorem nonempty_splitData (h : σ.IsSplitSeam j b) : Nonempty (σ.SplitData h) := by
  obtain ⟨δ, hδ, ΘV, ΘH, hV, hH⟩ := σ.exists_standardSplit h
  exact ⟨⟨δ, hδ, ΘV, ΘH, hV, hH⟩⟩

def splitData (h : σ.IsSplitSeam j b) : σ.SplitData h := Classical.choice (σ.nonempty_splitData h)

variable (j) in
def seamCoord : Bool → (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ)
  | true => Diffeomorph.refl signedCollarModel (Torus × ℝ) ∞
  | false => (σ.toTorus.pairing.matching j).symm.prodCongr
      (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph

variable (j) in
theorem seamCoord_apply :
    ∀ (b : Bool) (q : Torus × ℝ), σ.seamCoord j b q = (σ.leftOfSide j b q.1, sideHeight b (-q.2))
  | true, q => by simp [seamCoord, leftOfSide, sideHeight]
  | false, q => by
    simp only [seamCoord, leftOfSide, sideHeight]
    rfl

end SplitData

section Instance

def solidMap {h : σ.IsSplitSeam j b} (S : σ.SplitData h) : ℂ × Circle → Q.Carrier :=
  σ.toTorus.pieceChart (σ.seamPiece j b) (discPlanarBase.{u} 1) S.ΘV clampDisc

def hostMap {h : σ.IsSplitSeam j b} (S : σ.SplitData h) : ℂ × Circle → Q.Carrier :=
  σ.toTorus.pieceChart (σ.hostPiece j b) pantsPlanarBase.{u} S.ΘH clampPants

variable (j b) in
def seamMap (q : Torus × ℝ) : Q.Carrier :=
  σ.toTorus.seam j (σ.seamCoord j b q)

def hostSide (h : σ.IsSplitSeam j b) : Fin 3 :=
  (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1).symm
    ⟨σ.seamSide j !b, σ.sidePiece_seamSide j !b⟩

theorem crossUnit_zero (h : σ.IsSplitSeam j b) :
    (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := by
  have h0 := h.2.2.2
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_zero] at h0
  exact h0

variable (j b) in
theorem seamMap_zero (t : Torus) :
    σ.seamMap j b (t, 0) =
      σ.toTorus.cutMap (σ.toTorus.sideCollar (σ.seamSide j b) (t, halfZero)) := by
  rw [seamMap, seamCoord_apply, neg_zero]
  exact (σ.cutMap_sideCollar_eq_seam j b t 0 le_rfl zero_lt_one).symm

variable (j b) in
theorem seamMap_local {q : Torus × ℝ} (hq : |q.2| < 1) :
    IsLocalDiffeomorphAt signedCollarModel (𝓡 3) ∞ (σ.seamMap j b) q := by
  have hmem : σ.seamCoord j b q ∈ (σ.toTorus.seam j).source := by
    rw [σ.toTorus.seam_source, seamCoord_apply]
    have h1 := abs_lt.mp hq
    cases b <;> simp only [sideHeight, neg_neg, id] <;> constructor <;> linarith
  exact ((σ.seamCoord j b).isLocalDiffeomorph q).comp _ _
    ((σ.toTorus.seam j).isLocalDiffeomorphAt _ _ ∞ hmem)

variable (j b) in
theorem seamMap_inj {t t' : Torus} (h : σ.seamMap j b (t, 0) = σ.seamMap j b (t', 0)) :
    t = t' := by
  have hmem : ∀ x : Torus, σ.seamCoord j b (x, 0) ∈ (σ.toTorus.seam j).source := by
    intro x
    rw [σ.toTorus.seam_source, seamCoord_apply, neg_zero]
    change -1 < sideHeight b 0 ∧ sideHeight b 0 < 1
    cases b <;> simp [sideHeight]
  have := (σ.toTorus.seam j).toPartialEquiv.injOn (hmem t) (hmem t') h
  exact congrArg Prod.fst ((σ.seamCoord j b).injective this)

theorem standardPort_seamPiece (h : σ.IsSplitSeam j b) (l : Fin 1) :
    σ.standardPort (σ.seamPiece j b) (σ.seamPiece_not_frozen h) h.2.1 l =
      ⟨σ.seamSide j b, σ.sidePiece_seamSide j b⟩ := by
  have hs : Subsingleton (σ.toTorus.OwnedSide (σ.seamPiece j b)) :=
    Fintype.card_le_one_iff_subsingleton.mp (σ.card_ownedSide_seamPiece h).le
  exact Subsingleton.elim _ _

theorem standardPort_hostSide (h : σ.IsSplitSeam j b) :
    σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 (σ.hostSide h) =
      ⟨σ.seamSide j !b, σ.sidePiece_seamSide j !b⟩ :=
  Equiv.apply_symm_apply _ _

theorem seamMap_neg {h : σ.IsSplitSeam j b} (S : σ.SplitData h) (t : Torus) {r : ℝ}
    (hr : -min (S.δ / 2) (1 / 2) < r) (hr0 : r < 0) :
    σ.seamMap j b (t, r) = σ.solidMap S ((3 + 3 * r / 2 : ℝ) • (t.1 : ℂ), t.2) := by
  have hδ := S.hδ
  have hm1 := min_le_left (S.δ / 2) (1 / 2)
  have hm2 := min_le_right (S.δ / 2) (1 / 2)
  have hs0 : 0 ≤ -r := by linarith
  have hs1 : -r < 1 := by linarith
  rw [seamMap, seamCoord_apply, ← σ.cutMap_sideCollar_eq_seam j b t (-r) hs0 hs1]
  have hp : (t, halfPoint (-r) hs0) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply σ.toTorus (σ.seamPiece j b)
    ⟨σ.seamSide j b, σ.sidePiece_seamSide j b⟩ hp
  have e2 := S.hV 0 (t, halfPoint (-r) hs0) hp (by
    change -r < S.δ
    linarith)
  rw [σ.standardPort_seamPiece h] at e2
  rw [← e1, e2]
  change σ.toTorus.cutMap (S.ΘV ((discPlanarBase.{u} 1).collar 0
    (t.1, halfPoint (-r) hs0), t.2) : σ.toTorus.cutCarrier.Carrier) =
    σ.toTorus.cutMap (S.ΘV (clampDisc ((3 + 3 * r / 2 : ℝ) • (t.1 : ℂ)), t.2) :
      σ.toTorus.cutCarrier.Carrier)
  rw [discCollar_eq hs0 hs1]
  congr 4
  ring_nf

theorem seamMap_pos {h : σ.IsSplitSeam j b} (S : σ.SplitData h) (hlin : σ.IsLinearSeam j)
    (t : Torus) {r : ℝ}
    (hr0 : 0 < r) (hr : r < min (S.δ / 2) (1 / 2)) :
    σ.seamMap j b (t, r) = σ.hostMap S (planarCollarFormula 3 (σ.hostSide h)
      (((t.2 ^ (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : Circle) : ℂ), r),
      t.1 ^ (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
        t.2 ^ (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
  have hδ := S.hδ
  have hm1 := min_le_left (S.δ / 2) (1 / 2)
  have hm2 := min_le_right (S.δ / 2) (1 / 2)
  have hs1 : r < 1 := by linarith
  have hcross : σ.crossMap j b t = (t.2 ^ (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
      t.1 ^ (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
        t.2 ^ (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
    rw [hlin.crossMap_apply b t]
    simp [linearTorusMap, crossUnit_zero σ h]
  have e0 := σ.cutMap_sideCollar_eq_seam j (!b) (σ.crossMap j b t) r hr0.le hs1
  rw [leftOfSide_not_crossMap, sideHeight_not] at e0
  rw [seamMap, seamCoord_apply, sideHeight_neg, ← e0]
  have hp : (σ.crossMap j b t, halfPoint r hr0.le) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply σ.toTorus (σ.hostPiece j b)
    ⟨σ.seamSide j !b, σ.sidePiece_seamSide j !b⟩ hp
  have e2 := S.hH (σ.hostSide h) (σ.crossMap j b t, halfPoint r hr0.le) hp (by
    change r < S.δ
    linarith)
  rw [σ.standardPort_hostSide h] at e2
  rw [← e1, e2]
  change σ.toTorus.cutMap (S.ΘH (pantsPlanarBase.{u}.collar (σ.hostSide h)
    ((σ.crossMap j b t).1, halfPoint r hr0.le), (σ.crossMap j b t).2) :
      σ.toTorus.cutCarrier.Carrier) = _
  rw [pantsCollar_eq _ hr0.le hs1, hcross]
  rfl

theorem hostMap_local {h : σ.IsSplitSeam j b} (S : σ.SplitData h) {q : ℂ × Circle}
    (hq : q.1 ∈ SplitTube.pantsInterior) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ (σ.hostMap S) q :=
  σ.toTorus.isLocalDiffeomorphAt_pieceChart _ _ _ _ (isLocalDiffeomorphAt_clampPants hq)

theorem solidMap_local {h : σ.IsSplitSeam j b} (S : σ.SplitData h) {q : ℂ × Circle}
    (hq : ‖q.1‖ < 3) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ (σ.solidMap S) q :=
  σ.toTorus.isLocalDiffeomorphAt_pieceChart _ _ _ _ (isLocalDiffeomorphAt_clampDisc hq)

def splitCharts {h : σ.IsSplitSeam j b} (S : σ.SplitData h) (hlin : σ.IsLinearSeam j) :
    SplitTube.SplitCharts Q.Carrier where
  host := σ.hostSide h
  e₀ := (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  e₁ := (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  d := (σ.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  he₀ := (units_entries_of_zero _ (crossUnit_zero σ h)).2
  he₁ := (units_entries_of_zero _ (crossUnit_zero σ h)).1
  δ := min (S.δ / 2) (1 / 2)
  hδ := lt_min (half_pos S.hδ) (by norm_num)
  hδ1 := min_le_right _ _
  solid := σ.solidMap S
  hostMap := σ.hostMap S
  seam := σ.seamMap j b
  solid_local q hq := σ.solidMap_local S hq
  host_local q hq := σ.hostMap_local S hq
  seam_local q hq := σ.seamMap_local j b (lt_of_lt_of_le hq ((min_le_right _ _).trans
    (by norm_num)))
  solid_inj q q' hq hq' heq := by
    refine σ.toTorus.pieceChart_injOn _ _ _ _ (isLocalDiffeomorphAt_clampDisc hq) ?_ heq
    intro he
    have h1 := clampDisc_val.{u} hq.le
    have h2 := clampDisc_val.{u} hq'.le
    have := congrArg (fun x : (discPlanarBase.{u} 1).surface.Carrier => (x : discSet.{u}).val) he
    change (clampDisc.{u} q.1 : discSet.{u}).val = (clampDisc.{u} q'.1 : discSet.{u}).val at this
    rw [h1, h2] at this
    exact congrArg ULift.down this
  host_inj q q' hq hq' heq := by
    refine σ.toTorus.pieceChart_injOn _ _ _ _ (isLocalDiffeomorphAt_clampPants hq) ?_ heq
    intro he
    have h1 := clampPants_val.{u} (SplitTube.pantsInterior_subset hq)
    have h2 := clampPants_val.{u} (SplitTube.pantsInterior_subset hq')
    have := congrArg (fun x : pantsPlanarBase.{u}.surface.Carrier =>
      (x : planarSet.{u} 3).val) he
    change (clampPants.{u} q.1 : planarSet.{u} 3).val =
      (clampPants.{u} q'.1 : planarSet.{u} 3).val at this
    rw [h1, h2] at this
    exact congrArg ULift.down this
  seam_inj t t' := σ.seamMap_inj j b
  solid_ne_host q q' hq _ :=
    σ.toTorus.pieceChart_ne _ _ _ _ (σ.seamPiece_ne_hostPiece h) _ _ _
      (isLocalDiffeomorphAt_clampDisc hq)
  seam_ne_solid t q hq := by
    rw [σ.seamMap_zero]
    exact σ.toTorus.cutMap_ne_pieceChart _ _ _ _
      (σ.toTorus.sideCollar_zero_mem _ t).1 (isLocalDiffeomorphAt_clampDisc hq)
  seam_ne_host t q hq := by
    rw [σ.seamMap_zero]
    exact σ.toTorus.cutMap_ne_pieceChart _ _ _ _
      (σ.toTorus.sideCollar_zero_mem _ t).1 (isLocalDiffeomorphAt_clampPants hq)
  seam_neg t r hr hr0 := σ.seamMap_neg S t hr hr0
  seam_pos t r hr0 hr := σ.seamMap_pos S hlin t hr0 hr

end Instance

def splitSeamTube {h : σ.IsSplitSeam j b} (S : σ.SplitData h) (hlin : σ.IsLinearSeam j) :
    SphericalTubeSystem Q.toClosedOrientedManifold :=
  SplitTube.SplitCharts.tubeSystem (Q := Q.toClosedOrientedManifold) (σ.splitCharts S hlin)

def splitSeamSphere {h : σ.IsSplitSeam j b} (S : σ.SplitData h) (hlin : σ.IsLinearSeam j) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → Q.Carrier :=
  (σ.splitCharts S hlin).sphere

theorem tubeMiddleSphere_splitSeamTube {h : σ.IsSplitSeam j b} (S : σ.SplitData h)
    (hlin : σ.IsLinearSeam j) :
    tubeMiddleSphere (σ.splitSeamTube S hlin) () = σ.splitSeamSphere S hlin := rfl

end GC.Seifert.RelativeNormalization.MixedStage
