import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepShift
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationLevel

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.LongTime.CuspP1
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

/-- Height translation of `T² × ℝ` by `S`. -/
def heightTranslate_C2a (S : ℝ) : Diffeomorph (torusModel.prod 𝓘(ℝ, ℝ)) (torusModel.prod 𝓘(ℝ, ℝ))
    (Torus × ℝ) (Torus × ℝ) ∞ :=
  (Diffeomorph.refl torusModel Torus ∞).prodCongr (translate_CPA2 S)

theorem isOpen_signedCollarSource_C2a : IsOpen signedCollarSource := by
  have h : signedCollarSource = (fun p : Torus × ℝ => p.2) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext p; simp [signedCollarSource]
  rw [h]; exact isOpen_Ioo.preimage continuous_snd

/-- The signed (two-sided) collar of the level-`S` torus of the `i`-th cusp, `S ≥ 2`:
`(x, s) ↦ cuspMap i (x, S + s)` on `|s| < 1`. -/
def levelSignedCollar_C2a (S : ℝ) (i : Fin T.count) :
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) H.Carrier ∞ :=
  (((heightTranslate_C2a S).toPartialDiffeomorph.trans interiorLift_CPA2).trans
    (cuspChart_CPA2 T i)).restrict signedCollarSource isOpen_signedCollarSource_C2a

theorem levelSignedCollar_apply_C2a (S : ℝ) (i : Fin T.count) (p : Torus × ℝ) :
    levelSignedCollar_C2a T S i p = T.cuspMap i (p.1, halfSpaceOneLift (p.2 + S)) := by
  change cuspChart_CPA2 T i (interiorLift_CPA2 (p.1, p.2 + S)) = _
  rw [interiorLift_apply_CPA2, cuspChart_apply_CPA2]

theorem levelSignedCollar_source_C2a {S : ℝ} (hS : 2 ≤ S) (i : Fin T.count) :
    (levelSignedCollar_C2a T S i).source = signedCollarSource := by
  change _ ∩ signedCollarSource = signedCollarSource
  refine inter_eq_right.mpr ?_
  intro p hp
  have h1 : -1 < p.2 := hp.1
  have h2 : p ∈ ((heightTranslate_C2a S).toPartialDiffeomorph.trans interiorLift_CPA2).source := by
    refine ⟨trivial, ?_⟩
    change (heightTranslate_C2a S p) ∈ interiorLift_CPA2.source
    rw [interiorLift_source_CPA2]
    exact ⟨trivial, show (0 : ℝ) < p.2 + S by linarith⟩
  refine ⟨h2, ?_⟩
  change interiorLift_CPA2 (heightTranslate_C2a S p) ∈ (cuspChart_CPA2 T i).source
  rw [cuspChart_source_CPA2]
  change 0 < (halfSpaceOneLift (p.2 + S)).val 0
  exact lift_height_pos_CPA2 (by linarith)

/-- On the torus itself the signed collar is the level-`S` cusp torus, i.e. the cut torus of
`truncationAtLevel_C1 T hS`. -/
theorem levelSignedCollar_zero_C2a {S : ℝ} (hS : 2 ≤ S) (i : Fin T.count) (x : Torus) :
    levelSignedCollar_C2a T S i (x, 0) = (truncationAtLevel_C1 T hS).cuspMap i (x, halfZero) := by
  rw [levelSignedCollar_apply_C2a, truncationAtLevel_cusp_zero_C1 T hS, zero_add]

/-- Positive side lies in the cusp beyond the new truncation level. -/
theorem levelSignedCollar_pos_C2a {S : ℝ} (hS : 2 ≤ S) (i : Fin T.count) (x : Torus) (s : ℝ)
    (hs : 0 ≤ s) :
    levelSignedCollar_C2a T S i (x, s) =
      (truncationAtLevel_C1 T hS).cuspMap i (x, halfPoint s hs) := by
  rw [levelSignedCollar_apply_C2a, truncationAtLevel_cuspMap_C1 T hS]
  rfl

theorem levelSignedCollar_target_subset_C2a {S : ℝ} (i : Fin T.count) :
    (levelSignedCollar_C2a T S i).target ⊆ range (T.cuspMap i) := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ (levelSignedCollar_C2a T S i).source, levelSignedCollar_C2a T S i p = y :=
    ⟨(levelSignedCollar_C2a T S i).symm y, (levelSignedCollar_C2a T S i).map_target hy,
      (levelSignedCollar_C2a T S i).right_inv hy⟩
  rw [levelSignedCollar_apply_C2a]
  exact mem_range_self _

theorem levelSignedCollar_disjoint_C2a {S : ℝ} {i j : Fin T.count} (hij : i ≠ j) :
    Disjoint (levelSignedCollar_C2a T S i).target (levelSignedCollar_C2a T S j).target :=
  (T.cusp_disjoint hij).mono (levelSignedCollar_target_subset_C2a T i)
    (levelSignedCollar_target_subset_C2a T j)

/-- The collar of the level-`S` torus stays within heights `< S + 1` of the cusp. -/
theorem levelSignedCollar_height_C2a {S : ℝ} (hS : 2 ≤ S) (i : Fin T.count) {y : H.Carrier}
    (hy : y ∈ (levelSignedCollar_C2a T S i).target) :
    ∃ p : CuspHalfSpace, p.2.val 0 ≤ S + 1 ∧ T.cuspMap i p = y := by
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ (levelSignedCollar_C2a T S i).source, levelSignedCollar_C2a T S i p = y :=
    ⟨(levelSignedCollar_C2a T S i).symm y, (levelSignedCollar_C2a T S i).map_target hy,
      (levelSignedCollar_C2a T S i).right_inv hy⟩
  have hp' : p ∈ signedCollarSource := by
    rwa [levelSignedCollar_source_C2a T hS] at hp
  have h1 : -1 < p.2 := hp'.1
  have h2 : p.2 < 1 := hp'.2
  refine ⟨(p.1, halfSpaceOneLift (p.2 + S)), ?_, (levelSignedCollar_apply_C2a T S i p).symm⟩
  change (halfSpaceOneLift (p.2 + S)).val 0 ≤ S + 1
  rw [lift_height_CPA2 (by linarith)]
  linarith

end GC.LongTime.Ch12
