import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryCollar

/-!
# CH12-S34 G1: the thin (right) collar of a cut torus, lifted to the cut carrier

For a collared torus family `F` on `M`, a torus `i` and a map `φ : CuspHalfSpace → M` agreeing with the
signed collar `F.collar i` for heights `< 1` and avoiding all closed slabs `σ_j(T² × [-7/8, 7/8])` for
heights `≥ 1` (inside `cuspDomain`), the map
`L(t,z) = σ_i(t, ψ z)` (`z < 1`) , `φ(t,z)` (`z ≥ 1`) is a smooth map `cuspDomain → K = cutCarrier_C2a F`
with `rmapK ∘ L = φ` on `cuspDomain`; its height-zero slice is the right side torus of `σ_i`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff

universe u

namespace GC.LongTime.Ch12

section RightLift

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)
  (i : Fin F.count) (φ : CuspHalfSpace → M.Carrier)

theorem tubeOpen_subset_slab_S34 (j : Fin F.count) :
    tubeOpen_C2a F j ⊆ F.collar j '' (univ ×ˢ Icc (-7 / 8 : ℝ) (7 / 8)) :=
  image_mono (prod_mono (subset_refl _) (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩))

theorem mem_cutSet_of_out_S34
    (hout : ∀ p ∈ cuspDomain, 1 ≤ p.2.val 0 →
      ∀ j, φ p ∉ F.collar j '' (univ ×ˢ Icc (-7 / 8 : ℝ) (7 / 8))) :
    ∀ p ∈ cuspDomain, 1 ≤ p.2.val 0 → φ p ∈ cutSet_C2a F := by
  intro p hp h1 hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  exact hout p hp h1 j (tubeOpen_subset_slab_S34 F j hj)

/-- A point of the cut set as a point of the cut carrier. -/
def liftPt_S34 (x : M.Carrier) (hx : x ∈ cutSet_C2a F) : (cutCarrier_C2a F).Carrier := ⟨x, hx⟩

theorem liftPt_val_S34 (x : M.Carrier) (hx : x ∈ cutSet_C2a F) : (liftPt_S34 F x hx).1 = x := rfl

variable (hmem : ∀ p ∈ cuspDomain, 1 ≤ p.2.val 0 → φ p ∈ cutSet_C2a F)

/-- The lift `L` of the thin collar. -/
def rightLift_S34 : CuspHalfSpace → (cutCarrier_C2a F).Carrier := fun p =>
  open Classical in
  if h : 1 ≤ p.2.val 0 ∧ p ∈ cuspDomain then liftPt_S34 F (φ p) (hmem p h.2 h.1)
  else sideCollar_S12 F i hR_C2a p

include hmem in
theorem rightLift_of_lt_S34 {p : CuspHalfSpace} (h : p.2.val 0 < 1) :
    rightLift_S34 F i φ hmem p = sideCollar_S12 F i hR_C2a p := by
  unfold rightLift_S34
  exact dite_eq_right (fun h' => absurd h'.1 (not_le.mpr h))

include hmem in
theorem rightLift_val_of_ge_S34 {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (h : 1 ≤ p.2.val 0) :
    (rightLift_S34 F i φ hmem p).1 = φ p := by
  have : rightLift_S34 F i φ hmem p = liftPt_S34 F (φ p) (hmem p hp h) := by
    unfold rightLift_S34; exact dite_eq_left ⟨h, hp⟩
  rw [this]; rfl

include hmem in
theorem rightLift_val_S34
    (hcol : ∀ p : CuspHalfSpace, p.2.val 0 < 1 → φ p = F.collar i (p.1, p.2.val 0))
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (h : 7/8 < p.2.val 0) :
    (rightLift_S34 F i φ hmem p).1 = φ p := by
  by_cases h1 : 1 ≤ p.2.val 0
  · exact rightLift_val_of_ge_S34 F i φ hmem hp h1
  · push Not at h1
    rw [rightLift_of_lt_S34 F i φ hmem h1, sideCollar_val_S12 F i hR_C2a h1, hcol p h1,
      one_mul, psi_of_ge_S12 h.le]

include hmem in
theorem rmapK_rightLift_S34
    (hcol : ∀ p : CuspHalfSpace, p.2.val 0 < 1 → φ p = F.collar i (p.1, p.2.val 0))
    (hout : ∀ p ∈ cuspDomain, 1 ≤ p.2.val 0 →
      ∀ j, φ p ∉ F.collar j '' (univ ×ˢ Icc (-7 / 8 : ℝ) (7 / 8)))
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    rmapK_S12 F (rightLift_S34 F i φ hmem p) = φ p := by
  by_cases h1 : 1 ≤ p.2.val 0
  · have hv := rightLift_val_of_ge_S34 F i φ hmem hp h1
    change rmap_S12 (rightLift_S34 F i φ hmem p) = _
    rw [rmap_eq_val_S12 (x := rightLift_S34 F i φ hmem p) (by rw [hv]; exact hout p hp h1), hv]
  · push Not at h1
    rw [rightLift_of_lt_S34 F i φ hmem h1, rmapK_rightCollar_S12 F i h1, hcol p h1]

include hmem in
theorem contMDiffOn_rightLift_S34
    (hcol : ∀ p : CuspHalfSpace, p.2.val 0 < 1 → φ p = F.collar i (p.1, p.2.val 0))
    (hsm : ContMDiffOn halfCollarModel (𝓡 3) ∞ φ cuspDomain) :
    ContMDiffOn halfCollarModel (cutCarrier_C2a F).model ∞
      (rightLift_S34 F i φ hmem) cuspDomain := by
  have hcoord : Continuous (fun p : CuspHalfSpace => p.2.val 0) :=
    (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd :
      ContMDiff halfCollarModel 𝓘(ℝ, ℝ) ∞ (fun p : CuspHalfSpace => p.2.val 0)).continuous
  refine contMDiffOn_of_locally_contMDiffOn fun x hx => ?_
  by_cases h1 : x.2.val 0 < 1
  · refine ⟨{p | p.2.val 0 < 1}, isOpen_lt hcoord continuous_const, h1, ?_⟩
    refine (((sideCollar_S12 F i hR_C2a).contMDiffOn).mono ?_).congr ?_
    · exact fun p hp => hp.2
    · exact fun p hp => rightLift_of_lt_S34 F i φ hmem hp.2
  · push Not at h1
    refine ⟨{p | 7 / 8 < p.2.val 0}, isOpen_lt continuous_const hcoord, (show (7 : ℝ) / 8 < x.2.val 0 by linarith), ?_⟩
    refine ((cutAtlas_C2a F).contMDiffOn_iff_subtype_val _ _).mpr ?_
    refine (hsm.mono inter_subset_left).congr ?_
    exact fun p hp => rightLift_val_S34 F i φ hmem hcol hp.1 hp.2

include hmem in
theorem rightLift_zero_S34 (t : Torus) :
    rightLift_S34 F i φ hmem (t, halfZero) = sideTorus_C2a F i hR_C2a t := by
  rw [rightLift_of_lt_S34 F i φ hmem (p := (t, halfZero)) (by change (0 : ℝ) < 1; norm_num)]
  exact sideCollar_zero_S12 F i hR_C2a t

theorem mem_boundary_of_val_S34 (x : (cutCarrier_C2a F).Carrier) (t : Torus)
    (hx : x.1 = F.collar i (t, 1 / 2)) :
    x ∈ (cutCarrier_C2a F).model.boundary (cutCarrier_C2a F).Carrier :=
  (cutIncl_boundary_iff_C2a F x).mpr ⟨i, Or.inl ⟨t, hx⟩⟩

/-- **G1.** The lift of the thin collar to the cut carrier. -/
theorem exists_rightLift_S34
    (hcol : ∀ p : CuspHalfSpace, p.2.val 0 < 1 → φ p = F.collar i (p.1, p.2.val 0))
    (hout : ∀ p ∈ cuspDomain, 1 ≤ p.2.val 0 →
      ∀ j, φ p ∉ F.collar j '' (univ ×ˢ Icc (-7 / 8 : ℝ) (7 / 8)))
    (hsm : ContMDiffOn halfCollarModel (𝓡 3) ∞ φ cuspDomain) :
    ∃ L : CuspHalfSpace → (cutCarrier_C2a F).Carrier,
      ContMDiffOn halfCollarModel (cutCarrier_C2a F).model ∞ L cuspDomain ∧
      (∀ p ∈ cuspDomain, rmapK_S12 F (L p) = φ p) ∧
      (∀ t, L (t, halfZero) = sideTorus_C2a F i hR_C2a t) ∧
      (∀ t, L (t, halfZero) ∈ (cutCarrier_C2a F).model.boundary (cutCarrier_C2a F).Carrier) := by
  have hmem := mem_cutSet_of_out_S34 F φ hout
  refine ⟨rightLift_S34 F i φ hmem, contMDiffOn_rightLift_S34 F i φ hmem hcol hsm,
    fun p hp => rmapK_rightLift_S34 F i φ hmem hcol hout hp, rightLift_zero_S34 F i φ hmem,
    fun t => ?_⟩
  refine mem_boundary_of_val_S34 F i _ t ?_
  rw [rightLift_zero_S34 F i φ hmem t]
  change F.collar i (t, sideParam_C2a 1 0) = _
  simp [sideParam_C2a]

end RightLift

end GC.LongTime.Ch12
