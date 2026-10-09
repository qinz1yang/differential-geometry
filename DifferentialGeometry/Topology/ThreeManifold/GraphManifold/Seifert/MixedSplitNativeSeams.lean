import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitNativeSides

/-!
# Seam charts of the native mixed split system

Lane MS, tier MS4 (design `handoffs/20261004-design-ms-mixed-split.md` §3.3). The chart of a
surviving seam `c ≠ j` is the seam of the fixed presentation read through the core:
`capSeam c = coreMap K ∘ (capTorus D hC).seam c` on `signedCollarSource` (identity (I1) of the
design: the old seam at `(sideTwist D c true t, δ₂ s)`). It lies in the interior of the core by
the capping conditions, so it is a partial diffeomorphism (`capSeam`, `capSeam_apply`). Its two
halves read the native collars of `capSide c true` and `capSide c false` with the fixed matching
(`capSeam_neg`, `capSeam_pos`): through Lane BA's seam formulas of the cut system on passive
sides, through `solid_collar_eq_fixed` (I3) on host ports.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {S : σ.SplitData h}
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N T} {a : T.Index} {δ₂ : ℝ}
  (D : σ.SideData S K a δ₂) (hC : σ.CappedConditions S a δ₂)

def capSeamFun (c : CapSeam σ j) (p : Torus × ℝ) : N.Carrier :=
  SplitTube.coreMap K ((capTorus D hC).seam c.1 p)

theorem capSeam_core (c : CapSeam σ j) {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    (capTorus D hC).seam c.1 p ∈ T.core ∧
      ∀ b' z, T.boundarySphere b' z ≠ (capTorus D hC).seam c.1 p := by
  have hp' : |p.2| < 1 := abs_lt.mpr ⟨hp.1, hp.2⟩
  have hδ := hC.pos
  have hlt : |δ₂ * p.2| < δ₂ := by
    rw [abs_mul, abs_of_pos hδ]
    nlinarith [abs_nonneg p.2]
  rw [fixedCapPresentation_seam]
  exact hC.seam c.1 c.2 _ _ hlt

theorem isLocalDiffeomorphOn_capSeamFun (c : CapSeam σ j) :
    IsLocalDiffeomorphOn signedCollarModel (𝓡 3) ∞ (capSeamFun D hC c) signedCollarSource := by
  intro x
  obtain ⟨hcore, hne⟩ := capSeam_core D hC c x.2
  have hsrc : (x : Torus × ℝ) ∈ ((capTorus D hC).seam c.1).source :=
    (Set.ext_iff.mp ((capTorus D hC).seam_source c.1) x).mpr x.2
  have hs := ((capTorus D hC).seam c.1).isLocalDiffeomorphAt _ _ ∞ hsrc
  have hcm := SplitTube.isLocalDiffeomorphAt_coreMap K ⟨_, hcore⟩
    (SplitTube.isInteriorPoint_of_forall_ne K ⟨_, hcore⟩ hne)
  exact hs.comp _ _ hcm

theorem injOn_capSeamFun (c : CapSeam σ j) : InjOn (capSeamFun D hC c) signedCollarSource := by
  intro p hp p' hp' he
  have h1 := SplitTube.coreMap_injOn K (capSeam_core D hC c hp).1 (capSeam_core D hC c hp').1 he
  have hs : ∀ {q : Torus × ℝ}, q ∈ signedCollarSource → q ∈ ((capTorus D hC).seam c.1).source :=
    fun hq => (Set.ext_iff.mp ((capTorus D hC).seam_source c.1) _).mpr hq
  exact ((capTorus D hC).seam c.1).toPartialEquiv.injOn (hs hp) (hs hp') h1

theorem exists_capSeam (c : CapSeam σ j) :
    ∃ Φ : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N.Carrier ∞,
      Φ.source = signedCollarSource ∧ Φ.target = capSeamFun D hC c '' signedCollarSource ∧
        (Φ : Torus × ℝ → N.Carrier) = capSeamFun D hC c :=
  (isLocalDiffeomorphOn_capSeamFun D hC c).exists_partialDiffeomorph_of_injOn
    signedCollarSource_isOpen ⟨((1 : Torus), 0), by constructor <;> norm_num⟩
    (injOn_capSeamFun D hC c)

def capSeam (c : CapSeam σ j) :
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N.Carrier ∞ :=
  (exists_capSeam D hC c).choose

theorem capSeam_source (c : CapSeam σ j) : (capSeam D hC c).source = signedCollarSource :=
  (exists_capSeam D hC c).choose_spec.1

theorem capSeam_apply (c : CapSeam σ j) (p : Torus × ℝ) :
    capSeam D hC c p = capSeamFun D hC c p :=
  congrFun (exists_capSeam D hC c).choose_spec.2.2 p

def capMatching (c : CapSeam σ j) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (capTorus D hC).pairing.matching c.1

theorem capSeam_neg (c : CapSeam σ j) (t : Torus) (s : ℝ) (hs : s ≤ 0) (h1 : -1 < s) :
    capSeam D hC c (t, s) = capMap D hC (capSide D hC c true).1
      (capCollar D hC _ (capSide D hC c true).2 (t, halfPoint (-s) (neg_nonneg.2 hs))) := by
  rw [capSeam_apply]
  have hs1 : -s < 1 := by linarith
  by_cases hH : σ.seamPiece c.1 true = σ.hostPiece j b
  · rw [capSide_of_host D hC c hH]
    change _ = D.solid (D.solidOf (σ.hostPortOf h hH)) (discTheta.symm (discTheta
      ((discPlanarBase.{u} 1).collar 0 (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)))
    rw [Diffeomorph.symm_apply_apply, solid_collar_eq_fixed D hC.pos hC.le_one c.2 hH t
      (neg_nonneg.2 hs) hs1 hC.lt_split]
    change SplitTube.coreMap K ((capTorus D hC).seam c.1 (t, s)) =
      SplitTube.coreMap K ((capTorus D hC).cutMap ((capTorus D hC).pairing.leftCollar c.1
        (t, halfPoint (-s) (neg_nonneg.2 hs))))
    rw [(capTorus D hC).cutMap_leftCollar c.1 (p := (t, halfPoint (-s) (neg_nonneg.2 hs))) hs1]
    congr 3
    change s = -(-s)
    ring
  · rw [capSide_of_not_host D hC c hH]
    exact congrArg (SplitTube.coreMap K) ((capCut D hC).seam_neg c.1 t s hs h1)

theorem capSeam_pos (c : CapSeam σ j) (t : Torus) (s : ℝ) (hs : 0 ≤ s) (h1 : s < 1) :
    capSeam D hC c (t, s) = capMap D hC (capSide D hC c false).1
      (capCollar D hC _ (capSide D hC c false).2 (capMatching D hC c t, halfPoint s hs)) := by
  rw [capSeam_apply]
  by_cases hH : σ.seamPiece c.1 false = σ.hostPiece j b
  · rw [capSide_of_host D hC c hH]
    change _ = D.solid (D.solidOf (σ.hostPortOf h hH)) (discTheta.symm (discTheta
      ((discPlanarBase.{u} 1).collar 0 ((capMatching D hC c t).1, halfPoint s hs),
        (capMatching D hC c t).2)))
    rw [Diffeomorph.symm_apply_apply, solid_collar_eq_fixed D hC.pos hC.le_one c.2 hH _ hs h1
      hC.lt_split]
    change SplitTube.coreMap K ((capTorus D hC).seam c.1 (t, s)) =
      SplitTube.coreMap K ((capTorus D hC).cutMap ((capTorus D hC).pairing.rightCollar c.1
        ((capTorus D hC).pairing.matching c.1 t, halfPoint s hs)))
    rw [(capTorus D hC).cutMap_rightCollar c.1
      (p := ((capTorus D hC).pairing.matching c.1 t, halfPoint s hs)) h1,
      Diffeomorph.symm_apply_apply]
    rfl
  · rw [capSide_of_not_host D hC c hH]
    exact congrArg (SplitTube.coreMap K) ((capCut D hC).seam_pos c.1 t s hs h1)

end GC.Seifert.RelativeNormalization.MixedStage
