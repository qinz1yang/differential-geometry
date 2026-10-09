import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ConnectedSumFold
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product

/-!
Actual radial factor formulas supply the full smooth local collar of the same connected-sum fold.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private abbrev Sphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev CollarModel := (𝓡 2).prod 𝓘(ℝ, ℝ)

variable (M N Q : ConnectedClosedOrientedManifold.{u} 3)
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)
  (fL : c.toBallChart.Punctured → Q.Carrier) (fR : d.toBallChart.Punctured → Q.Carrier)

private theorem foldCollar_local_left
    (hsL : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fL ∘ c.toBallChart.interiorToPunctured))
    (p : ConnectedSumQuotient.CollarDomain) (hp : 0 < (p.2 : ℝ)) :
    IsLocalDiffeomorphAt CollarModel (𝓡 3) ∞
      (connectedSumFoldCollar M N Q c d a fL fR) p := by
  let S := smoothConnectedSum M N c d a
  let := S.charts
  let x : c.toBallChart.interior :=
    ⟨c.toBallChart.radialMap p.1 (1 + (p.2 : ℝ))
      ⟨by linarith, by linarith [p.2.2.2]⟩,
      ConnectedSumQuotient.radialMap_mem_interior _ _ (by linarith)⟩
  have he : ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p =
      ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x := by
    rw [ConnectedSumQuotient.collarMap_of_nonneg _ _ _ _ hp.le]
    rfl
  let hi := S.interiorLeft_localDiffeomorph x
  have hc := S.collar_localDiffeomorph p
  have hv : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hi.localInverse
      (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p) := by
    rw [he]
    exact hi.localInverse_isLocalDiffeomorphAt
  have hcomp := (hc.comp (𝓡 3) _ hv).comp (𝓡 3) Q.Carrier
    (hsL (hi.localInverse (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p)))
  apply IsLocalDiffeomorphAt.of_eventuallyEq ?_ hcomp
  have hinv := hi.localInverse_eventuallyEq_right
  rw [← he] at hinv
  have hnear := hinv.comp_tendsto hc.contMDiffAt.continuousAt.tendsto
  have hpos : ∀ᶠ y : ConnectedSumQuotient.CollarDomain in 𝓝 p, 0 < (y.2 : ℝ) :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).mem_nhds hp
  filter_upwards [hnear, hpos] with y hy hyt
  let xy : c.toBallChart.interior :=
    ⟨c.toBallChart.radialMap y.1 (1 + (y.2 : ℝ))
      ⟨by linarith, by linarith [y.2.2.2]⟩,
      ConnectedSumQuotient.radialMap_mem_interior _ _ (by linarith)⟩
  have hyc : ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 y =
      ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 xy := by
    rw [ConnectedSumQuotient.collarMap_of_nonneg _ _ _ _ hyt.le]
    rfl
  have hxy : hi.localInverse (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart
      a.1 y) = xy := ConnectedSumQuotient.interiorLeft_injective _ _ _ (hy.trans hyc)
  change connectedSumFoldCollar M N Q c d a fL fR y =
    fL (c.toBallChart.interiorToPunctured (hi.localInverse
      (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 y)))
  rw [hxy]
  simp only [connectedSumFoldCollar, dite_eq_left hyt.le]
  rfl

private theorem foldCollar_local_right
    (hsR : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fR ∘ d.toBallChart.interiorToPunctured))
    (p : ConnectedSumQuotient.CollarDomain) (hp : (p.2 : ℝ) < 0) :
    IsLocalDiffeomorphAt CollarModel (𝓡 3) ∞
      (connectedSumFoldCollar M N Q c d a fL fR) p := by
  let S := smoothConnectedSum M N c d a
  let := S.charts
  let x : d.toBallChart.interior :=
    ⟨d.toBallChart.radialMap (a.1 p.1) (1 - (p.2 : ℝ))
      ⟨by linarith, by linarith [p.2.2.1]⟩,
      ConnectedSumQuotient.radialMap_mem_interior _ _ (by linarith)⟩
  have he : ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p =
      ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x := by
    rw [ConnectedSumQuotient.collarMap_of_neg _ _ _ _ hp]
    rfl
  let hi := S.interiorRight_localDiffeomorph x
  have hc := S.collar_localDiffeomorph p
  have hv : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hi.localInverse
      (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p) := by
    rw [he]
    exact hi.localInverse_isLocalDiffeomorphAt
  have hcomp := (hc.comp (𝓡 3) _ hv).comp (𝓡 3) Q.Carrier
    (hsR (hi.localInverse (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p)))
  apply IsLocalDiffeomorphAt.of_eventuallyEq ?_ hcomp
  have hinv := hi.localInverse_eventuallyEq_right
  rw [← he] at hinv
  have hnear := hinv.comp_tendsto hc.contMDiffAt.continuousAt.tendsto
  have hneg : ∀ᶠ y : ConnectedSumQuotient.CollarDomain in 𝓝 p, (y.2 : ℝ) < 0 :=
    (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const).mem_nhds hp
  filter_upwards [hnear, hneg] with y hy hyt
  let xy : d.toBallChart.interior :=
    ⟨d.toBallChart.radialMap (a.1 y.1) (1 - (y.2 : ℝ))
      ⟨by linarith, by linarith [y.2.2.1]⟩,
      ConnectedSumQuotient.radialMap_mem_interior _ _ (by linarith)⟩
  have hyc : ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 y =
      ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 xy := by
    rw [ConnectedSumQuotient.collarMap_of_neg _ _ _ _ hyt]
    rfl
  have hxy : hi.localInverse (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart
      a.1 y) = xy := ConnectedSumQuotient.interiorRight_injective _ _ _ (hy.trans hyc)
  change connectedSumFoldCollar M N Q c d a fL fR y =
    fR (d.toBallChart.interiorToPunctured (hi.localInverse
      (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 y)))
  rw [hxy]
  simp only [connectedSumFoldCollar, dite_eq_right (not_le.mpr hyt)]
  rfl

variable
  (q : PartialDiffeomorph CollarModel (𝓡 3) (Sphere × ℝ) Q.Carrier ∞)
  (aL aR : Sphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere)
  (hangle : ∀ z : Sphere, aR (a.1 z) = aL z)
  (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
  (hq : ∀ z : Sphere, ∀ s : ℝ, |s| < 2 * δ → (z, s) ∈ q.source)
  (hL : ∀ (z : Sphere) (s : ℝ) (hs : 0 ≤ s) (hlt : s < δ),
    fL (c.toBallChart.radialMap z (1 + s)
      ⟨by linarith, by linarith⟩) = q (aL z, 2 * s))
  (hR : ∀ (z : Sphere) (s : ℝ) (hs : 0 ≤ s) (hlt : s < δ),
    fR (d.toBallChart.radialMap z (1 + s)
      ⟨by linarith, by linarith⟩) = q (aR z, -(2 * s)))
  (hsL : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (fL ∘ c.toBallChart.interiorToPunctured))
  (hsR : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (fR ∘ d.toBallChart.interiorToPunctured))

include hangle hδ hq hL hR hsL hsR in
theorem connectedSumFoldCollar_isLocalDiffeomorph :
    IsLocalDiffeomorph CollarModel (𝓡 3) ∞
      (connectedSumFoldCollar M N Q c d a fL fR) := by
  intro p
  by_cases hp : (p.2 : ℝ) = 0
  · let A := (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
      (Units.mk0 (2 : ℝ) (by norm_num))).toDiffeomorph
    have hv := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := 𝓘(ℝ, ℝ))
      ConnectedSumQuotient.collarInterval p.2
    have ht := hv.comp 𝓘(ℝ, ℝ) ℝ (A.isLocalDiffeomorph (p.2 : ℝ))
    have hparam := (aL.isLocalDiffeomorph p.1).prodMap ht
    have hsrc : (aL p.1, 2 * (p.2 : ℝ)) ∈ q.source := by
      apply hq
      simpa only [hp, mul_zero, abs_zero] using (mul_pos (by norm_num : (0 : ℝ) < 2) hδ)
    have hlocal := hparam.comp (𝓡 3) Q.Carrier (q.isLocalDiffeomorphAt _ _ ∞ hsrc)
    apply IsLocalDiffeomorphAt.of_eventuallyEq ?_ hlocal
    have hsmall : ∀ᶠ y : ConnectedSumQuotient.CollarDomain in 𝓝 p, |(y.2 : ℝ)| < δ :=
      (isOpen_lt (continuous_subtype_val.comp continuous_snd).abs continuous_const).mem_nhds
        (by change |(p.2 : ℝ)| < δ; simpa only [hp, abs_zero] using hδ)
    filter_upwards [hsmall] with y hy
    change connectedSumFoldCollar M N Q c d a fL fR y = q (aL y.1, 2 * (y.2 : ℝ))
    by_cases ht : 0 ≤ (y.2 : ℝ)
    · simp only [connectedSumFoldCollar, dite_eq_left ht]
      exact hL y.1 (y.2 : ℝ) ht ((le_abs_self _).trans_lt hy)
    · have hneg : (y.2 : ℝ) < 0 := lt_of_not_ge ht
      simp only [connectedSumFoldCollar, dite_eq_right ht]
      have h := hR (a.1 y.1) (-(y.2 : ℝ)) (by linarith)
        (by rw [abs_of_neg hneg] at hy; exact hy)
      simpa only [sub_eq_add_neg, hangle, mul_neg, neg_neg] using h
  · rcases lt_or_gt_of_ne hp with hneg | hpos
    · exact foldCollar_local_right M N Q c d a fL fR hsR p hneg
    · exact foldCollar_local_left M N Q c d a fL fR hsL p hpos

end GC.GraphManifold
