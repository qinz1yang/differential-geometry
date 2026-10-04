import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataGerm
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn

/-!
Actual normal profiles and native bounded host collars for the fibre-plug solid models.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

def boundedPlugCapProfile (r : ℝ) : ℝ :=
  r - (2 - r) * (1 - seamCut (r - 1))

theorem boundedPlugCapProfile_smooth : ContDiff ℝ ∞ boundedPlugCapProfile :=
  contDiff_id.sub ((contDiff_const.sub contDiff_id).mul
    (contDiff_const.sub (contDiff_seamCut.comp (contDiff_id.sub contDiff_const))))

theorem boundedPlugCapProfile_inner {r : ℝ} (hr : r ≤ 5 / 4) :
    boundedPlugCapProfile r = 2 * r - 2 := by
  rw [boundedPlugCapProfile, seamCut_of_le (show r - 1 ≤ 1 / 4 by linarith)]
  ring

theorem boundedPlugCapProfile_outer {r : ℝ} (hr : 3 / 2 ≤ r) :
    boundedPlugCapProfile r = r := by
  rw [boundedPlugCapProfile, seamCut_of_ge (show 1 / 2 ≤ r - 1 by linarith)]
  ring

theorem boundedPlugCapProfile_hasDerivAt (r : ℝ) :
    HasDerivAt boundedPlugCapProfile
      (2 - seamCut (r - 1) + (2 - r) * deriv seamCut (r - 1)) r := by
  have hc0 : HasDerivAt seamCut (deriv seamCut (r - 1)) (r - 1) :=
    (contDiff_seamCut.differentiable (by simp)).differentiableAt.hasDerivAt
  have hc := hc0.comp r ((hasDerivAt_id r).sub_const 1)
  have h := (hasDerivAt_id r).sub (((hasDerivAt_const r 2).sub (hasDerivAt_id r)).mul
    ((hasDerivAt_const r 1).sub hc))
  convert h using 1
  · ext x
    dsimp [boundedPlugCapProfile]
  · dsimp
    ring

theorem boundedPlugCapProfile_deriv_pos (r : ℝ) :
    0 < deriv boundedPlugCapProfile r := by
  rw [(boundedPlugCapProfile_hasDerivAt r).deriv]
  have hc1 : seamCut (r - 1) ≤ 1 := Real.smoothTransition.le_one _
  have hd0 : 0 ≤ deriv seamCut (r - 1) :=
    (show Monotone seamCut from fun x y hxy =>
      Real.smoothTransition.monotone (by linarith)).deriv_nonneg
  by_cases hr : r ≤ 3 / 2
  · have hm : 0 ≤ (2 - r) * deriv seamCut (r - 1) :=
      mul_nonneg (by linarith) hd0
    linarith
  · have he : seamCut =ᶠ[𝓝 (r - 1)] fun x => (1 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds
        (show 1 / 2 < r - 1 by linarith [not_le.mp hr])] with x hx
      exact seamCut_of_ge hx.le
    have hd : deriv seamCut (r - 1) = 0 := by rw [he.deriv_eq, deriv_const]
    rw [hd]
    linarith

theorem boundedPlugCapProfile_strictMono : StrictMono boundedPlugCapProfile :=
  strictMono_of_deriv_pos boundedPlugCapProfile_deriv_pos

theorem boundedPlugCapProfile_surjective : Function.Surjective boundedPlugCapProfile := by
  intro y
  let a := min ((y + 2) / 2) 1
  let b := max y 2
  have ha1 : a ≤ 1 := min_le_right _ _
  have hay : a ≤ (y + 2) / 2 := min_le_left _ _
  have hb2 : 2 ≤ b := le_max_right _ _
  have hby : y ≤ b := le_max_left _ _
  have hab : a ≤ b := by linarith
  have hleft : boundedPlugCapProfile a ≤ y := by
    rw [boundedPlugCapProfile_inner (by linarith)]
    linarith
  have hright : y ≤ boundedPlugCapProfile b := by
    rw [boundedPlugCapProfile_outer (by linarith)]
    exact hby
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc hab
    boundedPlugCapProfile_smooth.continuous.continuousOn ⟨hleft, hright⟩
  exact ⟨x, he⟩

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapProfile_local (r : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) ∞ boundedPlugCapProfile r := by
  let L : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.smulOfUnit (Units.mk0 (deriv boundedPlugCapProfile r)
      (ne_of_gt (boundedPlugCapProfile_deriv_pos r)))).toContinuousLinearEquiv
  apply isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    boundedPlugCapProfile boundedPlugCapProfile_smooth.contDiffOn.contMDiffOn
    isOpen_univ r (mem_univ r) L
  change HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) boundedPlugCapProfile r
    (deriv boundedPlugCapProfile r • ContinuousLinearMap.id ℝ ℝ)
  have h := (boundedPlugCapProfile_hasDerivAt r).hasFDerivAt.hasMFDerivAt
  have he : ContinuousLinearMap.toSpanSingleton ℝ (deriv boundedPlugCapProfile r) =
      deriv boundedPlugCapProfile r • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    simp [mul_comm]
  rw [← he]
  simpa only [(boundedPlugCapProfile_hasDerivAt r).deriv] using h

def boundedPlugCapProfileDiffeomorph : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ :=
  (show IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ∞ boundedPlugCapProfile from
    boundedPlugCapProfile_local).diffeomorphOfBijective
    ⟨boundedPlugCapProfile_strictMono.injective, boundedPlugCapProfile_surjective⟩

theorem boundedPlugCapProfileDiffeomorph_apply (r : ℝ) :
    boundedPlugCapProfileDiffeomorph r = boundedPlugCapProfile r := rfl

end GC.GraphManifold

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

def boundedModelHostPoint (z : ℂ) (ν : Circle) : E.toTorus.cutCarrier.Carrier :=
  ((E.splitData h).ΘH (clampPants z, ν)).val

theorem boundedModelHostPoint_collar (l : Fin 3) (θ ν : Circle) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) (hδ : s < (E.splitData h).δ) :
    E.boundedModelHostPoint h (planarCollarFormula 3 l ((θ : ℂ), s)) ν =
      E.toTorus.sideCollar (E.standardPort (E.hostPiece j b) h.2.1 l).val
        ((θ, ν), halfPoint s hs) := by
  have hp : ((θ, ν), halfPoint s hs) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.hostPiece j b)
    (E.standardPort (E.hostPiece j b) h.2.1 l) hp
  have e2 := (E.splitData h).hH l ((θ, ν), halfPoint s hs) hp hδ
  rw [← e1, e2]
  change ((E.splitData h).ΘH
    (clampPants (planarCollarFormula 3 l ((θ : ℂ), s)), ν)).val =
    ((E.splitData h).ΘH (pantsPlanarBase.{u}.collar l (θ, halfPoint s hs), ν)).val
  rw [pantsCollar_eq l hs hs1]

theorem boundedModelHostPoint_holonomy (l : Fin 3) (k e : ℤ)
    (he : e = 1 ∨ e = -1) (p : Torus) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) (hδ : s < (E.splitData h).δ) :
    E.toTorus.cutMap (E.boundedModelHostPoint h
      (planarCollarFormula 3 l (((germHol k e he p).1 : ℂ), s))
      (germHol k e he p).2) =
      E.toTorus.cutMap (E.toTorus.sideCollar
        (E.standardPort (E.hostPiece j b) h.2.1 l).val
        (germHol k e he p, halfPoint s hs)) := by
  rw [E.boundedModelHostPoint_collar h l _ _ hs hs1 hδ]

theorem boundedSolidHolonomy_meridian (k e : ℤ) (he : e = 1 ∨ e = -1) (a : Circle) :
    germHol k e he (a, 1) = (1, a ^ e) := by
  rw [germHol_apply]
  simp

theorem boundedSolidHolonomy_fibre (k e : ℤ) (he : e = 1 ∨ e = -1) (a : Circle) :
    germHol k e he (1, a) = (a⁻¹, a ^ k) := by
  rw [germHol_apply]
  simp

theorem boundedSolidHolonomy_canonical (p : Torus) :
    germHol 0 1 (Or.inl rfl) p = (p.2⁻¹, p.1) := by
  rw [germHol_apply]
  simp

end GC.Seifert.ElementaryPresentation
