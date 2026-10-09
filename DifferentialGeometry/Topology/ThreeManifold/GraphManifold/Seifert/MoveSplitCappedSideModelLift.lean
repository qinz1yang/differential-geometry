import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelFamily

/-!
# The lift of the nested circle family to the split charts

Lane N2d, side model, step 4 (lift, generic part). For split charts `C` and a side `t`, the
solid torus coordinates `(ζ, u) ∈ ℂ × S¹` are lifted to `M` by `liftMap C t`: on the meridian
discs of `V` (`‖ζ‖ ≤ 3/2`) it is `C.solid (2 ζ, u ^ e₀)`, and beyond it is
`C.hostMap (hostChart (point (u, ‖ζ‖)), u ^ (e₀ d) · unit(ζ) ^ e₁)` with `point` the nested circle
family `sideData C.host t` in the host chart `w`. Near `‖ζ‖ = 3/2` both read the seam chart
`C.seam ((unit ζ, u ^ e₀), (4 ‖ζ‖ - 6) / 3)`. The lift is a local diffeomorphism on the meridian
discs, near the seam circle and wherever the host point lies in the interior of the pants
(`isLocalDiffeomorphAt_liftMap`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

open GC.GraphManifold

def polarPD : PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓘(ℝ, ℝ).prod (𝓡 1)) ℂ (ℝ × Circle) ∞ where
  toFun ζ := (‖ζ‖, unitOf ζ)
  invFun p := p.1 • (p.2 : ℂ)
  source := {ζ | ζ ≠ 0}
  target := {p | 0 < p.1}
  map_source' ζ hζ := norm_pos_iff.mpr hζ
  map_target' p hp := smul_ne_zero (ne_of_gt hp) (Circle.coe_ne_zero _)
  left_inv' ζ _ := norm_smul_unitOf ζ
  right_inv' p hp := by
    have hp' : (0 : ℝ) < p.1 := hp
    have h1 : ‖p.1 • (p.2 : ℂ)‖ = p.1 := by
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hp'.le]
    simp only [h1, unitOf_smul hp' p.2]
  open_source := isOpen_ne
  open_target := isOpen_lt continuous_const continuous_fst
  contMDiffOn_toFun := by
    refine ContMDiffOn.prodMk ?_ contMDiffOn_unitOf
    intro ζ hζ
    exact (contDiffAt_norm ℝ hζ).contMDiffAt.contMDiffWithinAt
  contMDiffOn_invFun := by
    have h2 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞ (fun p : ℝ × Circle => (p.2 : ℂ)) :=
      contMDiff_circle_coe.comp contMDiff_snd
    exact (contMDiff_fst.smul h2).contMDiffOn

theorem contMDiff_circle_zpow' (k : ℤ) : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun u : Circle => u ^ k) := by
  rcases k with n | n
  · simpa using contMDiff_pow (I := 𝓡 1) (G := Circle) n
  · simpa [zpow_negSucc] using (contMDiff_pow (I := 𝓡 1) (G := Circle) (n + 1)).inv

theorem contMDiff_real_comp' {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f :=
  hf.contMDiff

def circleShear (k e : ℤ) (he : e = 1 ∨ e = -1) :
    ((Circle × ℝ) × Circle) ≃ₘ⟮((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1),
      ((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1)⟯ ((Circle × ℝ) × Circle) where
  toFun q := (q.1, q.1.1 ^ k * q.2 ^ e)
  invFun q := (q.1, (q.2 * (q.1.1 ^ k)⁻¹) ^ e)
  left_inv q := by
    simp only [mul_inv_cancel_comm, zpow_zpow_unit he]
  right_inv q := by
    simp only [zpow_zpow_unit he]
    rw [mul_comm, inv_mul_cancel_right]
  contMDiff_toFun := by
    have hk : ContMDiff (((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1)) (𝓡 1) ∞
        (fun q : (Circle × ℝ) × Circle => q.1.1 ^ k) :=
      (contMDiff_circle_zpow' k).comp (contMDiff_fst.comp contMDiff_fst)
    exact contMDiff_fst.prodMk (hk.mul ((contMDiff_circle_zpow he).comp contMDiff_snd))
  contMDiff_invFun := by
    have hk : ContMDiff (((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1)) (𝓡 1) ∞
        (fun q : (Circle × ℝ) × Circle => q.1.1 ^ k) :=
      (contMDiff_circle_zpow' k).comp (contMDiff_fst.comp contMDiff_fst)
    exact contMDiff_fst.prodMk ((contMDiff_circle_zpow he).comp (contMDiff_snd.mul hk.inv))

def polarSwap :
    ((ℝ × Circle) × Circle) ≃ₘ⟮((𝓘(ℝ, ℝ)).prod (𝓡 1)).prod (𝓡 1),
      ((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1)⟯ ((Circle × ℝ) × Circle) where
  toFun q := ((q.2, q.1.1), q.1.2)
  invFun q := ((q.1.2, q.2), q.1.1)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (contMDiff_snd.prodMk (contMDiff_fst.comp contMDiff_fst)).prodMk
    (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun := ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
    (contMDiff_fst.comp contMDiff_fst)

def circleZpowDiffeo (e : ℤ) (he : e = 1 ∨ e = -1) : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun u := u ^ e
  invFun u := u ^ e
  left_inv u := zpow_zpow_unit he u
  right_inv u := zpow_zpow_unit he u
  contMDiff_toFun := contMDiff_circle_zpow he
  contMDiff_invFun := contMDiff_circle_zpow he

def seamPolar (e : ℤ) (he : e = 1 ∨ e = -1) :
    ((ℝ × Circle) × Circle) ≃ₘ⟮((𝓘(ℝ, ℝ)).prod (𝓡 1)).prod (𝓡 1),
      GC.Endpoint.signedCollarModel⟯ (GC.Endpoint.Torus × ℝ) where
  toFun q := ((q.1.2, q.2 ^ e), (4 * q.1.1 - 6) / 3)
  invFun q := (((3 * q.2 + 6) / 4, q.1.1), q.1.2 ^ e)
  left_inv q := by
    simp only [zpow_zpow_unit he]
    congr 2
    ring
  right_inv q := by
    simp only [zpow_zpow_unit he]
    congr 1
    ring
  contMDiff_toFun := by
    refine ((contMDiff_snd.comp contMDiff_fst).prodMk
      ((contMDiff_circle_zpow he).comp contMDiff_snd)).prodMk ?_
    exact (contMDiff_real_comp' ((contDiff_const.mul contDiff_id).sub contDiff_const |>.div_const
      3)).comp (contMDiff_fst.comp contMDiff_fst)
  contMDiff_invFun := by
    refine ContMDiff.prodMk (ContMDiff.prodMk ?_ (contMDiff_fst.comp contMDiff_fst))
      ((contMDiff_circle_zpow he).comp (contMDiff_snd.comp contMDiff_fst))
    exact (((contDiff_const.mul contDiff_id).add contDiff_const).div_const 4).contMDiff.comp
      contMDiff_snd

namespace SplitCharts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  (C : SplitCharts M)

def liftV (q : ℂ × Circle) : M := C.solid ((2 : ℝ) • q.1, q.2 ^ C.e₀)

def liftH (t : Bool) (q : ℂ × Circle) : M :=
  C.hostMap (hostChart C.host ((sideData C.host t).point (q.2, ‖q.1‖)),
    q.2 ^ (C.e₀ * C.d) * unitOf q.1 ^ C.e₁)

def liftS (q : ℂ × Circle) : M := C.seam ((unitOf q.1, q.2 ^ C.e₀), (4 * ‖q.1‖ - 6) / 3)

def liftMap (t : Bool) (q : ℂ × Circle) : M := if ‖q.1‖ ≤ 3 / 2 then C.liftV q else C.liftH t q

theorem liftMap_of_le (t : Bool) {q : ℂ × Circle} (h : ‖q.1‖ ≤ 3 / 2) :
    C.liftMap t q = C.liftV q := ite_eq_left h

theorem liftMap_of_gt (t : Bool) {q : ℂ × Circle} (h : 3 / 2 < ‖q.1‖) :
    C.liftMap t q = C.liftH t q := ite_eq_right (not_le.mpr h)

theorem liftS_eq_liftV {q : ℂ × Circle} (h : ‖q.1‖ < 3 / 2) (hδ : -C.δ < (4 * ‖q.1‖ - 6) / 3) :
    C.liftS q = C.liftV q := by
  unfold liftS liftV
  rw [C.seam_neg _ _ hδ (by linarith)]
  have e : (3 + 3 * ((4 * ‖q.1‖ - 6) / 3) / 2 : ℝ) • (unitOf q.1 : ℂ) = (2 : ℝ) • q.1 := by
    rw [show (3 + 3 * ((4 * ‖q.1‖ - 6) / 3) / 2 : ℝ) = 2 * ‖q.1‖ by ring, mul_smul,
      norm_smul_unitOf]
  rw [e]

theorem liftS_eq_liftV_of_eq (hseam0 : ∀ τ : GC.Endpoint.Torus,
    C.seam (τ, 0) = C.solid ((3 : ℝ) • (τ.1 : ℂ), τ.2)) {q : ℂ × Circle} (h : ‖q.1‖ = 3 / 2) :
    C.liftS q = C.liftV q := by
  unfold liftS liftV
  rw [h, show (4 * (3 / 2 : ℝ) - 6) / 3 = 0 by norm_num, hseam0]
  have e : (3 : ℝ) • (unitOf q.1 : ℂ) = (2 : ℝ) • q.1 := by
    rw [← norm_smul_unitOf q.1, h, smul_smul, unitOf_smul (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  rw [e]

theorem hostChart_point_of_le (t : Bool) {u : Circle} {ρ : ℝ} (h1 : 1 ≤ ρ) (h2 : ρ ≤ 2) :
    hostChart C.host ((sideData C.host t).point (u, ρ)) =
      planarCollarFormula 3 C.host ((u : ℂ), (4 * ρ - 6) / 3) := by
  rw [CollarData.point_of_le_two _ h2, vRadius_of_two_le _ (by linarith)]
  rw [← hostChart_collar C.host u (by linarith)]
  congr 2
  ring_nf

theorem liftS_eq_liftH (t : Bool) {q : ℂ × Circle} (h : 3 / 2 < ‖q.1‖)
    (hδ : (4 * ‖q.1‖ - 6) / 3 < C.δ) (h2 : ‖q.1‖ ≤ 2) : C.liftS q = C.liftH t q := by
  unfold liftS liftH
  rw [C.seam_pos _ _ (by linarith) hδ, C.hostChart_point_of_le t (by linarith) h2,
    zpow_zpow_unit C.he₀, ← zpow_mul, mul_comm (unitOf q.1 ^ C.e₁)]

theorem isLocalDiffeomorphAt_liftV {q : ℂ × Circle} (h : ‖q.1‖ < 3 / 2) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ C.liftV q := by
  let L : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.smulOfUnit (Units.mk0 (2 : ℝ) (by norm_num))).toContinuousLinearEquiv
  let A := L.toDiffeomorph.prodCongr (circleZpowDiffeo C.e₀ C.he₀)
  have hA : C.liftV = C.solid ∘ A := rfl
  rw [hA]
  refine (A.isLocalDiffeomorph q).comp _ _ (C.solid_local _ ?_)
  change ‖(2 : ℝ) • q.1‖ < 3
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

theorem isLocalDiffeomorphAt_liftS {q : ℂ × Circle} (h0 : q.1 ≠ 0)
    (hδ : |(4 * ‖q.1‖ - 6) / 3| < C.δ) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ C.liftS q := by
  have h1 : IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (((𝓘(ℝ, ℝ)).prod (𝓡 1)).prod (𝓡 1)) ∞
      (Prod.map polarPD id) q :=
    (polarPD.isLocalDiffeomorphAt _ _ ∞ (show q.1 ∈ polarPD.source from h0)).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph q.2)
  have h2 := h1.comp _ _ ((seamPolar C.e₀ C.he₀).isLocalDiffeomorph _)
  have h3 := h2.comp _ _ (C.seam_local _ hδ)
  exact h3

theorem isLocalDiffeomorphAt_liftH (t : Bool) {q : ℂ × Circle} (h1 : 1 < ‖q.1‖) (h3 : ‖q.1‖ < 3)
    (hint : hostChart C.host ((sideData C.host t).point (q.2, ‖q.1‖)) ∈ pantsInterior)
    (hne : C.host.val ≠ 0 → (sideData C.host t).point (q.2, ‖q.1‖) ≠ 0) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ (C.liftH t) q := by
  have h0 : q.1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have a1 : IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (((𝓘(ℝ, ℝ)).prod (𝓡 1)).prod (𝓡 1)) ∞
      (Prod.map polarPD id) q :=
    (polarPD.isLocalDiffeomorphAt _ _ ∞ (show q.1 ∈ polarPD.source from h0)).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph q.2)
  have a2 := a1.comp _ _ (polarSwap.isLocalDiffeomorph _)
  have a3 := a2.comp _ _ ((circleShear (C.e₀ * C.d) C.e₁ C.he₁).isLocalDiffeomorph _)
  have a4 := a3.comp (𝓘(ℝ, ℂ).prod (𝓡 1)) (ℂ × Circle)
    (((sideData C.host t).isLocalDiffeomorphAt_point (u := q.2) ⟨h1, h3.le⟩ h3).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph _))
  have a5 := a4.comp (𝓘(ℝ, ℂ).prod (𝓡 1)) (ℂ × Circle)
    ((isLocalDiffeomorphAt_hostChart C.host hne).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph _))
  exact a5.comp _ _ (C.host_local _ hint)

theorem isLocalDiffeomorphAt_liftMap (hseam0 : ∀ τ : GC.Endpoint.Torus,
    C.seam (τ, 0) = C.solid ((3 : ℝ) • (τ.1 : ℂ), τ.2)) (t : Bool) {q : ℂ × Circle}
    (h3 : ‖q.1‖ < 3)
    (hH : 3 / 2 < ‖q.1‖ →
      hostChart C.host ((sideData C.host t).point (q.2, ‖q.1‖)) ∈ pantsInterior ∧
        (C.host.val ≠ 0 → (sideData C.host t).point (q.2, ‖q.1‖) ≠ 0)) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ (C.liftMap t) q := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  rcases lt_trichotomy ‖q.1‖ (3 / 2) with hlt | heq | hgt
  · have hU : IsOpen {q : ℂ × Circle | ‖q.1‖ < 3 / 2} := isOpen_lt hcn continuous_const
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (C.isLocalDiffeomorphAt_liftV hlt)
    exact Filter.eventuallyEq_of_mem (hU.mem_nhds hlt) fun q' hq' =>
      C.liftMap_of_le t (le_of_lt hq')
  · have hδ := C.hδ
    have hδ1 := C.hδ1
    let U : Set (ℂ × Circle) := {q | |‖q.1‖ - 3 / 2| < 3 * C.δ / 4}
    have hU : IsOpen U := isOpen_lt (continuous_abs.comp (hcn.sub continuous_const))
      continuous_const
    have hqU : q ∈ U := by
      change |‖q.1‖ - 3 / 2| < 3 * C.δ / 4
      rw [heq, sub_self, abs_zero]
      positivity
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (C.isLocalDiffeomorphAt_liftS
      (norm_pos_iff.mp (by linarith)) (by rw [heq]; norm_num; exact hδ))
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds hqU) fun q' hq' => ?_
    have hq'' := abs_lt.mp (show |‖q'.1‖ - 3 / 2| < 3 * C.δ / 4 from hq')
    rcases lt_trichotomy ‖q'.1‖ (3 / 2) with h1 | h1 | h1
    · rw [C.liftMap_of_le t h1.le, C.liftS_eq_liftV h1 (by linarith)]
    · rw [C.liftMap_of_le t h1.le, C.liftS_eq_liftV_of_eq hseam0 h1]
    · rw [C.liftMap_of_gt t h1, C.liftS_eq_liftH t h1 (by linarith) (by linarith)]
  · have hU : IsOpen {q : ℂ × Circle | 3 / 2 < ‖q.1‖} := isOpen_lt continuous_const hcn
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_
      (C.isLocalDiffeomorphAt_liftH t (by linarith) h3 (hH hgt).1 (hH hgt).2)
    exact Filter.eventuallyEq_of_mem (hU.mem_nhds hgt) fun q' hq' => C.liftMap_of_gt t hq'

end SplitCharts

end GC.Seifert.SplitTube
