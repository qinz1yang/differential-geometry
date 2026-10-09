import DifferentialGeometry.Analysis.Elliptic.Planar.NodalArcs
import DifferentialGeometry.Analysis.Calculus.RadialReparametrization.SmoothZeroArc
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Analysis

/-- A continuous real height agrees with its unit rotation somewhere on each
positive complex circle. No finite order or orbit argument is required. -/
theorem exists_eq_unit_rotation_on_sphere
    (H : ℂ → ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r)
    (hH : ContinuousOn H (Metric.sphere (0 : ℂ) r)) :
    ∃ z ∈ Metric.sphere (0 : ℂ) r, H z = H (ζ * z) := by
  have hnonempty : (Metric.sphere (0 : ℂ) r).Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp only [Metric.mem_sphere, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  have hrotate : MapsTo (fun z : ℂ => ζ * z)
      (Metric.sphere (0 : ℂ) r) (Metric.sphere (0 : ℂ) r) := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz ⊢
    rw [norm_mul, hζ, hz, one_mul]
  have hrotcont : ContinuousOn (fun z : ℂ => H (ζ * z))
      (Metric.sphere (0 : ℂ) r) :=
    hH.comp (continuous_const.mul continuous_id).continuousOn hrotate
  obtain ⟨x, hx, hmin⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMinOn hnonempty hH
  obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn hnonempty hH
  have hconnected : IsPreconnected (Metric.sphere (0 : ℂ) r) :=
    _root_.isPreconnected_sphere (by simp [Complex.rank_real_complex]) 0 r
  exact hconnected.intermediate_value₂ hx hy hH hrotcont
    (hmin (hrotate hx)) (hmax (hrotate hy))

private theorem exists_index_of_deck_nodal_cover
    {H : ℂ → ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (e : OpenPartialHomeomorph ℂ ℂ) (he0 : (0 : ℂ) ∈ e.source) (hezero : e 0 = 0)
    (hH : ContinuousOn H e.source) {ρ : ℝ} (hρ : 0 < ρ)
    {S : Set ℝ} {Γ : S → ℝ → ℂ}
    (hcover : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      H (e.symm z) - H (ζ * e.symm z) = 0 ↔
        z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r) :
    Nonempty S := by
  have hnear : e.source ∩ e ⁻¹' Metric.ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := by
    apply inter_mem (e.open_source.mem_nhds he0)
    apply e.continuousAt he0
    simpa only [hezero] using Metric.ball_mem_nhds (0 : ℂ) hρ
  obtain ⟨κ, hκ, hκsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hsphere : Metric.sphere (0 : ℂ) (κ / 2) ⊆ Metric.ball (0 : ℂ) κ := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right, hz]
    exact half_lt_self hκ
  obtain ⟨w, hw, hheight⟩ := exists_eq_unit_rotation_on_sphere H hζ (half_pos hκ)
    (hH.mono (fun z hz => (hκsub (hsphere hz)).1))
  have hwsource := (hκsub (hsphere hw)).1
  have hewball := (hκsub (hsphere hw)).2
  have hwne : w ≠ 0 := by
    intro h
    have hn : ‖w‖ = κ / 2 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hw
    rw [h, norm_zero] at hn
    exact (half_pos hκ).ne hn
  have hewne : e w ≠ 0 := by
    intro h
    exact hwne (e.injOn hwsource he0 (h.trans hezero.symm))
  have hzero : H (e.symm (e w)) - H (ζ * e.symm (e w)) = 0 := by
    rw [e.left_inv hwsource, hheight, sub_self]
  rcases (hcover (e w) hewball).mp hzero with hzero | ⟨s, _, _, _⟩
  · exact (hewne hzero).elim
  · exact ⟨s⟩

private theorem inverse_coordinate_derivative_injective_at_zero
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he0 : (0 : ℂ) ∈ e.source) (hezero : e 0 = 0)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target) :
    Function.Injective (fderiv ℝ (e.symm : ℂ → ℂ) 0) := by
  have h0target : (0 : ℂ) ∈ e.target := hezero ▸ e.map_source he0
  have hizero : e.symm 0 = 0 := by
    calc
      e.symm 0 = e.symm (e 0) := congrArg e.symm hezero.symm
      _ = 0 := e.left_inv he0
  have heAt : DifferentiableAt ℝ (e : ℂ → ℂ) 0 :=
    (he.contDiffAt (e.open_source.mem_nhds he0)).differentiableAt one_ne_zero
  have hiAt : DifferentiableAt ℝ (e.symm : ℂ → ℂ) 0 :=
    (hei.contDiffAt (e.open_target.mem_nhds h0target)).differentiableAt one_ne_zero
  have hcomp : HasFDerivAt ((e : ℂ → ℂ) ∘ (e.symm : ℂ → ℂ))
      ((fderiv ℝ (e : ℂ → ℂ) 0).comp (fderiv ℝ (e.symm : ℂ → ℂ) 0)) 0 := by
    have heBack : HasFDerivAt (e : ℂ → ℂ)
        (fderiv ℝ (e : ℂ → ℂ) 0) (e.symm 0) := by
      simpa only [hizero] using heAt.hasFDerivAt
    exact heBack.comp 0 hiAt.hasFDerivAt
  have hlocal : ((e : ℂ → ℂ) ∘ (e.symm : ℂ → ℂ)) =ᶠ[𝓝 (0 : ℂ)] id := by
    filter_upwards [e.open_target.mem_nhds h0target] with z hz
    exact e.right_inv hz
  have hder := hcomp.unique ((hasFDerivAt_id (0 : ℂ)).congr_of_eventuallyEq hlocal)
  intro u v huv
  have hh := congrArg (fderiv ℝ (e : ℂ → ℂ) 0) huv
  change ((fderiv ℝ (e : ℂ → ℂ) 0).comp
    (fderiv ℝ (e.symm : ℂ → ℂ) 0)) u =
      ((fderiv ℝ (e : ℂ → ℂ) 0).comp (fderiv ℝ (e.symm : ℂ → ℂ) 0)) v at hh
  simpa only [hder, ContinuousLinearMap.id_apply] using hh

/-- Pull one actual C¹ nodal arc back through the same isothermal coordinate
and parametrize it by its original radius. The original height difference,
coordinate, arc index and inverse-radius map remain explicit. Smoothness is
asserted only at positive radius; the final closed root disk lies in the supplied
neighborhood. The nodal-family inputs are precisely the output of the analytic
inverse-gauge nodal theorem at zero. -/
theorem exists_original_radius_arc_of_deck_nodal_family
    (H : ℂ → ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (e : OpenPartialHomeomorph ℂ ℂ) (he0 : (0 : ℂ) ∈ e.source) (hezero : e 0 = 0)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (hH : ContinuousOn H e.source) :
    let d : ℂ → ℝ := fun z => H z - H (ζ * z)
    let v : ℂ → ℝ := d ∘ e.symm
    ContDiffOn ℝ ∞ d (e.source \ {0}) →
    ∀ (ρ : ℝ), 0 < ρ → Metric.ball (0 : ℂ) ρ ⊆ e.target →
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, z ≠ 0 → fderiv ℝ v z ≠ 0) →
      ∀ (S : Set ℝ) (Γ : S → ℝ → ℂ),
        (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
          HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
          Set.InjOn (Γ s) (Ico 0 ρ) ∧
          ∀ r ∈ Ico 0 ρ, ‖Γ s r - 0‖ = r ∧ v (Γ s r) = 0) →
        (∀ z ∈ Metric.ball (0 : ℂ) ρ,
          v z = 0 ↔ z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r) →
        ∀ (O : Set ℂ), IsOpen O → (0 : ℂ) ∈ O →
          ∃ s : S, ∃ T : ℝ, 0 < T ∧ T < ρ ∧
            let β : ℝ → ℂ := e.symm ∘ Γ s
            let R := ‖β T‖
            let τ := Function.invFunOn (fun t => ‖β t‖) (Icc 0 T)
            let α := β ∘ τ
            0 < R ∧ Metric.closedBall (0 : ℂ) R ⊆ O ∧ α 0 = 0 ∧
              (∀ r ∈ Icc 0 R, ‖α r‖ = r ∧ d (α r) = 0) ∧
              (∃ L : ℝ≥0, LipschitzOnWith L α (Icc 0 R)) ∧
              ContDiffOn ℝ ∞ α (Ioo 0 R) ∧
              ∀ r ∈ Ioc 0 R, fderiv ℝ d (α r) ≠ 0 := by
  intro d v hd ρ hρ hρtarget hregular S Γ hΓ hcover O hO h0O
  classical
  obtain ⟨s⟩ := exists_index_of_deck_nodal_cover hζ e he0 hezero hH hρ hcover
  obtain ⟨hΓzero, hΓC1, hΓderiv, _hΓinj, hΓvalues⟩ := hΓ s
  have h0target : (0 : ℂ) ∈ e.target := hezero ▸ e.map_source he0
  have hizero : e.symm 0 = 0 := by
    calc
      e.symm 0 = e.symm (e 0) := congrArg e.symm hezero.symm
      _ = 0 := e.left_inv he0
  let β : ℝ → ℂ := e.symm ∘ Γ s
  have hΓat : ContDiffAt ℝ 1 (Γ s) 0 :=
    hΓC1.contDiffAt (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hρ, hρ⟩)
  have hiAt : ContDiffAt ℝ 1 (e.symm : ℂ → ℂ) 0 :=
    hei.contDiffAt (e.open_target.mem_nhds h0target)
  have hβat : ContDiffAt ℝ 1 β 0 := by
    apply ContDiffAt.comp 0 _ hΓat
    simpa only [hΓzero] using hiAt
  have hβzero : β 0 = 0 := by
    simp only [β, Function.comp_apply, hΓzero, hizero]
  let tangent : ℂ := fderiv ℝ (e.symm : ℂ → ℂ) 0
    (Complex.exp (((s : ℝ) : ℂ) * Complex.I))
  have hβderiv : HasDerivAt β tangent 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 _ hΓderiv
    simpa only [hΓzero] using (hiAt.differentiableAt one_ne_zero).hasFDerivAt
  have htangent : tangent ≠ 0 := by
    intro hzero
    have hinj := inverse_coordinate_derivative_injective_at_zero e he0 hezero he hei
    have hexp := hinj
      (hzero.trans (map_zero (fderiv ℝ (e.symm : ℂ → ℂ) 0)).symm)
    exact Complex.exp_ne_zero _ hexp
  obtain ⟨η, hη, hηO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h0O)
  have hnear : {t : ℝ | t ∈ Ioo (-ρ) ρ ∧ Γ s t ∈ e.target ∧
      β t ∈ Metric.ball (0 : ℂ) η} ∈ 𝓝 (0 : ℝ) := by
    have hΓnear : ∀ᶠ t in 𝓝 (0 : ℝ), Γ s t ∈ e.target := by
      apply hΓat.continuousAt
      simpa only [hΓzero] using e.open_target.mem_nhds h0target
    have hβnear : ∀ᶠ t in 𝓝 (0 : ℝ), β t ∈ Metric.ball (0 : ℂ) η := by
      apply hβat.continuousAt
      simpa only [hβzero] using Metric.ball_mem_nhds (0 : ℂ) hη
    filter_upwards [isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hρ, hρ⟩,
      hΓnear, hβnear] with t ht hΓt hβt
    exact ⟨ht, hΓt, hβt⟩
  obtain ⟨tmax, htmax, htmaxsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hsmall {t : ℝ} (ht : t ∈ Ioo (-tmax) tmax) :
      t ∈ Ioo (-ρ) ρ ∧ Γ s t ∈ e.target ∧ β t ∈ Metric.ball (0 : ℂ) η := by
    apply htmaxsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨ht.1, ht.2⟩
  have hβC1 : ContDiffOn ℝ 1 β (Ioo (-tmax) tmax) := by
    intro t ht
    have hi := hei.contDiffAt (e.open_target.mem_nhds (hsmall ht).2.1)
    have hΓt := hΓC1.contDiffAt (isOpen_Ioo.mem_nhds (hsmall ht).1)
    exact (hi.comp t hΓt).contDiffWithinAt
  have hβzeroArc : ∀ t ∈ Ico 0 tmax, d (β t) = 0 := by
    intro t ht
    have htsmall : t ∈ Ioo (-tmax) tmax :=
      ⟨(neg_lt_zero.mpr htmax).trans_le ht.1, ht.2⟩
    exact (hΓvalues t ⟨ht.1, (hsmall htsmall).1.2⟩).2
  have hβregular : ∀ t ∈ Ioo 0 tmax,
      ContDiffAt ℝ ∞ d (β t) ∧ fderiv ℝ d (β t) ≠ 0 := by
    intro t ht
    have htsmall : t ∈ Ioo (-tmax) tmax :=
      ⟨(neg_lt_zero.mpr htmax).trans ht.1, ht.2⟩
    have hΓnorm : ‖Γ s t‖ = t := by
      simpa only [sub_zero] using (hΓvalues t ⟨ht.1.le, (hsmall htsmall).1.2⟩).1
    have hΓball : Γ s t ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right, hΓnorm]
      exact (hsmall htsmall).1.2
    have hΓtarget := hρtarget hΓball
    have hΓne : Γ s t ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hΓnorm
      exact ht.1.ne hΓnorm
    have hβsource : β t ∈ e.source := e.map_target hΓtarget
    have hβne : β t ≠ 0 := by
      intro hzero
      apply hΓne
      calc
        Γ s t = e (β t) := (e.right_inv hΓtarget).symm
        _ = 0 := by rw [hzero, hezero]
    have hdAt : ContDiffAt ℝ ∞ d (β t) :=
      hd.contDiffAt ((e.open_source.sdiff isClosed_singleton).mem_nhds ⟨hβsource, hβne⟩)
    refine ⟨hdAt, ?_⟩
    intro hdzero
    have hi := (hei.contDiffAt (e.open_target.mem_nhds hΓtarget)).differentiableAt one_ne_zero
    have hcomp := (hdAt.differentiableAt (by simp)).hasFDerivAt.comp (Γ s t) hi.hasFDerivAt
    have hD : fderiv ℝ v (Γ s t) = 0 := by
      change fderiv ℝ (d ∘ (e.symm : ℂ → ℂ)) (Γ s t) = 0
      calc
        _ = (fderiv ℝ d (β t)).comp
            (fderiv ℝ (e.symm : ℂ → ℂ) (Γ s t)) := hcomp.fderiv
        _ = 0 := by rw [hdzero, ContinuousLinearMap.zero_comp]
    exact hregular (Γ s t) hΓball hΓne hD
  obtain ⟨T, hT, hTmax, hR, hαzero, hαvalues, hαLip, hαsmooth, hαregular⟩ :=
    exists_smooth_punctured_radial_reparametrization_of_zero_arc
      htmax hβC1 hβzero hβderiv htangent hβzeroArc hβregular
  have hTsmall : T ∈ Ioo (-tmax) tmax :=
    ⟨(neg_lt_zero.mpr htmax).trans hT, hTmax⟩
  refine ⟨s, T, hT, (hsmall hTsmall).1.2, hR, ?_, hαzero,
    hαvalues, hαLip, hαsmooth, hαregular⟩
  intro z hz
  apply hηO
  have hRη : ‖β T‖ < η := by
    simpa only [Metric.mem_ball, dist_zero_right] using (hsmall hTsmall).2.2
  rw [Metric.mem_ball, dist_zero_right]
  exact (mem_closedBall_zero_iff.mp hz).trans_lt hRη

end DifferentialGeometry.Analysis
