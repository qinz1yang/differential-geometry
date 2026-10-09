import DifferentialGeometry.Analysis.Complex.BoundaryLens.Parametrization
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.BoundaryLensEnergy
import DifferentialGeometry.Analysis.Complex.BoundaryLens.Geometry
import DifferentialGeometry.Analysis.Calculus.Interpolation.MonotoneArc
import DifferentialGeometry.Analysis.Sobolev.Interpolation.BoundaryCap
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone

noncomputable section

open Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis

private theorem circleMap_eq_of_coe_eq {s t : ℝ} (h : (s : loopCircle) = (t : loopCircle)) :
    circleMap 0 1 (2 * Real.pi * s) = circleMap 0 1 (2 * Real.pi * t) := by
  have hh := congrArg (fun x : loopCircle => (AddCircle.toCircle x : ℂ)) h
  simpa only [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one, circleMap,
    Complex.ofReal_one, one_mul, zero_add] using hh

private theorem periodic_comp_lift {F : Type*} {Γ : ℝ → F} (hΓ : Function.Periodic Γ 1)
    (ψ : CircleDeg1Lift) : Function.Periodic (fun t => Γ (ψ t)) 1 := by
  intro t
  change Γ (ψ (t + 1)) = Γ (ψ t)
  rw [ψ.map_add_one, hΓ]

private theorem periodic_eq_of_coe_eq {F : Type*} {a : ℝ → F} (ha : Function.Periodic a 1)
    {s t : ℝ} (h : (s : loopCircle) = (t : loopCircle)) : a s = a t := by
  simpa only [Function.Periodic.lift_coe] using congrArg ha.lift h

private theorem lens_arc_endpoints {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let α := Real.arccos (ρ / 2)
    let inner : ℝ → ℂ := fun s => circleMap (-1) ρ (-α + 2 * α * s)
    let outer : ℝ → ℂ := fun s => circleMap 0 1 (2 * α + (2 * Real.pi - 4 * α) * s)
    inner 1 = outer 0 ∧ outer 1 = inner 0 := by
  dsimp only
  constructor
  · convert circleMap_neg_one_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2) using 1 <;>
      congr 1 <;> ring
  · symm
    convert circleMap_neg_one_neg_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2) using 1 <;>
      congr 1 <;> ring

private theorem cap_boundary_profile_inner_outer
    {F : Type*} {q : ℂ → F} {a b : ℝ → F} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hab : a 1 = b 0) (hba : b 1 = a 0)
    (htrace : ∀ t : ℝ, q (lensBoundaryLoop ρ t) = joinedLoop a b t) :
    (∀ s ∈ Icc (0 : ℝ) 1,
      q (circleMap (-1) ρ (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s)) = a s) ∧
    (∀ s ∈ Icc (0 : ℝ) 1,
      q (circleMap 0 1 (2 * Real.arccos (ρ / 2) +
        (2 * Real.pi - 4 * Real.arccos (ρ / 2)) * s)) = b s) := by
  have hend := lens_arc_endpoints hρ hρ1
  constructor
  · intro s hs
    have h := htrace (s / 2)
    rw [lensBoundaryLoop, joinedLoop_first hend.2 (by constructor <;> linarith [hs.1, hs.2]),
      joinedLoop_first hba (by constructor <;> linarith [hs.1, hs.2])] at h
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
  · intro s hs
    have h := htrace ((s + 1) / 2)
    rw [lensBoundaryLoop, joinedLoop_second hend.1 hend.2
      (by constructor <;> linarith [hs.1, hs.2]),
      joinedLoop_second hab hba (by constructor <;> linarith [hs.1, hs.2])] at h
    have he : 2 * ((s + 1) / 2) - 1 = s := by ring
    simpa only [he] using h

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_boundary_cap_of_short_lift_increment
    {K U : Set F} (Γ : ℝ → F) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ Γ) (hperiod : Function.Periodic Γ 1)
    (hInv : AntilipschitzWith J (hperiod.lift : loopCircle → F)) (hΓK : range Γ ⊆ K)
    (f : ℂ → F) {Kf : ℝ≥0} (hf : LipschitzWith Kf f)
    (hfK : MapsTo f (closedBall (0 : ℂ) 1) K)
    (ψ : CircleDeg1Lift) (hψ : Continuous ψ)
    (htrace : ∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψ t))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hshort : ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
      ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3)
    {η : ℝ}
    (hηU : closedBall (f (circleMap (-1) ρ (-Real.arccos (ρ / 2)))) η ⊆ U)
    (hsmall : (1 + 2 * (KΓ : ℝ) * (J : ℝ)) * Real.sqrt
      (∫ s in Icc (0 : ℝ) 1, ‖deriv (fun s => f (circleMap (-1) ρ
        (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))) s‖ ^ 2) ≤ η)
    (T : F → F) (hT : Differentiable ℝ T) {LT : ℝ≥0}
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    let a₀ := Real.arccos (ρ / 2) / Real.pi
    let b₀ := 1 - a₀
    let a : ℝ → F := fun s => f (circleMap (-1) ρ
      (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))
    let b : ℝ → F := fun s => Γ ((1 - s) * ψ a₀ + s * ψ b₀)
    ∃ (ψbar : CircleDeg1Lift) (h : ℂ ≃ₜ ℂ) (q : ℂ → F),
      Continuous ψbar ∧
      EqOn ψbar ψ (⋃ k : ℤ, Ioo (a₀ + k) (b₀ + k))ᶜ ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        ψbar (a₀ + s * (b₀ - a₀)) = (1 - s) * ψ a₀ + s * ψ b₀) ∧
      h '' closedBall (0 : ℂ) 1 = boundaryLens ρ ∧
      (∀ t : ℝ, h (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = lensBoundaryLoop ρ t) ∧
      q = T ∘ periodicLoopCone (a 0) (joinedLoop_periodic a b) ∘ h.symm ∧
      (∃ Cq : ℝ≥0, LipschitzWith Cq q) ∧
      MapsTo q (boundaryLens ρ) K ∧
      EqOn q f (closedBall (0 : ℂ) 1 ∩ sphere (-1) ρ) ∧
      (∀ t : ℝ, attachBoundaryCap f q ρ (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψbar t)) ∧
      (∫ z in boundaryLens ρ,
        (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤
        2 * (144 * (16 * Real.pi + 1) * (18 * Real.pi ^ 2 + 1)) ^ 2 * (LT : ℝ) ^ 2 *
          ((Real.pi / 2) * (1 + 2 * (KΓ : ℝ) * (J : ℝ)) ^ 2 +
            (2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) / (8 * Real.pi)) *
          (∫ s in Icc (0 : ℝ) 1, ‖deriv a s‖ ^ 2) := by
  let α := Real.arccos (ρ / 2)
  let a₀ := α / Real.pi
  let b₀ := 1 - a₀
  let inner : ℝ → ℂ := fun s => circleMap (-1) ρ (-α + 2 * α * s)
  let outer : ℝ → ℂ := fun s => circleMap 0 1 (2 * α + (2 * Real.pi - 4 * α) * s)
  let a : ℝ → F := f ∘ inner
  let b : ℝ → F := fun s => Γ ((1 - s) * ψ a₀ + s * ψ b₀)
  have hα : 0 < α := Real.arccos_pos.mpr (by linarith)
  have hαhalf : α < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have ha₀ : 0 < a₀ := div_pos hα Real.pi_pos
  have ha₀b₀ : a₀ < b₀ := by
    have h : α / Real.pi < 1 / 2 :=
      (div_lt_iff₀ Real.pi_pos).mpr (by linarith)
    dsimp only [a₀, b₀]
    nlinarith
  have hb₀a₀ : b₀ < a₀ + 1 := by dsimp only [b₀]; linarith
  have houter (s : ℝ) : outer s = circleMap 0 1 (2 * Real.pi * (a₀ + s * (b₀ - a₀))) := by
    dsimp only [outer]
    congr 1
    dsimp only [a₀, b₀]
    field_simp
    ring
  have hend := lens_arc_endpoints hρ hρ1
  change inner 1 = outer 0 ∧ outer 1 = inner 0 at hend
  have ha₀eq : a 0 = Γ (ψ b₀) := by
    change f (inner 0) = _
    rw [← hend.2, houter]
    simpa only [mul_zero, zero_add, one_mul, add_sub_cancel] using htrace b₀
  have ha₁eq : a 1 = Γ (ψ a₀) := by
    change f (inner 1) = _
    rw [hend.1, houter]
    simpa only [mul_zero, zero_mul, add_zero] using htrace a₀
  have haLip : LipschitzWith (Kf * (Real.nnabs ρ * Real.nnabs (2 * α))) a := by
    have hparam : LipschitzWith (Real.nnabs (2 * α)) (fun s : ℝ => -α + 2 * α * s) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, Real.coe_nnabs]
      exact le_rfl
    exact hf.comp ((lipschitzWith_circleMap (-1) ρ).comp hparam)
  have haK : MapsTo a (Icc (0 : ℝ) 1) K := by
    intro s hs
    apply hfK
    apply Complex.circleMap_neg_one_mem_closedBall ρ hρ.le (hρ1.le.trans (by norm_num))
    change -α ≤ -α + 2 * α * s ∧ -α + 2 * α * s ≤ α
    constructor <;> nlinarith [hs.1, hs.2]
  obtain ⟨ψbar, hψbar, hsame, hline, _, _⟩ :=
    ψ.exists_continuous_affine_interpolation hψ ha₀b₀ hb₀a₀
  obtain ⟨h, hLip, hInvLip, himage, _, hboundary⟩ :=
    exists_natural_boundaryLens_bilipschitz_homeomorph hρ hρ1.le
  let q : ℂ → F := T ∘ periodicLoopCone (a 0) (joinedLoop_periodic a b) ∘ h.symm
  obtain ⟨hqLip, hqK, _, hqBoundary, hqEnergy⟩ :=
    retracted_joinedLoop_affine_arc_homeomorph_filling h hLip hInvLip a Γ haLip hΓ hperiod hInv
      (ψ.monotone ha₀b₀.le) hshort ha₀eq ha₁eq haK hΓK
      (by simpa only [a, inner, Function.comp_apply, mul_zero, add_zero, α] using hηU)
      hsmall T hT hLT hmap hfix
  have hqTrace (t : ℝ) : q (lensBoundaryLoop ρ t) = joinedLoop a b t := by
    rw [← hboundary t]
    exact hqBoundary t
  have hab : a 1 = b 0 := by simpa only [b, sub_zero, one_mul, zero_mul, add_zero] using ha₁eq
  have hba : b 1 = a 0 := by simpa only [b, sub_self, zero_mul, one_mul, zero_add] using ha₀eq.symm
  obtain ⟨hqi, hqo⟩ := cap_boundary_profile_inner_outer hρ hρ1 hab hba hqTrace
  have hseam : EqOn q f (closedBall (0 : ℂ) 1 ∩ sphere (-1) ρ) := by
    intro z hz
    have hz' : z ∈ circleMap (-1) ρ '' Icc (-α) α := by
      rw [← sphere_inter_closedDisk_eq_inner_arc_image hρ (hρ1.le.trans (by norm_num))]
      exact ⟨hz.2, hz.1⟩
    obtain ⟨θ, hθ, rfl⟩ := hz'
    let s := (θ + α) / (2 * α)
    have hs : s ∈ Icc (0 : ℝ) 1 := by
      constructor
      · apply div_nonneg <;> linarith [hθ.1]
      · apply (div_le_one (by positivity : 0 < 2 * α)).mpr
        linarith [hθ.2]
    have he : -α + 2 * α * s = θ := by dsimp only [s]; field_simp; ring
    have hx := hqi s hs
    change q (circleMap (-1) ρ (-α + 2 * α * s)) = f (circleMap (-1) ρ (-α + 2 * α * s)) at hx
    simpa only [he] using hx
  have hqOuter (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      q (circleMap 0 1 (2 * Real.pi * (a₀ + s * (b₀ - a₀)))) =
        Γ (ψbar (a₀ + s * (b₀ - a₀))) := by
    rw [hline s hs]
    change q _ = b s
    rw [← houter]
    exact hqo s hs
  have hcapTrace (t : ℝ) : attachBoundaryCap f q ρ (circleMap 0 1 (2 * Real.pi * t)) =
      Γ (ψbar t) := by
    let x : ℂ := circleMap 0 1 (2 * Real.pi * t)
    have hxd : x = (diskBoundary (t : loopCircle) : ℂ) := by
      simp only [x, diskBoundary_coe, circleMap, Complex.ofReal_one, one_mul, zero_add]
    have hxD : x ∈ closedBall (0 : ℂ) 1 := circleMap_mem_closedBall _ (by norm_num) _
    by_cases hxin : x ∈ ball (-1 : ℂ) ρ
    · have htmem : (t : loopCircle) ∈ (fun s : ℝ => (s : loopCircle)) '' Ioo a₀ b₀ := by
        apply (diskBoundary_mem_ball_iff_mem_outer_arc hρ (hρ1.trans (by norm_num)) _).mp
        rwa [← hxd]
      obtain ⟨t₀, ht₀, hcoe⟩ := htmem
      let s := (t₀ - a₀) / (b₀ - a₀)
      have hs : s ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (sub_nonneg.mpr ht₀.1.le) (sub_pos.mpr ha₀b₀).le
        · exact (div_le_one (sub_pos.mpr ha₀b₀)).mpr (by linarith [ht₀.2])
      have he : a₀ + s * (b₀ - a₀) = t₀ := by
        dsimp only [s]
        rw [div_mul_cancel₀ _ (sub_ne_zero.mpr ha₀b₀.ne')]
        ring
      have hqt := hqOuter s hs
      rw [he] at hqt
      rw [show attachBoundaryCap f q ρ x = q x from attachBoundaryCap_inner f q ρ
        (by simpa only [mem_closedBall, dist_eq_norm, sub_neg_eq_add] using
          (ball_subset_closedBall hxin))]
      change q (circleMap 0 1 (2 * Real.pi * t)) = _
      rw [← circleMap_eq_of_coe_eq hcoe, hqt]
      exact periodic_eq_of_coe_eq (periodic_comp_lift hperiod ψbar) hcoe
    · have htout : t ∉ ⋃ k : ℤ, Ioo (a₀ + k) (b₀ + k) := by
        intro htmem
        obtain ⟨k, hk⟩ := mem_iUnion.mp htmem
        apply hxin
        rw [hxd]
        apply (diskBoundary_mem_ball_iff_mem_outer_arc hρ (hρ1.trans (by norm_num)) _).mpr
        refine ⟨t - (k : ℝ), ⟨by linarith [hk.1], by linarith [hk.2]⟩, ?_⟩
        have hk0 : ((k : ℝ) : loopCircle) = 0 :=
          (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k, by simp⟩
        change ((t - (k : ℝ) : ℝ) : loopCircle) = (t : loopCircle)
        rw [AddCircle.coe_sub, hk0, sub_zero]
      have hout := attachBoundaryCap_outer f q ρ hseam hxD
        (by simpa only [mem_ball, dist_eq_norm, sub_neg_eq_add, not_lt] using hxin)
      rw [hsame htout]
      exact hout.trans (htrace t)
  refine ⟨ψbar, h, q, hψbar, hsame, hline, himage, hboundary, rfl, ⟨_, hqLip⟩,
    by simpa only [himage] using hqK, hseam, hcapTrace, ?_⟩
  have hcoef :
      2 * (Real.toNNReal (12 * ρ * (16 * Real.pi + 1)) : ℝ) ^ 2 *
        (Real.toNNReal ((12 / ρ) * (18 * Real.pi ^ 2 + 1)) : ℝ) ^ 2 * (LT : ℝ) ^ 2 =
        2 * (144 * (16 * Real.pi + 1) * (18 * Real.pi ^ 2 + 1)) ^ 2 * (LT : ℝ) ^ 2 := by
    rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
    field_simp
    ring
  simpa only [himage, hcoef, q, a, b, inner, α, a₀, b₀, Function.comp_def] using hqEnergy

end DifferentialGeometry.Analysis

namespace CircleDeg1Lift

theorem sub_shifted_arccos_endpoints_le_two_thirds
    (ψ : CircleDeg1Lift)
    (h₁ : ψ (1 / 3 : ℝ) = ψ 0 + 1 / 3)
    (h₂ : ψ (2 / 3 : ℝ) = ψ 0 + 2 / 3)
    (d : ℝ) {ρ : ℝ} (hρ1 : ρ < 1) :
    ψ (d + (1 - Real.arccos (ρ / 2) / Real.pi)) -
      ψ (d + Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3 := by
  apply ψ.sub_le_two_thirds_of_map_thirds h₁ h₂
  have h := Real.one_sub_two_mul_arccos_div_pi_lt_one_third hρ1
  calc
    _ = 1 - 2 * Real.arccos (ρ / 2) / Real.pi := by ring
    _ ≤ 1 / 3 := h.le

end CircleDeg1Lift

end
