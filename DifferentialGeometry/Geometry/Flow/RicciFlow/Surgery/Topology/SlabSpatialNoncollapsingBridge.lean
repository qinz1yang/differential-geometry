import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabPointPicking

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

private theorem continuousWithinAt_scalar_time (G : P.IncomingSlab a s) (y : P.Carrier)
    {t : ℝ} (ht : t ∈ Ico a s) :
    ContinuousWithinAt (fun v => G.flow.scalar v y) (Ico a s) t :=
  (G.equation.scalarTime (K := Ico a s) ht (fun _ h => h) y).continuousWithinAt

private theorem hasDerivAt_scalar_time (G : P.IncomingSlab a s) (y : P.Carrier) {t : ℝ}
    (ht : t ∈ Ioo a s) :
    HasDerivAt (fun v => G.flow.scalar v y)
      (derivWithin (fun v => G.flow.scalar v y) (Iic t) t) t := by
  have hd : DifferentiableAt ℝ (fun v => G.flow.scalar v y) t :=
    (G.equation.scalarTime (K := Ioo a s) ht (fun _ h => Ioo_subset_Ico_self h)
      y).differentiableAt (Ioo_mem_nhds ht.1 ht.2)
  rw [hd.derivWithin (uniqueDiffWithinAt_Iic t)]
  exact hd.hasDerivAt

private theorem scalar_le_on_backward_window_of_derivativeBoundBefore
    (G : P.IncomingSlab a s) {Ctime : ℝ≥0} {qcan t' δ r τ : ℝ}
    (hder : G.DerivativeBoundBefore Ctime qcan t') (y : P.Carrier)
    (hr : 0 < r) (hδ1 : δ < 1) (hδC : (Ctime : ℝ) * δ < 1 / 18)
    (hτs : τ < s) (ha : a ≤ τ - r ^ 2) (hτt : τ ≤ t') (hq : qcan < 9 / r ^ 2)
    (hy : G.flow.scalar τ y ≤ 9 / r ^ 2) :
    ∀ u ∈ Icc (τ - δ * r ^ 2) τ, G.flow.scalar u y ≤ 18 / r ^ 2 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hh : δ * r ^ 2 < r ^ 2 := by nlinarith
  have hwin : Icc (τ - δ * r ^ 2) τ ⊆ Ico a s := fun t ht =>
    ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hτs⟩
  have hcont : ContinuousOn (fun σ => G.flow.scalar (τ - σ) y) (Icc 0 (δ * r ^ 2)) := by
    have hc : ContinuousOn (fun v => G.flow.scalar v y) (Icc (τ - δ * r ^ 2) τ) :=
      fun t ht => (continuousWithinAt_scalar_time G y (hwin ht)).mono hwin
    refine hc.comp (continuous_const.sub continuous_id).continuousOn ?_
    intro σ hσ
    exact ⟨show τ - δ * r ^ 2 ≤ τ - σ by linarith [hσ.2],
      show τ - σ ≤ τ by linarith [hσ.1]⟩
  have hBpos : 0 < 9 / r ^ 2 := by positivity
  have hBC : 9 / r ^ 2 < 18 / r ^ 2 := div_lt_div_of_pos_right (by norm_num) hr2
  have hkey := Perelman.CanonicalNeighborhood.forall_le_of_no_crossing (a := 0)
    (b := δ * r ^ 2) (B := 9 / r ^ 2) (C := 18 / r ^ 2)
    (f := fun σ => G.flow.scalar (τ - σ) y) hBC hcont ?_
  · intro u hu
    have h := hkey (τ - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    simpa only [sub_sub_cancel] using h
  intro u v h0u huv hvh hge hstart hend
  have hq' : G.flow.scalar (τ - u) y ≤ 9 / r ^ 2 := by
    refine le_trans hstart (max_le le_rfl ?_)
    simpa only [sub_zero] using hy
  have hp' : 18 / r ^ 2 ≤ G.flow.scalar (τ - v) y := hend
  have hge' : ∀ t ∈ Icc (τ - v) (τ - u), 9 / r ^ 2 ≤ G.flow.scalar t y := by
    intro t ht
    have h := hge (τ - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [sub_sub_cancel] using h
  have hpq : τ - v ≤ τ - u := by linarith
  have hsub : Icc (τ - v) (τ - u) ⊆ Ico a s := fun t ht =>
    hwin ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hpos : ∀ t ∈ Icc (τ - v) (τ - u), 0 < G.flow.scalar t y := fun t ht =>
    hBpos.trans_le (hge' t ht)
  have hFc : ContinuousOn (fun t => (G.flow.scalar t y)⁻¹) (Icc (τ - v) (τ - u)) := by
    refine ContinuousOn.inv₀ ?_ (fun t ht => (hpos t ht).ne')
    exact fun t ht => (continuousWithinAt_scalar_time G y (hsub ht)).mono hsub
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun t => (G.flow.scalar t y)⁻¹)
    (f' := fun t => -(derivWithin (fun v => G.flow.scalar v y) (Iic t) t) /
      G.flow.scalar t y ^ 2)
    (C := (Ctime : ℝ)) hFc ?_ ?_ (τ - u) (right_mem_Icc.2 hpq)
  · have hA : (9 / r ^ 2)⁻¹ ≤ (G.flow.scalar (τ - u) y)⁻¹ :=
      inv_anti₀ (hpos (τ - u) (right_mem_Icc.2 hpq)) hq'
    have hB : (G.flow.scalar (τ - v) y)⁻¹ ≤ (18 / r ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hp'
    rw [inv_div] at hA hB
    rw [Real.norm_eq_abs] at hmvt
    have habs := le_abs_self ((G.flow.scalar (τ - u) y)⁻¹ - (G.flow.scalar (τ - v) y)⁻¹)
    have hC0 : (0 : ℝ) ≤ Ctime := Ctime.2
    have hlen : τ - u - (τ - v) ≤ δ * r ^ 2 := by linarith
    have hCl : (Ctime : ℝ) * (τ - u - (τ - v)) ≤ (Ctime : ℝ) * δ * r ^ 2 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hlen hC0
    have hfin : (Ctime : ℝ) * δ * r ^ 2 < r ^ 2 / 18 := by nlinarith
    have h9 : r ^ 2 / 9 - r ^ 2 / 18 = r ^ 2 / 18 := by ring
    linarith
  · intro x hx
    have hxs : x ∈ Ioo a s := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact ((hasDerivAt_scalar_time G y hxs).inv
      (hpos x ⟨hx.1, hx.2.le⟩).ne').hasDerivWithinAt
  · intro x hx
    rw [Real.norm_eq_abs]
    refine Perelman.CanonicalNeighborhood.abs_deriv_inv_le (hpos x ⟨hx.1, hx.2.le⟩) ?_
    exact hder y x ⟨by linarith [hx.1], by linarith [hx.2]⟩
      (lt_of_lt_of_le hq (hge' x ⟨hx.1, hx.2.le⟩))

theorem exists_spatial_noncollapsing_of_parabolic_of_derivative_bound
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi) (Ctime : ℝ≥0) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
        {qcan t' κ ρ₀ : ℝ},
        Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi →
        G.DerivativeBoundBefore Ctime qcan t' →
        (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) ≤ t' → B.radius ≤ ρ₀ →
            B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ) →
        ∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ),
          a ≤ (τ : ℝ) - B.radius ^ 2 → (τ : ℝ) ≤ t' → c * B.radius ≤ ρ₀ →
          B.radius ≤ 1 → qcan * B.radius ^ 2 < 9 →
          B.IsSpatiallyKappaNoncollapsed (κ * c ^ 3) := by
  set Cp : ℝ := 4 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) with hCp
  have hCp0 : 0 < Cp := by
    have h1 := hPhi.pos 1
    have h0 := hPhi.pos 0
    have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  set δ : ℝ := 1 / (36 * ((Ctime : ℝ) + 1)) with hδ
  have hC0 : (0 : ℝ) ≤ Ctime := Ctime.2
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by positivity)]
    nlinarith
  have hδC : (Ctime : ℝ) * δ < 1 / 18 := by
    rw [hδ, mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set c : ℝ := min (1 / 2) (min δ (1 / (18 * Cp))) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcδ : c ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hcCp : c ≤ 1 / (18 * Cp) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, hc1, ?_⟩
  intro P a s G qcan t' κ ρ₀ hpinch hder hpar τ B ha hτt hcρ hr1 hq hRm
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hr := B.radius_pos
  have hr2 : 0 < B.radius ^ 2 := by positivity
  have hτs : (τ : ℝ) < s := τ.2.2
  have hcr : (c * B.radius) ^ 2 ≤ δ * B.radius ^ 2 := by
    rw [mul_pow]
    have : c ^ 2 ≤ δ := by nlinarith
    exact mul_le_mul_of_nonneg_right this hr2.le
  have hcr1 : (c * B.radius) ^ 2 ≤ B.radius ^ 2 := hcr.trans (by nlinarith)
  have hpar' : (B.shrink c hc0).IsParabolicallyRmControlled := by
    refine ⟨fun t ht => ⟨?_, lt_of_le_of_lt ht.2 hτs⟩, ?_⟩
    · have h := ht.1
      change (τ : ℝ) - (c * B.radius) ^ 2 ≤ t at h
      linarith
    intro u hu x hx
    change (τ : ℝ) - (c * B.radius) ^ 2 ≤ u ∧ u ≤ (τ : ℝ) at hu
    change (c * B.radius) ^ 4 * Perelman.FlowMetricBall.rmNormSq G.flow u x ≤ 1
    have hxB : x ∈ B.set := Perelman.FlowMetricBall.shrink_setAt B hc0 hc1 τ hx
    have hsp := Perelman.scalar_le_of_spatial_rm B hRm hxB
    have h9 : ((3 : ℕ) : ℝ) ^ 2 = 9 := by norm_num
    rw [hdim, h9] at hsp
    have hy : G.flow.scalar (τ : ℝ) x ≤ 9 / B.radius ^ 2 := by
      rw [le_div_iff₀ hr2, mul_comm]
      exact hsp
    have hq' : qcan < 9 / B.radius ^ 2 := by
      rw [lt_div_iff₀ hr2]
      exact hq
    have hsc := scalar_le_on_backward_window_of_derivativeBoundBefore G hder x hr hδ1 hδC
      hτs ha hτt hq' hy u ⟨by linarith [hu.1], hu.2⟩
    have hut : u ∈ Ico a s := ⟨by linarith [hu.1], lt_of_le_of_lt hu.2 hτs⟩
    have hpin :=
      Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_mul_max_scalar_one_of_phiAlmostNonnegative
        hPhi hpinch hdim hut x
    rw [← hCp] at hpin
    have h18 : 1 ≤ 18 / B.radius ^ 2 := by
      rw [le_div_iff₀ hr2]
      nlinarith
    have hmax : max (G.flow.scalar u x) 1 ≤ 18 / B.radius ^ 2 := max_le hsc h18
    have hsq : Real.sqrt (Perelman.FlowMetricBall.rmNormSq G.flow u x) ≤
        Cp * (18 / B.radius ^ 2) :=
      hpin.trans (mul_le_mul_of_nonneg_left hmax hCp0.le)
    have hkey : (c * B.radius) ^ 2 *
        Real.sqrt (Perelman.FlowMetricBall.rmNormSq G.flow u x) ≤ 1 := by
      have h1 : (c * B.radius) ^ 2 * (Cp * (18 / B.radius ^ 2)) = 18 * Cp * c ^ 2 := by
        field_simp
      have h2 : 18 * Cp * c ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hcCp
        linarith
      have h3 : 18 * Cp * c ^ 2 ≤ 1 := by nlinarith
      calc (c * B.radius) ^ 2 * Real.sqrt (Perelman.FlowMetricBall.rmNormSq G.flow u x)
          ≤ (c * B.radius) ^ 2 * (Cp * (18 / B.radius ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = 18 * Cp * c ^ 2 := h1
        _ ≤ 1 := h3
    rcases le_or_gt 0 (Perelman.FlowMetricBall.rmNormSq G.flow u x) with hN | hN
    · have hNeq := Real.sq_sqrt hN
      have hnn : 0 ≤ (c * B.radius) ^ 2 *
          Real.sqrt (Perelman.FlowMetricBall.rmNormSq G.flow u x) := by positivity
      calc (c * B.radius) ^ 4 * Perelman.FlowMetricBall.rmNormSq G.flow u x
          = (c * B.radius) ^ 4 *
              Real.sqrt (Perelman.FlowMetricBall.rmNormSq G.flow u x) ^ 2 := by
            rw [hNeq]
        _ = ((c * B.radius) ^ 2 *
              Real.sqrt (Perelman.FlowMetricBall.rmNormSq G.flow u x)) ^ 2 := by ring
        _ ≤ 1 := pow_le_one₀ hnn hkey
    · have : (c * B.radius) ^ 4 * Perelman.FlowMetricBall.rmNormSq G.flow u x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hN.le
      linarith
  have hk := hpar τ (B.shrink c hc0) hτt hcρ hpar'
  have hvol : (B.shrink c hc0).volume ≤ B.volume :=
    Perelman.FlowMetricBall.volume_mono (Perelman.FlowMetricBall.shrink_nested B hc0 hc1)
  refine ⟨mul_pos hk.1 (pow_pos hc0 3), ?_⟩
  have hk2 := hk.2
  rw [hdim] at hk2 ⊢
  change ENNReal.ofReal κ * ENNReal.ofReal (c * B.radius) ^ 3 ≤ _ at hk2
  have heq : ENNReal.ofReal (κ * c ^ 3) * ENNReal.ofReal B.radius ^ 3 =
      ENNReal.ofReal κ * ENNReal.ofReal (c * B.radius) ^ 3 := by
    rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (mul_pos hk.1 (pow_pos hc0 3)).le,
      ← ENNReal.ofReal_pow (mul_pos hc0 hr).le, ← ENNReal.ofReal_mul hk.1.le]
    congr 1
    ring
  rw [heq]
  exact hk2.trans hvol

theorem exists_spatial_noncollapsing_on_window_of_parabolic_of_derivative_bound
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi) (Ctime : ℝ≥0) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
        {qcan t' κ ρ₀ rho t₀ t₁ : ℝ},
        Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi →
        G.DerivativeBoundBefore Ctime qcan t' →
        (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) ≤ t' → B.radius ≤ ρ₀ →
            B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ) →
        rho ≤ 1 → c * rho ≤ ρ₀ → qcan * rho ^ 2 < 9 → a ≤ t₀ - rho ^ 2 →
        t₁ ≤ t' →
        ∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ),
          t₀ ≤ (τ : ℝ) → (τ : ℝ) ≤ t₁ → B.radius ≤ rho →
          B.IsSpatiallyKappaNoncollapsed (κ * c ^ 3) := by
  obtain ⟨c, hc0, hc1, hmain⟩ :=
    exists_spatial_noncollapsing_of_parabolic_of_derivative_bound hPhi Ctime
  refine ⟨c, hc0, hc1, ?_⟩
  intro P a s G qcan t' κ ρ₀ rho t₀ t₁ hpinch hder hpar hrho1 hcρ hq ha ht₁ τ B
    hτ₀ hτ₁ hrB
  have hr := B.radius_pos
  have hsq : B.radius ^ 2 ≤ rho ^ 2 := pow_le_pow_left₀ hr.le hrB 2
  have hq0 : qcan * B.radius ^ 2 < 9 := by
    rcases le_or_gt qcan 0 with hq0 | hq0
    · nlinarith [sq_nonneg B.radius]
    · nlinarith
  refine hmain G hpinch hder hpar τ B (by linarith) (hτ₁.trans ht₁) ?_ (hrB.trans hrho1) hq0
  exact (mul_le_mul_of_nonneg_left hrB hc0.le).trans hcρ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
