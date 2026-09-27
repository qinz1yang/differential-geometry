import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampWindowData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularityFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSliceRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveRegularityInput
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampProductLengthEvolution

noncomputable section

open Manifold Set MeasureTheory
open scoped ContDiff
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q]
    {D : RealTimeInterval} {a b : ℝ}

theorem rfs_ramp_window_data_of_length_evolution_of_radius_le
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ ell eta threshold : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hslice : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ t ∈ Icc a b, c.SliceRegularity B.family.metric lambda t)
    (hL₀ : 0 ≤ L₀) (hell : 0 < ell) (heta : 0 < eta) (hthreshold : 0 < threshold)
    (r : ℝ) (hr : 0 < r) (hradius : r ≤ K.radius)
    (hlength : r ≤ Real.exp (-(B.B₀ * (b - a))) * ell / 2)
    (henergy : r ≤ K.delta ^ 2 / threshold) :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b,
          Real.exp (-(B.B₀ * (b - a))) * ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          goodWindowUnion starts (K.delta * r ^ 2) ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts (K.delta * r ^ 2)) ≤
            ENNReal.ofReal (K.delta * r ^ 2 + Real.exp (B.B₀ * (b - a)) * L₀ / threshold) ∧
          ∀ x t, t ∈ goodWindowUnion starts (K.delta * r ^ 2) →
            0 < c.angle B.family.metric lambda x t ∧
            c.angle B.family.metric lambda x t ≤ eta) := by
  let K' := K.tighten K.delta_pos le_rfl hr hradius (fun _ => le_rfl)
  have hmin : min r (min (Real.exp (-(B.B₀ * (b - a))) * ell / 2)
      (K.delta ^ 2 / threshold)) = r := min_eq_left (le_min hlength henergy)
  simpa only [K', CurveShorteningRegularityInput.tighten, hmin] using
    rfs_ramp_window_data_of_length_evolution B L₀ Theta₀ ell eta threshold K' hev hslice
      hL₀ hell heta hthreshold

theorem exists_ramp_window_data_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ ell eta threshold : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hslice : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ t ∈ Icc a b, c.SliceRegularity B.family.metric lambda t)
    (hL₀ : 0 ≤ L₀) (hell : 0 < ell) (heta : 0 < eta) (hthreshold : 0 < threshold)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ d : ℝ, 0 < d ∧ d < epsilon ∧
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b,
          Real.exp (-(B.B₀ * (b - a))) * ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          goodWindowUnion starts d ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts d) ≤
            ENNReal.ofReal (d + Real.exp (B.B₀ * (b - a)) * L₀ / threshold) ∧
          ∀ x t, t ∈ goodWindowUnion starts d →
            0 < c.angle B.family.metric lambda x t ∧
            c.angle B.family.metric lambda x t ≤ eta) := by
  let r := min (epsilon / 2) (min K.radius
    (min (Real.exp (-(B.B₀ * (b - a))) * ell / 2) (K.delta ^ 2 / threshold)))
  have hr : 0 < r := lt_min (half_pos hepsilon) (lt_min K.radius_pos
    (lt_min (half_pos (mul_pos (Real.exp_pos _) hell))
      (div_pos (sq_pos_of_pos K.delta_pos) hthreshold)))
  have hradius : r ≤ K.radius := (min_le_right _ _).trans (min_le_left _ _)
  have hlength : r ≤ Real.exp (-(B.B₀ * (b - a))) * ell / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have henergy : r ≤ K.delta ^ 2 / threshold :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr_one : r ≤ 1 := hradius.trans K.radius_le_one
  have hsmall : K.delta * r ^ 2 < epsilon := by
    have hsq : r ^ 2 ≤ r := by nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr_one)]
    have hmul : K.delta * r ^ 2 ≤ r ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg r) K.delta_lt_one.le
    have hre : r ≤ epsilon / 2 := min_le_left _ _
    linarith only [hsq, hmul, hre, hepsilon]
  refine ⟨K.delta * r ^ 2, mul_pos K.delta_pos (sq_pos_of_pos hr), hsmall, ?_⟩
  exact rfs_ramp_window_data_of_length_evolution_of_radius_le B L₀ Theta₀ ell eta threshold
    K hev hslice hL₀ hell heta hthreshold r hr hradius hlength henergy

theorem exists_ramp_angle_windows_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ ell eta : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hslice : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ t ∈ Icc a b, c.SliceRegularity B.family.metric lambda t)
    (hL₀ : 0 ≤ L₀) (hell : 0 < ell) (heta : 0 < eta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ d : ℝ, 0 < d ∧ d < epsilon ∧
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b,
          Real.exp (-(B.B₀ * (b - a))) * ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          goodWindowUnion starts d ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts d) ≤
            ENNReal.ofReal epsilon ∧
          ∀ x t, t ∈ goodWindowUnion starts d →
            0 < c.angle B.family.metric lambda x t ∧
            c.angle B.family.metric lambda x t ≤ eta) := by
  let C := Real.exp (B.B₀ * (b - a)) * L₀
  let threshold := max 1 (2 * C / epsilon)
  have hthreshold : 0 < threshold := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : C / threshold ≤ epsilon / 2 := by
    rw [div_le_div_iff₀ hthreshold (by norm_num : (0 : ℝ) < 2)]
    have h := (div_le_iff₀ hepsilon).mp (le_max_right 1 (2 * C / epsilon))
    nlinarith only [h]
  obtain ⟨d, hd, hdsmall, lambda₀, hlambda₀, hlambda₀_one, hwindows⟩ :=
    exists_ramp_window_data_of_length_evolution B L₀ Theta₀ ell eta threshold K hev hslice
      hL₀ hell heta hthreshold (epsilon / 2) (half_pos hepsilon)
  refine ⟨d, hd, hdsmall.trans (half_lt_self hepsilon), lambda₀, hlambda₀, hlambda₀_one, ?_⟩
  intro lambda hlambda hlambda_le c hsol hramp hdeg hlen hcurv hlower
  obtain ⟨starts, hsub, hvol, hangle⟩ :=
    hwindows lambda hlambda hlambda_le c hsol hramp hdeg hlen hcurv hlower
  refine ⟨starts, hsub, hvol.trans (ENNReal.ofReal_le_ofReal ?_), hangle⟩
  change d + C / threshold ≤ epsilon
  linarith only [hdsmall, hC]

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q] [CompactSpace Q] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

theorem exists_ramp_window_data
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ ell eta threshold : ℝ)
    (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hell : 0 < ell) (heta : 0 < eta) (hthreshold : 0 < threshold)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ d : ℝ, 0 < d ∧ d < epsilon ∧
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b,
          Real.exp (-(B.B₀ * (b - a))) * ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          goodWindowUnion starts d ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts d) ≤
            ENNReal.ofReal (d + Real.exp (B.B₀ * (b - a)) * L₀ / threshold) ∧
          ∀ x t, t ∈ goodWindowUnion starts d →
            0 < c.angle B.family.metric lambda x t ∧
            c.angle B.family.metric lambda x t ≤ eta) := by
  exact exists_ramp_window_data_of_length_evolution B L₀ Theta₀ ell eta threshold
    (curveShorteningRegularityInput B L₀ Theta₀ hL₀ hTheta₀) (ramp_length_evolution B)
    (fun lambda hlambda _ c hsol _ t ht =>
      c.sliceRegularity_of_immersedOn B.family.metric lambda hlambda hsol.smooth hsol.immersed t ht)
    hL₀ hell heta hthreshold epsilon hepsilon

theorem exists_ramp_angle_windows
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ ell eta : ℝ)
    (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hell : 0 < ell) (heta : 0 < eta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ d : ℝ, 0 < d ∧ d < epsilon ∧
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b,
          Real.exp (-(B.B₀ * (b - a))) * ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          goodWindowUnion starts d ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts d) ≤
            ENNReal.ofReal epsilon ∧
          ∀ x t, t ∈ goodWindowUnion starts d →
            0 < c.angle B.family.metric lambda x t ∧
            c.angle B.family.metric lambda x t ≤ eta) := by
  exact exists_ramp_angle_windows_of_length_evolution B L₀ Theta₀ ell eta
    (curveShorteningRegularityInput B L₀ Theta₀ hL₀ hTheta₀) (ramp_length_evolution B)
    (fun lambda hlambda _ c hsol _ t ht =>
      c.sliceRegularity_of_immersedOn B.family.metric lambda hlambda hsol.smooth hsol.immersed t ht)
    hL₀ hell heta epsilon hepsilon

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
