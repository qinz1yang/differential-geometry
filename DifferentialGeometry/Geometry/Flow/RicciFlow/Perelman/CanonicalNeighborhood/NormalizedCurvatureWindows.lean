import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_parabolic_curvature_bound_at_terminal_scalar_scale {kappa : ℝ}
    (hkappa : 0 < kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ Q : ℝ, 1 ≤ Q → ∀ p : (X.term i).M, (X.term i).S.scalar 0 p ≤ Q →
              Icc (-c / Q) 0 ⊆ (X.interval i).carrier ∧
                ∀ t ∈ Icc (-c / Q) 0,
                  ∀ y ∈ riemannianClosedBallOf ((X.term i).S.base.metric 0) p (c / Real.sqrt Q),
                    Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S t y) ≤ C * Q := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    canonical_neighborhood_local_propagation.{u} hkappa
  refine ⟨epsStar, c / 3, 4 * C, hepsStar, by positivity, by positivity, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  obtain ⟨S0, hS0, hsmall⟩ :=
    exists_forall_rescalePinchingFunction_le (B := 12) hPhi (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.scale_tendsto.eventually_ge_atTop (max S0 (6 * Phi 0))] with i hlocal hscale
  intro Q hQ p hp
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hlow := neg_six_mul_phi_zero_le_scalar (hPhi.rescale (X.scale_pos i))
    (X.pinching i) hdim hzero p
  have hlow' : -1 ≤ (X.term i).S.scalar 0 p := by
    have hs : 6 * Phi 0 ≤ X.scale i := (le_max_right _ _).trans hscale
    have hratio : 6 * Phi 0 / X.scale i ≤ 1 := (div_le_one (X.scale_pos i)).mpr hs
    dsimp only [rescalePinchingFunction] at hlow
    simp only [mul_zero] at hlow
    rw [div_eq_mul_inv] at hratio
    nlinarith
  let L : ℝ := 1 + |(X.term i).S.scalar 0 p|
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith [abs_nonneg ((X.term i).S.scalar 0 p)]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hLQ : L ≤ 3 * Q := by
    have habs : |(X.term i).S.scalar 0 p| ≤ Q := abs_le.mpr ⟨by linarith, hp⟩
    dsimp only [L]
    linarith
  have hscaleQ : S0 ≤ X.scale i * Q :=
    ((le_max_left _ _).trans hscale).trans (le_mul_of_one_le_right (X.scale_pos i).le hQ)
  have harg : 4 * L / Q ∈ Icc (0 : ℝ) 12 := by
    refine ⟨by positivity, (div_le_iff₀ hQpos).mpr ?_⟩
    linarith
  have hsmallL := hsmall (X.scale i * Q) hscaleQ (4 * L / Q) harg
  have hsmall0 := hsmall (X.scale i * Q) hscaleQ 0 (by norm_num)
  have herror : (Phi (4 * X.scale i * L) + Phi 0) / X.scale i ≤ Q := by
    have heq : (X.scale i * Q) * (4 * L / Q) = 4 * X.scale i * L := by field_simp
    simp only [rescalePinchingFunction, heq, mul_zero] at hsmallL hsmall0
    have hh : (Phi (4 * X.scale i * L) + Phi 0) / (X.scale i * Q) ≤ 1 := by
      rw [add_div, div_eq_mul_inv, div_eq_mul_inv]
      nlinarith
    have hm := (div_le_one (mul_pos (X.scale_pos i) hQpos)).mp hh
    exact (div_le_iff₀ (X.scale_pos i)).mpr (by nlinarith)
  have htime : c / 3 / Q ≤ c / L := by
    apply (div_le_div_iff₀ hQpos hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hLQ hc.le]
  have hrad : c / 3 / Real.sqrt Q ≤ c / Real.sqrt L := by
    have hsqrt : Real.sqrt L ≤ 3 * Real.sqrt Q := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity, by nlinarith [Real.sq_sqrt hQpos.le]⟩
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hQpos) (Real.sqrt_pos.mpr hL)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hc.le]
  have hwin : Icc (-(c / 3) / Q) 0 ⊆ Icc (0 - c / L) 0 := by
    intro t ht
    have hleft : -(c / L) ≤ -(c / 3) / Q := by
      simpa only [neg_div] using neg_le_neg htime
    exact ⟨by simpa only [zero_sub] using hleft.trans ht.1, ht.2⟩
  have hprop' := hlocal 0 ⟨by linarith [X.depth_pos i], le_rfl⟩ p
  refine ⟨hwin.trans hprop'.1, ?_⟩
  intro t ht y hy
  have hmem : (y, t) ∈ frozenBackwardCylinder (X.term i).S p 0 c c L :=
    ⟨hy.trans (ENNReal.ofReal_le_ofReal hrad), hwin ht⟩
  have hb := (hprop'.2 y t hmem).2.2
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hLQ hC.le,
    mul_le_mul_of_nonneg_left herror hC.le])

theorem exists_curvDerivNorm_bound_at_terminal_scalar_scale {kappa : ℝ}
    (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ Q : ℝ, 1 ≤ Q → ∀ p : (X.term i).M, (X.term i).S.scalar 0 p ≤ Q →
              ∀ m : ℕ, curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) p ≤
                B m * Q * Real.sqrt Q ^ m := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_parabolic_curvature_bound_at_terminal_scalar_scale.{u} hkappa
  let B : ℕ → ℝ := fun m =>
    shiLocalUniformBound 3 m (C * c) (c * Real.sqrt C / (4 * Real.exp (9 * C * c))) *
      C / Real.sqrt c ^ m
  have hB (m : ℕ) : 0 ≤ B m :=
    div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hC.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨epsStar, hepsStar, B, hB, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.depth_tendsto.eventually_ge_atTop c] with i hi hdepth
  intro Q hQ p hp m
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  obtain ⟨hcarrier, hcurv⟩ := hi Q hQ p hp
  have htime : c / Q ≤ X.depth i :=
    ((div_le_self hc.le hQ)).trans hdepth
  have hregular : Ico (-c / Q) 0 ⊆ (X.interval i).regular := by
    rw [X.regular_eq i]
    intro t ht
    rw [neg_div] at ht
    exact ⟨by linarith [ht.1, X.depth_pos i], ht.2⟩
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier :=
    hcarrier ⟨div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hQpos.le, le_rfl⟩
  have hcompact : IsCompact (riemannianClosedBallOf ((X.term i).S.base.metric 0) p
      (c / Real.sqrt Q)) :=
    (show RiemannianMetricComplete ((X.term i).S.base.metric 0) from
      ⟨X.complete i 0 hzero⟩).closedEBall_isCompact p _
  have hb := shi_curvDerivNorm_terminal_of_terminal_ball (X.term i).S (X.term i).isSolution
    (a := -c / Q) (b := 0) (K := C * Q) (R := c / Real.sqrt Q)
    (by exact div_neg_of_neg_of_pos (neg_neg_of_pos hc) hQpos)
    (mul_pos hC hQpos) (div_pos hc (Real.sqrt_pos.mpr hQpos)) hcarrier hregular p hcompact
    (fun t ht y hy => (Real.sqrt_le_iff.mp (hcurv t ht y hy)).2) m
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have htime_eq : 0 - -c / Q = c / Q := by ring
  have hprod : C * Q * (c / Q) = C * c := by field_simp
  have hexp : 9 * (C * Q) * (c / Q) = 9 * C * c := by field_simp
  have hrad : c / Real.sqrt Q * Real.sqrt (C * Q) / (4 * Real.exp (9 * C * c)) =
      c * Real.sqrt C / (4 * Real.exp (9 * C * c)) := by
    rw [Real.sqrt_mul hC.le]
    field_simp
  simp only [hdim, Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num,
    htime_eq, hprod, hexp, hrad, Real.sqrt_div hc.le] at hb
  apply hb.trans_eq
  dsimp only [B]
  rw [div_pow]
  field_simp

theorem exists_curvDerivNorm_bound_on_terminal_cylinder {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar tau r : ℝ, 0 < epsStar ∧ 0 < tau ∧ 0 < r ∧
      ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            Icc (-(2 * tau)) 0 ⊆ (X.interval i).carrier ∧
            Ico (-(2 * tau)) 0 ⊆ (X.interval i).regular ∧
            ∀ m : ℕ, ∀ t ∈ Icc (-tau) 0,
              ∀ y ∈ riemannianClosedBallOf ((X.term i).S.base.metric 0) (X.term i).basepoint r,
                curvDerivNorm m ((X.term i).S.base.metric t) y ≤ B m := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_parabolic_curvature_bound_at_terminal_scalar_scale.{u} hkappa
  let B : ℕ → ℝ := fun m =>
    shiLocalUniformBound 3 m (C * (c / 4))
      ((c / (4 * Real.exp (9 * C * c))) * Real.sqrt C /
        (4 * Real.exp (9 * C * (c / 4)))) * C / Real.sqrt (c / 4) ^ m
  have hB (m : ℕ) : 0 ≤ B m := by
    exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hC.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨epsStar, c / 2, c / 4, hepsStar, by positivity, by positivity, B, hB, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.depth_tendsto.eventually_ge_atTop c] with i hi hdepth
  have hbase : (X.term i).S.scalar 0 (X.term i).basepoint = 1 := X.base_one i
  obtain ⟨hcarrier, hcurv⟩ := hi 1 le_rfl (X.term i).basepoint hbase.le
  simp only [div_one, Real.sqrt_one, mul_one] at hcarrier hcurv
  have hreg : Ico (-c) 0 ⊆ (X.interval i).regular := by
    rw [X.regular_eq]
    intro t ht
    exact ⟨by linarith [ht.1, X.depth_pos i], ht.2⟩
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := hcarrier ⟨by linarith, le_rfl⟩
  have hcompact : IsCompact
      (riemannianClosedBallOf ((X.term i).S.base.metric 0) (X.term i).basepoint c) :=
    (show RiemannianMetricComplete ((X.term i).S.base.metric 0) from
      ⟨X.complete i 0 hzero⟩).closedEBall_isCompact _ _
  have hb := shi_curvDerivNorm_on_terminal_ball (X.term i).S (X.term i).isSolution
    (a := -c) (b := 0) (K := C) (R := c) (by linarith) hC hc hcarrier
    (Ioo_subset_Ico_self.trans hreg) (X.term i).basepoint hcompact
    (fun t ht y hy => (Real.sqrt_le_iff.mp (hcurv t ht y hy)).2)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show 2 * (c / 2) = c by ring] using hcarrier
  · simpa only [show 2 * (c / 2) = c by ring] using hreg
  · simpa only [B, show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace],
      Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num, zero_sub, neg_neg,
      add_zero, neg_div] using hb


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
