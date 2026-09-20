import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthTimeRatio

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

private theorem max_sq_ratio_sub_one_le_of_le
    {a b s t : ℝ} (ha : 0 < a) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) :
    0 ≤ max ((s / t) ^ 2) ((t / s) ^ 2) - 1 ∧
      max ((s / t) ^ 2) ((t / s) ^ 2) - 1 ≤
        (2 * max b 0 / a ^ 2) * |s - t| := by
  have hspos : 0 < s := ha.trans_le hs.1
  have htpos : 0 < t := ha.trans_le ht.1
  have hsmall : (s / t) ^ 2 ≤ 1 := by
    have hle : s / t ≤ 1 := (div_le_one htpos).mpr hst
    have hnonneg : 0 ≤ s / t := div_nonneg hspos.le htpos.le
    simpa only [one_pow] using (sq_le_sq₀ hnonneg zero_le_one).mpr hle
  have hlarge : 1 ≤ (t / s) ^ 2 := by
    have hle : 1 ≤ t / s := (one_le_div hspos).mpr hst
    simpa only [one_pow] using (sq_le_sq₀ zero_le_one (zero_le_one.trans hle)).mpr hle
  rw [max_eq_right (hsmall.trans hlarge)]
  refine ⟨sub_nonneg.mpr hlarge, ?_⟩
  have hfactor : t + s ≤ 2 * max b 0 := by
    have hs' := hs.2.trans (le_max_left b 0)
    have ht' := ht.2.trans (le_max_left b 0)
    linarith
  have hnum : (t - s) * (t + s) ≤ (t - s) * (2 * max b 0) :=
    mul_le_mul_of_nonneg_left hfactor (sub_nonneg.mpr hst)
  have hsquare : a ^ 2 ≤ s ^ 2 := (sq_le_sq₀ ha.le hspos.le).mpr hs.1
  calc
    (t / s) ^ 2 - 1 = ((t - s) * (t + s)) / s ^ 2 := by
      field_simp [hspos.ne']
      ring
    _ ≤ ((t - s) * (2 * max b 0)) / s ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg s)
    _ ≤ ((t - s) * (2 * max b 0)) / a ^ 2 :=
      div_le_div_of_nonneg_left
        (mul_nonneg (sub_nonneg.mpr hst) (mul_nonneg (by norm_num) (le_max_right _ _)))
        (sq_pos_of_pos ha) hsquare
    _ = (2 * max b 0 / a ^ 2) * |s - t| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      ring

private theorem abs_sub_le_of_max_sq_ratio
    {a b s t x y U : ℝ} (ha : 0 < a) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hU : 0 ≤ U) (hx : x ≤ U) (hy : y ≤ U)
    (hxy : x ≤ max ((s / t) ^ 2) ((t / s) ^ 2) * y)
    (hyx : y ≤ max ((s / t) ^ 2) ((t / s) ^ 2) * x) :
    |x - y| ≤ ((2 * max b 0 / a ^ 2) * U) * |s - t| := by
  have hratio :
      0 ≤ max ((s / t) ^ 2) ((t / s) ^ 2) - 1 ∧
        max ((s / t) ^ 2) ((t / s) ^ 2) - 1 ≤
          (2 * max b 0 / a ^ 2) * |s - t| := by
    rcases le_total s t with hst | hts
    · exact max_sq_ratio_sub_one_le_of_le ha hs ht hst
    · have h := max_sq_ratio_sub_one_le_of_le ha ht hs hts
      simpa only [max_comm ((t / s) ^ 2) ((s / t) ^ 2), abs_sub_comm t s] using h
  have hside (u v : ℝ)
      (huv : u ≤ max ((s / t) ^ 2) ((t / s) ^ 2) * v) (hv : v ≤ U) :
      u - v ≤ ((2 * max b 0 / a ^ 2) * U) * |s - t| := by
    calc
      u - v ≤ (max ((s / t) ^ 2) ((t / s) ^ 2) - 1) * v := by nlinarith
      _ ≤ (max ((s / t) ^ 2) ((t / s) ^ 2) - 1) * U :=
        mul_le_mul_of_nonneg_left hv hratio.1
      _ ≤ ((2 * max b 0 / a ^ 2) * |s - t|) * U :=
        mul_le_mul_of_nonneg_right hratio.2 hU
      _ = ((2 * max b 0 / a ^ 2) * U) * |s - t| := by ring
  exact abs_sub_le_iff.mpr ⟨hside x y hxy hy, hside y x hyx hx⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancient_abs_redLength_sub_le_mul_abs_sub_of_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p q : F.M)
    {a b s t U : ℝ} (ha : 0 < a) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hU : 0 ≤ U) (hsbound : redLength F.S 0 p q s ≤ U)
    (htbound : redLength F.S 0 p q t ≤ U) :
    |redLength F.S 0 p q s - redLength F.S 0 p q t| ≤
      ((2 * max b 0 / a ^ 2) * U) * |s - t| := by
  apply abs_sub_le_of_max_sq_ratio ha hs ht hU hsbound htbound
  · exact ancient_redLength_le_mul_time_ratio F hF p q
      (ha.trans_le ht.1) (ha.trans_le hs.1)
  · have h := ancient_redLength_le_mul_time_ratio F hF p q
      (ha.trans_le hs.1) (ha.trans_le ht.1)
    simpa only [max_comm ((t / s) ^ 2) ((s / t) ^ 2)] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
