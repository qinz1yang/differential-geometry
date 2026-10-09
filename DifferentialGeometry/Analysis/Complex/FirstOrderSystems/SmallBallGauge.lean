import DifferentialGeometry.Analysis.Complex.CauchyTransform.FixedPoint
import DifferentialGeometry.Analysis.Schauder.Holder.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Analysis

private theorem holderWith_half_of_norm_sub_le
    {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {f : X → F} (K : ℝ≥0)
    (h : ∀ x y, ‖f x - f y‖ ≤ (K : ℝ) * Real.sqrt (dist x y)) :
    HolderWith K (1 / 2 : ℝ≥0) f := by
  intro x y
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist (f x) (f y)) ≤
    (K : ENNReal) * ENNReal.ofReal (dist x y) ^ (1 / 2 : ℝ)
  have hreal : dist (f x) (f y) ≤ (K : ℝ) * dist x y ^ (1 / 2 : ℝ) := by
    rw [dist_eq_norm, ← Real.sqrt_eq_rpow]
    exact h x y
  calc
    ENNReal.ofReal (dist (f x) (f y)) ≤
        ENNReal.ofReal ((K : ℝ) * dist x y ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (K : ENNReal) * ENNReal.ofReal (dist x y ^ (1 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    _ = (K : ENNReal) * ENNReal.ofReal (dist x y) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V]

/-- A locally `C¹` coefficient gives a unit integral gauge on a buffered smaller disk.
The Hölder estimate and ambient integral representative use the same constructed gauge. -/
theorem exists_small_ball_unit_integral_gauge
    {s : Set ℂ} (hs : IsOpen s) {a : ℂ} (ha : a ∈ s)
    (A : ℂ → V →L[ℂ] V) (hA : ContDiffOn ℝ 1 A s) :
    ∃ (R : ℝ) (hR : 0 < R),
      closedBall a (2 * R) ⊆ s ∧
      ∃ A_R : C(closedBall a R, V →L[ℂ] V),
        (∀ z : closedBall a R, A_R z = A (z : ℂ)) ∧
        4 * R * ‖A_R‖ < (1 / 4 : ℝ) ∧
        ∃ P : C(closedBall a R, V →L[ℂ] V),
          P = 1 + diskCauchyTransform a R hR (A_R * P) ∧
          ‖P - 1‖ ≤ (4 * R * ‖A_R‖) / (1 - 4 * R * ‖A_R‖) ∧
          ‖P‖ ≤ 2 ∧
          (∀ z : closedBall a R, IsUnit (P z)) ∧
          (∀ z w : closedBall a R,
            ‖P z - P w‖ ≤
              16 * Real.sqrt R * ‖A_R * P‖ *
                Real.sqrt ‖(z : ℂ) - (w : ℂ)‖) ∧
          (∃ H : ℝ≥0,
            HolderWith H (1 / 2 : ℝ≥0)
              (fun z : closedBall a R => A_R z * P z)) ∧
          (let P₀ : ℂ → V →L[ℂ] V := fun z =>
            1 + (Real.pi : ℂ)⁻¹ •
              ∫ w : closedBall a R,
                (z - (w : ℂ))⁻¹ • (A_R w * P w)
                ∂(volume.comap ((↑) : closedBall a R → ℂ))
           (∀ z : closedBall a R, P₀ (z : ℂ) = P z) ∧
             ∀ z ∈ closedBall a R, IsUnit (P₀ z)) := by
  obtain ⟨ρ, hρ, hρs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds ha)
  let A_big : C(closedBall a ρ, V →L[ℂ] V) :=
    ⟨fun z => A (z : ℂ), (hA.continuousOn.mono hρs).domRestrict⟩
  let M : ℝ := ‖A_big‖
  have hM : 0 ≤ M := norm_nonneg _
  let R : ℝ := min (ρ / 2) (1 / (16 * (M + 1)))
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRhalf : R ≤ ρ / 2 := min_le_left _ _
  have hRρ : R ≤ ρ := by linarith
  have hbuffer : closedBall a (2 * R) ⊆ s :=
    (closedBall_subset_closedBall (by linarith : 2 * R ≤ ρ)).trans hρs
  have hsmall : closedBall a R ⊆ closedBall a ρ := closedBall_subset_closedBall hRρ
  let A_R : C(closedBall a R, V →L[ℂ] V) :=
    ⟨fun z => A (z : ℂ), (hA.continuousOn.mono (hsmall.trans hρs)).domRestrict⟩
  have hnormA : ‖A_R‖ ≤ M := by
    apply (ContinuousMap.norm_le _ hM).mpr
    intro z
    exact A_big.norm_coe_le_norm ⟨z, hsmall z.property⟩
  have hRbound : R * (16 * (M + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (M + 1))).mp (min_le_right _ _)
  have hk : 4 * R * ‖A_R‖ < (1 / 4 : ℝ) := by
    have hle := mul_le_mul_of_nonneg_left hnormA (by positivity : 0 ≤ 4 * R)
    nlinarith
  obtain ⟨P, hP, hnear, hunit, hintegral⟩ :=
    CauchyTransform.exists_unit_integral_fixedPoint a R hR A_R (by linarith)
  have hI : ‖(1 : C(closedBall a R, V →L[ℂ] V))‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro z
    exact ContinuousLinearMap.norm_id_le
  have hnear_one : ‖P - 1‖ < 1 := by
    apply hnear.trans_lt
    apply (div_lt_one (by linarith : 0 < 1 - 4 * R * ‖A_R‖)).mpr
    linarith
  have hnormP : ‖P‖ ≤ 2 := by
    have htriangle : ‖P‖ ≤ ‖P - 1‖ + 1 := by
      calc
        _ = ‖(P - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖P - 1‖ + ‖(1 : C(closedBall a R, V →L[ℂ] V))‖ := norm_add_le _ _
        _ ≤ _ := add_le_add le_rfl hI
    linarith
  have hPdiff (z w : closedBall a R) :
      ‖P z - P w‖ ≤ 16 * Real.sqrt R * ‖A_R * P‖ *
        Real.sqrt ‖(z : ℂ) - (w : ℂ)‖ := by
    have hz := congrArg (fun Q : C(closedBall a R, V →L[ℂ] V) => Q z) hP
    have hw := congrArg (fun Q : C(closedBall a R, V →L[ℂ] V) => Q w) hP
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply] at hz hw
    rw [hz, hw, add_sub_add_left_eq_sub]
    exact diskCauchyTransform_sub_le a R hR (A_R * P) z w
  obtain ⟨K, hK⟩ := (hA.mono hρs).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall a ρ) (isCompact_closedBall a ρ)
  have hAlip : LipschitzWith K (fun z : closedBall a R => A_R z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    exact hK.dist_le_mul z (hsmall z.property) w (hsmall w.property)
  let Mnn : ℝ≥0 := ⟨M, hM⟩
  have hAbound (z : closedBall a R) : ‖A_R z‖ ≤ Mnn :=
    (A_R.norm_coe_le_norm z).trans hnormA
  have hAholder : HolderWith (max (2 * Mnn) K) (1 / 2 : ℝ≥0)
      (fun z : closedBall a R => A_R z) :=
    (Schauder.holderWith_zero_of_norm_le hAbound).of_le_of_le hAlip.holderWith
      (by positivity) (by norm_num)
  let KP : ℝ≥0 := ⟨16 * Real.sqrt R * ‖A_R * P‖, by positivity⟩
  have hPholder : HolderWith KP (1 / 2 : ℝ≥0)
      (fun z : closedBall a R => P z) := by
    apply holderWith_half_of_norm_sub_le KP
    intro z w
    have hKP : (KP : ℝ) = 16 * Real.sqrt R * ‖A_R * P‖ := rfl
    change ‖P z - P w‖ ≤ (KP : ℝ) * Real.sqrt (dist z w)
    rw [hKP, Subtype.dist_eq, dist_eq_norm]
    exact hPdiff z w
  have hPbound (z : closedBall a R) : ‖P z‖ ≤ (2 : ℝ≥0) :=
    (P.norm_coe_le_norm z).trans hnormP
  have hproduct := Schauder.holderWith_bilinear_of_norm_le
    (ContinuousLinearMap.mul ℝ (V →L[ℂ] V))
    (fun B C => norm_mul_le B C) hAholder hPholder hAbound hPbound
  refine ⟨R, hR, hbuffer, A_R, (fun _ => rfl), hk, P, hP, hnear, hnormP,
    hunit, hPdiff, ⟨Mnn * KP + 2 * max (2 * Mnn) K, hproduct⟩, ?_⟩
  change (∀ z : closedBall a R,
      1 + (Real.pi : ℂ)⁻¹ • ∫ w : closedBall a R,
        ((z : ℂ) - (w : ℂ))⁻¹ • (A_R w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ)) = P z) ∧ _
  refine ⟨fun z => (hintegral z).symm, ?_⟩
  intro z hz
  exact (congrArg (fun B : V →L[ℂ] V => IsUnit B)
    (hintegral ⟨z, hz⟩)).mp (hunit ⟨z, hz⟩)

end DifferentialGeometry.Analysis
