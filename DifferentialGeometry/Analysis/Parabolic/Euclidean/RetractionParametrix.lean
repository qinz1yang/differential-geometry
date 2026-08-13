import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp
noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]

variable
    {J₂ J₁₀ : Type*}
    [NormedAddCommGroup J₂] [NormedSpace ℝ J₂]
    [NormedAddCommGroup J₁₀] [NormedSpace ℝ J₁₀]

def localParametrix
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U) (R : U →L[ℝ] X) : Y →L[ℝ] X :=
  R.comp (H.comp E)

def localErrorArm
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U) (C : U →L[ℝ] Y) : Y →L[ℝ] Y :=
  C.comp (H.comp E)

def principalError
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₂ : U →L[ℝ] J₂) (C₂ : J₂ →L[ℝ] Y) : Y →L[ℝ] Y :=
  C₂.comp (D₂.comp (H.comp E))

def lowerError
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₁₀ : U →L[ℝ] J₁₀) (C₁₀ : J₁₀ →L[ℝ] Y) : Y →L[ℝ] Y :=
  C₁₀.comp (D₁₀.comp (H.comp E))

def factoredError
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₂ : U →L[ℝ] J₂) (C₂ : J₂ →L[ℝ] Y)
    (D₁₀ : U →L[ℝ] J₁₀) (C₁₀ : J₁₀ →L[ℝ] Y) : Y →L[ℝ] Y :=
  principalError E H D₂ C₂ + lowerError E H D₁₀ C₁₀

theorem principalError_norm
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₂ : U →L[ℝ] J₂) (C₂ : J₂ →L[ℝ] Y) :
    ‖principalError E H D₂ C₂‖ ≤
      ‖C₂‖ * ‖D₂.comp (H.comp E)‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

theorem principalError_le
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₂ : U →L[ℝ] J₂) (C₂ : J₂ →L[ℝ] Y)
    {δ₂ K₂ : ℝ} (hδ₂ : 0 ≤ δ₂)
    (hC₂ : ‖C₂‖ ≤ δ₂) (hD₂ : ‖D₂.comp (H.comp E)‖ ≤ K₂) :
    ‖principalError E H D₂ C₂‖ ≤ δ₂ * K₂ := by
  refine (principalError_norm E H D₂ C₂).trans ?_
  exact mul_le_mul hC₂ hD₂ (norm_nonneg _) hδ₂

theorem lowerError_norm
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₁₀ : U →L[ℝ] J₁₀) (C₁₀ : J₁₀ →L[ℝ] Y) :
    ‖lowerError E H D₁₀ C₁₀‖ ≤
      ‖C₁₀‖ * ‖D₁₀.comp (H.comp E)‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

theorem lowerError_le
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₁₀ : U →L[ℝ] J₁₀) (C₁₀ : J₁₀ →L[ℝ] Y)
    {δ₁₀ K₁₀ : ℝ} (hδ₁₀ : 0 ≤ δ₁₀)
    (hC₁₀ : ‖C₁₀‖ ≤ δ₁₀) (hD₁₀ : ‖D₁₀.comp (H.comp E)‖ ≤ K₁₀) :
    ‖lowerError E H D₁₀ C₁₀‖ ≤ δ₁₀ * K₁₀ := by
  refine (lowerError_norm E H D₁₀ C₁₀).trans ?_
  exact mul_le_mul hC₁₀ hD₁₀ (norm_nonneg _) hδ₁₀

theorem factoredError_norm
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₂ : U →L[ℝ] J₂) (C₂ : J₂ →L[ℝ] Y)
    (D₁₀ : U →L[ℝ] J₁₀) (C₁₀ : J₁₀ →L[ℝ] Y) :
    ‖factoredError E H D₂ C₂ D₁₀ C₁₀‖ ≤
      ‖C₂‖ * ‖D₂.comp (H.comp E)‖ +
        ‖C₁₀‖ * ‖D₁₀.comp (H.comp E)‖ := by
  rw [factoredError]
  exact (norm_add_le _ _).trans
    (add_le_add (principalError_norm E H D₂ C₂)
      (lowerError_norm E H D₁₀ C₁₀))

theorem factoredError_le
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₂ : U →L[ℝ] J₂) (C₂ : J₂ →L[ℝ] Y)
    (D₁₀ : U →L[ℝ] J₁₀) (C₁₀ : J₁₀ →L[ℝ] Y)
    {δ₂ K₂ δ₁₀ K₁₀ : ℝ} (hδ₂ : 0 ≤ δ₂) (hδ₁₀ : 0 ≤ δ₁₀)
    (hC₂ : ‖C₂‖ ≤ δ₂) (hD₂ : ‖D₂.comp (H.comp E)‖ ≤ K₂)
    (hC₁₀ : ‖C₁₀‖ ≤ δ₁₀) (hD₁₀ : ‖D₁₀.comp (H.comp E)‖ ≤ K₁₀) :
    ‖factoredError E H D₂ C₂ D₁₀ C₁₀‖ ≤
      δ₂ * K₂ + δ₁₀ * K₁₀ := by
  rw [factoredError]
  exact (norm_add_le _ _).trans
    (add_le_add
      (principalError_le E H D₂ C₂ hδ₂ hC₂ hD₂)
      (lowerError_le E H D₁₀ C₁₀ hδ₁₀ hC₁₀ hD₁₀))

def lowerTime (C K : ℝ) : ℝ :=
  min 1 ((1 / (8 * (C + 1) * (K + 1))) ^ 2)
theorem lowerTime_pos {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 < lowerTime C K := by
  have hCp : 0 < C + 1 := by linarith
  have hKp : 0 < K + 1 := by linarith
  have hden : 0 < (8 : ℝ) * (C + 1) * (K + 1) :=
    mul_pos (mul_pos (by norm_num) hCp) hKp
  rw [lowerTime]
  exact lt_min one_pos (pow_pos (one_div_pos.mpr hden) 2)

theorem lowerTime_le_one (C K : ℝ) : lowerTime C K ≤ 1 :=
  min_le_left _ _

theorem lowerTime_small {C K τ : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hτ : τ ≤ lowerTime C K) :
    C * (K * Real.sqrt τ) < (1 : ℝ) / 4 := by
  have hCp : 0 < C + 1 := by linarith
  have hKp : 0 < K + 1 := by linarith
  have hden : 0 < (8 : ℝ) * (C + 1) * (K + 1) :=
    mul_pos (mul_pos (by norm_num) hCp) hKp
  have hbase : 0 ≤ 1 / (8 * (C + 1) * (K + 1)) :=
    (one_div_pos.mpr hden).le
  have hτsq : τ ≤ (1 / (8 * (C + 1) * (K + 1))) ^ 2 :=
    hτ.trans (min_le_right _ _)
  have hsqrt : Real.sqrt τ ≤ 1 / (8 * (C + 1) * (K + 1)) := by
    calc
      Real.sqrt τ ≤ Real.sqrt
          ((1 / (8 * (C + 1) * (K + 1))) ^ 2) :=
        Real.sqrt_le_sqrt hτsq
      _ = 1 / (8 * (C + 1) * (K + 1)) :=
        Real.sqrt_sq hbase
  calc
    C * (K * Real.sqrt τ) = (C * K) * Real.sqrt τ := by ring
    _ ≤ (C * K) * (1 / (8 * (C + 1) * (K + 1))) :=
      mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hC hK)
    _ = (C * K) / (8 * (C + 1) * (K + 1)) := by ring
    _ < (1 : ℝ) / 4 := by
      rw [div_lt_iff₀ hden]
      nlinarith

theorem b10Error_quarter
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₁₀ : U →L[ℝ] J₁₀) (C₁₀ : J₁₀ →L[ℝ] Y)
    {C K τ : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hτ : τ ≤ lowerTime C K)
    (hC₁₀ : ‖C₁₀‖ ≤ C)
    (hD₁₀ : ‖D₁₀.comp (H.comp E)‖ ≤ K * Real.sqrt τ) :
    ‖lowerError E H D₁₀ C₁₀‖ < (1 : ℝ) / 4 := by
  exact (lowerError_le E H D₁₀ C₁₀ hC hC₁₀ hD₁₀).trans_lt
    (lowerTime_small hC hK hτ)

theorem fixedReassemble_dt
    (R : U →L[ℝ] X) {u : ℝ → U} {u' : U} {t : ℝ}
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => R (u s)) (R u') t :=
  R.hasFDerivAt.comp_hasDerivAt t hu

theorem fixedExtract_dt
    (E : X →L[ℝ] U) {u : ℝ → X} {u' : X} {t : ℝ}
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => E (u s)) (E u') t :=
  E.hasFDerivAt.comp_hasDerivAt t hu

def chartProjection (E : X →L[ℝ] U) (R : U →L[ℝ] X) : U →L[ℝ] U :=
  E.comp R

theorem chartProjection_idem
    (E : X →L[ℝ] U) (R : U →L[ℝ] X)
    (hRE : R.comp E = ContinuousLinearMap.id ℝ X) :
    (chartProjection E R).comp (chartProjection E R) =
      chartProjection E R := by
  ext u
  simp only [chartProjection, ContinuousLinearMap.comp_apply]
  have h := congrArg (fun A : X →L[ℝ] X => A (R u)) hRE
  apply congrArg (fun x : X => E x)
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

theorem retractParametrix
    (T : X →L[ℝ] Y) (R : U →L[ℝ] X)
    (E : Y →L[ℝ] V) (RF : V →L[ℝ] Y)
    (L : U →L[ℝ] V) (H : V →L[ℝ] U) (C : U →L[ℝ] Y)
    (hTR : T.comp R = RF.comp L + C)
    (hLH : L.comp H = ContinuousLinearMap.id ℝ V)
    (hRE : RF.comp E = ContinuousLinearMap.id ℝ Y) :
    T.comp (localParametrix E H R) =
      ContinuousLinearMap.id ℝ Y + localErrorArm E H C := by
  ext y
  have hTRy := congrArg (fun A : U →L[ℝ] Y => A (H (E y))) hTR
  have hLHy := congrArg (fun A : V →L[ℝ] V => A (E y)) hLH
  have hREy := congrArg (fun A : Y →L[ℝ] Y => A y) hRE
  simp only [localParametrix, localErrorArm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] at hTRy
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hLHy hREy
  rw [hTRy, hLHy, hREy]

theorem retractParam_split
    (T : X →L[ℝ] Y) (R : U →L[ℝ] X)
    (E : Y →L[ℝ] V) (RF : V →L[ℝ] Y)
    (L : U →L[ℝ] V) (H : V →L[ℝ] U)
    (C₂ C₁₀ : U →L[ℝ] Y)
    (hTR : T.comp R = RF.comp L + C₂ + C₁₀)
    (hLH : L.comp H = ContinuousLinearMap.id ℝ V)
    (hRE : RF.comp E = ContinuousLinearMap.id ℝ Y) :
    T.comp (localParametrix E H R) =
      ContinuousLinearMap.id ℝ Y + localErrorArm E H C₂ +
        localErrorArm E H C₁₀ := by
  ext y
  have hTRy := congrArg (fun A : U →L[ℝ] Y => A (H (E y))) hTR
  have hLHy := congrArg (fun A : V →L[ℝ] V => A (E y)) hLH
  have hREy := congrArg (fun A : Y →L[ℝ] Y => A y) hRE
  simp only [localParametrix, localErrorArm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] at hTRy
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hLHy hREy
  rw [hTRy, hLHy, hREy]

theorem retractParam_factor
    (T : X →L[ℝ] Y) (R : U →L[ℝ] X)
    (E : Y →L[ℝ] V) (RF : V →L[ℝ] Y)
    (L : U →L[ℝ] V) (H : V →L[ℝ] U)
    (D₂ : U →L[ℝ] J₂) (C₂ : J₂ →L[ℝ] Y)
    (D₁₀ : U →L[ℝ] J₁₀) (C₁₀ : J₁₀ →L[ℝ] Y)
    (hTR : T.comp R = RF.comp L + C₂.comp D₂ + C₁₀.comp D₁₀)
    (hLH : L.comp H = ContinuousLinearMap.id ℝ V)
    (hRE : RF.comp E = ContinuousLinearMap.id ℝ Y) :
    T.comp (localParametrix E H R) =
      ContinuousLinearMap.id ℝ Y +
        factoredError E H D₂ C₂ D₁₀ C₁₀ := by
  have h := retractParam_split T R E RF L H
    (C₂.comp D₂) (C₁₀.comp D₁₀) hTR hLH hRE
  simpa only [factoredError, principalError, lowerError, localErrorArm,
    ContinuousLinearMap.comp_assoc, add_assoc] using h
def parametrixError (T : X →L[ℝ] Y) (Q : Y →L[ℝ] X) : Y →L[ℝ] Y :=
  T.comp Q - ContinuousLinearMap.id ℝ Y

theorem parametrixError_id (T : X →L[ℝ] Y) (Q : Y →L[ℝ] X) :
    T.comp Q = ContinuousLinearMap.id ℝ Y + parametrixError T Q := by
  simp only [parametrixError]
  abel

end DifferentialGeometry.Analysis.Parabolic.Euclidean
