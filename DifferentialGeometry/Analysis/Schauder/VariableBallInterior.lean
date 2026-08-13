import DifferentialGeometry.Analysis.Schauder.BallCutoffHessian
import DifferentialGeometry.Analysis.Schauder.VariableInterior

noncomputable section

open Real Set
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def variableBallCutoffSourceSupConst
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (A : n → n → NNReal)
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) : NNReal :=
  variableCutoffSourceSupConst A
    ‖ballCutoffFDerivBcf center hr hrR‖₊ ‖du‖₊
    (Real.toNNReal (ballCutoffFDeriv2Bound r R)) ‖u‖₊
    (ballCutoffBcf center hr hrR) f

def variableBallCutoffSourceHolderConst
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (A Ka : n → n → NNReal) (Kf Kdu Kd2chi Ku : NNReal)
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) : NNReal :=
  variableCutoffSourceHolderConst A Ka
    (ballCutoffHolderConst r R) Kf
    (ballCutoffFDerivHolderConst r R) Kdu Kd2chi Ku
    ‖ballCutoffFDerivBcf center hr hrR‖₊ ‖du‖₊
    (Real.toNNReal (ballCutoffFDeriv2Bound r R)) ‖u‖₊
    (ballCutoffBcf center hr hrR) f

def variableBallInteriorSchauderConst
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (alpha : NNReal) (A Ka omega : n → n → NNReal)
    (Kf Kdu Kd2chi Ku : NNReal)
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) : NNReal :=
  (spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
      (variableBallCutoffSourceHolderConst center hr hrR
        A Ka Kf Kdu Kd2chi Ku f u du)
      (variableBallCutoffSourceSupConst center hr hrR A f u du)
      (cutoffValue (ballCutoffBcf center hr hrR) u)) /
    (1 - spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j))

theorem variable_coefficient_ball_interior_schauder_estimate_of_cutoffJet2_control
    {center : Euc n} {rho r R : Real}
    (hrho : 0 ≤ rho) (hrhor : rho < r) (hrR : r < R)
    {alpha Kf Kdu Kd2chi Ku Kd2w Md2w : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hsource : ∀ x ∈ Metric.ball center R,
      variableMatrixLap a d2u x = f x)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hfHolder : HolderWith Kf alpha (f : Euc n → F))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hd2chiHolder : HolderWith Kd2chi alpha
      (ballCutoffFDeriv2Bcf center (hrho.trans hrhor.le) hrR :
        Euc n → Euc n →L[Real] Euc n →L[Real] Real))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hd2wNorm : ∀ x,
      ‖cutoffJet2
        (ballCutoffBcf center (hrho.trans hrhor.le) hrR)
        (ballCutoffFDerivBcf center (hrho.trans hrhor.le) hrR)
        (ballCutoffFDeriv2Bcf center (hrho.trans hrhor.le) hrR)
        u du d2u x‖ ≤ Md2w)
    (hd2wHolder : HolderWith Kd2w alpha
      (cutoffJet2
        (ballCutoffBcf center (hrho.trans hrhor.le) hrR)
        (ballCutoffFDerivBcf center (hrho.trans hrhor.le) hrR)
        (ballCutoffFDeriv2Bcf center (hrho.trans hrhor.le) hrR)
        u du d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha (Metric.closedBall center rho)
        (u : Euc n → F) ≤
      variableBallInteriorSchauderConst center (hrho.trans hrhor.le) hrR
        a x0 hA alpha (fun i j ↦ ‖a i j‖₊) Ka omega
        Kf Kdu Kd2chi Ku f u du := by
  let hr : 0 ≤ r := hrho.trans hrhor.le
  let chi := ballCutoffBcf center hr hrR
  let dchi := ballCutoffFDerivBcf center hr hrR
  let d2chi := ballCutoffFDeriv2Bcf center hr hrR
  have hsU : Metric.closedBall center rho ⊆ Metric.ball center r := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hrhor)
  have hchiOne : ∀ x ∈ Metric.ball center r, chi x = 1 := by
    intro x hx
    exact ballCutoff_eq_one_of_mem_closedBall hr hrR
      (Metric.ball_subset_closedBall hx)
  have hchi : ∀ x, HasFDerivAt (chi : Euc n → Real) (dchi x) x :=
    hasFDerivAt_ballCutoff center r R
  have hdchi : ∀ x,
      HasFDerivAt (dchi : Euc n → Euc n →L[Real] Real) (d2chi x) x :=
    hasFDerivAt_ballCutoffFDeriv center r R
  have hsource' : ∀ x, chi x ≠ 0 → variableMatrixLap a d2u x = f x := by
    intro x hx
    apply hsource x
    by_contra hxball
    exact hx (ballCutoff_eq_zero_of_not_mem_ball hr hrR hxball)
  apply variable_coefficient_interior_schauder_estimate_of_cutoffJet2_control
    (s := Metric.closedBall center rho) (U := Metric.ball center r)
    (Kchi := ballCutoffHolderConst r R)
    (Kdchi := ballCutoffFDerivHolderConst r R)
    (Mdchi := ‖dchi‖₊) (Mdu := ‖du‖₊)
    (Md2chi := Real.toNNReal (ballCutoffFDeriv2Bound r R)) (Mu := ‖u‖₊)
    Metric.isOpen_ball hsU halpha0 halpha1 a x0 hA chi dchi d2chi
    f u du d2u hchiOne hchi hdchi hu hdu hsource'
    (fun i j ↦ ‖a i j‖₊) Ka omega ha homega
  · exact fun i j x ↦ by simpa using (a i j).norm_coe_le_norm x
  · exact ballCutoff_holderWith hr hrR halpha0.le halpha1.le
  · exact hfHolder
  · exact ballCutoffFDeriv_holderWith hr hrR halpha0.le halpha1.le
  · exact hduHolder
  · exact hd2chiHolder
  · exact huHolder
  · exact fun x ↦ by simpa using dchi.norm_coe_le_norm x
  · exact fun x ↦ by simpa using du.norm_coe_le_norm x
  · intro x
    change ‖ballCutoffFDeriv2 center r R x‖ ≤
      (Real.toNNReal (ballCutoffFDeriv2Bound r R) : Real)
    rw [Real.coe_toNNReal _ (ballCutoffFDeriv2Bound_nonneg hr hrR)]
    exact norm_ballCutoffFDeriv2_le hr hrR x
  · exact fun x ↦ by simpa using u.norm_coe_le_norm x
  · exact hd2wNorm
  · exact hd2wHolder
  · exact hsmall

theorem variable_coefficient_ball_interior_schauder_estimate_of_global_small_coefficient_oscillation
    {center : Euc n} {rho r R : Real}
    (hrho : 0 ≤ rho) (hrhor : rho < r) (hrR : r < R)
    {alpha Kf Kdu Ku Kd2u Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hsource : ∀ x ∈ Metric.ball center R,
      variableMatrixLap a d2u x = f x)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hfHolder : HolderWith Kf alpha (f : Euc n → F))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2uNorm : ∀ x, ‖d2u x‖ ≤ Md2u)
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha (Metric.closedBall center rho)
        (u : Euc n → F) ≤
      variableBallInteriorSchauderConst center (hrho.trans hrhor.le) hrR
        a x0 hA alpha (fun i j ↦ ‖a i j‖₊) Ka omega Kf Kdu
        (ballCutoffFDeriv2HolderConst center (hrho.trans hrhor.le) hrR)
        Ku f u du := by
  let hr : 0 ≤ r := hrho.trans hrhor.le
  let chi := ballCutoffBcf center hr hrR
  let dchi := ballCutoffFDerivBcf center hr hrR
  let d2chi := ballCutoffFDeriv2Bcf center hr hrR
  let Kchi := ballCutoffHolderConst r R
  let Kdchi := ballCutoffFDerivHolderConst r R
  let Kd2chi := ballCutoffFDeriv2HolderConst center hr hrR
  let Mdchi := ‖dchi‖₊
  let Md2chi := Real.toNNReal (ballCutoffFDeriv2Bound r R)
  let Kd2w := cutoffJet2HolderConst
    Kchi Kdchi Kd2chi Ku Kdu Kd2u
    1 Mdchi Md2chi ‖u‖₊ ‖du‖₊ Md2u
  let Md2w := cutoffJet2SupConst 1 Mdchi Md2chi ‖u‖₊ ‖du‖₊ Md2u
  have hchiNorm : ∀ x, ‖chi x‖ ≤ (1 : NNReal) := by
    intro x
    rw [show chi x = ballCutoff center r R x from rfl, Real.norm_eq_abs,
      abs_of_nonneg (ballCutoff_mem_Icc center r R x).1]
    exact_mod_cast (ballCutoff_mem_Icc center r R x).2
  have hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi :=
    fun x ↦ by simpa only [Mdchi] using dchi.norm_coe_le_norm x
  have hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi := by
    intro x
    change ‖ballCutoffFDeriv2 center r R x‖ ≤
      (Real.toNNReal (ballCutoffFDeriv2Bound r R) : Real)
    rw [Real.coe_toNNReal _ (ballCutoffFDeriv2Bound_nonneg hr hrR)]
    exact norm_ballCutoffFDeriv2_le hr hrR x
  have huNorm : ∀ x, ‖u x‖ ≤ ‖u‖₊ :=
    fun x ↦ by simpa using u.norm_coe_le_norm x
  have hduNorm : ∀ x, ‖du x‖ ≤ ‖du‖₊ :=
    fun x ↦ by simpa using du.norm_coe_le_norm x
  apply variable_coefficient_ball_interior_schauder_estimate_of_cutoffJet2_control
    (Kd2chi := Kd2chi) (Kd2w := Kd2w) (Md2w := Md2w)
    hrho hrhor hrR halpha0 halpha1 a x0 hA f u du d2u hu hdu hsource
    Ka omega ha homega hfHolder hduHolder
  · exact ballCutoffFDeriv2_holderWith hr hrR halpha0.le halpha1.le
  · exact huHolder
  · exact fun x ↦ norm_cutoffJet2_le chi dchi d2chi u du d2u
      1 Mdchi Md2chi ‖u‖₊ ‖du‖₊ Md2u hchiNorm hdchiNorm hd2chiNorm
      huNorm hduNorm hd2uNorm x
  · exact cutoffJet2_holderWith chi dchi d2chi u du d2u
      (ballCutoff_holderWith hr hrR halpha0.le halpha1.le)
      (ballCutoffFDeriv_holderWith hr hrR halpha0.le halpha1.le)
      (ballCutoffFDeriv2_holderWith hr hrR halpha0.le halpha1.le)
      huHolder hduHolder hd2uHolder hchiNorm hdchiNorm hd2chiNorm
      huNorm hduNorm hd2uNorm
  · exact hsmall

theorem variable_coefficient_ball_interior_schauder_estimate_of_coefficient_oscillation
    {center : Euc n} {rho r R : Real}
    (hrho : 0 ≤ rho) (hrhor : rho < r) (hrR : r < R)
    {alpha Kf Kdu Ku Kd2u Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (hA : Matrix.PosDef (fun i j ↦ a i j center))
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hsource : ∀ x ∈ Metric.ball center R,
      variableMatrixLap a d2u x = f x)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((Metric.ball center R).restrict (a i j : Euc n → Real)))
    (homega : ∀ i j x, x ∈ Metric.ball center R →
      ‖a i j center - a i j x‖ ≤ omega i j)
    (haNorm : ∀ i j x, x ∈ Metric.ball center R →
      ‖a i j x‖ ≤ A i j)
    (hfHolder : HolderWith Kf alpha (f : Euc n → F))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2uNorm : ∀ x, ‖d2u x‖ ≤ Md2u)
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j center) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha (Metric.closedBall center rho)
        (u : Euc n → F) ≤
      variableBallInteriorSchauderConst center (hrho.trans hrhor.le) hrR
        a center hA alpha A Ka omega Kf Kdu
        (ballCutoffFDeriv2HolderConst center (hrho.trans hrhor.le) hrR)
        Ku f u du := by
  let hr : 0 ≤ r := hrho.trans hrhor.le
  let chi := ballCutoffBcf center hr hrR
  let dchi := ballCutoffFDerivBcf center hr hrR
  let d2chi := ballCutoffFDeriv2Bcf center hr hrR
  let Kchi := ballCutoffHolderConst r R
  let Kdchi := ballCutoffFDerivHolderConst r R
  let Kd2chi := ballCutoffFDeriv2HolderConst center hr hrR
  let Mdchi := ‖dchi‖₊
  let Md2chi := Real.toNNReal (ballCutoffFDeriv2Bound r R)
  let Kd2w := cutoffJet2HolderConst
    Kchi Kdchi Kd2chi Ku Kdu Kd2u
    1 Mdchi Md2chi ‖u‖₊ ‖du‖₊ Md2u
  let Md2w := cutoffJet2SupConst 1 Mdchi Md2chi ‖u‖₊ ‖du‖₊ Md2u
  have hsU : Metric.closedBall center rho ⊆ Metric.ball center r := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hrhor)
  have hchiOne : ∀ x ∈ Metric.ball center r, chi x = 1 := by
    intro x hx
    exact ballCutoff_eq_one_of_mem_closedBall hr hrR
      (Metric.ball_subset_closedBall hx)
  have hchi : ∀ x, HasFDerivAt (chi : Euc n → Real) (dchi x) x :=
    hasFDerivAt_ballCutoff center r R
  have hdchi : ∀ x,
      HasFDerivAt (dchi : Euc n → Euc n →L[Real] Real) (d2chi x) x :=
    hasFDerivAt_ballCutoffFDeriv center r R
  have hsource' : ∀ x, chi x ≠ 0 → variableMatrixLap a d2u x = f x := by
    intro x hx
    apply hsource x
    by_contra hxball
    exact hx (ballCutoff_eq_zero_of_not_mem_ball hr hrR hxball)
  have hchiNorm : ∀ x, ‖chi x‖ ≤ (1 : NNReal) := by
    intro x
    rw [show chi x = ballCutoff center r R x from rfl, Real.norm_eq_abs,
      abs_of_nonneg (ballCutoff_mem_Icc center r R x).1]
    exact_mod_cast (ballCutoff_mem_Icc center r R x).2
  have hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi :=
    fun x ↦ by simpa only [Mdchi] using dchi.norm_coe_le_norm x
  have hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi := by
    intro x
    change ‖ballCutoffFDeriv2 center r R x‖ ≤
      (Real.toNNReal (ballCutoffFDeriv2Bound r R) : Real)
    rw [Real.coe_toNNReal _ (ballCutoffFDeriv2Bound_nonneg hr hrR)]
    exact norm_ballCutoffFDeriv2_le hr hrR x
  have huNorm : ∀ x, ‖u x‖ ≤ ‖u‖₊ :=
    fun x ↦ by simpa using u.norm_coe_le_norm x
  have hduNorm : ∀ x, ‖du x‖ ≤ ‖du‖₊ :=
    fun x ↦ by simpa using du.norm_coe_le_norm x
  have hchiSupport : ∀ x, x ∉ Metric.ball center R → chi x = 0 := by
    intro x hx
    exact ballCutoff_eq_zero_of_not_mem_ball hr hrR hx
  have hdchiSupport : ∀ x, x ∉ Metric.ball center R → dchi x = 0 := by
    intro x hx
    exact ballCutoffFDeriv_eq_zero_of_not_mem_ball hr hrR hx
  have hd2chiSupport : ∀ x, x ∉ Metric.ball center R → d2chi x = 0 := by
    intro x hx
    exact ballCutoffFDeriv2_eq_zero_of_not_mem_ball hr hrR hx
  apply variable_coefficient_interior_schauder_estimate_of_cutoffJet2_control_on
    (s := Metric.closedBall center rho) (U := Metric.ball center r)
    (Kchi := Kchi) (Kdchi := Kdchi) (Kd2chi := Kd2chi)
    (Mdchi := Mdchi) (Mdu := ‖du‖₊) (Md2chi := Md2chi) (Mu := ‖u‖₊)
    (Kd2w := Kd2w) (Md2w := Md2w)
    Metric.isOpen_ball hsU (Metric.ball center R) halpha0 halpha1
    a center hA chi dchi d2chi f u du d2u hchiOne hchi hdchi hu hdu
    hsource' A Ka omega ha homega haNorm
  · exact ballCutoff_holderWith hr hrR halpha0.le halpha1.le
  · exact hfHolder
  · exact ballCutoffFDeriv_holderWith hr hrR halpha0.le halpha1.le
  · exact hduHolder
  · exact ballCutoffFDeriv2_holderWith hr hrR halpha0.le halpha1.le
  · exact huHolder
  · exact hdchiNorm
  · exact hduNorm
  · exact hd2chiNorm
  · exact huNorm
  · exact hchiSupport
  · exact hdchiSupport
  · exact hd2chiSupport
  · exact fun x ↦ norm_cutoffJet2_le chi dchi d2chi u du d2u
      1 Mdchi Md2chi ‖u‖₊ ‖du‖₊ Md2u hchiNorm hdchiNorm hd2chiNorm
      huNorm hduNorm hd2uNorm x
  · exact cutoffJet2_holderWith chi dchi d2chi u du d2u
      (ballCutoff_holderWith hr hrR halpha0.le halpha1.le)
      (ballCutoffFDeriv_holderWith hr hrR halpha0.le halpha1.le)
      (ballCutoffFDeriv2_holderWith hr hrR halpha0.le halpha1.le)
      huHolder hduHolder hd2uHolder hchiNorm hdchiNorm hd2chiNorm
      huNorm hduNorm hd2uNorm
  · exact hsmall

theorem variable_coefficient_ball_interior_schauder_estimate_of_small_coefficient_oscillation
    {center : Euc n} {rho r R : Real}
    (hrho : 0 ≤ rho) (hrhor : rho < r) (hrR : r < R)
    {alpha Kf Kdu Ku Kd2u Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (hA : Matrix.PosDef (fun i j ↦ a i j center))
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hsource : ∀ x ∈ Metric.ball center R,
      variableMatrixLap a d2u x = f x)
    (A Ka : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((Metric.ball center R).restrict (a i j : Euc n → Real)))
    (haNorm : ∀ i j x, x ∈ Metric.ball center R →
      ‖a i j x‖ ≤ A i j)
    (hfHolder : HolderWith Kf alpha (f : Euc n → F))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2uNorm : ∀ x, ‖d2u x‖ ≤ Md2u)
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j center) hA alpha
        (∑ i, ∑ j,
          (holderBallOscillationConst R alpha (Ka i j) + Ka i j))
        (∑ i, ∑ j, holderBallOscillationConst R alpha (Ka i j)) < 1) :
    eContDiffHolderGaugeOn 2 alpha (Metric.closedBall center rho)
        (u : Euc n → F) ≤
      variableBallInteriorSchauderConst center (hrho.trans hrhor.le) hrR
        a center hA alpha A Ka
        (fun i j ↦ holderBallOscillationConst R alpha (Ka i j))
        Kf Kdu
        (ballCutoffFDeriv2HolderConst center (hrho.trans hrhor.le) hrR)
        Ku f u du := by
  have hR : 0 < R := (hrho.trans_lt hrhor).trans hrR
  apply variable_coefficient_ball_interior_schauder_estimate_of_coefficient_oscillation
    hrho hrhor hrR halpha0 halpha1 a hA f u du d2u hu hdu hsource
    A Ka (fun i j ↦ holderBallOscillationConst R alpha (Ka i j)) ha
  · exact fun i j x hx ↦
      norm_sub_le_holderBallOscillationConst_of_mem_ball hR (ha i j) hx
  · exact haNorm
  · exact hfHolder
  · exact hduHolder
  · exact huHolder
  · exact hd2uHolder
  · exact hd2uNorm
  · exact hsmall

end DifferentialGeometry.Analysis.Schauder

end
