import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotentialSPD
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatSemigroupSchauder
import DifferentialGeometry.Analysis.Schauder.Absorption
import DifferentialGeometry.Analysis.Schauder.BilinearHolder
import DifferentialGeometry.Analysis.Schauder.Localization

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicHessianComponent
    (u : Real → Euc n → F) (i j : n) : ParabolicPoint (Euc n) → F :=
  fun p ↦
    hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p)
      (EuclideanSpace.basisFun n Real i)
      (EuclideanSpace.basisFun n Real j)

def parabolicVariableMatrixLap
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ matrixLap (fun i j ↦ a i j p)
    (hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p))

def parabolicFrozenMatrixLap
    (A : Matrix n n Real) (u : Real → Euc n → F) :
    ParabolicPoint (Euc n) → F :=
  fun p ↦ matrixLap A
    (hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p))

def parabolicVariableMatrixOperator
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ parabolicTimeDerivative u p - parabolicVariableMatrixLap a u p

def parabolicFrozenMatrixOperator
    (A : Matrix n n Real) (u : Real → Euc n → F) :
    ParabolicPoint (Euc n) → F :=
  fun p ↦ parabolicTimeDerivative u p - parabolicFrozenMatrixLap A u p

def parabolicMatrixLapFreezeDefect
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F) :
    ParabolicPoint (Euc n) → F :=
  fun p ↦ ∑ i, ∑ j, (a i j p0 - a i j p) • parabolicHessianComponent u i j p

def parabolicMatrixFreezeHolderConst
    (Ka omega : n → n → NNReal) : NNReal :=
  ∑ i, ∑ j, (omega i j + Ka i j)

def parabolicMatrixFreezeSupConst (omega : n → n → NNReal) : NNReal :=
  ∑ i, ∑ j, omega i j

def spdParabolicSchauderDefectConst
    (A : Matrix n n Real) (hA : A.PosDef) (alpha : NNReal)
    (Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  spdHeatPotentialSchauderConst A hA alpha
    (parabolicMatrixFreezeHolderConst Ka omega)
    (parabolicMatrixFreezeSupConst omega) T

def parabolicMatrixCoefficientRescale
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real) :
    n → n → ParabolicPoint (Euc n) → Real :=
  fun i j p ↦ a i j (parabolicDilationAt r p0 p)

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicMatrixCoefficientRescale_apply
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (i j : n) (p : ParabolicPoint (Euc n)) :
    parabolicMatrixCoefficientRescale r p0 a i j p =
      a i j (parabolicDilationAt r p0 p) := rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixCoefficientRescale_origin
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real) (i j : n) :
    parabolicMatrixCoefficientRescale r p0 a i j
        (parabolicPoint 0 0) = a i j p0 := by
  simp [parabolicMatrixCoefficientRescale]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixCoefficientRescale_holderWith_unitBall
    {alpha : NNReal} (r : NNReal) (hr : 0 < r)
    (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (Ka : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((Metric.ball p0 r).restrict (a i j))) :
    ∀ i j, HolderWith (Ka i j * r ^ (alpha : Real)) alpha
      ((Metric.ball (parabolicPoint 0 0) 1).restrict
        (parabolicMatrixCoefficientRescale r p0 a i j)) := by
  intro i j
  simpa only [Function.comp_def, parabolicMatrixCoefficientRescale] using
    parabolicHolder_dilationAt_unitBall r hr p0 (ha i j)

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixCoefficientRescale_norm_sub_le_of_mem_unitBall
    {alpha : NNReal} (r : NNReal) (hr : 0 < r)
    (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (Ka : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((Metric.ball p0 r).restrict (a i j)))
    (i j : n) (p : ParabolicPoint (Euc n))
    (hp : p ∈ Metric.ball (parabolicPoint 0 0) 1) :
    ‖a i j p0 - parabolicMatrixCoefficientRescale r p0 a i j p‖ ≤
      Ka i j * r ^ (alpha : Real) := by
  have h := norm_sub_le_holderBallOscillationConst_of_mem_ball
    (show (0 : Real) < 1 by norm_num)
    (parabolicMatrixCoefficientRescale_holderWith_unitBall
      r hr p0 a Ka ha i j) hp
  simpa [holderBallOscillationConst] using h

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixFreezeHolderConst_mul
    (Ka omega : n → n → NNReal) (X : NNReal) :
    (∑ i, ∑ j, (omega i j * X + X * Ka i j)) =
      X * parabolicMatrixFreezeHolderConst Ka omega := by
  classical
  unfold parabolicMatrixFreezeHolderConst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixFreezeSupConst_mul
    (omega : n → n → NNReal) (X : NNReal) :
    (∑ i, ∑ j, omega i j * X) =
      X * parabolicMatrixFreezeSupConst omega := by
  classical
  unfold parabolicMatrixFreezeSupConst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixFreezeHolderConst_rescale
    (Ka : n → n → NNReal) (c : NNReal) :
    parabolicMatrixFreezeHolderConst
        (fun i j ↦ Ka i j * c) (fun i j ↦ Ka i j * c) =
      c * parabolicMatrixFreezeHolderConst Ka Ka := by
  simpa only [parabolicMatrixFreezeHolderConst, mul_comm] using
    parabolicMatrixFreezeHolderConst_mul Ka Ka c

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixFreezeSupConst_rescale
    (Ka : n → n → NNReal) (c : NNReal) :
    parabolicMatrixFreezeSupConst (fun i j ↦ Ka i j * c) =
      c * parabolicMatrixFreezeSupConst Ka := by
  simpa only [mul_comm] using parabolicMatrixFreezeSupConst_mul Ka c

omit [Nonempty n] [NormedSpace Real F] in
theorem spdParabolicSchauderDefectConst_rescale
    (A : Matrix n n Real) (hA : A.PosDef) (alpha : NNReal)
    (Ka : n → n → NNReal) (c : NNReal) (T : Real) :
    spdParabolicSchauderDefectConst A hA alpha
        (fun i j ↦ Ka i j * c) (fun i j ↦ Ka i j * c) T =
      c * spdParabolicSchauderDefectConst A hA alpha Ka Ka T := by
  unfold spdParabolicSchauderDefectConst
  rw [parabolicMatrixFreezeHolderConst_rescale,
    parabolicMatrixFreezeSupConst_rescale,
    spdHeatPotentialSchauderConst_nnreal_mul]

omit [Nonempty n] [NormedSpace Real F] in
theorem spdParabolicSchauderDefectConst_rescale_lt_one
    (A : Matrix n n Real) (hA : A.PosDef) (alpha : NNReal)
    (Ka : n → n → NNReal) (c : NNReal) (T : Real)
    (hsmall : c * spdParabolicSchauderDefectConst
      A hA alpha Ka Ka T < 1) :
    spdParabolicSchauderDefectConst A hA alpha
        (fun i j ↦ Ka i j * c) (fun i j ↦ Ka i j * c) T < 1 := by
  rw [spdParabolicSchauderDefectConst_rescale]
  exact hsmall

omit [Nonempty n] [NormedSpace Real F] in
theorem exists_pos_rescale_spdParabolicSchauderDefectConst_lt_one
    (A : Matrix n n Real) (hA : A.PosDef) (alpha : NNReal)
    (Ka : n → n → NNReal) (T : Real) :
    ∃ c : NNReal, 0 < c ∧ c ≤ 1 ∧
      spdParabolicSchauderDefectConst A hA alpha
        (fun i j ↦ Ka i j * c) (fun i j ↦ Ka i j * c) T < 1 := by
  let C := spdParabolicSchauderDefectConst A hA alpha Ka Ka T
  let c : NNReal := 1 / (2 * (C + 1))
  have hcpos : 0 < c := by
    dsimp only [c]
    positivity
  have hcle : c ≤ 1 := by
    dsimp only [c]
    rw [div_le_one (by positivity)]
    calc
      1 ≤ C + 1 := by simp
      _ = 1 * (C + 1) := by simp
      _ ≤ 2 * (C + 1) := mul_le_mul_left (by norm_num) _
  have hsmall : c * C < 1 := by
    calc
      c * C = C / (2 * (C + 1)) := by
        dsimp only [c]
        field_simp
      _ < 1 := (div_lt_one (by positivity)).2 <| lt_of_lt_of_le
        (lt_add_one C) <| by
          calc
            C + 1 = 1 * (C + 1) := by simp
            _ ≤ 2 * (C + 1) := mul_le_mul_left (by norm_num) _
  refine ⟨c, hcpos, hcle, ?_⟩
  exact spdParabolicSchauderDefectConst_rescale_lt_one
    A hA alpha Ka c T hsmall

omit [Nonempty n] [NormedSpace Real F] in
theorem exists_pos_le_rescale_spdParabolicSchauderDefectConst_lt_one
    (A : Matrix n n Real) (hA : A.PosDef) (alpha : NNReal)
    (halpha : 0 < alpha) (Ka : n → n → NNReal) (T : Real)
    (R : NNReal) (hR : 0 < R) :
    ∃ r : NNReal, 0 < r ∧ r ≤ R ∧
      spdParabolicSchauderDefectConst A hA alpha
        (fun i j ↦ Ka i j * r ^ (alpha : Real))
        (fun i j ↦ Ka i j * r ^ (alpha : Real)) T < 1 := by
  obtain ⟨c, hcpos, _, hsmall⟩ :=
    exists_pos_rescale_spdParabolicSchauderDefectConst_lt_one
      A hA alpha Ka T
  let d : NNReal := min c (R ^ (alpha : Real))
  let r : NNReal := d ^ ((alpha : Real)⁻¹)
  have hdpos : 0 < d := by
    dsimp only [d]
    exact lt_min hcpos (NNReal.rpow_pos hR)
  have hrpos : 0 < r := NNReal.rpow_pos hdpos
  have halphaReal : (0 : Real) < alpha := by exact_mod_cast halpha
  have halphaNe : (alpha : Real) ≠ 0 := halphaReal.ne'
  have hrpow : r ^ (alpha : Real) = d := by
    dsimp only [r]
    rw [← NNReal.rpow_mul, inv_mul_cancel₀ halphaNe, NNReal.rpow_one]
  have hrle : r ≤ R := by
    dsimp only [r]
    calc
      d ^ ((alpha : Real)⁻¹) ≤
          (R ^ (alpha : Real)) ^ ((alpha : Real)⁻¹) :=
        NNReal.rpow_le_rpow (min_le_right _ _) (inv_nonneg.mpr halphaReal.le)
      _ = R := by
        rw [← NNReal.rpow_mul, mul_inv_cancel₀ halphaNe, NNReal.rpow_one]
  refine ⟨r, hrpos, hrle, ?_⟩
  rw [hrpow]
  apply spdParabolicSchauderDefectConst_rescale_lt_one
  have hcsmall : c * spdParabolicSchauderDefectConst A hA alpha Ka Ka T < 1 := by
    rw [← spdParabolicSchauderDefectConst_rescale]
    exact hsmall
  exact lt_of_le_of_lt (mul_le_mul_left (min_le_left _ _) _) hcsmall

omit [Nonempty n] [NormedSpace Real F] in
theorem exists_parabolicMatrixCoefficientRescale_schauder_bounds_of_holderWith
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : (Matrix.of fun i j ↦ a i j p0).PosDef)
    (alpha : NNReal) (halpha : 0 < alpha) (Ka : n → n → NNReal)
    (T : Real) (R : NNReal) (hR : 0 < R)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((Metric.ball p0 R).restrict (a i j))) :
    ∃ r : NNReal, 0 < r ∧ r ≤ R ∧
      (∀ i j, HolderWith (Ka i j * r ^ (alpha : Real)) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicMatrixCoefficientRescale r p0 a i j))) ∧
      (∀ i j p, p ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖a i j p0 - parabolicMatrixCoefficientRescale r p0 a i j p‖ ≤
          Ka i j * r ^ (alpha : Real)) ∧
      spdParabolicSchauderDefectConst
        (Matrix.of fun i j ↦ a i j p0) hA alpha
        (fun i j ↦ Ka i j * r ^ (alpha : Real))
        (fun i j ↦ Ka i j * r ^ (alpha : Real)) T < 1 := by
  obtain ⟨r, hr, hrR, hsmall⟩ :=
    exists_pos_le_rescale_spdParabolicSchauderDefectConst_lt_one
      (Matrix.of fun i j ↦ a i j p0) hA alpha halpha Ka T R hR
  have har : ∀ i j, HolderWith (Ka i j) alpha
      ((Metric.ball p0 r).restrict (a i j)) := by
    intro i j
    apply HolderOnWith.holderWith
    exact (HolderWith.restrict_iff.mp (ha i j)).mono
      (Metric.ball_subset_ball (by exact_mod_cast hrR))
  refine ⟨r, hr, hrR, ?_, ?_, hsmall⟩
  · intro i j
    exact parabolicMatrixCoefficientRescale_holderWith_unitBall
      r hr p0 a Ka har i j
  · intro i j p hp
    exact parabolicMatrixCoefficientRescale_norm_sub_le_of_mem_unitBall
      r hr p0 a Ka har i j p hp

omit [Nonempty n] [NormedSpace Real F] in
theorem exists_parabolicMatrixCoefficientRescale_schauder_bounds_of_holderWith_on_parabolicCylinder
    (coeff : n → n → ParabolicPoint (Euc n) → Real)
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R)
    {center : Euc n} {p0 : ParabolicPoint (Euc n)}
    (hp0 : p0 ∈ parabolicCylinder (Set.Icc t₀ t₁)
      (Metric.closedBall center r))
    (hA : (Matrix.of fun i j ↦ coeff i j p0).PosDef)
    (alpha : NNReal) (halpha : 0 < alpha) (Ka : n → n → NNReal)
    (T : Real)
    (hcoeff : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (coeff i j))) :
    ∃ rho : NNReal, 0 < rho ∧ rho ≤ 1 ∧
      (rho : Real) ≤ parabolicInteriorRadius a t₀ t₁ b r R ∧
      (∀ i j, HolderWith (Ka i j * rho ^ (alpha : Real)) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicMatrixCoefficientRescale rho p0 coeff i j))) ∧
      (∀ i j p, p ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖coeff i j p0 - parabolicMatrixCoefficientRescale rho p0 coeff i j p‖ ≤
          Ka i j * rho ^ (alpha : Real)) ∧
      spdParabolicSchauderDefectConst
        (Matrix.of fun i j ↦ coeff i j p0) hA alpha
        (fun i j ↦ Ka i j * rho ^ (alpha : Real))
        (fun i j ↦ Ka i j * rho ^ (alpha : Real)) T < 1 := by
  let delta := parabolicInteriorRadius a t₀ t₁ b r R
  have hdelta : 0 < delta := parabolicInteriorRadius_pos hat₀ ht₁b hrR
  let radius : NNReal := ⟨min delta 1, le_min hdelta.le zero_le_one⟩
  have hradius : 0 < radius := by
    exact_mod_cast lt_min hdelta zero_lt_one
  have hball : Metric.ball p0 (radius : Real) ⊆
      parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) := by
    apply (Metric.ball_subset_ball ?_).trans
      (ball_parabolicInteriorRadius_subset_parabolicCylinder
        hat₀ ht₁b hrR hp0)
    simpa only [radius, delta, NNReal.coe_mk] using min_le_left delta 1
  have hlocal : ∀ i j, HolderWith (Ka i j) alpha
      ((Metric.ball p0 radius).restrict (coeff i j)) := by
    intro i j
    exact ((HolderWith.restrict_iff.mp (hcoeff i j)).mono hball).holderWith
  obtain ⟨rho, hrho, hrhoRadius, hholder, hoscillation, hsmall⟩ :=
    exists_parabolicMatrixCoefficientRescale_schauder_bounds_of_holderWith
      coeff p0 hA alpha halpha Ka T radius hradius hlocal
  refine ⟨rho, hrho, ?_, ?_, hholder, hoscillation, hsmall⟩
  · calc
      rho ≤ radius := hrhoRadius
      _ ≤ 1 := by
        exact_mod_cast (min_le_right delta 1)
  · calc
      (rho : Real) ≤ radius := by exact_mod_cast hrhoRadius
      _ ≤ delta := by
        simpa only [radius, NNReal.coe_mk] using min_le_left delta 1

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicVariableMatrixLap_apply
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n)) :
    parabolicVariableMatrixLap a u p =
      ∑ i, ∑ j, a i j p • parabolicHessianComponent u i j p := by
  rfl

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicFrozenMatrixLap_apply
    (A : Matrix n n Real) (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicFrozenMatrixLap A u p =
      ∑ i, ∑ j, A i j • parabolicHessianComponent u i j p := by
  rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicHessianComponent_rescaleAt
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (u : Real → Euc n → F) (i j : n) (p : ParabolicPoint (Euc n))
    (hspace : ContDiff Real 2
      (u (p0.time + (r : Real) ^ 2 * p.time))) :
    parabolicHessianComponent (parabolicRescaleAt r p0 u) i j p =
      (r : Real) ^ 2 •
        parabolicHessianComponent u i j (parabolicDilationAt r p0 p) := by
  unfold parabolicHessianComponent
  rw [parabolicSpatialJet_rescaleAt r p0 u 2 p hspace]
  simp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicVariableMatrixLap_rescaleAt
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n))
    (hspace : ContDiff Real 2
      (u (p0.time + (r : Real) ^ 2 * p.time))) :
    parabolicVariableMatrixLap
        (parabolicMatrixCoefficientRescale r p0 a)
        (parabolicRescaleAt r p0 u) p =
      (r : Real) ^ 2 •
        parabolicVariableMatrixLap a u (parabolicDilationAt r p0 p) := by
  simp only [parabolicVariableMatrixLap_apply,
    parabolicMatrixCoefficientRescale_apply,
    parabolicHessianComponent_rescaleAt r p0 u _ _ p hspace]
  simp only [smul_smul, Finset.smul_sum]
  congr 1
  funext i
  congr 1
  funext j
  rw [mul_comm]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicVariableMatrixOperator_rescaleAt
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n))
    (hspace : ContDiff Real 2
      (u (p0.time + (r : Real) ^ 2 * p.time))) :
    parabolicVariableMatrixOperator
        (parabolicMatrixCoefficientRescale r p0 a)
        (parabolicRescaleAt r p0 u) p =
      parabolicSourceRescaleAt r p0
        (parabolicVariableMatrixOperator a u) p := by
  unfold parabolicVariableMatrixOperator
  rw [parabolicTimeDerivative_rescaleAt,
    parabolicVariableMatrixLap_rescaleAt r p0 a u p hspace, ← smul_sub]
  rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicVariableMatrixOperator_rescaleAt_holderWith_unitBall
    {alpha K : NNReal} (r : NNReal) (hr : 0 < r)
    (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (hspace : ∀ t, ContDiff Real 2 (u t))
    (hoperator : HolderWith K alpha
      ((Metric.ball p0 r).restrict (parabolicVariableMatrixOperator a u))) :
    HolderWith (K * r ^ (alpha : Real) * r ^ 2) alpha
      ((Metric.ball (parabolicPoint 0 0) 1).restrict
        (parabolicVariableMatrixOperator
          (parabolicMatrixCoefficientRescale r p0 a)
          (parabolicRescaleAt r p0 u))) := by
  have heq :
      (Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicVariableMatrixOperator
            (parabolicMatrixCoefficientRescale r p0 a)
            (parabolicRescaleAt r p0 u)) =
        (Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicSourceRescaleAt r p0
            (parabolicVariableMatrixOperator a u)) := by
    funext p
    exact parabolicVariableMatrixOperator_rescaleAt
      r p0 a u p.1 (hspace _)
  rw [heq]
  exact parabolicSourceRescaleAt_holderWith_unitBall r hr p0 _ hoperator

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicVariableMatrixOperator_rescaleAt_le_of_mem_unitBall
    (r : NNReal) (hr : 0 < r) (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (hspace : ∀ t, ContDiff Real 2 (u t))
    (B : NNReal)
    (hoperator : ∀ p, p ∈ Metric.ball p0 r →
      ‖parabolicVariableMatrixOperator a u p‖ ≤ B)
    (p : ParabolicPoint (Euc n))
    (hp : p ∈ Metric.ball (parabolicPoint 0 0) 1) :
    ‖parabolicVariableMatrixOperator
        (parabolicMatrixCoefficientRescale r p0 a)
        (parabolicRescaleAt r p0 u) p‖ ≤ r ^ 2 * B := by
  rw [parabolicVariableMatrixOperator_rescaleAt r p0 a u p (hspace _)]
  exact norm_parabolicSourceRescaleAt_le_of_mem_unitBall
    r hr p0 _ B hoperator p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicFrozenMatrixLap_eq_variable_add_defect
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicFrozenMatrixLap (fun i j ↦ a i j p0) u p =
      parabolicVariableMatrixLap a u p +
        parabolicMatrixLapFreezeDefect a p0 u p := by
  simp only [parabolicFrozenMatrixLap_apply,
    parabolicVariableMatrixLap_apply, parabolicMatrixLapFreezeDefect]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  module

omit [DecidableEq n] [Nonempty n] in
theorem parabolicTimeDerivative_sub_frozenMatrixLap
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicTimeDerivative u p -
        parabolicFrozenMatrixLap (fun i j ↦ a i j p0) u p =
      (parabolicTimeDerivative u p - parabolicVariableMatrixLap a u p) -
        parabolicMatrixLapFreezeDefect a p0 u p := by
  rw [parabolicFrozenMatrixLap_eq_variable_add_defect]
  abel

omit [DecidableEq n] [Nonempty n] in
theorem parabolicFrozenMatrixOperator_eq_variable_sub_defect
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u p =
      parabolicVariableMatrixOperator a u p -
        parabolicMatrixLapFreezeDefect a p0 u p := by
  exact parabolicTimeDerivative_sub_frozenMatrixLap a p0 u p

omit [DecidableEq n] [Nonempty n] in
theorem parabolicHessianComponent_norm_le
    (u : Real → Euc n → F) (i j : n) (p : ParabolicPoint (Euc n)) :
    ‖parabolicHessianComponent u i j p‖ ≤ ‖parabolicSpatialJet 2 u p‖ := by
  let H := hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p)
  calc
    ‖parabolicHessianComponent u i j p‖ =
        ‖H (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ := rfl
    _ ≤ ‖H (EuclideanSpace.basisFun n Real i)‖ *
        ‖EuclideanSpace.basisFun n Real j‖ :=
      (H (EuclideanSpace.basisFun n Real i)).le_opNorm _
    _ ≤ (‖H‖ * ‖EuclideanSpace.basisFun n Real i‖) *
        ‖EuclideanSpace.basisFun n Real j‖ := by
      gcongr
      exact H.le_opNorm _
    _ = ‖H‖ := by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
        (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
        mul_one, mul_one]
    _ = ‖parabolicSpatialJet 2 u p‖ :=
      (hessianCurryEquiv (Euc n) F).norm_map _

omit [DecidableEq n] [Nonempty n] in
theorem parabolicHessianComponent_holderWith_restrict
    {alpha X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    {u : Real → Euc n → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ X) (i j : n) :
    HolderWith X alpha (Q.restrict (parabolicHessianComponent u i j)) := by
  have hjet := parabolicSpatialJet_holderWith_restrict h
  intro p q
  rw [edist_dist, edist_dist]
  have hreal :
      dist (parabolicHessianComponent u i j p.1)
          (parabolicHessianComponent u i j q.1) ≤
        (X : Real) * dist p q ^ (alpha : Real) := by
    rw [dist_eq_norm]
    change ‖hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p.1)
          (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j) -
        hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u q.1)
          (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤ _
    rw [← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.sub_apply,
      ← map_sub]
    calc
      ‖hessianCurryEquiv (Euc n) F
          (parabolicSpatialJet 2 u p.1 - parabolicSpatialJet 2 u q.1)
          (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤
          ‖hessianCurryEquiv (Euc n) F
            (parabolicSpatialJet 2 u p.1 - parabolicSpatialJet 2 u q.1)‖ := by
        let H := hessianCurryEquiv (Euc n) F
          (parabolicSpatialJet 2 u p.1 - parabolicSpatialJet 2 u q.1)
        calc
          ‖H (EuclideanSpace.basisFun n Real i)
              (EuclideanSpace.basisFun n Real j)‖ ≤
              ‖H (EuclideanSpace.basisFun n Real i)‖ *
                ‖EuclideanSpace.basisFun n Real j‖ :=
            (H (EuclideanSpace.basisFun n Real i)).le_opNorm _
          _ ≤ (‖H‖ * ‖EuclideanSpace.basisFun n Real i‖) *
                ‖EuclideanSpace.basisFun n Real j‖ := by
            gcongr
            exact H.le_opNorm _
          _ = ‖H‖ := by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
              (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
              mul_one, mul_one]
      _ = ‖parabolicSpatialJet 2 u p.1 - parabolicSpatialJet 2 u q.1‖ :=
        (hessianCurryEquiv (Euc n) F).norm_map _
      _ = dist (parabolicSpatialJet 2 u p.1)
          (parabolicSpatialJet 2 u q.1) :=
        (dist_eq_norm _ _).symm
      _ ≤ (X : Real) * dist p q ^ (alpha : Real) := hjet.dist_le p q
  calc
    ENNReal.ofReal
        (dist (parabolicHessianComponent u i j p.1)
          (parabolicHessianComponent u i j q.1)) ≤
        ENNReal.ofReal ((X : Real) * dist p q ^ (alpha : Real)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (X : ENNReal) * ENNReal.ofReal (dist p q ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul X.coe_nonneg]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = (X : ENNReal) * ENNReal.ofReal (dist p q) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg alpha.coe_nonneg]

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicMatrixLapFreezeDefect_le
    {alpha X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (omega : n → n → NNReal)
    (homega : ∀ i j p, p ∈ Q → ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha Q u ≤ X)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicMatrixLapFreezeDefect a p0 u p‖ ≤
      (∑ i, ∑ j, omega i j * X : NNReal) := by
  unfold parabolicMatrixLapFreezeDefect
  calc
    ‖∑ i, ∑ j, (a i j p0 - a i j p) •
        parabolicHessianComponent u i j p‖ ≤
        ∑ i, ∑ j, ‖(a i j p0 - a i j p) •
          parabolicHessianComponent u i j p‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, (omega i j : Real) * X := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      rw [norm_smul]
      exact mul_le_mul (homega i j p hp)
        ((parabolicHessianComponent_norm_le u i j p).trans
          (parabolicSpatialJet_norm_le hu le_rfl hp))
        (norm_nonneg _) (by positivity)
    _ = (∑ i, ∑ j, omega i j * X : NNReal) := by
      push_cast
      rfl

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicMatrixLapFreezeDefect_le
    {alpha X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (omega : n → n → NNReal)
    (homega : ∀ i j p, p ∈ Q → ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha Q u ≤ X) :
    eSupNormOn Q (parabolicMatrixLapFreezeDefect a p0 u) ≤
      (∑ i, ∑ j, omega i j * X : NNReal) := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicMatrixLapFreezeDefect_le
    a p0 u omega homega hu p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixLapFreezeDefect_holderWith_restrict
    {alpha X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (homega : ∀ i j p, p ∈ Q → ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha Q u ≤ X) :
    HolderWith
      (∑ i, ∑ j, (omega i j * X + X * Ka i j)) alpha
      (Q.restrict (parabolicMatrixLapFreezeDefect a p0 u)) := by
  classical
  let C : n → n → NNReal :=
    fun i j ↦ omega i j * X + X * Ka i j
  have hcomponent : ∀ i j, HolderWith (C i j) alpha
      (fun p : Q ↦ (a i j p0 - a i j p.1) •
        parabolicHessianComponent u i j p.1) := by
    intro i j
    have hcoeff : HolderWith (Ka i j) alpha
        (fun p : Q ↦ a i j p0 - a i j p.1) := by
      intro p q
      change edist (a i j p0 - a i j p.1) (a i j p0 - a i j q.1) ≤ _
      rw [show edist (a i j p0 - a i j p.1)
          (a i j p0 - a i j q.1) = edist (a i j p.1) (a i j q.1) by
        simp only [edist_dist, Real.dist_eq]
        rw [show a i j p0 - a i j p.1 - (a i j p0 - a i j q.1) =
          -(a i j p.1 - a i j q.1) by ring, abs_neg]]
      exact ha i j p q
    have hhess := parabolicHessianComponent_holderWith_restrict hu i j
    apply holderWith_smul_of_norm_le hcoeff hhess
    · exact fun p ↦ homega i j p.1 p.2
    · intro p
      exact (parabolicHessianComponent_norm_le u i j p.1).trans
        (parabolicSpatialJet_norm_le hu le_rfl p.2)
  have hinner : ∀ i, HolderWith (∑ j, C i j) alpha
      (fun p : Q ↦ ∑ j, (a i j p0 - a i j p.1) •
        parabolicHessianComponent u i j p.1) := by
    intro i
    exact holderWith_finset_sum Finset.univ
      (fun j _ ↦ hcomponent i j)
  have hall := holderWith_finset_sum Finset.univ
    (K := fun i ↦ ∑ j, C i j)
    (f := fun (i : n) (p : Q) ↦ ∑ j, (a i j p0 - a i j p.1) •
      parabolicHessianComponent u i j p.1)
    (fun i _ ↦ hinner i)
  simpa only [C, parabolicMatrixLapFreezeDefect, Set.restrict_apply] using hall

omit [DecidableEq n] [Nonempty n] in
theorem parabolicFrozenMatrixOperator_source_estimate
    {alpha Kf Bf X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (Ka omega : n → n → NNReal)
    (hsourceBound :
      eSupNormOn Q (parabolicVariableMatrixOperator a u) ≤ Bf)
    (hsourceHolder : HolderWith Kf alpha
      (Q.restrict (parabolicVariableMatrixOperator a u)))
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (homega : ∀ i j p, p ∈ Q → ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha Q u ≤ X) :
    eSupNormOn Q
        (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u) ≤
        Bf + ∑ i, ∑ j, omega i j * X ∧
      HolderWith
        (Kf + ∑ i, ∑ j, (omega i j * X + X * Ka i j)) alpha
        (Q.restrict
          (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)) := by
  have heq :
      parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u =
        parabolicVariableMatrixOperator a u -
          parabolicMatrixLapFreezeDefect a p0 u := by
    funext p
    exact parabolicFrozenMatrixOperator_eq_variable_sub_defect a p0 u p
  rw [heq]
  constructor
  · exact (eSupNormOn_sub_le Q _ _).trans
      (add_le_add hsourceBound
        (eSupNormOn_parabolicMatrixLapFreezeDefect_le
          a p0 u omega homega hu))
  · exact holderWith_sub hsourceHolder
      (parabolicMatrixLapFreezeDefect_holderWith_restrict
        a p0 u Ka omega ha homega hu)

section FrozenSolution

variable [CompleteSpace F]

theorem spdHeatDuh_parabolicFrozenMatrixOperator_eq
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S : Real} (p : ParabolicPoint (Euc n)) (hp : p.time ∈ Ioo (0 : Real) S)
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun q ↦ f q.time q.space))) :
    parabolicFrozenMatrixOperator A
        (fun t x ↦ spdHeatDuh A hA t f x) p =
      f p.time p.space := by
  let w : Euc n → F := spdHeatDuh A hA p.time f
  let dw : Euc n → Euc n →L[Real] F :=
    spdHeatDuhGradient A hA p.time f
  let d2w : Euc n → Euc n →L[Real] Euc n →L[Real] F :=
    spdHeatDuhHessian A hA p.time f
  have hpde : ∀ x : Euc n,
      HasFDerivAt w (dw x) x ∧
        HasFDerivAt dw (d2w x) x ∧
        HasDerivAt (fun t : Real ↦ spdHeatDuh A hA t f x)
          (matrixLap A (d2w x) + f p.time x) p.time := by
    intro x
    exact spdHeatDuh_pde halpha0 halpha1 hp A hA f hbound hsource x
  have hhess :
      hessianCurryEquiv (Euc n) F
          (parabolicSpatialJet 2
            (fun t x ↦ spdHeatDuh A hA t f x) p) =
        d2w p.space := by
    unfold parabolicSpatialJet
    exact hessianCurryEquiv_iteratedFDeriv_two w dw d2w
      (fun x ↦ (hpde x).1) (fun x ↦ (hpde x).2.1) p.space
  have htime :
      parabolicTimeDerivative (fun t x ↦ spdHeatDuh A hA t f x) p =
        matrixLap A (d2w p.space) + f p.time p.space := by
    unfold parabolicTimeDerivative
    rw [(hpde p.space).2.2.hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  unfold parabolicFrozenMatrixOperator parabolicFrozenMatrixLap
  rw [htime, hhess]
  abel

theorem spdHeatDuh_parabolic_schauder_solution
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ f p.time p.space))) :
    (∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
        parabolicFrozenMatrixOperator A
            (fun t x ↦ spdHeatDuh A hA t f x) p =
          f p.time p.space) ∧
      eParabolicC2HolderGaugeOn alpha
          (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
          (fun t x ↦ spdHeatDuh A hA t f x) ≤
        spdHeatPotentialSchauderConst A hA alpha K B T := by
  constructor
  · intro p hp
    exact spdHeatDuh_parabolicFrozenMatrixOperator_eq
      halpha0 halpha1 p ⟨hp.1.1, hp.1.2.trans_lt hTS⟩
        A hA f hbound hsource
  · exact spdHeatDuh_schauder_estimate_euclidean
      halpha0 halpha1 hT hTS A hA f hbound hsource

theorem parabolic_variable_coefficient_schauder_estimate_of_frozen_representation_on
    {alpha Kf Bf X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u : Real → Euc n → F)
    (g : Real → BoundedContinuousFunction (Euc n) F)
    (hrep : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ spdHeatDuh (fun i j ↦ a i j p0) hA
        p.time g p.space)
      (parabolicCylinder (Ioo (0 : Real) S) Set.univ))
    (hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)
      (parabolicCylinder (Icc (0 : Real) S) Set.univ))
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicVariableMatrixOperator a u) ≤ Bf)
    (hsourceHolder : HolderWith Kf alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a u)))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ) u ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (Kf + X * parabolicMatrixFreezeHolderConst Ka omega)
        (Bf + X * parabolicMatrixFreezeSupConst omega) T := by
  let Q : Set (ParabolicPoint (Euc n)) :=
    parabolicCylinder (Icc (0 : Real) S) Set.univ
  let A : Matrix n n Real := fun i j ↦ a i j p0
  let Kdefect := X * parabolicMatrixFreezeHolderConst Ka omega
  let Bdefect := X * parabolicMatrixFreezeSupConst omega
  have hfrozen := parabolicFrozenMatrixOperator_source_estimate
    a p0 u Ka omega hsourceBound hsourceHolder ha homega hu
  rw [parabolicMatrixFreezeHolderConst_mul,
    parabolicMatrixFreezeSupConst_mul] at hfrozen
  have hboundG : ∀ r ∈ Icc (0 : Real) S, ‖g r‖ ≤ Bf + Bdefect := by
    intro r hr
    rw [BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    let p : ParabolicPoint (Euc n) := parabolicPoint r x
    have hp : p ∈ Q := ⟨hr, Set.mem_univ x⟩
    have heq := hgfrozen hp
    calc
      ‖g r x‖ = ‖parabolicFrozenMatrixOperator A u p‖ := by
        exact congrArg norm heq
      _ ≤ Bf + Bdefect := by
        change ‖parabolicFrozenMatrixOperator A u p‖ ≤
          ((Bf + Bdefect : NNReal) : Real)
        rw [← ENNReal.ofReal_le_coe]
        exact (norm_le_eSupNormOn Q
          (parabolicFrozenMatrixOperator A u) p hp).trans (by
            simpa only [ENNReal.coe_add] using hfrozen.1)
  have hholderG : HolderWith (Kf + Kdefect) alpha
      (Q.restrict (fun p ↦ g p.time p.space)) := by
    have heq : Q.restrict (fun p ↦ g p.time p.space) =
        Q.restrict (parabolicFrozenMatrixOperator A u) := by
      funext p
      exact hgfrozen p.2
    rw [heq]
    exact hfrozen.2
  calc
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u =
        eParabolicC2HolderGaugeOn alpha
          (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
          (fun t x ↦ spdHeatDuh A hA t g x) := by
      apply eParabolicC2HolderGaugeOn_congr_of_eqOn_open
        (isOpen_parabolicCylinder isOpen_Ioo isOpen_univ)
      · intro p hp
        exact ⟨⟨hp.1.1, hp.1.2.trans_lt hTS⟩, hp.2⟩
      · simpa only [A] using hrep
    _ ≤ spdHeatPotentialSchauderConst A hA alpha
        (Kf + Kdefect) (Bf + Bdefect) T :=
      spdHeatDuh_schauder_estimate_euclidean
        halpha0 halpha1 hT hTS A hA g hboundG hholderG

theorem parabolic_variable_coefficient_schauder_estimate_of_frozen_representation
    {alpha Kf Bf X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u : Real → Euc n → F)
    (g : Real → BoundedContinuousFunction (Euc n) F)
    (hrep : u = fun t x ↦
      spdHeatDuh (fun i j ↦ a i j p0) hA t g x)
    (hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)
      (parabolicCylinder (Icc (0 : Real) S) Set.univ))
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicVariableMatrixOperator a u) ≤ Bf)
    (hsourceHolder : HolderWith Kf alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a u)))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ) u ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (Kf + X * parabolicMatrixFreezeHolderConst Ka omega)
        (Bf + X * parabolicMatrixFreezeSupConst omega) T := by
  apply parabolic_variable_coefficient_schauder_estimate_of_frozen_representation_on
    halpha0 halpha1 hT hTS a p0 hA u g
  · intro p _hp
    exact congrFun (congrFun hrep p.time) p.space
  · exact hgfrozen
  · exact hsourceBound
  · exact hsourceHolder
  · exact ha
  · exact homega
  · exact hu

omit [Nonempty n] [CompleteSpace F] in
theorem parabolic_schauder_estimate_of_small_freeze_defect
    {alpha Kf Bf X : NNReal} (halpha1 : alpha < 1)
    {T : Real} (hT : 0 ≤ T)
    (A : Matrix n n Real) (hA : A.PosDef)
    (Ka omega : n → n → NNReal)
    (u : Real → Euc n → F)
    (hraw : eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      spdHeatPotentialSchauderConst A hA alpha
        (Kf + X * parabolicMatrixFreezeHolderConst Ka omega)
        (Bf + X * parabolicMatrixFreezeSupConst omega) T)
    (hX : (X : ENNReal) ≤ eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u)
    (hsmall : spdParabolicSchauderDefectConst
      A hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      (spdHeatPotentialSchauderConst A hA alpha Kf Bf T /
        (1 - spdParabolicSchauderDefectConst
          A hA alpha Ka omega T) : NNReal) := by
  let Kosc := parabolicMatrixFreezeHolderConst Ka omega
  let Bosc := parabolicMatrixFreezeSupConst omega
  let delta := spdParabolicSchauderDefectConst A hA alpha Ka omega T
  let C := spdHeatPotentialSchauderConst A hA alpha Kf Bf T
  rw [spdHeatPotentialSchauderConst_add halpha1 A hA
      Kf (X * Kosc) Bf (X * Bosc) hT,
    spdHeatPotentialSchauderConst_nnreal_mul
      A hA alpha X Kosc Bosc T] at hraw
  have hraw' : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
        (C : ENNReal) + (delta : ENNReal) * X := by
    simpa only [C, delta, Kosc, Bosc, spdParabolicSchauderDefectConst,
      ENNReal.coe_add, ENNReal.coe_mul, mul_comm] using hraw
  have hself : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
        (C : ENNReal) + (delta : ENNReal) *
          eParabolicC2HolderGaugeOn alpha
            (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u :=
    hraw'.trans (by gcongr)
  have hfinite : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≠ ⊤ :=
    ne_of_lt (hraw'.trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.coe_lt_top,
        ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top⟩))
  have habsorb := ennreal_le_coe_div_one_sub_of_le_add_mul
    hfinite (show delta < 1 by simpa only [delta] using hsmall) hself
  simpa only [C, delta] using habsorb

end FrozenSolution

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
