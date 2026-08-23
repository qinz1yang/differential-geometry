import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrectionZeroNormalForm.ZeroOrderRemainderNormalForm

noncomputable section

open scoped BigOperators

namespace DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroMatrixNormalForm

abbrev curvatureConnectionActionBlock {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.curvatureConnectionActionBlock n
abbrev curvatureContractionBlock {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.curvatureContractionBlock n
abbrev connectionDifferenceDerivativeDefect {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceDerivativeDefect n
abbrev connectionDifferenceInsertion {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion n
abbrev connectionDifferenceQuadraticBlock {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock n
abbrev mixedConnectionHalfBlock {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock n
abbrev r4F {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.r4F n
abbrev r4pfB {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.r4pfB n
abbrev t2F {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.t2F n
abbrev tpfF {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.tpfF n
abbrev r3B {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.r3B n
abbrev christoffelCorrection {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.christoffelCorrection n
abbrev deTurckVectorCorrection {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorCorrection n
abbrev deTurckVectorFieldDerivative {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDerivative n
abbrev zeroOrderDerivativeCorrection {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderDerivativeCorrection n
abbrev zeroOrderCorrection {n : ℕ} :=
  @DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderCorrection n
abbrev deTurckVectorFieldDifference {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDifference n
abbrev covariantDerivativeConnectionDifference {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeConnectionDifference n
abbrev covariantDerivativeDeTurckVectorDifference {n : ℕ} := @DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeDeTurckVectorDifference n
abbrev zeroOrderVectorCorrection {n : ℕ} :=
  @DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderVectorCorrection n
abbrev firstDerivativeRemainder {n : ℕ} :=
  @DeTurckCoefficients.LieCorrectionZeroNormalForm.firstDerivativeRemainder n

theorem lie_correction_zero_matrix_normal_form {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) *
      ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    zeroOrderVectorCorrection ig cg f dig ga1 gbg dga1 dgbg i j
      + connectionDifferenceInsertion ig dig ga1 ga0 gbg dga1 dga0 f i j
      + connectionDifferenceQuadraticBlock ig cg ga1 ga0 f i j
      + (2 : ℝ) * (mixedConnectionHalfBlock ig cg ga1 ga0 gbg f i j + mixedConnectionHalfBlock ig cg ga1 ga0 gbg f j i)
      + curvatureContractionBlock ig ga0 dga0 f i j
    = zeroOrderCorrection ig cg f dg dig ga1 gbg gb dga1 dgbg dgb i j
      - (t2F ig ga0 dga0 f f3 i j - tpfF ig ga0 f3 i j)
      - firstDerivativeRemainder ig cg f ga0 ga1 gbg i j := by
  exact DeTurckCoefficients.LieCorrectionZeroNormalForm.lie_correction_zero_normal_form ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0
    dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s
    hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

end DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroMatrixNormalForm
