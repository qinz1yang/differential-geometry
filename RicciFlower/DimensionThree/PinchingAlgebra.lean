import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Three-dimensional pinching algebra

This file contains the pure eigenvalue algebra used in Hamilton's three
dimensional pinching argument.  It is intentionally independent of the synthetic
Ricci-flow layer and of geometric realization data.
-/

namespace RicciFlower
namespace DimensionThree

variable {R : Type*}

/-- Scalar curvature written as the sum of three Ricci eigenvalues. -/
def ricciEigenScalar3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 + l2 + l3

/-- Squared Ricci norm written in Ricci eigenvalues. -/
def ricciEigenNormSq3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 ^ 2 + l2 ^ 2 + l3 ^ 2

/-- If the Ricci eigenvalues are nonnegative, then `|Ric|^2 <= R^2`. -/
theorem ricciEigenNormSq3_le_scalar_sq_of_nonnegative
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (l1 l2 l3 : R) (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3) :
    ricciEigenNormSq3 l1 l2 l3 <= ricciEigenScalar3 l1 l2 l3 ^ 2 := by
  unfold ricciEigenNormSq3 ricciEigenScalar3
  nlinarith

/-- Cubic trace `tr(Ric^3)` written in Ricci eigenvalues. -/
def ricciEigenTraceCube3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 ^ 3 + l2 ^ 3 + l3 ^ 3

/-- Hamilton's cubic reaction quantity `Q` in dimension three, in Ricci eigenvalues. -/
def hamiltonCubicQ3 [CommRing R] (l1 l2 l3 : R) : R :=
  2 * ricciEigenNormSq3 l1 l2 l3 ^ 2 +
    ricciEigenScalar3 l1 l2 l3 ^ 4 -
    5 * ricciEigenScalar3 l1 l2 l3 ^ 2 * ricciEigenNormSq3 l1 l2 l3 +
    4 * ricciEigenScalar3 l1 l2 l3 * ricciEigenTraceCube3 l1 l2 l3

/-- Factorized form of Hamilton's cubic `Q`, Lemma 10.7 in eigenvalue form. -/
def hamiltonCubicQFactorized3 [CommRing R] (l1 l2 l3 : R) : R :=
  (l1 - l2) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l3) ^ 2 +
    (l1 - l3) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l2) ^ 2 +
    (l2 - l3) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l1) ^ 2

/-- LaTeX Lemma 10.7: Hamilton's cubic `Q` factorizes into eigenvalue gaps. -/
theorem hamiltonCubicQ3_factorized [CommRing R] (l1 l2 l3 : R) :
    hamiltonCubicQ3 l1 l2 l3 = hamiltonCubicQFactorized3 l1 l2 l3 := by
  unfold hamiltonCubicQ3 hamiltonCubicQFactorized3 ricciEigenScalar3 ricciEigenNormSq3
    ricciEigenTraceCube3
  ring

/-- Pairwise eigenvalue-gap square sum. -/
def ricciEigenPairwiseGapSq3 [CommRing R] (l1 l2 l3 : R) : R :=
  (l1 - l2) ^ 2 + (l1 - l3) ^ 2 + (l2 - l3) ^ 2

/-- Trace-free Ricci norm in dimension three, written in eigenvalue gaps. -/
def tracefreeRicciEigenNormSq3 [Field R] (l1 l2 l3 : R) : R :=
  ricciEigenPairwiseGapSq3 l1 l2 l3 / 3

/-- Hamilton's factorized `Q` after setting
`l1 = z + b + a`, `l2 = z + b`, `l3 = z`. -/
def hamiltonCubicQOrderedGaps3 [CommRing R] (a b z : R) : R :=
  a ^ 2 * (z + a + 2 * b) ^ 2 +
    (a + b) ^ 2 * (z + a) ^ 2 +
    b ^ 2 * (z - a) ^ 2

/-- Pairwise eigenvalue-gap square sum in ordered-gap variables. -/
def orderedEigenPairwiseGapSq3 [CommRing R] (a b : R) : R :=
  a ^ 2 + (a + b) ^ 2 + b ^ 2

theorem hamiltonCubicQ3_ordered_gaps [CommRing R] (a b z : R) :
    hamiltonCubicQ3 (z + b + a) (z + b) z =
      hamiltonCubicQOrderedGaps3 a b z := by
  rw [hamiltonCubicQ3_factorized]
  unfold hamiltonCubicQFactorized3 hamiltonCubicQOrderedGaps3 ricciEigenScalar3
  ring

theorem ricciEigenPairwiseGapSq3_ordered_gaps [CommRing R] (a b z : R) :
    ricciEigenPairwiseGapSq3 (z + b + a) (z + b) z =
      orderedEigenPairwiseGapSq3 a b := by
  unfold ricciEigenPairwiseGapSq3 orderedEigenPairwiseGapSq3
  ring

theorem hamiltonCubicQOrderedGaps3_sub_zSq_pairwise [CommRing R] (a b z : R) :
    hamiltonCubicQOrderedGaps3 a b z - z ^ 2 * orderedEigenPairwiseGapSq3 a b =
      2 * a ^ 2 * (a ^ 2 + 3 * a * b + 2 * a * z + 3 * b ^ 2 + 4 * b * z) := by
  unfold hamiltonCubicQOrderedGaps3 orderedEigenPairwiseGapSq3
  ring

theorem hamiltonCubicQOrderedGaps3_ge_zSq_pairwise
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b z : R) (ha : 0 <= a) (hb : 0 <= b) (hz : 0 <= z) :
    z ^ 2 * orderedEigenPairwiseGapSq3 a b <= hamiltonCubicQOrderedGaps3 a b z := by
  have hdiff := hamiltonCubicQOrderedGaps3_sub_zSq_pairwise (R := R) a b z
  have hnonneg :
      0 <= 2 * a ^ 2 * (a ^ 2 + 3 * a * b + 2 * a * z + 3 * b ^ 2 + 4 * b * z) := by
    positivity
  nlinarith

/-- Lemma 10.8 in ordered-gap variables. The hypotheses are the algebraic
content of `Ric >= delta R g` after diagonalizing and ordering eigenvalues. -/
theorem hamiltonCubicQOrderedGaps3_lower_bound
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b z delta scalar ricciNormSq : R)
    (ha : 0 <= a) (hb : 0 <= b) (hz : 0 <= z)
    (hdelta : 0 <= delta) (hscalar : 0 <= scalar)
    (hpinch : delta * scalar <= z)
    (hnorm : ricciNormSq <= scalar ^ 2) :
    2 * delta ^ 2 * ricciNormSq * (orderedEigenPairwiseGapSq3 a b / 3) <=
      hamiltonCubicQOrderedGaps3 a b z := by
  have hgap_ge :
      z ^ 2 * orderedEigenPairwiseGapSq3 a b <= hamiltonCubicQOrderedGaps3 a b z :=
    hamiltonCubicQOrderedGaps3_ge_zSq_pairwise a b z ha hb hz
  have htf_nonneg : 0 <= orderedEigenPairwiseGapSq3 a b / 3 := by
    have hpair : 0 <= orderedEigenPairwiseGapSq3 a b := by
      unfold orderedEigenPairwiseGapSq3
      positivity
    have hthree : (0 : R) <= 3 := by positivity
    exact div_nonneg hpair hthree
  have hdelta_sq_norm_le_zsq : delta ^ 2 * ricciNormSq <= z ^ 2 := by
    have hds_nonneg : 0 <= delta * scalar := mul_nonneg hdelta hscalar
    have hds_sq_le : (delta * scalar) ^ 2 <= z ^ 2 := by
      nlinarith [sq_nonneg (z - delta * scalar)]
    nlinarith [sq_nonneg delta, sq_nonneg scalar]
  have hscaled :
      2 * delta ^ 2 * ricciNormSq * (orderedEigenPairwiseGapSq3 a b / 3) <=
        3 * z ^ 2 * (orderedEigenPairwiseGapSq3 a b / 3) := by
    nlinarith [mul_le_mul_of_nonneg_right hdelta_sq_norm_le_zsq htf_nonneg]
  have hthree :
      3 * z ^ 2 * (orderedEigenPairwiseGapSq3 a b / 3) =
        z ^ 2 * orderedEigenPairwiseGapSq3 a b := by
    ring_nf
  rw [hthree] at hscaled
  exact le_trans hscaled hgap_ge

/-- Lemma 10.8 in ordered Ricci eigenvalues. This is the polynomial/inequality
core of the lower bound `Q >= 2 delta^2 |Ric|^2 |Ric°|^2`; the geometric
diagonalization and translation of `Ric >= delta R g` are separate realization
steps. -/
theorem hamiltonCubicQ3_lower_bound_ordered_eigenvalues
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (l1 l2 l3 delta : R)
    (h12 : l2 <= l1) (h23 : l3 <= l2)
    (hdelta : 0 <= delta)
    (hscalar : 0 <= ricciEigenScalar3 l1 l2 l3)
    (hpinch : delta * ricciEigenScalar3 l1 l2 l3 <= l3)
    (hnorm : ricciEigenNormSq3 l1 l2 l3 <= ricciEigenScalar3 l1 l2 l3 ^ 2) :
    2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 <=
      hamiltonCubicQ3 l1 l2 l3 := by
  let a := l1 - l2
  let b := l2 - l3
  let z := l3
  have ha : 0 <= a := by
    dsimp [a]
    linarith
  have hb : 0 <= b := by
    dsimp [b]
    linarith
  have hz : 0 <= z := by
    dsimp [z]
    have hds_nonneg : 0 <= delta * ricciEigenScalar3 l1 l2 l3 :=
      mul_nonneg hdelta hscalar
    exact le_trans hds_nonneg hpinch
  have hgap_lower :
      2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
          (orderedEigenPairwiseGapSq3 a b / 3) <=
        hamiltonCubicQOrderedGaps3 a b z :=
    hamiltonCubicQOrderedGaps3_lower_bound a b z delta
      (ricciEigenScalar3 l1 l2 l3) (ricciEigenNormSq3 l1 l2 l3)
      ha hb hz hdelta hscalar hpinch hnorm
  have hQ_gap : hamiltonCubicQ3 l1 l2 l3 = hamiltonCubicQOrderedGaps3 a b z := by
    dsimp [a, b, z]
    unfold hamiltonCubicQ3 hamiltonCubicQOrderedGaps3 ricciEigenScalar3 ricciEigenNormSq3
      ricciEigenTraceCube3
    ring
  have htf_gap :
      tracefreeRicciEigenNormSq3 l1 l2 l3 = orderedEigenPairwiseGapSq3 a b / 3 := by
    dsimp [a, b]
    unfold tracefreeRicciEigenNormSq3 ricciEigenPairwiseGapSq3 orderedEigenPairwiseGapSq3
    ring
  rw [htf_gap, hQ_gap]
  exact hgap_lower

/-- LaTeX Lemma 10.8 with `|Ric|^2 <= R^2` derived from nonnegative Ricci
eigenvalues instead of supplied as a separate hypothesis. -/
theorem hamiltonCubicQ3_lower_bound_ordered_nonnegative_eigenvalues
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (l1 l2 l3 delta : R)
    (h12 : l2 <= l1) (h23 : l3 <= l2)
    (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3)
    (hdelta : 0 <= delta)
    (hpinch : delta * ricciEigenScalar3 l1 l2 l3 <= l3) :
    2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 <=
      hamiltonCubicQ3 l1 l2 l3 := by
  exact hamiltonCubicQ3_lower_bound_ordered_eigenvalues l1 l2 l3 delta h12 h23 hdelta
    (by
      unfold ricciEigenScalar3
      nlinarith)
    hpinch
    (ricciEigenNormSq3_le_scalar_sq_of_nonnegative l1 l2 l3 h1 h2 h3)

end DimensionThree
end RicciFlower
