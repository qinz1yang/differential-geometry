import DifferentialGeometry.Geometry.Comparison.Toponogov.Convexity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set Topology

noncomputable section

namespace DifferentialGeometry.Toponogov

structure C2LowerSupportAt (f : ℝ → ℝ) (I : Set ℝ) (x : ℝ) where

  left : ℝ

  right : ℝ

  center_mem : x ∈ Ioo left right

  interval_subset : Ioo left right ⊆ I

  support : ℝ → ℝ

  contDiffOn_support : ContDiffOn ℝ 2 support (Ioo left right)

  support_le : ∀ y ∈ Ioo left right, support y ≤ f y

  support_eq : support x = f x

  secondDeriv_nonneg : 0 ≤ deriv (deriv support) x

def C2LowerSupportAt.toLowerSupportAt {f : ℝ → ℝ} {I : Set ℝ} {x : ℝ}
    (S : C2LowerSupportAt f I x) : LowerSupportAt f I x where
  support := S.support
  supportDeriv := deriv S.support
  supportSecondDeriv := deriv (deriv S.support) x
  domain := Ioo S.left S.right
  domain_mem_nhds := Ioo_mem_nhds S.center_mem.1 S.center_mem.2
  domain_subset := S.interval_subset
  support_le := S.support_le
  support_eq := S.support_eq
  hasDerivAt_support := by
    intro y hy
    exact ((S.contDiffOn_support.differentiableOn (by norm_num)) y hy).differentiableAt
      (isOpen_Ioo.mem_nhds hy) |>.hasDerivAt
  hasDerivAt_supportDeriv := by
    have hderiv : ContDiffOn ℝ 1 (deriv S.support) (Ioo S.left S.right) :=
      S.contDiffOn_support.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact ((hderiv.differentiableOn (by norm_num)) x S.center_mem).differentiableAt
      (isOpen_Ioo.mem_nhds S.center_mem) |>.hasDerivAt
  supportSecondDeriv_nonneg := S.secondDeriv_nonneg

theorem convexOn_of_c2LowerSupport {I : Set ℝ} {f : ℝ → ℝ}
    (hI : Convex ℝ I) (hf : ContinuousOn f I)
    (hsupport : ∀ x ∈ interior I, C2LowerSupportAt f I x) :
    ConvexOn ℝ I f := by
  exact convexOn_of_lowerSupport hI hf fun x hx ↦ (hsupport x hx).toLowerSupportAt

end DifferentialGeometry.Toponogov
