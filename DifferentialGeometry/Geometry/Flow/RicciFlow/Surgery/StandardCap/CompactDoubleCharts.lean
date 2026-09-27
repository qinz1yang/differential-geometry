import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDouble
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

private def capCoordinateDiffeomorph (R : ℝ) : E3 ≃ₘ[ℝ] E3 :=
  radialExponentialDiffeomorph.trans
    (LinearEquiv.smulOfNeZero ℝ E3 (2 * Real.exp (-R))
      (mul_ne_zero (by norm_num) (Real.exp_ne_zero _))).toContinuousLinearEquiv.toDiffeomorph

private theorem native_chart_eq (north : S3) : chartAt E3 (-north) = stereographic' 3 north := by
  change stereographic' 3 (-(-north)) = stereographic' 3 north
  rw [neg_neg]

private def nativeStereoPartial (north : S3) : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 E3 ∞ where
  toPartialEquiv := (stereographic' 3 north).toPartialEquiv
  open_source := (stereographic' 3 north).open_source
  open_target := (stereographic' 3 north).open_target
  contMDiffOn_toFun := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (stereographic' 3 north) (stereographic' 3 north).source
    rw [← native_chart_eq]
    exact contMDiffOn_chart
  contMDiffOn_invFun := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (stereographic' 3 north).symm (stereographic' 3 north).target
    rw [← native_chart_eq]
    exact contMDiffOn_chart_symm

private def fullCapPartial (north : S3) (R : ℝ) : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ :=
  (capCoordinateDiffeomorph R).toPartialDiffeomorph.trans (nativeStereoPartial north).symm

private theorem fullCapPartial_source (north : S3) (R : ℝ) :
    (fullCapPartial north R).source = univ := by
  change univ ∩ (capCoordinateDiffeomorph R) ⁻¹' (stereographic' 3 north).target = univ
  simp only [stereographic'_target, preimage_univ, inter_self]

def compactDoubleCapPartialDiffeomorph (north : S3) (R : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ := by
  let Φ := fullCapPartial north R
  have hsrc : Metric.ball (0 : E3) (R + 1) ⊆ Φ.source := by
    rw [fullCapPartial_source]
    exact subset_univ _
  exact PartialDiffeomorph.ofOpenPartialHomeomorphRestr Φ.toOpenPartialHomeomorph
    (Metric.ball 0 (R + 1)) Metric.isOpen_ball hsrc
    (Φ.contMDiffOn_toFun.mono hsrc)
    (Φ.contMDiffOn_invFun.mono (by rintro _ ⟨x, hx, rfl⟩; exact Φ.map_source' (hsrc hx)))

theorem compactDoubleCapPartialDiffeomorph_apply (north : S3) (R : ℝ) (x : E3) :
    compactDoubleCapPartialDiffeomorph north R x = compactDoubleCapMap north R x := rfl

theorem compactDoubleCapPartialDiffeomorph_source (north : S3) (R : ℝ) :
    (compactDoubleCapPartialDiffeomorph north R).source = Metric.ball 0 (R + 1) := rfl

theorem compactDoubleCapPartialDiffeomorph_target (north : S3) (R : ℝ) :
    (compactDoubleCapPartialDiffeomorph north R).target =
      compactDoubleCapMap north R '' Metric.ball 0 (R + 1) := rfl

theorem compactDoubleCapPartialDiffeomorph_symm_apply (north : S3) (R : ℝ) (p : S3) :
    (compactDoubleCapPartialDiffeomorph north R).symm p =
      radialExponentialDiffeomorph.symm ((2 * Real.exp (-R))⁻¹ • stereographic' 3 north p) := rfl

theorem compactDoubleCapMap_zero (north : S3) (R : ℝ) : compactDoubleCapMap north R 0 = -north := by
  unfold compactDoubleCapMap
  rw [radialExponentialDiffeomorph_of_norm_le_one 0 (by simp), smul_zero]
  apply Subtype.ext
  change ((stereographic' 3 north).symm 0 : E4) = -(north : E4)
  norm_num [stereographic'_symm_apply, smul_smul]

theorem compactDoubleCapPartialDiffeomorph_pullback (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (x : E3)
    (hx : x ∈ (compactDoubleCapPartialDiffeomorph north R).source) (v w : E3) :
    (compactDoubleMetric north R hR).inner (compactDoubleCapPartialDiffeomorph north R x)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapPartialDiffeomorph north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapPartialDiffeomorph north R) x w) = metric.inner x v w :=
  compactDoubleMetric_cap_pullback north R hR x hx v w
end DifferentialGeometry.PDE.RicciFlow.StandardCap
