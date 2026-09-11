import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoublePatch

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

def compactDoubleCorePartialDiffeomorph (north : S3) (R : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ := by
  let Φ := compactDoubleCapPartialDiffeomorph north R
  have hsrc : Metric.ball (0 : E3) (R - 2) ⊆ Φ.source := by
    change Metric.ball (0 : E3) (R - 2) ⊆ Metric.ball 0 (R + 1)
    exact Metric.ball_subset_ball (by linarith)
  exact PartialDiffeomorph.ofOpenPartialHomeomorphRestr
    Φ.toOpenPartialHomeomorph
    (Metric.ball 0 (R - 2)) Metric.isOpen_ball hsrc
    (Φ.contMDiffOn_toFun.mono hsrc)
    (Φ.contMDiffOn_invFun.mono (by
      rintro _ ⟨x, hx, rfl⟩
      exact Φ.map_source' (hsrc hx)))

theorem compactDoubleCorePartialDiffeomorph_apply
    (north : S3) (R : ℝ) (x : E3) :
    compactDoubleCorePartialDiffeomorph north R x =
      compactDoubleCapMap north R x := rfl

theorem compactDoubleCorePartialDiffeomorph_symm_apply
    (north : S3) (R : ℝ) (p : S3) :
    (compactDoubleCorePartialDiffeomorph north R).symm p =
      (compactDoubleCapPartialDiffeomorph north R).symm p := rfl

theorem compactDoubleCorePartialDiffeomorph_source
    (north : S3) (R : ℝ) :
    (compactDoubleCorePartialDiffeomorph north R).source =
      Metric.ball 0 (R - 2) := rfl

theorem compactDoubleCorePartialDiffeomorph_target
    (north : S3) (R : ℝ) :
    (compactDoubleCorePartialDiffeomorph north R).target =
      compactDoubleCapMap north R '' Metric.ball 0 (R - 2) := rfl

theorem compactDoubleCorePartialDiffeomorph_mfderiv
    (north : S3) (R : ℝ) (x : E3) :
    mfderiv (𝓡 3) (𝓡 3) (compactDoubleCorePartialDiffeomorph north R) x =
      mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x := rfl

theorem compactDoubleCorePartialDiffeomorph_truncation_pullback
    (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R)
    (g : SmoothRiemannianMetric (𝓡 3) E3)
    (x : E3)
    (hx : x ∈ (compactDoubleCorePartialDiffeomorph north R).source)
    (v w : E3) :
    (compactDoubleTruncationMetric north R hR g).inner
      (compactDoubleCorePartialDiffeomorph north R x)
      (mfderiv (𝓡 3) (𝓡 3)
        (compactDoubleCorePartialDiffeomorph north R) x v)
      (mfderiv (𝓡 3) (𝓡 3)
        (compactDoubleCorePartialDiffeomorph north R) x w) =
      g.inner x v w := by
  have hn : ‖x‖ < R - 2 := by
    simpa only [compactDoubleCorePartialDiffeomorph_source,
      Metric.mem_ball, dist_zero_right] using hx
  exact compactDoubleTruncationMetric_cap_pullback_core
    north R hR g x hn.le v w

end DifferentialGeometry.PDE.RicciFlow.StandardCap
