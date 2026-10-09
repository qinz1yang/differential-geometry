import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Hyperbolic.ModelAtlasBridge
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

variable (H : FiniteVolumeHyperbolicModel.{u})

/-- Constant curvature `-1/4` in the form `Rm(X,Y,Y,X) = -1/4 · (|X|²|Y|² - ⟨X,Y⟩²)`. -/
theorem metricRm_eq_neg_quarter_S26 (x : H.Carrier) (X Y : TangentSpace (𝓡 3) x) :
    metricRm04StandardAt H.metric x X Y Y X =
      -(1 / 4 : ℝ) * (H.metric.inner x X X * H.metric.inner x Y Y -
        H.metric.inner x X Y * H.metric.inner x X Y) :=
  (GC.Geometry.hasConstantSectionalCurvature_iff H.metric (-(1 / 4 : ℝ))).mp
    H.curvature.toGC x X Y

/-- Sectional curvature `≥ -1/4` everywhere, in the `SectionalBoundedBelowAt` form. -/
theorem sectionalBoundedBelowAt_neg_quarter_S26 (x : H.Carrier) :
    SectionalBoundedBelowAt H.metric x (-(1 / 4 : ℝ)) := by
  intro v w
  rw [metricRm_eq_neg_quarter_S26 H x v w]
  apply le_of_eq
  ring

/-- **(G4)** The curvature radius of a hyperbolic model of curvature `-1/4` is `2` at every point. -/
theorem curvatureRadius_eq_two_S26 (y : H.Carrier) :
    curvatureRadius H.metric y = ENNReal.ofReal 2 := by
  apply le_antisymm
  · unfold curvatureRadius
    refine iSup_le fun r => iSup_le fun hr => iSup_le fun hball => ENNReal.ofReal_le_ofReal ?_
    have hy : y ∈ riemannianBallOf H.metric y r := by
      change riemannianEDistOf H.metric y y < ENNReal.ofReal r
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hr
    have hsec := hball y hy
    let v : TangentSpace (𝓡 3) y := EuclideanSpace.single 0 1
    let w : TangentSpace (𝓡 3) y := EuclideanSpace.single 1 1
    have hli : LinearIndependent ℝ ![v, w] := by
      have h := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent
      have hinj : Function.Injective (![0, 1] : Fin 2 → Fin 3) := by decide
      have h2 := h.comp (![0, 1] : Fin 2 → Fin 3) hinj
      have heq : (![v, w] : Fin 2 → TangentSpace (𝓡 3) y) =
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis ∘ (![0, 1] : Fin 2 → Fin 3) := by
        funext i
        fin_cases i
        · exact (EuclideanSpace.basisFun_apply (Fin 3) ℝ 0).symm
        · exact (EuclideanSpace.basisFun_apply (Fin 3) ℝ 1).symm
      rw [heq]
      exact h2
    have hden : 0 < H.metric.inner y v v * H.metric.inner y w w - H.metric.inner y v w ^ 2 := by
      simpa only [sectionalCurvatureDenominator_def] using
        sectionalCurvatureDenominator_pos_of_linearIndependent H.metric y v w hli
    have h1 := hsec v w
    rw [metricRm_eq_neg_quarter_S26 H y v w] at h1
    have h2 : -(r ^ 2)⁻¹ * (H.metric.inner y v v * H.metric.inner y w w -
        H.metric.inner y v w ^ 2) ≤
        -(1 / 4 : ℝ) * (H.metric.inner y v v * H.metric.inner y w w -
        H.metric.inner y v w ^ 2) := by
      convert h1 using 2
      ring
    have h3 : -(r ^ 2)⁻¹ ≤ -(1 / 4 : ℝ) := le_of_mul_le_mul_right h2 hden
    have h4 : (1 / 4 : ℝ) ≤ (r ^ 2)⁻¹ := by linarith
    have hr2 : 0 < r ^ 2 := by positivity
    have h5 : r ^ 2 ≤ 4 := by
      rw [← one_div, le_div_iff₀ hr2] at h4
      linarith
    nlinarith
  · unfold curvatureRadius
    refine le_iSup_of_le 2 (le_iSup_of_le (by norm_num) (le_iSup_of_le ?_ le_rfl))
    intro q _
    have h := sectionalBoundedBelowAt_neg_quarter_S26 H q
    convert h using 2
    norm_num

end GC.LongTime.Ch12
