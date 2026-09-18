import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderTimeErrorJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardNeck
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

private theorem bufferedJetNorm_add_le (epsilon : ℝ)
    (gCov gNorm : SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon))
    (A B : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (a : ℕ) (x : spatialNeckBuffer epsilon) :
    tensor02CovDerivNormWith a (A + B) gCov gNorm x ≤
      tensor02CovDerivNormWith a A gCov gNorm x +
        tensor02CovDerivNormWith a B gCov gNorm x := by
  simp only [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_add,
    ContMDiffSection.coe_add, Pi.add_apply]
  exact Tensor0SBundle.sqrt_normSq0S_add_le gNorm x (a + 2) _ _


def backwardForwardErrorJet (epsilon c : ℝ)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2) (q : ℕ) (s : ℝ) :
    Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2 :=
  (c * (-c⁻¹) ^ q) • J q (1 - s / c) + cylinderTimeErrorJet epsilon c q s


theorem backwardForwardErrorJet_zero (epsilon c : ℝ) (hc : (1 : ℝ) / 2 ≤ c)
    (G : ℝ → SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon))
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hJ : ∀ theta ∈ Icc (1 : ℝ) 3, ∀ x v,
      J 0 theta x v = (G theta).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1))
    (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : spatialNeckBuffer epsilon)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    backwardForwardErrorJet epsilon c J 0 s x v =
      (scaleMetric c (lt_of_lt_of_le (by norm_num) hc) (G (1 - s / c))).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon s).inner x (v 0) (v 1) := by
  have htheta := backwardForward_time_mapsTo hc hs
  have htime : 1 - (1 - s / c) = s / c := by ring
  simp only [backwardForwardErrorJet, pow_zero, mul_one, ContMDiffSection.coe_add,
    Pi.add_apply, add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply, smul_apply, smul_eq_mul]
  rw [hJ _ htheta, htime,
    cylinderTimeErrorJet_zero epsilon c (lt_of_lt_of_le (by norm_num) hc) s hs.2,
    scaleMetric_inner, scaleMetric_inner]
  ring


theorem backwardForwardErrorJet_hasDerivWithinAt
    (epsilon c : ℝ) (hc : (1 : ℝ) / 2 ≤ c)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hJ : ∀ q theta, theta ∈ Icc (1 : ℝ) 3 → ∀ (x : spatialNeckBuffer epsilon)
      (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
      HasDerivWithinAt (fun r => J q r x v) (J (q + 1) theta x v) (Icc (1 : ℝ) 3) theta)
    (q : ℕ) (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : spatialNeckBuffer epsilon)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    HasDerivWithinAt (fun r => backwardForwardErrorJet epsilon c J q r x v)
      (backwardForwardErrorJet epsilon c J (q + 1) s x v) (Icc (-1 : ℝ) 0) s := by
  have hmain := backwardForward_time_jet_derivative (fun b r => J b r x v) c
    (backwardForward_time_mapsTo hc) (fun b r hr => hJ b r hr x v) q s hs
  have herr := cylinderTimeErrorJet_hasDerivWithinAt epsilon c q s (Icc (-1 : ℝ) 0) x v
  simpa only [backwardForwardErrorJet, ContMDiffSection.coe_add, Pi.add_apply,
    add_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    smul_apply, smul_eq_mul, Pi.add_def] using hmain.add herr


theorem backwardForwardErrorJet_covNorm_le
    (epsilon c : ℝ) (hc : (1 : ℝ) / 2 ≤ c)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (a q : ℕ) (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : spatialNeckBuffer epsilon) :
    tensor02CovDerivNormWith a (backwardForwardErrorJet epsilon c J q s)
        (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x ≤
      (|c * (-c⁻¹) ^ q| * Real.sqrt ((3 : ℝ) ^ (a + 2))) *
        tensor02CovDerivNormWith a (J q (1 - s / c))
          (strongNeckBackgroundMetric epsilon (1 - (1 - s / c)))
          (strongNeckBackgroundMetric epsilon (1 - (1 - s / c))) x +
        |c - 1| * (3 * Real.sqrt 3) := by
  have hmodel := cylinderTimeErrorJet_covNorm_le epsilon c s hs q a x
  have hreference := strongNeckBackground_backward_forward_covNorm_le epsilon
    (1 - s / c) s (backwardForward_time_mapsTo hc hs) hs (J q (1 - s / c)) a x
  have hsum := bufferedJetNorm_add_le epsilon (strongNeckBackgroundMetric epsilon s)
    (strongNeckBackgroundMetric epsilon s) ((c * (-c⁻¹) ^ q) • J q (1 - s / c))
    (cylinderTimeErrorJet epsilon c q s) a x
  rw [tensor02CovDerivNormWith_smul] at hsum
  have hscale := mul_le_mul_of_nonneg_left hreference (abs_nonneg (c * (-c⁻¹) ^ q))
  exact hsum.trans ((add_le_add hscale hmodel).trans_eq (by ring))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
