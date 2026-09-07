import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Comparison.Busemann.Asymptotic
import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Mathlib.Topology.Separation.Connected

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Operator
open Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normGradSqFun_busemann_eq_one
    [ConnectedSpace M]
    [RiemannianBundle (fun z : M => TangentSpace I z)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun z : M => TangentSpace I z)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {gamma : Real → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) (x : M)
    (hB : MDifferentiableAt I 𝓘(Real, Real)
      (busemann (I := I) gamma) x) :
    normGradSqFun (I := I) g (busemann (I := I) gamma) x = 1 := by
  classical
  let _ : NeZero (Module.finrank Real E) := ⟨by
    intro hdim
    let _ : Subsingleton E := (Module.finrank_zero_iff (R := Real)).mp hdim
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let _ : Subsingleton M := PreconnectedSpace.trivial_of_discrete
    have hd := hgamma.edist_eq (s := 0) (t := 1) (by norm_num) (by norm_num)
    rw [Subsingleton.elim (gamma 0) (gamma 1), riemannianEDist_self] at hd
    norm_num at hd⟩
  let b : M → Real := busemann (I := I) gamma
  change MDifferentiableAt I 𝓘(Real, Real) b x at hB
  obtain ⟨u, hu, hdata⟩ :=
    exists_asymptotic_ray (I := I) g hEnorm hgamma x
  let sigma : Real → M := fun t ↦
    expMapIntrinsic (I := I) g hEnorm x (t • u)
  change IsMinimizingRay (I := I) g x sigma ∧
    (∀ (t : Real), 0 ≤ t → ∀ y : M,
      b y ≤ (riemannianEDist I (sigma t) y).toReal - t + b x) at hdata
  rcases hdata with ⟨hsigma, hsupport⟩
  have hsigma_zero : sigma 0 = x := hsigma.start_eq
  have hb_sigma : ∀ {t : Real}, 0 ≤ t →
      b (sigma t) = b x - t := by
    intro t ht
    have hupper := hsupport t ht (sigma t)
    have hlower := busemann_sub_le (I := I) hgamma x (sigma t)
    have hdist : (riemannianEDist I x (sigma t)).toReal = t := by
      rw [← hsigma_zero, hsigma.edist_eq (le_refl 0) ht, sub_zero,
        ENNReal.toReal_ofReal ht]
    simp only [riemannianEDist_self, ENNReal.toReal_zero, zero_sub] at hupper
    rw [hdist] at hlower
    linarith
  have hsigma_eq :
      sigma = intrinsicGeodesic (I := I) g hEnorm x u := by
    funext t
    simpa only [sigma, expMapIntrinsic_def] using
      intrinsicGeodesic_smul (I := I) g hEnorm x u t
  have hsigma_md : MDifferentiableAt 𝓘(Real, Real) I sigma 0 := by
    rw [hsigma_eq]
    exact (intrinsicGeodesic_contMDiff (I := I) g hEnorm x u).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hsigma_deriv :
      (mfderiv 𝓘(Real, Real) I sigma 0 (1 : Real) : E) = (u : E) := by
    rw [hsigma_eq]
    exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x u
  have hreal_one :
      DifferentialGeometry.Analysis.Calculus.realTangentOne 0 =
        (1 : TangentSpace 𝓘(Real, Real) (0 : Real)) := by
    apply (NormedSpace.fromTangentSpace 0).injective
    rw [DifferentialGeometry.Analysis.Calculus.fromTangentSpace_realTangentOne]
    rfl
  have hB_zero : MDifferentiableAt I 𝓘(Real, Real) b (sigma 0) := by
    simpa only [hsigma_zero] using hB
  let q : Real :=
    NormedSpace.fromTangentSpace (b (sigma 0))
      (mfderiv I 𝓘(Real, Real) b (sigma 0)
        (mfderiv 𝓘(Real, Real) I sigma 0
          (DifferentialGeometry.Analysis.Calculus.realTangentOne 0)))
  have hcurve : HasDerivAt (fun t : Real ↦ b (sigma t)) q 0 := by
    simpa only [q] using
      DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
        I b sigma 0 hB_zero hsigma_md
  have hlinear : HasDerivWithinAt ((fun _ : Real ↦ b x) - id) (0 - 1)
      (Ici 0) 0 :=
    ((hasDerivAt_const (x := (0 : Real)) (c := b x)).sub
      (hasDerivAt_id (x := (0 : Real)))).hasDerivWithinAt
  have hcurve_neg := hlinear.congr (f₁ := fun t : Real ↦ b (sigma t))
    (fun t ht ↦ by
      dsimp
      exact hb_sigma ht)
    (by
      dsimp
      exact hb_sigma (le_refl 0))
  have hq : q = 0 - 1 :=
    UniqueDiffWithinAt.eq_deriv (Ici (0 : Real))
      (uniqueDiffWithinAt_Ici (0 : Real)) hcurve.hasDerivWithinAt hcurve_neg
  have hpair_start :
      g.inner (sigma 0) (gradFun (I := I) g b (sigma 0))
        (mfderiv 𝓘(Real, Real) I sigma 0
          (DifferentialGeometry.Analysis.Calculus.realTangentOne 0)) = -1 := by
    rw [inner_gradFun (I := I) g b]
    change NormedSpace.fromTangentSpace (b (sigma 0))
      (mfderiv I 𝓘(Real, Real) b (sigma 0)
        (mfderiv 𝓘(Real, Real) I sigma 0
          (DifferentialGeometry.Analysis.Calculus.realTangentOne 0))) = -1
    simpa only [q, sub_eq_add_neg, zero_add] using hq
  let w : E := show E from mfderiv 𝓘(Real, Real) I sigma 0
    (DifferentialGeometry.Analysis.Calculus.realTangentOne 0)
  have hw : w = (u : E) := by
    dsimp only [w]
    rw [hreal_one]
    exact hsigma_deriv
  have pair_of_eq :
      ∀ (y : M) (hy : y = x) (z : TangentSpace I y),
        (show E from z) = (u : E) →
        g.inner y (gradFun (I := I) g b y) z = -1 →
        g.inner x (gradFun (I := I) g b x) u = -1 := by
    intro y hy z hz hpair_y
    subst y
    have hzu : z = u := hz
    rwa [hzu] at hpair_y
  have hpair : g.inner x (gradFun (I := I) g b x) u = -1 := by
    exact pair_of_eq (sigma 0) hsigma_zero
      (mfderiv 𝓘(Real, Real) I sigma 0
        (DifferentialGeometry.Analysis.Calculus.realTangentOne 0)) hw hpair_start
  have hb_lip : ∀ y z, edist (b y) (b z) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g y z := by
    intro y z
    simpa only [b, one_mul, riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
      using edist_busemann_le_riemannianEDist (I := I) hgamma y z
  have hupper : Real.sqrt
      (g.inner x (gradFun (I := I) g b x)
        (gradFun (I := I) g b x)) ≤ 1 := by
    have hgrad := grad_norm_le_lip (I := I) g hb_lip hB
    simpa only [NNReal.coe_one] using hgrad
  let v : TangentSpace I x := gradFun (I := I) g b x
  have hcs : |g.inner x v u| ≤
      Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x u u) := by
    exact
      DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
        (I := I) (M := M) g x v u
  have hlower : 1 ≤ Real.sqrt (g.inner x v v) := by
    rw [show g.inner x v u = -1 by simpa only [v] using hpair,
      abs_neg, abs_one, hu, Real.sqrt_one, mul_one] at hcs
    exact hcs
  have hsqrt : Real.sqrt (g.inner x v v) = 1 :=
    le_antisymm (by simpa only [v] using hupper) hlower
  have hnonneg : 0 ≤ g.inner x v v :=
    DifferentialGeometry.metric_inner_self_nonneg (I := I) (M := M) g x v
  change g.inner x v v = 1
  rw [← Real.sq_sqrt hnonneg, hsqrt, one_pow]

end Riemannian
end Geometry
end DifferentialGeometry
