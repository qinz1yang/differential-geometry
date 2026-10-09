import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedLimitDomain
import DifferentialGeometry.Geometry.Metric.Path.RiemannianHopfRinow

/-!
# Literal intrinsic distances on the original buffered open limit source

The inverse inclusion and the two buffered radial inequalities identify the actual restricted
metric distance near the center with the complete ambient distance, without source completeness.
-/

set_option autoImplicit false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem bufferedOpen_restricted_edist_eq
    (g : SmoothRiemannianMetric I M) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) (n q : U)
    (hbuffer : Metric.closedBall (n : M) 10 ⊆ U)
    (hq : (q : M) ∈ Metric.ball (n : M) 3) :
    riemannianEDistOf (g.restrictOpen U) n q = edist (n : M) (q : M) := by
  let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I) U ⟨n⟩
  have hjFun : (j : U → M) = Subtype.val :=
    U.openPartialHomeomorphSubtypeCoe_coe ⟨n⟩
  have hjTarget : j.target = U := U.openPartialHomeomorphSubtypeCoe_target ⟨n⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    hNorm.isContinuousRiemannianBundle
  have hd (x y : M) : riemannianEDistOf g x y = edist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist g hNorm,
      ← IsRiemannianManifold.out (I := I)]
  have hball : riemannianClosedBallOf g (n : M) 10 = Metric.closedBall (n : M) 10 := by
    ext x
    change riemannianEDistOf g (n : M) x ≤ ENNReal.ofReal 10 ↔ dist x (n : M) ≤ 10
    rw [hd, edist_dist]
    simpa only [dist_comm] using
      (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 10))
  let : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hcpt : IsCompact (riemannianClosedBallOf g (n : M) 10) :=
    hball ▸ isCompact_closedBall (n : M) 10
  have hsource : riemannianClosedBallOf g (n : M) 10 ⊆ j.symm.source := by
    rw [hball]
    change Metric.closedBall (n : M) 10 ⊆ j.target
    rw [hjTarget]
    exact hbuffer
  have hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      (g.restrictOpen U).inner x v w = g.inner (j x)
        (mfderiv I I (j : U → M) x v) (mfderiv I I (j : U → M) x w) := by
    intro x _hx v w
    change g.inner (x : M) v w = g.inner (x : M)
      (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w)
    rw [DifferentialGeometry.mfderiv_subtype_val_apply,
      DifferentialGeometry.mfderiv_subtype_val_apply]
  have hinverse (x : M) (hx : x ∈ riemannianClosedBallOf g (n : M) 10)
      (v : TangentSpace I x) : g.inner x v v =
        (g.restrictOpen U).inner (j.symm x)
          (mfderiv I I (j.symm : M → U) x v) (mfderiv I I (j.symm : M → U) x v) :=
    metric_identity_of_partialDiffeomorph_inverse (g.restrictOpen U) g j hmetric
      x (hsource hx) v v
  have hnear : riemannianEDistOf g (n : M) (q : M) < ENNReal.ofReal 10 := by
    rw [hd, edist_dist]
    apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.2
    rw [Metric.mem_ball] at hq
    simpa only [dist_comm] using hq.trans (by norm_num : (3 : ℝ) < 10)
  have hlo := le_riemannianEDistOf_map_of_buffered g (g.restrictOpen U) j.symm (n : M)
    (lam := 0) (by norm_num) hcpt hsource
    (fun x hx v => by simpa only [sub_zero, one_pow, one_mul] using (hinverse x hx v).le)
    hnear
  have hhi := riemannianEDistOf_map_le_of_buffered g (g.restrictOpen U) j.symm (n : M)
    (lam := 0) (by norm_num) (by norm_num) hsource
    (fun x hx v => by simpa only [add_zero, one_pow, one_mul] using (hinverse x hx v).symm.le)
    hnear
  have hnInv : j.symm (n : M) = n := by
    have hh := j.left_inv (show n ∈ j.source from mem_univ n)
    rwa [show j n = (n : M) from congrFun hjFun n] at hh
  have hqInv : j.symm (q : M) = q := by
    have hh := j.left_inv (show q ∈ j.source from mem_univ q)
    rwa [show j q = (q : M) from congrFun hjFun q] at hh
  rw [hnInv, hqInv, sub_zero, ENNReal.ofReal_one, one_mul, hd] at hlo
  rw [hnInv, hqInv, add_zero, ENNReal.ofReal_one, one_mul, hd] at hhi
  exact le_antisymm hhi hlo

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

theorem realOpen_restricted_edist_eq :
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-11) 11, isOpen_Ioo⟩
    let n : U := ⟨0, by constructor <;> norm_num⟩
    let q : U := ⟨1, by constructor <;> norm_num⟩
    riemannianEDistOf ((euclideanMetric (E := ℝ)).restrictOpen U) n q = edist (0 : ℝ) 1 := by
  let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-11) 11, isOpen_Ioo⟩
  let n : U := ⟨0, by constructor <;> norm_num⟩
  let q : U := ⟨1, by constructor <;> norm_num⟩
  apply bufferedOpen_restricted_edist_eq (euclideanMetric (E := ℝ)) realMetricNorm U n q
  · intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · norm_num [Metric.mem_ball, Real.dist_eq, n, q]

end DifferentialGeometry.Geometry.Riemannian.Geodesic
