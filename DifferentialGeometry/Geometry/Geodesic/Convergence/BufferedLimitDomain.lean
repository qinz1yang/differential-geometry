import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedLiftFlow
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype

/-!
# Actual limit geodesic-flow domain on a buffered open source

The complete ambient geodesic remains in the original buffered image by its unit-speed bound.
The native inverse equation then supplies the incomplete source flow on the entire interval.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem bufferedLimit_geodesicFlow_domain
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (j : PartialDiffeomorph I I N M ∞) (n : M)
    (hbuffer : Metric.ball n 10 ⊆ j.target)
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w = g.inner (j x)
        (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x w))
    {q : N} (hq : q ∈ j.source) (hnear : j q ∈ Metric.ball n 3)
    (v : TangentSpace I q) (hunit : h.inner q v v = 1)
    {L : ℝ} (hL : 0 ≤ L) (hLsix : L ≤ 6) :
    let w := mfderiv I I (j : N → M) q v
    let alpha := fun t => j.symm (intrinsicGeodesic g hNorm (j q) w t)
    ∀ t ∈ Icc 0 L, ((⟨q, v⟩ : TangentBundle I N), t) ∈ h.geodesicFlowDomain ∧
      h.geodesicFlow ⟨q, v⟩ t = DifferentialGeometry.velocityLift alpha t ∧
      j (h.geodesicFlow ⟨q, v⟩ t).proj = intrinsicGeodesic g hNorm (j q) w t := by
  let w := mfderiv I I (j : N → M) q v
  let gamma := intrinsicGeodesic g hNorm (j q) w
  let alpha := fun t => j.symm (gamma t)
  have hw : g.inner (j q) w w = 1 := (hmetric q hq v v).symm.trans hunit
  have hfull : ∀ t ∈ Icc 0 L, gamma t ∈ j.target := by
    intro t ht
    have hdisp := dist_intrinsicGeodesic_le_mul g hNorm (j q) w ht.1
    rw [intrinsicGeodesic_zero, hw, Real.sqrt_one, one_mul, sub_zero] at hdisp
    apply hbuffer
    rw [Metric.mem_ball, dist_comm] at hnear ⊢
    have htri := dist_triangle n (j q) (gamma t)
    dsimp only [gamma]
    linarith [ht.2]
  have hinverse : (mfderiv I I (j.symm : M → N) (j q) w : E) = (v : E) := by
    have heq : (j.symm : M → N) ∘ (j : N → M) =ᶠ[𝓝 q] id := by
      filter_upwards [j.open_source.mem_nhds hq] with x hx
      exact j.left_inv hx
    have hcomp := (mfderiv_comp q
      (j.symm.mdifferentiableAt (by simp) (j.map_source hq))
      (j.mdifferentiableAt (by simp) hq)).symm.trans heq.mfderiv_eq
    rw [mfderiv_id] at hcomp
    exact congrArg (fun D : E →L[ℝ] E => D v) hcomp
  have hinit : DifferentialGeometry.velocityLift (I := I) alpha 0 =
      (⟨q, v⟩ : TangentBundle I N) := by
    obtain ⟨hbase, hvel⟩ := inverseIntrinsicGeodesic_velocityLift_zero g hNorm j q hq w
    apply TotalSpace.ext hbase
    exact heq_of_eq (hvel.trans hinverse)
  have hflow := inverseIntrinsicGeodesic_eq_geodesicFlow_on_interval h g hNorm j hmetric
    (j q) w hL hfull
  dsimp only at hflow ⊢
  rw [hinit] at hflow
  intro t ht
  refine ⟨(hflow t ht).1, (hflow t ht).2, ?_⟩
  rw [(hflow t ht).2]
  exact j.right_inv (hfull t ht)

theorem bufferedOpenLimit_geodesicFlow_domain
    (g : SmoothRiemannianMetric I M) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) (n : M) (hbuffer : Metric.ball n 10 ⊆ U)
    (q : U) (hnear : (q : M) ∈ Metric.ball n 3) (v : TangentSpace I q)
    (hunit : (g.restrictOpen U).inner q v v = 1)
    {L : ℝ} (hL : 0 ≤ L) (hLsix : L ≤ 6) :
    ∀ t ∈ Icc 0 L,
      ((⟨q, v⟩ : TangentBundle I U), t) ∈ (g.restrictOpen U).geodesicFlowDomain ∧
      ((g.restrictOpen U).geodesicFlow ⟨q, v⟩ t).proj.val =
        intrinsicGeodesic g hNorm (q : M) (v : E) t := by
  let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I) U ⟨q⟩
  have hjFun : (j : U → M) = Subtype.val :=
    U.openPartialHomeomorphSubtypeCoe_coe ⟨q⟩
  have hjTarget : j.target = U := U.openPartialHomeomorphSubtypeCoe_target ⟨q⟩
  have hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      (g.restrictOpen U).inner x v w = g.inner (j x)
        (mfderiv I I (j : U → M) x v) (mfderiv I I (j : U → M) x w) := by
    intro x _hx v w
    change g.inner (x : M) v w = g.inner (x : M)
      (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w)
    rw [DifferentialGeometry.mfderiv_subtype_val_apply,
      DifferentialGeometry.mfderiv_subtype_val_apply]
  have hflow := bufferedLimit_geodesicFlow_domain (g.restrictOpen U) g hNorm j n
    (hjTarget.symm ▸ hbuffer) hmetric (by exact mem_univ q) hnear v hunit hL hLsix
  dsimp only at hflow
  intro t ht
  refine ⟨(hflow t ht).1, ?_⟩
  have heq := (hflow t ht).2.2
  change (j : U → M) ((g.restrictOpen U).geodesicFlow ⟨q, v⟩ t).proj =
    intrinsicGeodesic g hNorm ((j : U → M) q) (mfderiv I I (j : U → M) q v) t at heq
  rw [hjFun, DifferentialGeometry.mfderiv_subtype_val_apply] at heq
  exact heq


private instance realFinrankPositive : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

private instance realRiemannianContinuous :
    IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  realMetricNorm.isContinuousRiemannianBundle

theorem realOpenUnit_geodesicFlow_domain :
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-10) 10, isOpen_Ioo⟩
    let q : U := ⟨0, by constructor <;> norm_num⟩
    let g := (euclideanMetric (E := ℝ)).restrictOpen U
    ∀ t ∈ Icc 0 6, ((⟨q, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) U), t) ∈
      g.geodesicFlowDomain := by
  let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-10) 10, isOpen_Ioo⟩
  let q : U := ⟨0, by constructor <;> norm_num⟩
  have hbuffer : Metric.ball (0 : ℝ) 10 ⊆ U := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hx
    exact hx
  have hunit : ((euclideanMetric (E := ℝ)).restrictOpen U).inner q (1 : ℝ) (1 : ℝ) = 1 := by
    change inner ℝ (1 : ℝ) 1 = 1
    rw [real_inner_self_eq_norm_sq]
    norm_num
  have hflow := bufferedOpenLimit_geodesicFlow_domain (euclideanMetric (E := ℝ))
    realMetricNorm U 0 hbuffer q (by simp [q]) (1 : ℝ) hunit
    (L := 6) (by norm_num) (by norm_num)
  exact fun t ht => (hflow t ht).1

end DifferentialGeometry.Geometry.Riemannian.Geodesic
