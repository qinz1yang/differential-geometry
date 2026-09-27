import DifferentialGeometry.Geometry.Comparison.Soul.NormalTube
import DifferentialGeometry.Geometry.Comparison.Soul.DistanceGradient
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_smooth_infDist_tube
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {S : Set M} (hSne : S.Nonempty) (hScomp : IsCompact S)
    (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅) :
    ∃ ε > 0,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => (Metric.infDist q S) ^ 2)
        {q | Metric.infDist q S < ε} ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => Metric.infDist q S)
        {q | 0 < Metric.infDist q S ∧ Metric.infDist q S < ε} := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let FN := Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ
  let IN := (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod 𝓘(ℝ, FN)
  let NB := TotalSpace FN (normalBundleFiber g S)
  obtain ⟨ε, hε, Φ, _, htarget, _, _, hradius⟩ :=
    exists_normal_tube g hEnorm hsec hSne hScomp hconv hB
  have hnorm : ContMDiff IN 𝓘(ℝ, ℝ) ∞
      (fun z : NB => g.inner z.proj.1 z.snd.1 z.snd.1) :=
    (tangentSquaredLength_contMDiff g).comp
      (normalBundleInclusion_contMDiff g hEnorm hconv hB)
  have hnormInv := hnorm.comp_contMDiffOn Φ.contMDiffOn_invFun
  have hsquare : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => (Metric.infDist q S) ^ 2)
      Φ.target := by
    apply hnormInv.congr
    intro q hq
    have hr := (hradius (Φ.symm q) (Φ.map_target hq)).trans
      (congrArg (fun x : M => Metric.infDist x S) (Φ.toPartialEquiv.right_inv hq))
    have heq := congrArg (fun r : ℝ => r ^ 2) hr
    rw [Real.sq_sqrt (gInner_self_nonneg (I := I) g
      (Φ.symm q).proj.1 (Φ.symm q).snd.1)] at heq
    exact heq.symm
  rw [htarget] at hsquare
  refine ⟨ε, hε, hsquare, ?_⟩
  intro q hq
  have hregion : IsOpen {x : M | Metric.infDist x S < ε} :=
    isOpen_lt (Metric.continuous_infDist_pt S) continuous_const
  have hd := (hsquare q hq.2).contMDiffAt (hregion.mem_nhds hq.2)
  have hsqrt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => Real.sqrt ((Metric.infDist x S) ^ 2)) q :=
    (Real.contDiffAt_sqrt (sq_pos_of_pos hq.1).ne').contMDiffAt.comp q hd
  have heq : (fun x : M => Real.sqrt ((Metric.infDist x S) ^ 2)) =
      fun x => Metric.infDist x S := by
    funext x
    exact Real.sqrt_sq Metric.infDist_nonneg
  rw [heq] at hsqrt
  exact hsqrt.contMDiffWithinAt

theorem exists_smooth_unit_infDist_gradient_tube
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {S : Set M} (hSne : S.Nonempty) (hScomp : IsCompact S)
    (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅) :
    ∃ ε > 0,
      ContMDiffOn I I.tangent ∞
        (T% fun q => gradientFun g (fun x => Metric.infDist x S) q)
        {q | 0 < Metric.infDist q S ∧ Metric.infDist q S < ε} ∧
      ∀ q : M, 0 < Metric.infDist q S → Metric.infDist q S < ε →
        g.inner q (gradientFun g (fun x => Metric.infDist x S) q)
          (gradientFun g (fun x => Metric.infDist x S) q) = 1 ∧
        ∀ u : TangentSpace I q, g.inner q u u = 1 →
          Riemannian.Exponential.intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
          g.inner q (gradientFun g (fun x => Metric.infDist x S) q) u = -1 := by
  obtain ⟨ε, hε, _, hd⟩ := exists_smooth_infDist_tube g hEnorm hsec hSne hScomp hconv hB
  have hU : IsOpen {q : M | 0 < Metric.infDist q S ∧ Metric.infDist q S < ε} :=
    (isOpen_lt continuous_const (Metric.continuous_infDist_pt S)).inter
      (isOpen_lt (Metric.continuous_infDist_pt S) continuous_const)
  obtain ⟨hgrad, hout⟩ := infDist_gradient_smooth_outward_on g hEnorm hScomp hSne hU hd
    (fun _ hq => hq.1)
  exact ⟨ε, hε, hgrad, fun q hq0 hqε => hout q ⟨hq0, hqε⟩⟩

end DifferentialGeometry.Geometry.Topology
