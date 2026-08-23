import DifferentialGeometry.Analysis.Elliptic.MetricBounds

import DifferentialGeometry.Geometry.Exponential.IntrinsicMetricJets
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Estimates.HigherJacobiPair

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry
namespace HCGCompactness

open Geometry.Riemannian.Exponential
open Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

local instance formNormedAdd :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem intrMetricJet_abs_le
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r B : Real) (hB : 0 ≤ B)
    (hjet : forall k, k ≤ n ->
      Real.sqrt
        (g.inner
          (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
          (intrLaunchJet (I := I) g hEnorm p u a b k (r, 1))
          (intrLaunchJet (I := I) g hEnorm p u a b k (r, 1))) ≤ B) :
    |intrMetricJet (I := I) g hEnorm p u a b n r| ≤
      2 ^ n * B ^ 2 := by
  classical
  unfold intrMetricJet
  calc
    |∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) *
          g.inner
            (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
            (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))
            (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))| ≤
        ∑ i ∈ Finset.range (n + 1),
          |(n.choose i : Real) *
            g.inner
              (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
              (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))
              (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : Real) * B ^ 2 := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hin : i ≤ n := by
        have hi_lt := Finset.mem_range.mp hi
        omega
      have hleft := hjet i hin
      have hright := hjet (n - i) (Nat.sub_le n i)
      have hinner :=
        Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
          (I := I) (M := M) g
          (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
          (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))
          (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (n.choose i))
      have hprod :
          Real.sqrt
                (g.inner
                  (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
                  (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))
                  (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))) *
              Real.sqrt
                (g.inner
                  (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
                  (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))
                  (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))) ≤
            B * B :=
        mul_le_mul hleft hright (Real.sqrt_nonneg _) hB
      exact hinner.trans (by simpa only [pow_two] using hprod)
    _ = 2 ^ n * B ^ 2 := by
      rw [← Finset.sum_mul]
      have hsum :
          (∑ i ∈ Finset.range (n + 1), (n.choose i : Real)) =
            2 ^ n := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
      rw [hsum]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrMetricJet_tube
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (hP : BoundedGeometry (I := I) P)
    (p : P.M) (u a b : E) (n : Nat) {U D : Real} (hD : 0 ≤ D) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      simpa using
        (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v)
    Real.sqrt (P.metric.inner p u u) ≤ U →
    Real.sqrt (P.metric.inner p a a) ≤ D →
    Real.sqrt (P.metric.inner p b b) ≤ D →
    |intrMetricJet (I := I) P.metric hEnorm p u a b n 0| ≤
      2 ^ n * jetCap hP.C U D n ^ 2 := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  letI : EMetricSpace P.M := P.emetricSpace (I := I)
  letI : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  letI : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    simpa using
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) P.metric x v)
  dsimp only
  intro hu ha hb
  have hjets :=
    intrJet_upto_le (I := I) P hcomplete hconn hP p u
      (R := 0) (U := U) (D := D) hD (by simpa using hu)
      n a b ha hb 0 (by simp)
  apply intrMetricJet_abs_le (I := I) P.metric hEnorm p u a b n 0
    (jetCap hP.C U D n) (jetCap_nonneg hP.C hD n)
  intro k hk
  simpa only [IntrJetAtom.eval, intrLaunchJet] using
    hjets.1 k hk 1 (by constructor <;> norm_num)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrMetric_deriv_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (hP : BoundedGeometry (I := I) P)
    (p : P.M) (z : E) (n : Nat) (U : Real)
    (hzU : ‖z‖ ≤ U) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      simpa using
        (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v)
    ContDiffAt Real ∞
        (intrFrameMetric (I := I) P.metric hEnorm p) z →
      ‖iteratedFDeriv Real n
          (intrFrameMetric (I := I) P.metric hEnorm p) z‖ ≤
        ContinuousMultilinearMap.polarConst n *
          (2 * (2 ^ n * jetCap hP.C U 1 n ^ 2)) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  letI : EMetricSpace P.M := P.emetricSpace (I := I)
  letI : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  letI : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    simpa using
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) P.metric x v)
  dsimp only
  intro hsmooth
  let A :=
    iteratedFDeriv Real n
      (intrFrameMetric (I := I) P.metric hEnorm p) z
  let S : Real := 2 ^ n * jetCap hP.C U 1 n ^ 2
  have hS : 0 ≤ S := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have htwoS : 0 ≤ 2 * S := mul_nonneg (by norm_num) hS
  have hAsymm : A.IsSymmetric := by
    intro σ
    exact iterFDeriv_perm hsmooth σ
  have hdiag :
      ∀ a : E, ‖a‖ ≤ 1 → ‖A (fun _ => a)‖ ≤ 2 * S := by
    intro a ha
    let B : E →L[Real] E →L[Real] Real := A (fun _ => a)
    have hBsymm : ∀ v w : E, B v w = B w v := by
      intro v w
      have hmetric :
          (fun y : E =>
              intrFrameMetric (I := I) P.metric hEnorm p y v w) =
            fun y : E =>
              intrFrameMetric (I := I) P.metric hEnorm p y w v := by
        funext y
        rw [intrFrameMetric_apply, intrFrameMetric_apply]
        exact P.metric.symm _ _ _
      calc
        B v w =
            iteratedFDeriv Real n
              (fun y : E =>
                intrFrameMetric (I := I) P.metric hEnorm p y v w) z
              (fun _ => a) := by
          exact (iterFDeriv_apply₂ hsmooth n v w (fun _ => a)).symm
        _ = iteratedFDeriv Real n
              (fun y : E =>
                intrFrameMetric (I := I) P.metric hEnorm p y w v) z
              (fun _ => a) := by rw [hmetric]
        _ = B w v :=
          iterFDeriv_apply₂ hsmooth n w v (fun _ => a)
    have hBdiag : ∀ b : E, ‖b‖ ≤ 1 → |B b b| ≤ S := by
      intro b hb
      have hzu :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p z)
                (normalFrame (I := I) P.metric p z)) ≤ U := by
        simpa only [normalFrame_sqrt] using hzU
      have hau :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p a)
                (normalFrame (I := I) P.metric p a)) ≤ 1 := by
        simpa only [normalFrame_sqrt] using ha
      have hbu :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p b)
                (normalFrame (I := I) P.metric p b)) ≤ 1 := by
        simpa only [normalFrame_sqrt] using hb
      have hjet :=
        intrMetricJet_tube (I := I) P hcomplete hconn hP p
          (normalFrame (I := I) P.metric p z)
          (normalFrame (I := I) P.metric p a)
          (normalFrame (I := I) P.metric p b) n
          (U := U) (D := 1) (by norm_num) hzu hau hbu
      change
        |iteratedFDeriv Real n
            (intrFrameMetric (I := I) P.metric hEnorm p) z
            (fun _ => a) b b| ≤ S
      rw [intrMetric_diag_jet (I := I) P.metric hEnorm p z a b n
        hsmooth]
      exact hjet
    have hB :=
      ContinuousLinearMap.opNorm_le_diag2 B hBsymm hS hBdiag
    simpa only [B] using hB
  have hbound :=
    ContinuousMultilinearMap.opNorm_le_diag_unit
      hAsymm htwoS hdiag
  simpa only [A, S] using hbound

end HCGCompactness
end DifferentialGeometry

end
