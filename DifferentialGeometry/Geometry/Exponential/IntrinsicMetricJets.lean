import DifferentialGeometry.Geometry.Exponential.IntrinsicFramedJacobi
import DifferentialGeometry.Geometry.Exponential.IntrinsicJacobiJets
import DifferentialGeometry.Analysis.Calculus.DirectionalJet
import DifferentialGeometry.Tensor.Multilinear.Polarization
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff ENNReal Topology BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open Exponential
open Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
noncomputable def intrMetricJet
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r : Real) : Real :=
  Finset.sum (Finset.range (n + 1)) fun i =>
    (n.choose i : Real) *
      g.inner
        (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
        (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))
        (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
@[simp]
theorem intrMetricJet_zero
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r : Real) :
    intrMetricJet (I := I) g hEnorm p u a b 0 r =
      g.inner
        (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
        (intrLaunchJ (I := I) g hEnorm p u a b (r, 1))
        (intrLaunchJ (I := I) g hEnorm p u a b (r, 1)) := by
  simp only [intrMetricJet, Nat.zero_add, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.zero_sub]
  let hMetric : IsMetricNorm (I := I) (M := M) g := by
    unfold IsMetricNorm
    exact hEnorm
  have hzero : intrLaunchJet (I := I) g hEnorm p u a b 0 (r, 1) =
      intrLaunchJ (I := I) g hEnorm p u a b (r, 1) := by
    exact intrLaunchJet_zero (I := I) g hMetric p u a b (r, 1)
  rw [hzero]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem intrMetric_line
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z a b : E) (r : Real) :
    intrFrameMetric (I := I) g hEnorm p (z + r • a) b b =
      intrMetricJet (I := I) g hEnorm p
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p z))
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p a))
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p b)) 0 r := by
  let hMetric : IsMetricNorm (I := I) (M := M) g := by
    unfold IsMetricNorm
    exact hEnorm
  have hJ :
      intrLaunchJ (I := I) g hEnorm p
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p z))
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p a))
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p b)) (r, 1) =
        intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from
            tangentSpaceModelContinuousLinearEquiv (I := I) p
                (normalFrame (I := I) g p z) +
              r • tangentSpaceModelContinuousLinearEquiv (I := I) p
                (normalFrame (I := I) g p a))
          (show TangentSpace I p from
            tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p b)) 1 := by
    convert intrLaunchJ_at (I := I) g hMetric p
      (tangentSpaceModelContinuousLinearEquiv (I := I) p
        (normalFrame (I := I) g p z))
      (tangentSpaceModelContinuousLinearEquiv (I := I) p
        (normalFrame (I := I) g p a))
      (tangentSpaceModelContinuousLinearEquiv (I := I) p
        (normalFrame (I := I) g p b)) r 1 using 1
  have hu :
      (show TangentSpace I p from
        tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p z) +
          r • tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p a)) =
        normalFrame (I := I) g p z + r • normalFrame (I := I) g p a := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
    exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) p
      (normalFrame (I := I) g p z + r • normalFrame (I := I) g p a)
  have hb :
      (show TangentSpace I p from
        tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p b)) = normalFrame (I := I) g p b := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
    rfl
  have hbase :
      (show TangentSpace I p from
        tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p z) +
            r • tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p a) +
          (0 : Real) • tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p b)) =
        normalFrame (I := I) g p z + r • normalFrame (I := I) g p a := by
    have hmodel :
        tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p z) +
            r • tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p a) +
          (0 : Real) • tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p b) =
          tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p z) +
            r • tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p a) := by
      rw [zero_smul, add_zero]
    have ht := congrArg
      (tangentSpaceModelContinuousLinearEquiv (I := I) p).symm hmodel
    convert ht.trans hu using 1
    all_goals rfl
  rw [intrMetricJet_zero, intr_metric_jacobi, hJ,
    intrFrame_apply,
    (normalFrame (I := I) g p).map_add,
    (normalFrame (I := I) g p).map_smul]
  unfold expMapIntrinsic intrLaunch3
  rw [hu, hb]
  congr 3
  convert congrArg
    (fun v : TangentSpace I p => intrinsicGeodesic (I := I) g hMetric p v 1)
    hbase.symm using 1

private theorem metricJet_pascal (n : Nat) (q : Nat → Real) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : Real) * q (i + 1)) +
        (∑ i ∈ Finset.range (n + 1), (n.choose i : Real) * q i) =
      ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : Real) * q i := by
  rw [Finset.sum_range_succ'
      (fun i => ((n + 1).choose i : Real) * q i) (n + 1),
    Finset.sum_range_succ' (fun i => (n.choose i : Real) * q i) n]
  simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_zero_right,
    Nat.cast_one, add_mul, one_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ
      (fun i => (n.choose (i + 1) : Real) * q (i + 1)) n,
    Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem intrMetricJet_deriv
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r : Real) :
    HasDerivAt
      (intrMetricJet (I := I) g hEnorm p u a b n)
      (intrMetricJet (I := I) g hEnorm p u a b (n + 1) r) r := by
  classical
  let f : Real → Real → M := fun s t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t)
  let V : ∀ s t : Real, TangentSpace I (f s t) := fun s t =>
    intrLaunchJ (I := I) g hEnorm p u a b (s, t)
  let q : Nat → Real := fun i =>
    g.inner (f r 1)
      (Variation.covFstIter (I := I) g f i V r 1)
      (Variation.covFstIter (I := I) g f (n + 1 - i) V r 1)
  have hV :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun z : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f z.1 z.2) (V z.1 z.2) : TangentBundle I M)) := by
    simpa only [f, V] using
      intrLaunchJ_smooth (I := I) g hEnorm p u a b
  have hterms : ∀ i ∈ Finset.range (n + 1),
      HasDerivAt
        (fun s : Real =>
          (n.choose i : Real) *
            g.inner (f s 1)
              (Variation.covFstIter (I := I) g f i V s 1)
              (Variation.covFstIter (I := I) g f (n - i) V s 1))
        ((n.choose i : Real) * (q (i + 1) + q i)) r := by
    intro i hi
    have hi : i ≤ n := by
      have hi_lt := Finset.mem_range.mp hi
      omega
    have hsub_succ : n + 1 - (i + 1) = n - i := by
      omega
    have hsub : n + 1 - i = (n - i) + 1 := by
      omega
    have hinner :=
      Variation.innerJet_deriv (I := I) g f V V hV hV
        i (n - i) r 1
    simpa only [q, Nat.succ_eq_add_one, hsub_succ, hsub] using
      hinner.const_mul (n.choose i : Real)
  have hfun :
      (∑ i ∈ Finset.range (n + 1), fun s : Real =>
        (n.choose i : Real) *
          g.inner (f s 1)
            (Variation.covFstIter (I := I) g f i V s 1)
            (Variation.covFstIter (I := I) g f (n - i) V s 1)) =
        intrMetricJet (I := I) g hEnorm p u a b n := by
    funext s
    simp only [intrMetricJet, intrLaunchJet, f, V, Finset.sum_apply]
  have hsumRaw := HasDerivAt.sum hterms
  rw [hfun] at hsumRaw
  have hsum :
      HasDerivAt
        (intrMetricJet (I := I) g hEnorm p u a b n)
        ((∑ i ∈ Finset.range (n + 1),
            (n.choose i : Real) * q (i + 1)) +
          ∑ i ∈ Finset.range (n + 1), (n.choose i : Real) * q i) r := by
    simpa only [mul_add, Finset.sum_add_distrib] using hsumRaw
  rw [metricJet_pascal n q] at hsum
  simpa only [intrMetricJet, intrLaunchJet, q, f, V, Nat.add_assoc] using hsum

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem intrMetricJet_iter
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) :
    iteratedDeriv n (intrMetricJet (I := I) g hEnorm p u a b 0) =
      intrMetricJet (I := I) g hEnorm p u a b n := by
  induction n with
  | zero =>
      simp only [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      exact deriv_eq fun r =>
        intrMetricJet_deriv (I := I) g hEnorm p u a b n r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem intrMetric_diag_jet
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z a b : E) (n : Nat)
    (hsmooth :
      ContDiffAt Real ∞ (intrFrameMetric (I := I) g hEnorm p) z) :
    iteratedFDeriv Real n (intrFrameMetric (I := I) g hEnorm p) z
        (fun _ => a) b b =
      intrMetricJet (I := I) g hEnorm p
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p z))
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p a))
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p b)) n 0 := by
  have haff :
      ContDiffAt Real ∞ (fun r : Real => z + r • a) 0 :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
  have hline :
      ContDiffAt Real ∞
        (fun r : Real =>
          intrFrameMetric (I := I) g hEnorm p (z + r • a)) 0 := by
    have hsmooth0 :
        ContDiffAt Real ∞ (intrFrameMetric (I := I) g hEnorm p)
          (z + (0 : Real) • a) := by
      simpa only [zero_smul, add_zero] using hsmooth
    change ContDiffAt Real ∞
      (intrFrameMetric (I := I) g hEnorm p ∘ fun r : Real => z + r • a) 0
    exact hsmooth0.comp 0 haff
  have hdiag :
      iteratedDeriv n
          (fun r : Real =>
            intrFrameMetric (I := I) g hEnorm p (z + r • a) b b) 0 =
        iteratedFDeriv Real n
          (intrFrameMetric (I := I) g hEnorm p) z
          (fun _ => a) b b := by
    calc
      iteratedDeriv n
          (fun r : Real =>
            intrFrameMetric (I := I) g hEnorm p (z + r • a) b b) 0 =
          iteratedDeriv n
            (fun r : Real =>
              intrFrameMetric (I := I) g hEnorm p (z + r • a)) 0 b b :=
        iteratedDeriv_apply₂ hline n b b
      _ = iteratedFDeriv Real n
            (intrFrameMetric (I := I) g hEnorm p) z
            (fun _ => a) b b := by
        exact congrArg
          (fun B : E →L[Real] E →L[Real] Real => B b b)
          (iteratedDeriv_line hsmooth n)
  have hfun :
      (fun r : Real =>
        intrFrameMetric (I := I) g hEnorm p (z + r • a) b b) =
        intrMetricJet (I := I) g hEnorm p
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p z))
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p a))
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p b)) 0 := by
    funext r
    exact intrMetric_line (I := I) g hEnorm p z a b r
  rw [hfun, intrMetricJet_iter] at hdiag
  exact hdiag.symm

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry

end
