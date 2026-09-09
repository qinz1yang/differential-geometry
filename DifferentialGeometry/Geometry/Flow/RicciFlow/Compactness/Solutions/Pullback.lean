import DifferentialGeometry.Geometry.Metric.Family.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.PullbackCross
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Pullback

import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Family.Continuity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

section Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

def SolutionOn.pullback [T2Space M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N) :
    SolutionOn (I := I) (M := M) D :=
  { base := { metric := fun t => Diffeomorph.pullbackMetricCross (S.base.metric t) Φ } }

private theorem pullback_cross_coeff_eq
    [T2Space M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (X Y : TangentSpace I x) :
    (fun t : ℝ => ((SolutionOn.pullback (I := I) S Φ).family.metric t).inner x X Y)
      = fun t : ℝ => (S.family.metric t).inner (Φ x)
          (mfderiv I J (Φ : M → N) x X) (mfderiv I J (Φ : M → N) x Y) := by
  funext t
  exact Diffeomorph.pullbackMetricCross_inner (I := I) (S.family.metric t) Φ x X Y

variable [T2Space M] [T2Space N]
variable [BoundarylessManifold I M] [BoundarylessManifold J N]

private theorem pullback_equation
    {D : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D) (hS : IsSolutionOn (I := J) S)
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    MetricVariationEquationOn (I := I) (SolutionOn.pullback S Φ) := by
  intro t x X Y
  have hcoeff := pullback_cross_coeff_eq S Φ x X Y
  have hric :
      RicciAtFamily.toTensorField (I := I)
          (SolutionOn.pullback S Φ).ricciAt (t : ℝ) x X Y
        = RicciAtFamily.toTensorField (I := J) S.ricciAt (t : ℝ) (Φ x)
            (mfderiv I J (Φ : M → N) x X) (mfderiv I J (Φ : M → N) x Y) := by
    simp only [RicciAtFamily.toTensorField_apply]
    change metricRicciAt (I := I)
          (Diffeomorph.pullbackMetricCross (S.base.metric (t : ℝ)) Φ) x (vec2 X Y)
        = metricRicciAt (I := J) (S.base.metric (t : ℝ)) (Φ x)
            (vec2 (mfderiv I J (Φ : M → N) x X) (mfderiv I J (Φ : M → N) x Y))
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    exact ricciTensor_cross (S.base.metric (t : ℝ)) Φ x X Y
  rw [hcoeff, hric]
  exact hS.equation t (Φ x)
    (mfderiv I J (Φ : M → N) x X) (mfderiv I J (Φ : M → N) x Y)

theorem SolutionOn.pullback_scalar
    {D : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N) (t : ℝ) (x : M) :
    (SolutionOn.pullback S Φ).scalar t x = S.scalar t (Φ x) := by
  simp only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.pullback]
  exact metricScalar_cross (S.base.metric t) Φ x

theorem IsSolutionOn.pullback
    {D : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D) (hS : IsSolutionOn (I := J) S)
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    IsSolutionOn (I := I) (SolutionOn.pullback S Φ) where
  smoothMetric := hS.smoothMetric.pullback S.family.metric Φ
  smoothConnection := by
    intro t
    exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
      ((SolutionOn.pullback S Φ).base.metric (t : ℝ))
  equation := pullback_equation S hS Φ
  scalarCont := by
    have heq : (fun q : ℝ × M => (SolutionOn.pullback S Φ).scalar q.1 q.2)
        = (fun p : ℝ × N => S.scalar p.1 p.2)
            ∘ (fun q : ℝ × M => ((q.1, Φ q.2) : ℝ × N)) := by
      funext q
      exact SolutionOn.pullback_scalar S Φ q.1 q.2
    rw [heq]
    exact hS.scalarCont.comp
      (continuous_fst.prodMk (Φ.continuous.comp continuous_snd)).continuousOn
      (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  scalarTime := by
    intro K t htK hKsub x
    have heq : (fun s : ℝ => (SolutionOn.pullback S Φ).scalar s x)
        = fun s : ℝ => S.scalar s (Φ x) := by
      funext s
      exact SolutionOn.pullback_scalar S Φ s x
    rw [heq]
    exact hS.scalarTime htK hKsub (Φ x)
  ricciCont := by
    apply tensor0SFamilyContinuousOnSet.congr
      (tensor0SFamilyContinuousOnSet.pullback
        (fun t x => S.ricci t x) hS.ricciCont Φ)
    intro t _ht x
    ext slots
    exact (metricRicci_cross (S.base.metric t) Φ x slots).symm
  rm04Cont := by
    apply tensor0SFamilyContinuousOnSet.congr
      (tensor0SFamilyContinuousOnSet.pullback
        (fun t x => S.base.rm04 t x) hS.rm04Cont Φ)
    intro t _ht x
    ext slots
    exact (metricRm04_cross (S.base.metric t) Φ x slots).symm
  ricciNormSpace := by
    intro t _ht x
    have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (ricciNorm (I := I) (SolutionOn.pullback S Φ) t) := by
      refine (normSq02_smooth (I := I)
        ((SolutionOn.pullback S Φ).family.metric t)
        (metricRicci ((SolutionOn.pullback S Φ).family.metric t))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact hsm.mdifferentiableAt (by simp)
  ricciNormGrad := by
    intro t _ht x
    have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (ricciNorm (I := I) (SolutionOn.pullback S Φ) t) := by
      refine (normSq02_smooth (I := I)
        ((SolutionOn.pullback S Φ).family.metric t)
        (metricRicci ((SolutionOn.pullback S Φ).family.metric t))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact gradientFun_mdiffAt ((SolutionOn.pullback S Φ).family.metric t) hsm x

def CompleteBoundedCurvatureSolutionOn.pullback
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    {D : RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := J) (M := N) (D := D))
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D) where
  solution := SolutionOn.pullback S.solution Φ
  isSolution := IsSolutionOn.pullback S.solution S.isSolution Φ
  complete t ht := RiemannianMetricComplete.pullbackCross (S.solution.base.metric t) Φ
    (S.complete t ht)
  curvatureBound t ht := by
    obtain ⟨C, hC, hbound⟩ := S.curvatureBound t ht
    refine ⟨C, hC, fun x => ?_⟩
    change normSq0S (I := I) (Diffeomorph.pullbackMetricCross (S.solution.base.metric t) Φ) x 4
      (metricRm04At (I := I) (Diffeomorph.pullbackMetricCross (S.solution.base.metric t) Φ) x) ≤ C
    rw [riemannNormSq_cross]
    exact hbound (Φ x)

end Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem gradientFun_pullback
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (f : N → ℝ) (y : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Φ y)) :
    gradientFun (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) (f ∘ (Φ : M → N)) y
      = (Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm
          (gradientFun (I := I) g f (Φ y)) := by
  let _ := (inferInstance : (SigmaCompactSpace M))
  have he : mfderiv I I (Φ : M → N) y
      = ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y :
          TangentSpace I y →L[ℝ] TangentSpace I (Φ y))) :=
    (Φ.mfderivToContinuousLinearEquiv_coe infty_ne_zero (x := y)).symm
  apply (metricFlatEquiv (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) y).injective
  ext w
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, gradientFun_eq, inner_metricSharp,
    Diffeomorph.pullbackMetric_inner, he, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, gradientFun_eq, inner_metricSharp]
  change mvfderiv (I := I) (f ∘ (Φ : M → N)) y w =
    mvfderiv (I := I) f (Φ y)
      ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y) w)
  rw [mvfderiv_comp_apply y hf (Φ.contMDiff.mdifferentiableAt infty_ne_zero) w]
  simp only [he]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem mfderiv_symm_apply
    (Φ : M ≃ₘ⟮I, I⟯ N) (y : M) (v : TangentSpace I (Φ y)) :
    (Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v
      = mfderiv I I (Φ.symm : N → M) (Φ y) v := by
  have he : mfderiv I I (Φ : M → N) y
      = ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y :
          TangentSpace I y →L[ℝ] TangentSpace I (Φ y))) :=
    (Φ.mfderivToContinuousLinearEquiv_coe infty_ne_zero (x := y)).symm
  have heq : ((Φ.symm : N → M) ∘ (Φ : M → N)) =ᶠ[nhds y] id :=
    Filter.Eventually.of_forall (fun z => Φ.symm_apply_apply z)
  have hli : (mfderiv I I (Φ.symm : N → M) (Φ y)
      (mfderiv I I (Φ : M → N) y ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v))
        : TangentSpace I y)
      = (Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v := by
    rw [← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp y (Φ.symm.contMDiff.mdifferentiableAt infty_ne_zero)
        (Φ.contMDiff.mdifferentiableAt infty_ne_zero),
      heq.mfderiv_eq, mfderiv_id]
    exact ContinuousLinearMap.id_apply
      ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v)
  have h2 : mfderiv I I (Φ : M → N) y
      ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v) = v := by
    rw [he, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [h2] at hli
  exact hli.symm

def solutionOnPullback [hSigma : SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionOn (I := I) (M := M) D := by
  let _ := hSigma
  exact { base := { metric := fun t => Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem pullback_coeff_eq
    [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (x : M) (X Y : TangentSpace I x) :
    (fun t : ℝ => ((solutionOnPullback (I := I) S Φ).family.metric t).inner x X Y)
      = fun t : ℝ => (S.family.metric t).inner (Φ x)
          (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y) := by
  funext t
  exact Diffeomorph.pullbackMetric_inner (I := I) (S.family.metric t) Φ x X Y

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metricFamilySmoothOn_pullback
    [SigmaCompactSpace M] [T2Space M]
    [T2Space N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    MetricFamilySmoothOn (I := I) D (solutionOnPullback (I := I) S Φ).family.metric := by
  change MetricFamilySmoothOn D (fun t => Diffeomorph.pullbackMetric (S.base.metric t) Φ)
  simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric, SolutionOn.family_metric] using
    hS.smoothMetric.pullback S.family.metric Φ

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricVariationEquation_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M]
    [IsManifold I 1 N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    MetricVariationEquationOn (I := I) (solutionOnPullback (I := I) S Φ) := by
  intro t x X Y
  have hcoeff := pullback_coeff_eq (I := I) S Φ x X Y
  have hric :
      RicciAtFamily.toTensorField (I := I)
          (solutionOnPullback (I := I) S Φ).ricciAt (t : ℝ) x X Y
        = RicciAtFamily.toTensorField (I := I) S.ricciAt (t : ℝ) (Φ x)
            (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y) := by
    simp only [RicciAtFamily.toTensorField_apply]
    change metricRicciAt (I := I)
          (Diffeomorph.pullbackMetric (I := I) (S.base.metric (t : ℝ)) Φ) x (vec2 X Y)
        = metricRicciAt (I := I) (S.base.metric (t : ℝ)) (Φ x)
            (vec2 (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y))
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    exact DifferentialGeometry.HCGCompactness.ricciTensor_pullback (I := I)
      (S.base.metric (t : ℝ)) Φ x X Y
  rw [hcoeff, hric]
  exact hS.equation t (Φ x)
    (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [hManifoldM : IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [hManifoldN : IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (x : M) :
    (solutionOnPullback (I := I) S Φ).scalar t x = S.scalar t (Φ x) := by
  let _ := hManifoldM
  let _ := hManifoldN
  simp only [SolutionOn.scalar, SolutionFamily.scalar, solutionOnPullback]
  exact DifferentialGeometry.HCGCompactness.metricScalarAt_pullback (I := I)
    (S.base.metric t) Φ x

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarCont_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [hManifoldM : IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [hManifoldN : IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    ContinuousOn (fun q : ℝ × M => (solutionOnPullback (I := I) S Φ).scalar q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)) := by
  let _ := hManifoldM
  let _ := hManifoldN
  have heq : (fun q : ℝ × M => (solutionOnPullback (I := I) S Φ).scalar q.1 q.2)
      = (fun p : ℝ × N => S.scalar p.1 p.2)
          ∘ (fun q : ℝ × M => ((q.1, Φ q.2) : ℝ × N)) := by
    funext q; exact scalar_pullback (I := I) S Φ q.1 q.2
  rw [heq]
  exact hS.scalarCont.comp
    (continuous_fst.prodMk ((Φ.continuous).comp continuous_snd)).continuousOn
    (fun q hq => ⟨hq.1, Set.mem_univ _⟩)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarTime_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [hManifoldM : IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [hManifoldN : IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) {K : Set ℝ} {t : ℝ} (htK : t ∈ K) (hKsub : K ⊆ D.carrier)
    (x : M) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => (solutionOnPullback (I := I) S Φ).scalar s x) K t := by
  let _ := hManifoldM
  let _ := hManifoldN
  have heq : (fun s : ℝ => (solutionOnPullback (I := I) S Φ).scalar s x)
      = fun s : ℝ => S.scalar s (Φ x) := by
    funext s; exact scalar_pullback (I := I) S Φ s x
  rw [heq]
  exact hS.scalarTime htK hKsub (Φ x)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricRicci_pullback_eval
    [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M]
    [IsManifold I 1 N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M)
    (slots : Fin 2 → TangentSpace I x) :
    metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x slots
      = metricRicci (I := I) g (Φ x)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) x (slots q)) := by
  simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
    metricRicci_cross g Φ x slots

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciNorm_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [hManifoldM : IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [hManifoldN : IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (x : M) :
    ricciNorm (I := I) (solutionOnPullback (I := I) S Φ) t x = ricciNorm (I := I) S t (Φ x) := by
  let _ := hManifoldM
  let _ := hManifoldN
  obtain ⟨B, hB⟩ :=
    exists_gOrthonormalBasis (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x
  change Tensor0SBundle.normSq0S (I := I)
        (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x 2
        (metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x)
      = Tensor0SBundle.normSq0S (I := I) (S.base.metric t) (Φ x) 2
          (metricRicci (I := I) (S.base.metric t) (Φ x))
  exact DifferentialGeometry.HCGCompactness.normSq0S_pullback_eval_of_orthonormal (I := I)
    (g := S.base.metric t) Φ x 2 B hB
    (metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x)
    (metricRicci (I := I) (S.base.metric t) (Φ x))
    (fun slots => metricRicci_pullback_eval (I := I) (S.base.metric t) Φ x slots)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciNormSpace_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [hManifoldM : IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [hManifoldN : IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (ht : t ∈ D.carrier) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (ricciNorm (I := I) (solutionOnPullback (I := I) S Φ) t) x := by
  let _ := hManifoldM
  let _ := hManifoldN
  have heq : ricciNorm (I := I) (solutionOnPullback (I := I) S Φ) t
      = (ricciNorm (I := I) S t) ∘ (Φ : M → N) := by
    funext y; exact ricciNorm_pullback (I := I) S Φ t y
  rw [heq]
  exact (hS.ricciNormSpace t ht (Φ x)).comp x
    (Φ.contMDiff.mdifferentiableAt (by simp))

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciCont_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [hManifoldM : IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [hManifoldN : IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => (solutionOnPullback (I := I) S Φ).ricci t x) := by
  let _ := hManifoldM
  let _ := hManifoldN
  apply tensor0SFamilyContinuousOnSet.congr
    (tensor0SFamilyContinuousOnSet.pullback (I := I)
      (fun t x => S.ricci t x) hS.ricciCont Φ)
  intro t _ht x
  ext slots
  exact (metricRicci_pullback_eval (I := I) (S.base.metric t) Φ x slots).symm

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricRm04_pullback_eval
    [T2Space M]
    [T2Space N]
    [IsManifold I 1 M]
    [IsManifold I 1 N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M)
    (slots : Fin 4 → TangentSpace I x) :
    metricRm04 (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x slots
      = metricRm04 (I := I) g (Φ x)
          (fun q : Fin 4 => mfderiv I I (Φ : M → N) x (slots q)) := by
  simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
    metricRm04_cross g Φ x slots

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rm04Cont_pullback
    [SigmaCompactSpace M] [T2Space M]
    [T2Space N]
    [IsManifold I 1 M]
    [IsManifold I 1 N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.carrier
      (fun t x => (solutionOnPullback (I := I) S Φ).base.rm04 t x) := by
  apply tensor0SFamilyContinuousOnSet.congr
    (tensor0SFamilyContinuousOnSet.pullback (I := I)
      (fun t x => S.base.rm04 t x) hS.rm04Cont Φ)
  intro t _ht x
  ext slots
  exact (metricRm04_pullback_eval (I := I) (S.base.metric t) Φ x slots).symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem smoothConnection_pullback
    [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) :
    ConnectionFamilySmoothOn (I := I) (solutionOnPullback (I := I) S Φ).family := by
  intro t
  exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I)
    ((solutionOnPullback (I := I) S Φ).base.metric (t : ℝ))

omit [FiniteDimensional ℝ E] in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isSolutionOn_pullback
    [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 1 N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    IsSolutionOn (I := I) (solutionOnPullback (I := I) S Φ) := by
  have heq : solutionOnPullback S Φ = S.pullback Φ := by
    simp only [solutionOnPullback, SolutionOn.pullback,
      Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
  rw [heq]
  exact hS.pullback S Φ

end RicciFlow
end PDE
end DifferentialGeometry

end
