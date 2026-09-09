import DifferentialGeometry.Geometry.Metric.Family.Pullback
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Curvature.UniversalCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
open Bundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow
open Geometry.Riemannian.Topology
open Tensor.RSTensor
open Geometry.Riemannian.Topology.UniversalCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

def SolutionOn.universalCover {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    SolutionOn (I := I) (M := UniversalCover M) D :=
  { base := { metric := fun t => liftedMetric (S.base.metric t) } }

theorem SolutionOn.universalCover_scalar {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : UniversalCover M) :
    S.universalCover.scalar t x = S.scalar t (proj x) :=
  metricScalarAt_lifted (S.base.metric t) x

private theorem lifted_ricci (g : SmoothRiemannianMetric I M) (x : UniversalCover M)
    (v w : E) : ricciTensor (I := I) (liftedMetric g) x v w =
      ricciTensor (I := I) g (proj x) v w :=
  ricciTensor_lifted_natural g x v w
    (Geometry.Connection.chartRiemannBasisIdentity_holds (liftedMetric g) x)
    (Geometry.Connection.chartRiemannBasisIdentity_holds g (proj x))

private theorem lifted_metricRicci (g : SmoothRiemannianMetric I M) (x : UniversalCover M)
    (slots : Fin 2 → E) : metricRicciAt (I := I) (liftedMetric g) x slots =
      metricRicciAt (I := I) g (proj x) slots := by
  have hslots₁ : (vec2 (I := I) (x := x) (slots 0) (slots 1) : Fin 2 → E) = slots := by
    ext i; fin_cases i <;> rfl
  have hslots₂ : (vec2 (I := I) (x := proj x) (slots 0) (slots 1) : Fin 2 → E) = slots := by
    ext i; fin_cases i <;> rfl
  have h₁ := metricRicciAt_apply_eq_ricciTensor (I := I) (liftedMetric g) x (slots 0) (slots 1)
  have h₂ := metricRicciAt_apply_eq_ricciTensor (I := I) g (proj x) (slots 0) (slots 1)
  exact (congrArg (metricRicciAt (liftedMetric g) x) hslots₁.symm).trans
    (h₁.trans ((lifted_ricci g x _ _).trans
      (h₂.symm.trans (congrArg (metricRicciAt g (proj x)) hslots₂))))

theorem IsSolutionOn.universalCover {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    IsSolutionOn S.universalCover where
  smoothMetric := by
    apply hS.smoothMetric.of_pullback (fun t => liftedMetric (S.base.metric t))
      proj (proj_contMDiff (I := I))
    intro t x v w
    rw [(hasMFDerivAt_proj (I := I) x).mfderiv]
    rfl
  smoothConnection := by
    intro t
    exact Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
      (S.universalCover.base.metric (t : ℝ))
  equation := by
    intro t x v w
    have h := hS.equation t (proj x) v w
    have hRic := lifted_ricci (S.base.metric (t : ℝ)) x v w
    have hb := metricRicciAt_apply_eq_ricciTensor (I := I)
      (S.base.metric (t : ℝ)) (proj x) v w
    have hc := metricRicciAt_apply_eq_ricciTensor (I := I)
      (liftedMetric (S.base.metric (t : ℝ))) x v w
    change HasDerivWithinAt (fun s => (S.base.metric s).inner (proj x) v w)
      (-2 * metricRicciAt (S.base.metric (t : ℝ)) (proj x) (vec2 (x := proj x) v w))
      D.carrier (t : ℝ) at h
    have hd : metricRicciAt (S.base.metric (t : ℝ)) (proj x) (vec2 (x := proj x) v w) =
        metricRicciAt (liftedMetric (S.base.metric (t : ℝ))) x (vec2 (x := x) v w) :=
      hb.trans (hRic.symm.trans hc.symm)
    have hf : (fun s => (S.universalCover.family.metric s).inner x v w) =
        (fun s => (S.base.metric s).inner (proj x) v w) := by
      funext s
      exact (liftedMetric_inner_eq (S.base.metric s) x v w).symm
    change HasDerivWithinAt (fun s => (S.universalCover.family.metric s).inner x v w)
      (-2 * metricRicciAt (liftedMetric (S.base.metric (t : ℝ))) x (vec2 (x := x) v w))
      D.carrier (t : ℝ)
    rw [hf]
    exact h.congr_deriv (congrArg (fun z : ℝ => -2 * z) hd)

  scalarCont := by
    have heq : (fun q : ℝ × UniversalCover M => S.universalCover.scalar q.1 q.2) =
        (fun q : ℝ × M => S.scalar q.1 q.2) ∘
          (fun q : ℝ × UniversalCover M => (q.1, proj q.2)) := by
      funext q
      exact S.universalCover_scalar q.1 q.2
    rw [heq]
    exact hS.scalarCont.comp
      (continuous_fst.prodMk ((proj_contMDiff (I := I)).continuous.comp continuous_snd)).continuousOn
      (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  scalarTime := by
    intro K t htK hKsub x
    have heq : (fun s : ℝ => S.universalCover.scalar s x) =
        fun s : ℝ => S.scalar s (proj x) := by
      funext s
      exact S.universalCover_scalar s x
    rw [heq]
    exact hS.scalarTime htK hKsub (proj x)
  ricciCont := by
    apply tensor0SFamilyContinuousOnSet.congr
      (hS.ricciCont.pullback_of_contMDiff _ proj ((proj_contMDiff (I := I)).of_le (by norm_num)))
    intro t _ x
    ext slots
    change metricRicciAt (S.base.metric t) (proj x)
      (fun k => mfderiv I I proj x (slots k)) =
      metricRicciAt (liftedMetric (S.base.metric t)) x slots
    rw [(hasMFDerivAt_proj (I := I) x).mfderiv]
    exact (lifted_metricRicci (S.base.metric t) x slots).symm
  rm04Cont := by
    apply tensor0SFamilyContinuousOnSet.congr
      (hS.rm04Cont.pullback_of_contMDiff _ proj ((proj_contMDiff (I := I)).of_le (by norm_num)))
    intro t _ x
    ext slots
    change metricRm04At (S.base.metric t) (proj x)
      (fun k => mfderiv I I proj x (slots k)) =
      metricRm04At (liftedMetric (S.base.metric t)) x slots
    rw [(hasMFDerivAt_proj (I := I) x).mfderiv]
    exact (metricRm04At_liftedMetric_apply (S.base.metric t) x slots).symm
  ricciNormSpace := by
    intro t _ x
    have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ (ricciNorm S.universalCover t) := by
      refine (normSq02_smooth (S.universalCover.family.metric t)
        (metricRicci (S.universalCover.family.metric t))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact hsm.mdifferentiableAt (by simp)
  ricciNormGrad := by
    intro t _ x
    have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ (ricciNorm S.universalCover t) := by
      refine (normSq02_smooth (S.universalCover.family.metric t)
        (metricRicci (S.universalCover.family.metric t))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact Geometry.Operator.gradientFun_mdiffAt (S.universalCover.family.metric t) hsm x

omit [I.Boundaryless] in
theorem SolutionOn.universalCover_complete
    [SigmaCompactSpace M] [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (hcomplete : RiemannianMetricComplete (S.base.metric t)) :
    let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    RiemannianMetricComplete (S.universalCover.base.metric t) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact liftedMetric_complete (S.base.metric t) hcomplete

def CompleteBoundedCurvatureSolutionOn.universalCover
    [SigmaCompactSpace M] [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) :
    let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    CompleteBoundedCurvatureSolutionOn (I := I) (M := UniversalCover M) (D := D) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact {
    solution := S.solution.universalCover
    isSolution := S.isSolution.universalCover S.solution
    complete := fun t ht => S.solution.universalCover_complete t (S.complete t ht)
    curvatureBound := by
      intro t ht
      obtain ⟨C, hC, hbound⟩ := S.curvatureBound t ht
      refine ⟨C, hC, fun x => ?_⟩
      change normSq0S (liftedMetric (S.solution.base.metric t)) x 4
        (metricRm04At (liftedMetric (S.solution.base.metric t)) x) ≤ C
      rw [normSq0S_metricRm04At_liftedMetric]
      exact hbound (proj x) }

end DifferentialGeometry.PDE.RicciFlow
