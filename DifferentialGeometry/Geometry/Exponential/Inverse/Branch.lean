import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.Basic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

section ChartDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private def modelMFDerivAt (f : E → M) (u : E) : E →L[Real] E :=
  (tangentSpaceModelContinuousLinearEquiv (I := I) (f u)).toContinuousLinearMap.comp
    ((mfderiv 𝓘(Real, E) I f u).comp
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) u).symm.toContinuousLinearMap)

theorem hasFDerivAt_chart
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u) :
    HasFDerivAt
      ((extChartAt I (f u)) ∘ f)
      (modelMFDerivAt (I := I) f u)
      u := by
  have hf' : HasMFDerivAt 𝓘(Real, E) I f u
      (mfderiv 𝓘(Real, E) I f u) :=
    hf.hasMFDerivAt
  have hchart : HasMFDerivAt I 𝓘(Real, E) (extChartAt I (f u)) (f u)
      (ContinuousLinearMap.id Real E) := by
    have h :=
      (mdifferentiableAt_extChartAt (I := I)
        (mem_chart_source H (f u))).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := f u)] at h
    exact h
  have hcomp : HasMFDerivAt 𝓘(Real, E) 𝓘(Real, E)
      ((extChartAt I (f u)) ∘ f) u
      ((ContinuousLinearMap.id Real E).comp
        (mfderiv 𝓘(Real, E) I f u)) :=
    hchart.comp u hf'
  have hcomp' := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  exact hcomp'.congr_fderiv (by
    ext v
    with_unfolding_all rfl)

private theorem written_fderiv_inv
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u)
    (hinv : (mfderiv 𝓘(Real, E) I f u).IsInvertible) :
    (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (extChartAt 𝓘(Real, E) u u)).IsInvertible := by
  have hchart := hasFDerivAt_chart (I := I) hf
  have hwritten : HasFDerivAt
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (modelMFDerivAt (I := I) f u)
      (extChartAt 𝓘(Real, E) u u) := by
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id, id_eq] using hchart
  rw [hwritten.fderiv]
  simpa only [modelMFDerivAt, ContinuousLinearMap.isInvertible_comp_equiv,
    ContinuousLinearMap.isInvertible_equiv_comp] using hinv

end ChartDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [Module.Finite Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

structure ExponentialInverseBranch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) where
  hom : PartialDiffeomorph 𝓘(Real, E) I E M ∞
  hom_eq :
    EqOn
      (fun u : E =>
        expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u))
      hom
      hom.source

namespace ExponentialInverseBranch

def inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) : M → E :=
  B.hom.symm

def dom
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) : Set M :=
  B.hom.target

theorem right_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {y : M} (hy : y ∈ B.dom) :
    expMapIntrinsic (I := I) g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv y)) = y := by
  have hu : B.inv y ∈ B.hom.source := B.hom.map_target hy
  calc
    expMapIntrinsic (I := I) g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv y)) =
      B.hom (B.inv y) := B.hom_eq hu
    _ = y := B.hom.right_inv hy

theorem left_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : E} (hu : u ∈ B.hom.source) :
    B.inv
        (expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)) = u := by
  calc
    B.inv
        (expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)) =
      B.inv (B.hom u) := congrArg B.inv (B.hom_eq hu)
    _ = u := B.hom.left_inv hu

theorem inv_contMDiffOn
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) :
    ContMDiffOn I 𝓘(Real, E) ∞ B.inv B.dom := by
  exact B.hom.contMDiffOn_invFun

end ExponentialInverseBranch

private theorem branch_of_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {u : E}
    (hu : Function.Injective
      (modelMFDerivAt (I := I)
        (fun z : E =>
          expMapIntrinsic (I := I) g hEnorm p
            ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z))
        u)) :
    ∃ B : ExponentialInverseBranch (I := I) g hEnorm p, u ∈ B.hom.source := by
  classical
  let f : E → M := fun z : E =>
    expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z)
  have hf : ContMDiff 𝓘(Real, E) I ∞ f :=
    intrinsicFiber_smooth (I := I) g hEnorm p
  let A := modelMFDerivAt (I := I) f u
  have hAinj : Function.Injective A := by
    simpa only [f, A] using hu
  have hAsurj : Function.Surjective A :=
    LinearMap.surjective_of_injective hAinj
  let D : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hAinj)
      (LinearMap.range_eq_top.mpr hAsurj)
  have hAinv : A.IsInvertible := by
    refine ⟨D, ?_⟩
    rfl
  have hDinv : (mfderiv 𝓘(Real, E) I f u).IsInvertible := by
    simpa only [A, modelMFDerivAt, ContinuousLinearMap.isInvertible_comp_equiv,
      ContinuousLinearMap.isInvertible_equiv_comp] using hAinv
  have hfu : MDifferentiableAt 𝓘(Real, E) I f u :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hfd_u : (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (extChartAt 𝓘(Real, E) u u)).IsInvertible :=
    written_fderiv_inv (I := I) hfu hDinv
  have hf1 : ContMDiffAt 𝓘(Real, E) I 1 f u :=
    hf.contMDiffAt.of_le (by exact_mod_cast le_top)
  obtain ⟨Ψ, huΨ, hEqΨ⟩ :=
    Coordinates.contMDiffAt_isLocalDiffeomorphAt
      (I := 𝓘(Real, E)) (J := I)
      (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hf1 hfd_u
  have hinv_source : ∀ z ∈ Ψ.source,
      (fderiv Real
        (writtenInExtChartAt 𝓘(Real, E) I z f)
        (extChartAt 𝓘(Real, E) z z)).IsInvertible := by
    intro z hz
    have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1 f z :=
      ⟨Ψ, hz, hEqΨ⟩
    have hDzinv : (mfderiv 𝓘(Real, E) I f z).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    exact written_fderiv_inv (I := I)
      (hf.contMDiffAt.mdifferentiableAt (by simp)) hDzinv
  obtain ⟨Φ, huΦ, -, hEqΦ⟩ :=
    Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty (I := 𝓘(Real, E)) (J := I)
      Ψ.open_source huΨ hf.contMDiffOn hinv_source
  exact ⟨⟨Φ, hEqΦ⟩, huΦ⟩

theorem branch_of_not_conj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {u : TangentSpace I p}
    (hu : ¬ IsConjVec (I := I) g hEnorm p
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u)) :
    ∃ B : ExponentialInverseBranch (I := I) g hEnorm p,
      tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source := by
  classical
  apply branch_of_inj (I := I) g hEnorm
  have hu' : Function.Injective fun w : E =>
      mfderiv 𝓘(Real, E) I
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p u)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p u)).symm w) :=
    Classical.not_not.mp (by
      with_unfolding_all exact hu)
  intro v w hvw
  apply hu'
  exact (tangentSpaceModelContinuousLinearEquiv (I := I)
    (expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) p u)))).injective hvw

namespace ExponentialInverseBranch

theorem not_conj
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source) :
    ¬ IsConjVec (I := I) g hEnorm p
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u) := by
  classical
  let f : E → M := fun z : E =>
    expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z)
  have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I ∞ f
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u) :=
    ⟨B.hom, hu, B.hom_eq⟩
  let D := hloc.mfderivToContinuousLinearEquiv (by simp)
  have hinj := D.injective
  intro hconj
  have hnotinj : ¬ Function.Injective fun w : E =>
      mfderiv 𝓘(Real, E) I f (tangentSpaceModelContinuousLinearEquiv (I := I) p u)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p u)).symm w) := by
    with_unfolding_all exact hconj
  apply hnotinj
  intro v w hvw
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(Real, E))
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u)).symm.injective
  exact hinj hvw

end ExponentialInverseBranch

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
