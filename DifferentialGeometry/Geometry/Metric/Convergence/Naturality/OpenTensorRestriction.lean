import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {U V : TopologicalSpace.Opens M}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable [T2Space U] [T2Space V]

def restrictOpenTensor02FieldOfSubset (hVU : V ≤ U)
    (A : Tensor0SField (I := I) (M := U) ∞ 2) :
    Tensor0SField (I := I) (M := V) ∞ 2 :=
  pullbackTensor02FieldCross (flatNestedDiffeo (I := I) hVU)
    (restrictOpen0S 2 (V := nestedOpen (U := U) (V := V)) A)

omit [T2Space U] in
theorem restrictOpenTensor02FieldOfSubset_apply (hVU : V ≤ U)
    (A : Tensor0SField (I := I) (M := U) ∞ 2) (x : V)
    (v : Fin 2 → TangentSpace I x) :
    restrictOpenTensor02FieldOfSubset hVU A x v =
      A (TopologicalSpace.Opens.inclusion hVU x) v := by
  unfold restrictOpenTensor02FieldOfSubset
  rw [pullbackTensor02FieldCross_apply, flatNested_mfderiv]
  rfl

omit [T2Space U] in
theorem restrictOpenTensor02FieldOfSubset_eq (hVU : V ≤ U)
    (A : Tensor0SField (I := I) (M := U) ∞ 2) (x : V) :
    restrictOpenTensor02FieldOfSubset hVU A x =
      A (TopologicalSpace.Opens.inclusion hVU x) := by
  ext v
  exact restrictOpenTensor02FieldOfSubset_apply hVU A x v

omit [T2Space U] in
theorem iteratedDerivWithin_restrictOpenTensor02FieldOfSubset (hVU : V ≤ U)
    (A : ℝ → Tensor0SField (I := I) (M := U) ∞ 2) (b : ℕ) (x : V)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {t : ℝ} (ht : t ∈ s) :
    iteratedDerivWithin b (fun u => restrictOpenTensor02FieldOfSubset hVU (A u) x) s t =
      iteratedDerivWithin b (fun u => A u (TopologicalSpace.Opens.inclusion hVU x)) s t := by
  let L : Tensor0SSpace 2 I (TopologicalSpace.Opens.inclusion hVU x) ≃L[ℝ]
      Tensor0SSpace 2 I x :=
    (tensor0SSpaceContinuousLinearEquiv (I := I) 2
      (TopologicalSpace.Opens.inclusion hVU x)).trans
        (tensor0SSpaceContinuousLinearEquiv (I := I) 2 x).symm
  have hL (T : Tensor0SSpace 2 I (TopologicalSpace.Opens.inclusion hVU x)) : L T = T := by
    ext v
    rfl
  have hf : (fun u => restrictOpenTensor02FieldOfSubset hVU (A u) x) =
      L ∘ (fun u => A u (TopologicalSpace.Opens.inclusion hVU x)) := by
    funext u
    rw [Function.comp_apply, hL, restrictOpenTensor02FieldOfSubset_eq]
  rw [hf]
  have hD := congrArg (fun T => T (fun _ => (1 : ℝ)))
    (L.iteratedFDerivWithin_comp_left
      (fun u => A u (TopologicalSpace.Opens.inclusion hVU x)) hs ht b)
  exact hD.trans (hL _)

theorem tensor02CovDerivNormWith_restrictOpenOfSubset [SigmaCompactSpace U]
    (hVU : V ≤ U) (gcov gnorm : SmoothRiemannianMetric I U)
    (A : Tensor0SField (I := I) (M := U) ∞ 2) (a : ℕ) (x : V) :
    tensor02CovDerivNormWith a (restrictOpenTensor02FieldOfSubset hVU A)
      (gcov.restrictOpenOfSubset hVU) (gnorm.restrictOpenOfSubset hVU) x =
      tensor02CovDerivNormWith a A gcov gnorm (TopologicalSpace.Opens.inclusion hVU x) := by
  let W := nestedOpen (U := U) (V := V)
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let : SigmaCompactSpace V := by
    apply isSigmaCompact_univ_iff.mp
    have hh := isSigmaCompact_range (flatNestedDiffeo (I := I) hVU).symm.continuous
    rwa [EquivLike.range_eq_univ] at hh
  rw [restrictSubset_pull hVU gcov, restrictSubset_pull hVU gnorm]
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    ← Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
  exact (tensor02CovDerivNormWith_pullbackTensor02FieldCross
    (gcov.restrictOpen W) (gnorm.restrictOpen W) (flatNestedDiffeo (I := I) hVU)
    (restrictOpen0S 2 (V := W) A) a x).trans
      (tensor02CovDerivNormWith_restrictOpen0S W gcov gnorm A a
        (flatNestedDiffeo (I := I) hVU x))

end DifferentialGeometry.CheegerGromovCompactness
