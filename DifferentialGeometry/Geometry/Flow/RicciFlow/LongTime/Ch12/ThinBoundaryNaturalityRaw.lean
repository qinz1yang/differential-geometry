import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.SmoothCompatibility
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJetRestriction
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# CH12 C4 (G1): raw pullback-error norms as `metricDerivNorm` of smooth metrics on an open set

For a map `F` which is `C^∞` and an immersion on an open set `U`, the raw error norm
`‖∇^k (F^*g - G)‖_G (x)` (as used by `cuspMetricErrorBound` and `PersistentHyperbolicCores`) equals
`metricDerivNorm k (F^*g|_U) (G|_U) (G|_U) x`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Connection DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem infty_ne_zero_C4 : (∞ : WithTop ℕ∞) ≠ 0 := by decide

/-- The raw pullback error tensor `F^*g - G` (curried to a `(0,2)`-tensor). -/
def rawPullbackError_C4 (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    (Fm : M → N) (y : M) : Tensor0SSpace 2 I y :=
  ((continuousMultilinearCurryFin1 ℝ (TangentSpace I y) ℝ).symm.toContinuousLinearMap.comp
    (localPullInner g Fm y - G.inner y)).uncurryLeft

theorem mfderiv_comp_val_C4 (Fm : M → N) (U : Opens M) (hF : ContMDiffOn I J ∞ Fm U) (x : U)
    (v : TangentSpace I x) :
    mfderiv I J (fun z : U => Fm z) x v = mfderiv I J Fm (x : M) v := by
  have hx : ContMDiffAt I J ∞ Fm (x : M) := hF.contMDiffAt (U.isOpen.mem_nhds x.property)
  have h1 : MDifferentiableAt I J Fm (x : M) := hx.mdifferentiableAt infty_ne_zero_C4
  have h2 : MDifferentiableAt I I (Subtype.val : U → M) x :=
    (contMDiff_subtype_val (I := I) (U := U)).mdifferentiableAt infty_ne_zero_C4
  have := mfderiv_comp (I := I) (I' := I) (I'' := J) x h1 h2
  change mfderiv I J (Fm ∘ (Subtype.val : U → M)) x v = _
  rw [this]
  simp only [ContinuousLinearMap.comp_apply]
  rw [DifferentialGeometry.mfderiv_subtype_val_apply (I := I) U x v]

theorem contMDiff_restrict_C4 (Fm : M → N) (U : Opens M) (hF : ContMDiffOn I J ∞ Fm U) :
    ContMDiff I J ∞ (fun z : U => Fm z) := by
  intro x
  exact (hF.contMDiffAt (U.isOpen.mem_nhds x.property)).comp x
    (contMDiff_subtype_val (I := I) (U := U) x)

/-- **Raw error norm = `metricDerivNorm` on the open set.** -/
theorem rawNorm_eq_metricDerivNorm_C4 (g : SmoothRiemannianMetric J N)
    (G : SmoothRiemannianMetric I M) (Fm : M → N) (U : Opens M)
    (hF : ContMDiffOn I J ∞ Fm U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv I J Fm y)) (k : ℕ) (x : U) :
    tensor0SFiberNorm G (x : M) (2 + k)
        (iteratedMetricCovariantDerivative G 2 (rawPullbackError_C4 g G Fm) k (x : M)) =
      metricDerivNorm k
        (g.pullbackOfImmersion (I := I) (fun z : U => Fm z) (contMDiff_restrict_C4 Fm U hF)
          (fun z => by
            intro v w hvw
            exact hinj z z.property
              ((mfderiv_comp_val_C4 Fm U hF z v).symm.trans
                (hvw.trans (mfderiv_comp_val_C4 Fm U hF z w)))))
        (G.restrictOpen U) (G.restrictOpen U) x := by
  rw [metricDerivNorm_eq_iterated_inner_difference]
  rw [← tensor0SFiberNorm_iteratedMetricCovariantDerivative_restrictOpen G U
    (rawPullbackError_C4 g G Fm) k x]
  congr 3
  funext z
  have h1 : (g.pullbackOfImmersion (I := I) (fun z : U => Fm z) (contMDiff_restrict_C4 Fm U hF)
      (fun z => by
        intro v w hvw
        exact hinj z z.property
          ((mfderiv_comp_val_C4 Fm U hF z v).symm.trans
            (hvw.trans (mfderiv_comp_val_C4 Fm U hF z w))))).inner z =
      localPullInner (I := I) (J := J) g Fm (z : M) := by
    ext v w
    change localPullInner (I := I) (J := J) g (fun z : U => Fm z) z v w = _
    rw [localPullInner_apply, mfderiv_comp_val_C4 Fm U hF z v, mfderiv_comp_val_C4 Fm U hF z w]
    exact (localPullInner_apply (I := I) (J := J) g Fm (z : M) v w).symm
  rw [h1]
  rfl

/-- `metricDerivNorm` of smooth metrics is continuous. -/
theorem continuous_metricDerivNorm_C4 (g h G : SmoothRiemannianMetric I M) (k : ℕ) :
    Continuous (fun x : M => metricDerivNorm k g h G x) := by
  have hfun : (fun x : M => metricDerivNorm k g h G x) = fun x =>
      Real.sqrt (normSq0S G x (2 + k)
        (iterCov G 2 (metricTensorField g - metricTensorField h) k x)) := by
    funext x
    rw [metricDerivNorm_eq_iteratedMetricCovariantDerivative]
    unfold tensor0SFiberNorm
    have := iteratedMetricCovariantDerivative_eq_iterCov G 2
      (metricTensorField g - metricTensorField h) k x
    congr 2
  rw [hfun]
  exact Real.continuous_sqrt.comp (normSq0S_cont G _)

end GC.LongTime.Ch12
