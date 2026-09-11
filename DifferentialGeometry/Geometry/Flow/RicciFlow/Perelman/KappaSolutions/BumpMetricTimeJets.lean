import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorBumpTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricTimeJets


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance bumpMetricC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem exists_bump_metric_time_jets
    (R : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := U) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hsupp : tsupport χ ⊆ (U : Set M)) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
      (∀ t, B 0 t = metricTensorField
        (R.bumpExtendOpen U (S.base.metric t) χ hχ hχ01 hsupp)) ∧
      ∀ q t, t ≤ b → ∀ x : M,
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Iic b) t := by
  classical
  obtain ⟨A, hzero, hA⟩ := exists_ancient_ordinary_metric_time_jets S hS hcarrier hregular
  obtain ⟨C, hCvalue, hCout, hCderiv⟩ := exists_tensor_bump_time_tower U 2 A χ hχ hsupp (Iic b)
    (fun q t ht x => (hA q t ht x).2)
  let G : ℝ → SmoothRiemannianMetric I M :=
    fun t => R.bumpExtendOpen U (S.base.metric t) χ hχ hχ01 hsupp
  have hmetric (t : ℝ) (x : M) : metricTensorField (G t) x =
      C 0 t x + (1 - χ x) • metricTensorField R x := by
    apply tensor0SSpace_ext 2 x
    intro v
    simp only [metricTensorField_apply, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ U
    · rw [bumpExtendOpen_inner_of_mem R U (S.base.metric t) χ hχ hχ01 hsupp x hx,
        hCvalue 0 t x hx v, hzero t]
      erw [metricTensorField_apply (I := I) (M := U) (S.base.metric t) ⟨x, hx⟩ v]
      rfl
    · have hxSupp : x ∉ tsupport χ := fun h => hx (hsupp h)
      have hχzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hxSupp
      rw [bumpExtendOpen_inner_of_notMem_tsupport R U (S.base.metric t) χ hχ hχ01 hsupp x hxSupp,
        hCout 0 t x hx]
      simp only [hχzero, Tensor0SSpace.zero_apply, sub_zero, one_mul, zero_add]
  let B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2 := fun q t =>
    match q with
    | 0 => metricTensorField (G t)
    | q + 1 => C (q + 1) t
  refine ⟨B, fun _ => rfl, ?_⟩
  intro q t ht x
  cases q with
  | zero =>
    have hd := (hCderiv 0 t ht x).add_const ((1 - χ x) • metricTensorField R x)
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hmetric s x) (hmetric t x)
  | succ q => exact hCderiv (q + 1) t ht x

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
