import DifferentialGeometry.Topology.Morse.RelativePerturbation
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Function
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

theorem tsupport_gradientFun_subset (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    tsupport (gradientFun g f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxf
  apply hx
  apply gradientFun_eq_zero_of_mfderiv_eq_zero
  have he : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hxf
  rw [he.mfderiv_eq, mfderiv_const]
  rfl

theorem span_gradientFun_eq_top (g : SmoothRiemannianMetric I M)
    {ι : Type*} (φ : ι → M → ℝ) (x : M)
    (hspan : Submodule.span ℝ (range (fun i =>
      (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x))) = ⊤) :
    Submodule.span ℝ (range (fun i => gradientFun g (φ i) x)) = ⊤ := by
  let e : (TangentSpace I x →L[ℝ] ℝ) ≃ₗ[ℝ] TangentSpace I x :=
    LinearMap.toContinuousLinearMap.symm.trans (metricFlatMap g x).symm
  have he (i : ι) : e (mfderiv I 𝓘(ℝ, ℝ) (φ i) x) = gradientFun g (φ i) x := rfl
  have hh := congrArg (Submodule.map e.toLinearMap) hspan
  rw [Submodule.map_span, Submodule.map_top, e.range] at hh
  rw [← range_comp] at hh
  change Submodule.span ℝ (range (fun i => e (mfderiv I 𝓘(ℝ, ℝ) (φ i) x))) = ⊤ at hh
  simpa only [he] using hh

theorem hasFDerivAt_sum_gradientFun (g : SmoothRiemannianMetric I M)
    {ι : Type*} [Fintype ι] (φ : ι → M → ℝ) (x : M) (a : ι → ℝ) :
    HasFDerivAt (fun b : ι → ℝ => ∑ i, b i • gradientFun g (φ i) x)
      (∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight (gradientFun g (φ i) x)) a := by
  apply HasFDerivAt.fun_sum
  intro i _
  exact (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.smul_const _

theorem surjective_fderiv_sum_gradientFun (g : SmoothRiemannianMetric I M)
    {ι : Type*} [Fintype ι] (φ : ι → M → ℝ) (x : M) (a : ι → ℝ)
    (hspan : Submodule.span ℝ (range (fun i => gradientFun g (φ i) x)) = ⊤) :
    Surjective (fderiv ℝ (fun b : ι → ℝ => ∑ i, b i • gradientFun g (φ i) x) a) := by
  rw [(hasFDerivAt_sum_gradientFun g φ x a).fderiv]
  intro v
  obtain ⟨b,hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (hspan ▸ (show v ∈ (⊤ : Submodule ℝ (TangentSpace I x)) from trivial))
  exact ⟨b, by simpa using hb⟩

theorem exists_supported_gradients_span_of_isCompact [T2Space M]
    (g : SmoothRiemannianMetric I M) {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (φ : Fin n → M → ℝ),
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      (∀ i, ContMDiff I I.tangent ∞
          (fun x => (⟨x,gradientFun g (φ i) x⟩ : TangentBundle I M)) ∧
        HasCompactSupport (gradientFun g (φ i)) ∧ tsupport (gradientFun g (φ i)) ⊆ U) ∧
      (∀ i x (v : TangentSpace I x),
        g.inner x (gradientFun g (φ i) x) v = mfderiv I 𝓘(ℝ, ℝ) (φ i) x v) ∧
      ∀ x ∈ K, Submodule.span ℝ (range (fun i => gradientFun g (φ i) x)) = ⊤ := by
  obtain ⟨n,φ,hφ,hspan⟩ :=
    DifferentialGeometry.Morse.exists_supported_differentials_span_of_isCompact (I := I) hK hU hKU
  refine ⟨n,φ,hφ,fun i => ?_,fun i x v => inner_gradientFun g (φ i) x v,
    fun x hx => span_gradientFun_eq_top g φ x (hspan x hx)⟩
  exact ⟨gradientFun_smooth g (hφ i).1,
    (hφ i).2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradientFun_subset g _),
    (tsupport_gradientFun_subset g _).trans (hφ i).2.2⟩

end DifferentialGeometry.VectorField
