import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open Operator

variable {E F H G S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]

omit [IsManifold I ∞ S] in
private theorem contMDiff_metric_pairing_along
    (g : SmoothRiemannianMetric J M) {f : S → M}
    (hf : ContMDiff I J ∞ f) {V W : ∀ s, TangentSpace J (f s)}
    (hV : ContMDiff I J.tangent ∞ (fun s => (⟨f s, V s⟩ : TangentBundle J M)))
    (hW : ContMDiff I J.tangent ∞ (fun s => (⟨f s, W s⟩ : TangentBundle J M))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun s => g.inner (f s) (V s) (W s)) := by
  have hpair := ContMDiff.clm_bundle_apply₂
    (E₁ := TangentSpace J) (E₂ := TangentSpace J) (E₃ := fun _ : M => ℝ)
    (g.contMDiff.comp hf) hV hW
  intro s
  exact (contMDiffAt_totalSpace.mp (hpair s)).2

variable [FiniteDimensional ℝ E] [T2Space S]

/-- A smooth field transverse to a smooth immersion gives a smooth unit normal
for the actual ambient metric. The construction projects using the induced
metric and works in arbitrary codimension. -/
theorem exists_contMDiff_unit_normal_of_transverse
    (g : SmoothRiemannianMetric J M) {f : S → M}
    (hf : ContMDiff I J ∞ f)
    (hinj : ∀ s, Function.Injective (mfderiv I J f s))
    (V : ∀ s, TangentSpace J (f s))
    (hV : ContMDiff I J.tangent ∞ (fun s => (⟨f s, V s⟩ : TangentBundle J M)))
    (htrans : ∀ s, V s ∉ (mfderiv I J f s).range) :
    ∃ ν : ∀ s, TangentSpace J (f s),
      ContMDiff I J.tangent ∞ (fun s => (⟨f s, ν s⟩ : TangentBundle J M)) ∧
      (∀ s, g.inner (f s) (ν s) (ν s) = 1) ∧
      ∀ s v, g.inner (f s) (ν s) (mfderiv I J f s v) = 0 := by
  let h : SmoothRiemannianMetric I S := g.pullback f hf hinj
  let α : ∀ s, TangentSpace I s →ₗ[ℝ] ℝ := fun s =>
    ((g.inner (f s) (V s)).comp (mfderiv I J f s)).toLinearMap
  let X : ∀ s, TangentSpace I s := fun s => metricSharp h s (α s)
  have hdf : ContMDiff I.tangent J.tangent ∞ (tangentMap I J f) :=
    hf.contMDiff_tangentMap le_rfl
  have hX : ContMDiff I I.tangent ∞
      (fun s => (⟨s, X s⟩ : TangentBundle I S)) := by
    apply metricSharp_contMDiff_total h
    intro q j
    have hb := Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) q j
    rw [TangentBundle.trivializationAt_baseSet] at hb
    have hdfb := hdf.comp_contMDiffOn hb
    have hpair : ContMDiffOn I (J.prod 𝓘(ℝ, ℝ)) ∞
        (fun s => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) (f s)
          (g.inner (f s) (V s)
            (mfderiv I J f s (Tensor.Coordinates.chartBasisVecFiber (I := I) q j s))))
        (chartAt H q).source :=
      ContMDiffOn.clm_bundle_apply₂
        (E₁ := TangentSpace J) (E₂ := TangentSpace J) (E₃ := fun _ : M => ℝ)
        (g.contMDiff.comp hf).contMDiffOn hV.contMDiffOn hdfb
    intro s hs
    exact (contMDiffWithinAt_totalSpace.mp (hpair s hs)).2
  have hdfX : ContMDiff I J.tangent ∞
      (fun s => (⟨f s, mfderiv I J f s (X s)⟩ : TangentBundle J M)) :=
    hdf.comp hX
  let N : ∀ s, TangentSpace J (f s) := fun s => V s - mfderiv I J f s (X s)
  have hN : ContMDiff I J.tangent ∞
      (fun s => (⟨f s, N s⟩ : TangentBundle J M)) := by
    have hneg : ContMDiff I J.tangent ∞
        (fun s => (⟨f s, (-1 : ℝ) • mfderiv I J f s (X s)⟩ : TangentBundle J M)) :=
      contMDiff_const.smul_bundle hdfX
    simpa only [N, sub_eq_add_neg, neg_one_smul] using hV.add_bundle hneg
  have hNnormal (s : S) (v : TangentSpace I s) :
      g.inner (f s) (N s) (mfderiv I J f s v) = 0 := by
    dsimp only [N]
    rw [map_sub, sub_apply]
    change g.inner (f s) (V s) (mfderiv I J f s v) -
      h.inner s (metricSharp h s (α s)) v = 0
    rw [inner_metricSharp]
    exact sub_self _
  have hNne (s : S) : N s ≠ 0 := by
    intro hz
    apply htrans s
    exact ⟨X s, (sub_eq_zero.mp hz).symm⟩
  have hNpos (s : S) : 0 < g.inner (f s) (N s) (N s) :=
    g.pos (f s) (N s) (hNne s)
  let r : S → ℝ := fun s => Real.sqrt (g.inner (f s) (N s) (N s))
  have hrpos (s : S) : 0 < r s := Real.sqrt_pos.mpr (hNpos s)
  have hr : ContMDiff I 𝓘(ℝ, ℝ) ∞ r := by
    have hNN := contMDiff_metric_pairing_along g hf hN hN
    intro s
    exact (Real.contDiffAt_sqrt (hNpos s).ne').contMDiffAt.comp s (hNN s)
  let ν : ∀ s, TangentSpace J (f s) := fun s => (r s)⁻¹ • N s
  refine ⟨ν, (hr.inv₀ (fun s => (hrpos s).ne')).smul_bundle hN, ?_, ?_⟩
  · intro s
    have hr2 : r s * r s = g.inner (f s) (N s) (N s) := by
      exact Real.mul_self_sqrt (hNpos s).le
    change g.inner (f s) ((r s)⁻¹ • N s) ((r s)⁻¹ • N s) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← hr2]
    field_simp [(hrpos s).ne']
  · intro s v
    change g.inner (f s) ((r s)⁻¹ • N s) (mfderiv I J f s v) = 0
    rw [map_smul, smul_apply, smul_eq_mul, hNnormal, mul_zero]

end DifferentialGeometry.Geometry
