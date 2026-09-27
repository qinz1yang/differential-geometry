import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartDerivative
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartLp
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem MemW1pIntrinsicLp.memWkpChart [CompactSpace M] [T2Space M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : MemW1pIntrinsicLp g p u) :
    Chart.MemWkpChart (I := I) 1 p u := by
  classical
  let μ := riemannianVolumeMeasure I M g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨hu, G₀, hG₀, hGn₀⟩ := hu
  let G : ∀ x : M, TangentSpace I x := fun x => G₀ x
  have hG : HasWeakRiemannianGradLp g u G := hG₀
  intro α
  let ρ : M → ℝ := chartAtlasPOU I M α
  have hρ : ContMDiff I 𝓘(ℝ) ∞ ρ := (chartAtlasPOU I M α).contMDiff
  have hρs : tsupport ρ ⊆ (chartAt H α).source := chartAtlasPOU_isSubordinate I M α
  let v : M → ℝ := fun x => ρ x * u x
  let V : ∀ x : M, TangentSpace I x := fun x => ρ x • G x + u x • gradFun (I := I) g ρ x
  obtain ⟨hv, hV, hVn⟩ := hG.smooth_mul_witness hp hu hGn₀ hρ
  have hvs : tsupport v ⊆ (chartAt H α).source :=
    (tsupport_mul_subset_left : tsupport (fun x => ρ x * u x) ⊆ tsupport ρ).trans hρs
  have hVzero : ∀ x, x ∉ tsupport ρ → V x = 0 := by
    intro x hx
    have hρx : ρ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hgrad : gradFun (I := I) g ρ x = 0 :=
      Function.notMem_support.mp (fun h => hx (support_gradFun_subset g ρ h))
    dsimp only [V]
    rw [hρx, hgrad, zero_smul, smul_zero, add_zero]
  obtain ⟨χ, hχ, _hχrange, hχone, hχs⟩ := Chart.exists_chart_cutoff_M (I := I) α
  have hraw : DeGiorgi.MemW1p p (Chart.chartPushedRaw I α v)
      (Chart.chartTargetEuclid (I := I) α) := by
    refine ⟨memLp_chartPushedRaw_of_support g α hv hvs, fun i => ?_⟩
    let T := trivializationAt E (TangentSpace I) α
    have hχT : tsupport χ ⊆ T.baseSet := by
      simpa only [T, TangentBundle.trivializationAt_baseSet] using hχs
    let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨fun x => χ x • chartBasisVecFiber (I := I) α i x,
        hχ.contMDiffOn.smul_section_of_tsupport T.open_baseSet hχT
          (chartBasisVec_contMDiffOn α i)⟩
    let a : M → ℝ := fun x => g.inner x (V x) (chartBasisVecFiber (I := I) α i x)
    have haeq : (fun x => g.inner x (V x) (X x)) = a := by
      funext x
      by_cases hx : x ∈ tsupport ρ
      · change g.inner x (V x) (χ x • chartBasisVecFiber (I := I) α i x) = _
        rw [hχone x hx, one_smul]
      · dsimp only [a]
        rw [hVzero x hx, map_zero, zero_apply, zero_apply]
    have ha : MemLp a p μ := by
      rw [← haeq]
      exact hV.pairing_memLp hVn X
    have has : tsupport a ⊆ (chartAt H α).source := by
      apply subset_trans (closure_minimal (t := tsupport ρ) ?_ (isClosed_tsupport ρ)) hρs
      intro x hx
      by_contra hxρ
      apply hx
      dsimp only [a]
      rw [hVzero x hxρ, map_zero, zero_apply]
    refine ⟨Chart.chartPushedRaw I α a, memLp_chartPushedRaw_of_support g α ha has, ?_⟩
    exact hV.hasWeakPartialDeriv_chartPushedRaw
      (memLp_one_iff_integrable.mp (hv.mono_exponent hp))
      (memLp_one_iff_integrable.mp (hVn.mono_exponent hp)) α i
  apply Euclidean.MemWkp.one_iff_memW1p.mpr
  apply (Euclidean.MemW1p_congr_ae (Chart.chartTargetEuclid_isOpen (I := I) (α := α)) ?_).mp hraw
  filter_upwards [ae_restrict_mem (Chart.chartTargetEuclid_measurableSet (I := I) α)] with y hy
  rw [Chart.chartPushedRaw_apply_of_mem α v hy]
  rfl

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
