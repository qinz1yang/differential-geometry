import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartTest

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem HasWeakRiemannianGradLp.ae_eq [CompactSpace M] [T2Space M]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G G' : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G) (hG' : HasWeakRiemannianGradLp g u G')
    (hGn : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 1
      (riemannianVolumeMeasure I M g))
    (hG'n : MemLp (fun x => Real.sqrt (g.inner x (G' x) (G' x))) 1
      (riemannianVolumeMeasure I M g)) :
    G =ᵐ[riemannianVolumeMeasure I M g] G' := by
  classical
  let S := chartAtlasPOUFinset (I := I) (M := M)
  let X (α : S) (i : Fin (Module.finrank ℝ E)) :=
    weightedChartTest g α i (chartAtlasPOU I M α)
      (chartAtlasPOU I M α).contMDiff (chartAtlasPOU_isSubordinate I M α)
  have hpair (α : S) (i : Fin (Module.finrank ℝ E)) :
      ∀ᵐ x ∂riemannianVolumeMeasure I M g,
        g.inner x (G x) (X α i x) - g.inner x (G' x) (X α i x) = 0 :=
    hG.pairing_diff_smooth_aeEq_zero hG' hGn hG'n (X α i)
  have hall : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      ∀ (α : S) (i : Fin (Module.finrank ℝ E)),
        g.inner x (G x) (X α i x) - g.inner x (G' x) (X α i x) = 0 :=
    ae_all_iff.2 (fun α => ae_all_iff.2 (hpair α))
  filter_upwards [hall] with x hx
  obtain ⟨α, hαpos⟩ := (chartAtlasPOU I M).exists_pos_of_mem (mem_univ x)
  have hαS : α ∈ S := chartAtlasPOU_finset_mem.mpr ⟨x, hαpos.ne'⟩
  have hxsource : x ∈ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α (subset_tsupport _ hαpos.ne')
  have hxB : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxsource
  have hcoeff (i : Fin (Module.finrank ℝ E)) :
      g.inner x (G x) (chartBasisVecFiber (I := I) α i x) =
        g.inner x (G' x) (chartBasisVecFiber (I := I) α i x) := by
    have hi := hx ⟨α, hαS⟩ i
    dsimp only [X] at hi
    rw [weightedChartTest_apply, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      ← mul_sub] at hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left
      (div_ne_zero hαpos.ne' (chartDensity_pos g α hxB).ne'))
  have hlin : (g.inner x (G x)).toLinearMap = (g.inner x (G' x)).toLinearMap := by
    apply (chartBasisFamily (I := I) α hxB).ext
    intro i
    simpa only [ContinuousLinearMap.coe_coe, chartBasisFamily_apply] using hcoeff i
  have heval := congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L (G x - G' x)) hlin
  have hzero : g.inner x (G x - G' x) (G x - G' x) = 0 := by
    rw [map_sub (g.inner x), sub_apply]
    exact sub_eq_zero.mpr heval
  by_contra hne
  have hpos := g.pos x (G x - G' x) (sub_ne_zero.mpr hne)
  linarith

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
