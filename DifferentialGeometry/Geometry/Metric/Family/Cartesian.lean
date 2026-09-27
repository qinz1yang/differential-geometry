import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def cartesianMetricFamily (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p => by exact (g p.1).inner p.2

theorem metricFamilySmoothOn_of_cartesian_smooth (D : RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (D.carrier ×ˢ (univ : Set E))) :
    MetricFamilySmoothOn D g := by
  have hcoeff (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
      ContDiffOn ℝ ∞ (fun t => (g t).inner x v w) D.carrier := by
    have h := hg.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun t ht => ⟨ht, mem_univ x⟩)
    exact (h.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  refine ⟨fun x v w => (hcoeff x v w).mono D.regular_subset,
    fun x v w => (hcoeff x v w).continuousOn, ?_, ?_⟩
  · apply tensor0SFamilyContinuousOnSet_of_chartComp
      (N := fun _ => (univ : Set E)) (hN := fun _ => Filter.univ_mem)
    intro x₀ idx
    have hfull : Continuous (fun q : {t : ℝ // t ∈ D.carrier} × E =>
        cartesianMetricFamily g (q.1.val, q.2)) :=
      hg.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun q => ⟨q.1.property, mem_univ q.2⟩)
    have hpair := ((hfull.clm_apply (continuous_const (y := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 0)))).clm_apply
      (continuous_const (y := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 1))))
    simp only [metricTensorField_apply, TangentBundle.symmL_model_space]
    change ContinuousOn (fun q : {t : ℝ // t ∈ D.carrier} × E =>
      cartesianMetricFamily g (q.1.val, q.2) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 0))
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 1))) {q | q.2 ∈ (univ : Set E)}
    exact hpair.continuousOn
  · intro Idx _ frame u hframe i j
    have hf (k : Idx) : ContDiffOn ℝ ∞ (fun x : E => (frame k x : E)) u :=
      contMDiffOn_vectorSpace_iff_contDiffOn.mp (hframe.contMDiffOn k)
    have hF := hg.mono (prod_mono D.regular_subset (subset_univ u))
    have hv (k : Idx) : ContDiffOn ℝ ∞ (fun p : ℝ × E => (frame k p.2 : E))
        (D.regular ×ˢ u) :=
      (hf k).comp contDiffOn_snd (fun _ hp => hp.2)
    have h := (hF.clm_apply (hv i)).clm_apply (hv j)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact h.contMDiffOn

theorem cartesian_contDiffOn_of_chartGram
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hgram : ∀ (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet)) :
    ContDiffOn ℝ ∞ (cartesianMetricFamily g) (K ×ˢ (univ : Set E)) := by
  classical
  have he (i j : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun p : ℝ × E => (g p.1).inner p.2 (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j))
        (K ×ˢ (univ : Set E)) := by
    have hh := hgram 0 i j
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    have hb : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (0 : E)).baseSet = univ := rfl
    rw [hb] at hh
    apply hh.contDiffOn.congr
    intro p _
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber, TangentBundle.symmL_model_space]
    rfl
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  let c := fun v i => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v i
  have hs : ContDiffOn ℝ ∞
      (fun p : ℝ × E => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (c v i * c w j) * (g p.1).inner p.2 (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j))
      (K ×ˢ (univ : Set E)) := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact contDiffOn_const.mul (he i j)
  apply hs.congr
  intro p _
  let B : E →L[ℝ] E →L[ℝ] ℝ := cartesianMetricFamily g p
  change B v w = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (c v i * c w j) * B (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j)
  conv_lhs => rw [← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr v, ← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr w]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change c w j * (c v i * B (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j)) = _
  ring

end DifferentialGeometry.PDE.RicciFlow
