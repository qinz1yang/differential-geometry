import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricFamilyRegularity
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def cartesianTimeDerivative (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (K : Set ℝ) (p : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderivWithin ℝ (cartesianMetricFamily g) (K ×ˢ (univ : Set E)) p (1, 0)

def cartesianRicciFamily (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p => by exact ricciTensor (g p.1) p.2

omit [FiniteDimensional ℝ E] in
theorem cartesianTimeDerivative_contDiffOn
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hK : UniqueDiffOn ℝ K)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (K ×ˢ (univ : Set E))) :
    ContDiffOn ℝ ∞ (cartesianTimeDerivative g K) (K ×ˢ (univ : Set E)) := by
  exact (hg.fderivWithin (hK.prod uniqueDiffOn_univ) (by simp)).clm_apply contDiffOn_const

omit [FiniteDimensional ℝ E] in
private theorem timeDerivative_slot
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (K ×ˢ (univ : Set E)))
    (t : ℝ) (ht : t ∈ K) (x : E) (v w : E) :
    HasDerivWithinAt (fun s => (g s).inner x v w)
      (cartesianTimeDerivative g K (t, x) v w) K t := by
  have hG := (hg.differentiableOn (by simp)) (t, x) ⟨ht, mem_univ x⟩
  have hcurve : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) K t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hFD : HasFDerivWithinAt (cartesianMetricFamily g)
      (fderivWithin ℝ (cartesianMetricFamily g) (K ×ˢ (univ : Set E)) (t, x))
      (K ×ˢ (univ : Set E)) (t, x) := hG.hasFDerivWithinAt
  have hD : HasDerivWithinAt (fun s => cartesianMetricFamily g (s, x))
      (cartesianTimeDerivative g K (t, x)) K t := by
    have h := HasFDerivWithinAt.comp_hasDerivWithinAt
      (l := cartesianMetricFamily g)
      (l' := fderivWithin ℝ (cartesianMetricFamily g) (K ×ˢ (univ : Set E)) (t, x))
      (f := fun s : ℝ => (s, x)) (f' := (1, 0)) t hFD hcurve
      (show MapsTo (fun s : ℝ => (s, x)) K (K ×ˢ (univ : Set E)) from
        fun _ hs => ⟨hs, mem_univ x⟩)
    exact h
  have hfirst : HasDerivWithinAt (fun s => cartesianMetricFamily g (s, x) v)
      (cartesianTimeDerivative g K (t, x) v) K t := by
    simpa only [map_zero, add_zero] using hD.clm_apply (hasDerivWithinAt_const t K v)
  have hslot : HasDerivWithinAt (fun s => cartesianMetricFamily g (s, x) v w)
      (cartesianTimeDerivative g K (t, x) v w) K t := by
    simpa only [map_zero, add_zero] using hfirst.clm_apply (hasDerivWithinAt_const t K w)
  exact hslot

theorem cartesianRicciFamily_contDiffOn
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hK : UniqueDiffOn ℝ K)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (K ×ˢ (univ : Set E)))
    (hRF : ∀ t ∈ K, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) K t) :
    ContDiffOn ℝ ∞ (cartesianRicciFamily g) (K ×ˢ (univ : Set E)) := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have hD : ContDiffOn ℝ ∞ (fun p : ℝ × E => cartesianTimeDerivative g K p v w)
      (K ×ˢ (univ : Set E)) :=
    ((cartesianTimeDerivative_contDiffOn g K hK hg).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const
  have hscaled : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      (-1 / 2 : ℝ) * cartesianTimeDerivative g K p v w) (K ×ˢ (univ : Set E)) :=
    contDiffOn_const.mul hD
  apply hscaled.congr
  intro p hp
  have he := (hK p.1 hp.1).eq_deriv K
    (timeDerivative_slot g K hg p.1 hp.1 p.2 v w) (hRF p.1 hp.1 p.2 v w)
  change ricciTensor (g p.1) p.2 v w = (-1 / 2 : ℝ) * cartesianTimeDerivative g K p v w
  linarith

theorem uniqueDiffOn_lifetimeInterval (T : ℝ≥0∞) (hT : 0 < T) :
    UniqueDiffOn ℝ (lifetimeInterval T hT).carrier := by
  by_cases htop : T = ⊤
  · simpa only [lifetimeInterval, htop, dite_true, RealTimeInterval.closedInfinite] using
      uniqueDiffOn_Ici (0 : ℝ)
  · simpa only [lifetimeInterval, htop, dite_false, RealTimeInterval.closedOpen] using
      uniqueDiffOn_Ico (0 : ℝ) T.toReal

theorem PartialStandardSolution.ricci_contDiffOn (S : PartialStandardSolution) :
    ContDiffOn ℝ ∞ (cartesianRicciFamily S.metric)
      (S.domain ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  apply cartesianRicciFamily_contDiffOn S.metric S.domain
    (uniqueDiffOn_lifetimeInterval S.lifetime S.lifetime_pos) S.smooth
  intro t ht x v w
  exact (S.equation t ht x v w).mono
    (fun s hs => ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mp hs).1)

open DifferentialGeometry.Integral.Measure in
theorem ricciFamilyContinuous_of_cartesian
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hg : ContinuousOn (cartesianRicciFamily g) (K ×ˢ (univ : Set E))) :
    tensor0SFamilyContinuousOnSet (I := 𝓘(ℝ, E)) (M := E) 2 K
      (fun t x => metricRicci (g t) x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply tensor0SFamilyContinuousOnSet_of_chartComp
    (N := fun _ => (univ : Set E)) (hN := fun _ => Filter.univ_mem)
  intro x₀ idx
  have hfull : Continuous (fun q : {t : ℝ // t ∈ K} × E =>
      cartesianRicciFamily g (q.1.val, q.2)) :=
    hg.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun q => ⟨q.1.property, mem_univ q.2⟩)
  have hpair := (hfull.clm_apply (continuous_const (y := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 0)))).clm_apply
    (continuous_const (y := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 1)))
  apply hpair.continuousOn.congr
  intro q _
  simp only [metricRicci_apply, TangentBundle.symmL_model_space]
  change metricRicciAt (g q.1.val) q.2 (fun k => DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx k)) =
    cartesianRicciFamily g (q.1.val, q.2) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 0)) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 1))
  have he : (fun k : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx k)) =
      vec2 (I := 𝓘(ℝ, E)) (x := q.2) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 0)) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 1)) := by
    funext k
    fin_cases k <;> rfl
  rw [he]
  exact metricRicciAt_apply_eq_ricciTensor (g q.1.val) q.2
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 0)) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (idx 1))

theorem PartialStandardSolution.ricciFamilyContinuous (S : PartialStandardSolution) :
    tensor0SFamilyContinuousOnSet (I := 𝓡 3) (M := EuclideanSpace ℝ (Fin 3)) 2 S.domain
      (fun t x => metricRicci (S.metric t) x) :=
  ricciFamilyContinuous_of_cartesian S.metric S.domain S.ricci_contDiffOn.continuousOn
end DifferentialGeometry.PDE.RicciFlow
