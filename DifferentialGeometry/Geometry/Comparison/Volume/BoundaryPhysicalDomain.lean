import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhasePhysicalFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength

/-!
Actual phase rays with an original boundary pole have only positive physical existence times.
Whole positive birth and native maximal interval connectivity yield positive downclosure.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem physicalDomain_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryPhase_positive_physical_domain (g : SmoothRiemannianMetric I M)
    (p : M) (hp : I.IsBoundaryPoint p) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      physicalDomain_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (σ : E → TangentBundle 𝓘(ℝ, E) U) (W : Opens E),
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W →
      ∀ (v : E), v ∈ W → ∀ δ a : ℝ, 0 < δ → a ∈ Ioo 0 δ →
        (∀ t ∈ Ioo 0 δ, (σ v, t - a) ∈ k.geodesicFlowDomain) →
        Tendsto (fun t : ℝ => ((boundaryPhasePoint k σ v (t - a) : U) : M))
          (𝓝[>] (0 : ℝ)) (𝓝 p) →
        (∀ t : ℝ, (σ v, t - a) ∈ k.geodesicFlowDomain → 0 < t) ∧
        ∀ s t : ℝ, 0 < s → s ≤ t → (σ v, t - a) ∈ k.geodesicFlowDomain →
          (σ v, s - a) ∈ k.geodesicFlowDomain := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    physicalDomain_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro σ W hσ v hv δ a hδ ha hbirth hpole
  have hzero : (σ v, -a) ∉ k.geodesicFlowDomain := by
    intro hz
    have hz' : (σ v, (0 : ℝ) - a) ∈ k.geodesicFlowDomain := by
      simpa only [zero_sub] using hz
    have hphysical := (boundaryPhase_physical_geodesic k W σ hσ v hv a 0 hz').1
    have hval := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
      I ∞ physicalDomain_infty_ne_zero (M := M)
    have hcont : ContMDiffAt 𝓘(ℝ) I ∞
        (fun r => ((boundaryPhasePoint k σ v (r - a) : U) : M)) 0 :=
      hval.contMDiffAt.comp (f := fun r : ℝ =>
        (boundaryPhasePoint k σ v (r - a) : U)) 0 hphysical
    have hpoint : ((boundaryPhasePoint k σ v (0 - a) : U) : M) = p :=
      tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hpole
    have hinside : I.IsInteriorPoint p := hpoint ▸
      (boundaryPhasePoint k σ v (0 - a) : U).property
    exact (I.isInteriorPoint_iff_not_isBoundaryPoint p).mp hinside hp
  have hinterval : OrdConnected {r : ℝ | (σ v, r) ∈ k.geodesicFlowDomain} :=
    ordConnected_maximalIntegralCurveInterval
  refine ⟨?_, ?_⟩
  · intro t ht
    by_contra hnt
    have hle : t ≤ 0 := le_of_not_gt hnt
    apply hzero
    exact hinterval.out ht (k.mem_geodesicFlowDomain_zero (r := ⊤) le_top (σ v))
      ⟨by linarith, by linarith [ha.1]⟩
  · intro s t hs hst ht
    let r := min s δ / 2
    have hmin : 0 < min s δ := lt_min hs hδ
    have hr : r ∈ Ioo 0 δ :=
      ⟨by dsimp [r]; positivity, by dsimp [r]; linarith [min_le_right s δ]⟩
    have hrs : r ≤ s :=
      (half_le_self hmin.le).trans (min_le_left s δ)
    exact hinterval.out (hbirth r hr) ht
      ⟨by linarith, by linarith⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
