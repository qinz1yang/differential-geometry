import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import Mathlib.Geometry.Manifold.BumpFunction












noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [Measure.IsAddHaarMeasure μ]

theorem exists_open_ae_mdifferentiableAt_of_metric_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : V → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (z : V) : ∃ U : Set V, IsOpen U ∧ z ∈ U ∧
      ∀ᵐ w ∂μ, w ∈ U → MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) u w := by
  classical
  have huc := continuous_of_riemannian_lipschitz g hu
  let χ : SmoothBumpFunction 𝓘(ℝ, E) (u z) := Classical.choice inferInstance
  let F : M → E := fun p => χ p • (chartAt E (u z)) p
  have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F := χ.contMDiff_smul contMDiffOn_chart
  have hFc : HasCompactSupport F := χ.hasCompactSupport.smul_right
  obtain ⟨L, _, hL⟩ := exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport
    g (hF.of_le (by simp)) hFc
  have hcomp : LipschitzWith (L * C) (F ∘ u) := by
    intro x y
    apply (hL (u x) (u y)).trans
    calc
      (L : ℝ≥0∞) * riemannianEDistOf g (u x) (u y) ≤
          (L : ℝ≥0∞) * ((C : ℝ≥0∞) * edist x y) := by gcongr; exact hu x y
      _ = (↑(L * C) : ℝ≥0∞) * edist x y := by simp only [ENNReal.coe_mul, mul_assoc]
  have hlocal : ∀ᶠ w in 𝓝 z,
      χ (u w) = 1 ∧ u w ∈ (chartAt E (u z)).source :=
    (huc.continuousAt.eventually χ.eventuallyEq_one).and
      (huc.continuousAt ((chartAt E (u z)).open_source.mem_nhds (mem_chart_source E (u z))))
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hlocal
  refine ⟨U, hUopen, hzU, ?_⟩
  filter_upwards [hcomp.ae_differentiableAt] with w hw
  intro hwU
  have heq : ((chartAt E (u z)) ∘ u) =ᶠ[𝓝 w] (F ∘ u) := by
    filter_upwards [hUopen.mem_nhds hwU] with y hy
    simp only [Function.comp_apply, F, (hUsub hy).1, one_smul]
  have hchart := hw.congr_of_eventuallyEq heq
  have hi := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E))
    (ChartedSpace.chart_mem_atlas (u z)) ((chartAt E (u z)).map_source (hUsub hwU).2)
  have hh := hi.comp w hchart.mdifferentiableAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [hUopen.mem_nhds hwU] with y hy
  exact ((chartAt E (u z)).left_inv (hUsub hy).2).symm



theorem ae_mdifferentiableAt_of_metric_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : V → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    ∀ᵐ z ∂μ, MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) u z := by
  classical
  choose U hUopen hzU hd using exists_open_ae_mdifferentiableAt_of_metric_lipschitz (μ := μ) g hu
  have hcover : (univ : Set V) ⊆ ⋃ z, U z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, hzU z⟩
  obtain ⟨r, hr, hrc⟩ := isLindelof_univ.elim_countable_subcover U hUopen hcover
  let : Countable r := hr.to_subtype
  have ha : ∀ᵐ z ∂μ, ∀ i : r, z ∈ U i → MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) u z :=
    (ae_all_iff).mpr (fun i => hd i)
  filter_upwards [ha] with z hz
  obtain ⟨i, hir, hzi⟩ := mem_iUnion₂.mp (hrc (mem_univ z))
  exact hz ⟨i, hir⟩ hzi

end DifferentialGeometry.Geometry
