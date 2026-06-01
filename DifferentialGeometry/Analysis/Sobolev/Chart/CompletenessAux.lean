import DifferentialGeometry.Analysis.Sobolev.Chart.Banach
import DifferentialGeometry.Analysis.Sobolev.Chart.Completeness
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich
import DifferentialGeometry.Analysis.Sobolev.Chart.Atlas
import DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Chart-based Sobolev space `W^{k,p}_chart(M)`: structural lemmas for the
Banach-completeness program

This file collects auxiliary lemmas tying together the chart-pushed scalar
function machinery, the partition-of-unity-weighted bridge to the Riemannian
measure, and the per-chart Euclidean iterated-Sobolev limit. These structural
lemmas form the bridge layer that connects:

* the chart-by-chart Cauchy property of the chart-Sobolev seminorm
  (the per-chart Euclidean Sobolev limit and Steps 1–5 of `Completeness`), and
* the manifold-side Riemannian-measure `L^p` inner product / convergence
  framework (the `MeasureBridge` lemmas).

Specifically we develop:

1. The pointwise relationship `chartPushed ρ α u = chartPushedRaw α (ρ_α · u)`
   on the chart target image, and an a.e. version on `volume.restrict`.
2. Containment `tsupport (ρ_α · u) ⊆ tsupport ρ_α ⊆ chart α source`.
3. Continuity / measurability of POU weights as real-valued functions.
4. The corresponding `eLpNorm` equality between `chartPushed` and
   `chartPushedRaw (ρ_α · u)`.
5. The pointwise POU sum decomposition `u(x) = ∑_α∈S ρ_α(x) u(x)` valid on a
   compact manifold (where `S` is the finite chartAtlasPOU support set).
6. The order-zero `eLpNorm` ≤ order-`k` `wkpNorm` monotonicity.

These pieces are the prerequisites for the manifold-side `eLpNorm` Cauchy
inequality and the resulting `cauchy_complete_eLpNorm` application that yields
the manifold-side limit. The final composition step that completes the proof
of `CompleteSpace (WkpChartQuot g k p hp)` requires a uniform-in-`u`
constant in the bridge inequality `∫⁻ ‖ρ_α u‖^p dμ_g ≤ C · ∫⁻ ‖chartPushed‖^p dvol`.
The existing public API in `MeasureBridge` provides the bridge with a per-`u`
constant via `lintegral_riemannianMeasure_le_const_mul_lintegral_chartPushedRaw`,
and the auxiliary infrastructure here exposes the support-uniform structure
needed to derive the uniform constant in a follow-up file.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- On the chart-target image, `chartPushed ρ α u` agrees with the raw
chart-pushforward of the partition-of-unity-weighted function `ρ_α u`. -/
lemma chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α u y =
      chartPushedRaw I α (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) hy]
  unfold chartPushed
  rfl

/-- The raw chart-pushforward of the partition-of-unity-weighted function
`ρ_α u` agrees with `chartPushed ρ α u` on `volume.restrict (chartTargetEuclid α)`. -/
lemma chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    (fun y => chartPushedRaw I α
        (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y)
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) ρ α u := by
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  exact (chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (I := I) (M := M) ρ α u hy).symm

omit [IsManifold I ∞ M] in
/-- The pointwise support of `ρ_α · u` is contained in the support of `ρ_α`. -/
lemma support_pou_mul_fun_subset
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    Function.support (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      Function.support ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  apply hx
  rw [h]; ring

omit [IsManifold I ∞ M] in
/-- The `tsupport` of `ρ_α · u` is contained in the `tsupport` of `ρ_α`. -/
lemma tsupport_pou_mul_fun_subset
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    tsupport (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  closure_mono (support_pou_mul_fun_subset (I := I) (M := M) ρ α u)

/-- For `u : M → ℝ` the function `ρ_α · u` has `tsupport` inside
`(chartAt H α).source` whenever `ρ` is subordinate to the canonical chart family. -/
lemma tsupport_pou_mul_fun_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) (u : M → ℝ) :
    tsupport (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
  (tsupport_pou_mul_fun_subset (I := I) (M := M) ρ α u).trans (hρ α)

omit [IsManifold I ∞ M] in
/-- Continuity of `(ρ α : C^∞⟮I, M; ℝ⟯)` as a real-valued function on `M`. -/
lemma pou_continuous (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    Continuous ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := (ρ α).contMDiff.continuous

omit [IsManifold I ∞ M] in
/-- Measurability of `(ρ α : C^∞⟮I, M; ℝ⟯)` on `M`. -/
lemma pou_measurable (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    Measurable ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  (pou_continuous (I := I) (M := M) ρ α).measurable

/-- For a Wkp-chart member `u : M → ℝ`, the chart-`α` chart-pushed `eLpNorm`
on the chart target equals the chart-`α` chart-pushed-raw `eLpNorm` of
`ρ_α · u`. -/
lemma eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (p : ℝ≥0∞) :
    eLpNorm (chartPushed (I := I) (M := M) ρ α u) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm (chartPushedRaw I α
            (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_congr_ae
    (chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target
      (I := I) (M := M) ρ α u).symm

/-- On a compact manifold, the function `u : M → ℝ` decomposes pointwise as
the finite POU sum `u(x) = ∑_α∈S ρ_α(x) u(x)` over the
`chartAtlasPOU_finset`. -/
lemma fun_eq_finset_sum_pou_mul
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (u : M → ℝ) :
    u = fun x =>
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x := by
  classical
  funext x
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have h_eq : ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x =
      (∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x) * u x := by
    rw [Finset.sum_mul]
  rw [h_eq, hsum, one_mul]

/-- The order-zero `eLpNorm` of `chartPushed α u` on `chartTargetEuclid α` is
bounded by the chart-`α` `wkpNorm` of `chartPushed α u`. -/
lemma eLpNorm_chartPushed_le_wkpNorm_chartPushed
    {k : ℕ} {p : ℝ≥0∞} (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (u : M → ℝ) :
    eLpNorm (chartPushed (I := I) (M := M) ρ α u) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
  Euclidean.wkpNorm_zero_le_wkpNorm

/-- For each chart `α` (with non-empty `tsupport(ρ_α)`), the chart density is
bounded uniformly on the compact `(extChartAt I α)`-image of `tsupport(ρ_α)`. -/
lemma exists_sup_chartDensity_on_pou_tsupport_image
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M)
    (h_supp_ne : (tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty) :
    ∃ M_sup : ℝ, 0 < M_sup ∧
      ∀ y ∈ (extChartAt I α) '' (tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
        DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm y) ≤ M_sup := by
  classical
  have hsub :
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hK_decomp :=
    image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M)
      (u := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) (α := α) hsub
  obtain ⟨hK_compact, hK_sub_target⟩ := hK_decomp
  have hK_ne : ((extChartAt I α) '' (tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ))).Nonempty := h_supp_ne.image _
  exact exists_sup_chartDensity_on_compact_pos (I := I) (M := M)
    g α hK_compact hK_ne hK_sub_target

/-- Per-`u` `eLpNorm` bridge applied to `ρ_α u`: there is a constant
`C > 0` (depending on `u`) such that the manifold-side `eLpNorm` of `ρ_α u` is
bounded by `C` times the chart-target `eLpNorm` of `chartPushed α u`. -/
lemma eLpNorm_pou_mul_riemannianMeasure_le_const_mul_eLpNorm_chartPushed_per_u
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu_meas : Measurable u) :
    ∃ C : ℝ, 0 < C ∧
      eLpNorm
          (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C *
            eLpNorm
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) p
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set ρα : M → ℝ := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρα_def
  set ρu : M → ℝ := fun x => ρα x * u x with hρu_def
  have hρα_meas : Measurable ρα :=
    pou_measurable (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
  have hρu_meas : Measurable ρu := hρα_meas.mul hu_meas
  have hρu_supp : tsupport ρu ⊆ (chartAt H α).source :=
    tsupport_pou_mul_fun_subset_chartAt_source (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α u
  obtain ⟨C, hC_pos, hbnd⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw
      (I := I) (M := M) g α hp_one hp_top hρu_meas hρu_supp
  refine ⟨C, hC_pos, ?_⟩
  refine hbnd.trans ?_
  have h_eq :=
    eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u p
  rw [hρu_def, ← h_eq]

/-- The chart-local-measure integral of the indicator of `tsupport(ρ_α)`
under `chartLocalMeasure α`. This is a finite ℝ≥0∞ value when the manifold
is compact. -/
private noncomputable def chartLocalIntegralPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  ∫⁻ x, (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)).indicator (fun _ : M => (1 : ℝ≥0∞)) x
      ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α)

/-- The Euclidean integral of `density · indicator(...)` over the chart target,
which is the "RHS denominator" in the chart Haar factor extraction. -/
private noncomputable def euclideanDensityIntegralPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
    ENNReal.ofReal
        (DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm y))) *
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)).indicator (fun _ : M => (1 : ℝ≥0∞))
        ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))

/-- The chart Haar factor, defined as the ratio of the chart-local-measure
integral of the indicator of `tsupport(ρ_α)` and the corresponding Euclidean
density-weighted integral. By the public equality lemma
`chartLocalMeasure_lintegral_via_chartTargetEuclid`, this ratio equals
`(euclideanHaarFactor E : ℝ≥0∞)` (private in `MeasureBridge`). -/
private noncomputable def chartHaarFactor
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  chartLocalIntegralPouTsupport (I := I) (M := M) g α /
    euclideanDensityIntegralPouTsupport (I := I) (M := M) g α

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
