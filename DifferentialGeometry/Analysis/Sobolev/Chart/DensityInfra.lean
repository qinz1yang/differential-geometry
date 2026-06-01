import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.Atlas
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiply
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Chart.CompletenessAux
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Chart pullback and per-chart structure for the smooth-density program

For a smooth manifold `M` modelled on an inner-product space `E`, this file
develops infrastructure used in the smooth-density program for the chart-based
Sobolev space `W^{k,p}_chart(M)`:

* `chartPullback I α ψ` lifts a function `ψ : EuclN → ℝ` (where `EuclN` is the
  standard Euclidean space of dimension `finrank ℝ E`) to a function on `M`
  via the inverse chart, extended by zero outside the chart source. The
  pullback is linear in `ψ`.
* `chartPushed_chartPullback_apply_of_mem` establishes the pointwise identity
  `chartPushed ρ α (chartPullback I α ψ) y = ρ_α(z) · ψ(y)` for every
  `y ∈ chartTargetEuclid α`, where `z = (extChartAt I α).symm (toEuclidean.symm y)`.
* Support / compactness lemmas for the partition-of-unity-weighted product
  `ρ_α · u`, used for the Euclidean approximation hypothesis "the chart-pushed
  function has compact support strictly inside `chartTargetEuclid α`".
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
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

variable (I) in
/-- The chart-α pullback of `ψ : EuclN → ℝ`: it is `ψ ∘ toEuclidean ∘ extChartAt I α`
on `chart α source`, and `0` elsewhere. -/
def chartPullback (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) : M → ℝ := by
  classical
  exact fun x =>
    if x ∈ (chartAt H α).source then
      ψ (toEuclidean (extChartAt I α x))
    else 0

omit [IsManifold I ∞ M] in
/-- On `chart α source`, the pullback equals the composition. -/
lemma chartPullback_apply_of_mem (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartPullback I α ψ x = ψ (toEuclidean (extChartAt I α x)) := by
  classical
  unfold chartPullback
  simp [hx]

omit [IsManifold I ∞ M] in
/-- Off `chart α source`, the pullback is zero. -/
lemma chartPullback_apply_of_notMem (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    chartPullback I α ψ x = 0 := by
  classical
  unfold chartPullback
  simp [hx]

omit [IsManifold I ∞ M] in
/-- The chart pullback is additive. -/
lemma chartPullback_add (α : M)
    (ψ₁ ψ₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    chartPullback I α (fun y => ψ₁ y + ψ₂ y) =
      fun x => chartPullback I α ψ₁ x + chartPullback I α ψ₂ x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]

omit [IsManifold I ∞ M] in
/-- The chart pullback is homogeneous. -/
lemma chartPullback_const_smul (α : M) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    chartPullback I α (fun y => c * ψ y) =
      fun x => c * chartPullback I α ψ x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]

omit [IsManifold I ∞ M] in
/-- The chart pullback of the zero function is zero. -/
lemma chartPullback_zero_fun (α : M) :
    chartPullback I α (fun _ => (0 : ℝ)) = (fun _ : M => (0 : ℝ)) := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α (fun _ => (0 : ℝ)) hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α (fun _ => (0 : ℝ)) hx]

omit [IsManifold I ∞ M] in
/-- Off the chart-source, the pullback is identically zero, so its support
sits inside the chart source. -/
lemma support_chartPullback_subset_chartAt_source (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    Function.support (chartPullback I α ψ) ⊆ (chartAt H α).source := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  by_contra hx_off
  apply hx
  exact chartPullback_apply_of_notMem (I := I) (M := M) α ψ hx_off

omit [IsManifold I ∞ M] in
/-- For any `u : M → ℝ`, the (closed) support of `(ρ_α · u : M → ℝ)` is
contained in the (closed) support of `ρ_α`. -/
lemma tsupport_pou_mul_subset_tsupport_pou
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
        (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport (ρ α : M → ℝ) := by
  refine closure_mono ?_
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  simp only [Function.mem_support, ne_eq]
  intro h_pou_zero
  apply hx
  rw [h_pou_zero, zero_mul]

/-- For the canonical chart-atlas POU, the (closed) support of `ρ_α · u` is
contained in `chart α source`. -/
lemma tsupport_chartAtlasPOU_mul_subset_chartAt_source
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          u x) ⊆
      (chartAt H α).source :=
  Set.Subset.trans
    (tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

/-- For the canonical chart-atlas POU on a compact manifold, the closed
support of `ρ_α · u` is compact. -/
lemma hasCompactSupport_chartAtlasPOU_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    HasCompactSupport (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          u x) := by
  have h_subset := tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
  have h_compact : IsCompact (tsupport
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)) :=
    (isClosed_tsupport _).isCompact
  exact h_compact.of_isClosed_subset (isClosed_tsupport _) h_subset

/-- For `y` in `chartTargetEuclid α`, the chart-pushed value of the chart-α
pullback of `ψ` is `ρ_α(z) · ψ(y)`, where `z = symm_α(toEuclidean.symm y)`.

This algebraic identity, combined with the Euclidean smooth-density theorem
`MemWkp.exists_smooth_compactSupport_approx`, drives the per-chart smooth
approximation step in the chart-Sobolev density program. -/
lemma chartPushed_chartPullback_apply_of_mem
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α (chartPullback I α ψ) y =
      (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y)) *
      ψ y := by
  classical
  unfold chartPushed
  set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hz_source : z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hsymm_target
  have hz_chartAt_source : z ∈ (chartAt H α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)] at hz_source
    exact hz_source
  rw [chartPullback_apply_of_mem (I := I) (M := M) α ψ hz_chartAt_source]
  have hz_inv : (extChartAt I α) z = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hsymm_target
  rw [hz_inv]
  rw [(toEuclidean (E := E)).apply_symm_apply y]

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
