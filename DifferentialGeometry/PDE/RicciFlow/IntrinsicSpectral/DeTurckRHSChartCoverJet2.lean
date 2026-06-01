import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRHSAbstractJet2Bound

/-!
# Manifold chart-cover packaging of the Ricci–DeTurck `2`-jet frame-component bound

The committed per-chart pointwise bound
`abstractRHSFrameComponent_diff_abs_le_jet2` controls the chart-`α`-frame scalar
components of the Ricci–DeTurck right-hand-side difference
`deTurckRicciRHS g_bg g₁ − deTurckRicciRHS g_bg g₂` by a single constant `C`
times the chart `2`-jet seminorm `chartMetricJet2DiffSup g₁ g₂ α` of the metric
difference, uniformly over a compact subset `K` of the interior of the chart-`α`
target.  That bound is the *local* (single-chart) atom on which the eventual
`H^{a+1} → H^a` Sobolev-norm Lipschitz estimate for the DeTurck nonlinearity is
built: integrating the chart-component bound against the intrinsic `L²` norm over
a finite chart cover, then converting the chart `2`-jet seminorm into the
intrinsic Sobolev `2`-jet content, produces the Lipschitz bound consumed by the
spectral strong-existence engine.

This file performs the **finite chart-cover packaging** of that local atom: the
combinatorial step that lifts the per-chart constant to a *single* manifold
constant over a chosen finite family of charts whose interior-target compact
pieces cover the manifold.  It supplies:

* `exists_chart_target_compact_cover` — on a compact manifold every point lies in
  the interior of *its own* chart target, so the chart sources give an open cover;
  by compactness there is a finite set of chart centres whose source charts cover
  `M`, together with, for each, a compact subset of the chart-target interior
  containing the image of the chart centre.  (The model is boundaryless, so the
  chart targets are open and equal their interiors.)

* `abstractRHSFrameComponent_diff_abs_le_jet2_chartCenter` — the per-chart atom
  specialised to the compact singleton `{extChartAt I α α}` at the chart centre,
  the minimal compact piece always available.

* `exists_uniform_const_RHSFrameComponent_diff_jet2_on_finset` — the **headline**:
  for any finite family of `(chart centre, compact piece)` pairs there is a single
  constant `C > 0` dominating every per-chart `2`-jet Lipschitz constant; hence the
  frame-component bound holds with the *same* `C` on every piece of the family.

All bounds are chart-coordinate / model-norm-free in the sense of the underlying
atom: the right-hand side is the chart `2`-jet seminorm `chartMetricJet2DiffSup`,
not a trivialization-image operator norm; no chart-locality predicate
(`HasLocallyConstantChartAt`) and no parallelizability witness appears.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
/-- For a boundaryless model the chart-`α` target is open, so its interior is the
target itself; the chart-centre image `extChartAt I α α` lies in that interior. -/
theorem extChartAt_self_mem_interior_target (α : M) :
    extChartAt I α α ∈ interior ((extChartAt I α).target : Set E) := by
  rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
  exact mem_extChartAt_target (I := I) α

set_option linter.unusedSectionVars false in
/-- The singleton `{extChartAt I α α}` is a compact subset of the interior of the
chart-`α` target — the minimal compact piece on which the per-chart `2`-jet atom
always applies. -/
theorem singleton_chartCenter_subset_interior_target (α : M) :
    ({extChartAt I α α} : Set E) ⊆ interior ((extChartAt I α).target : Set E) :=
  Set.singleton_subset_iff.mpr (extChartAt_self_mem_interior_target (I := I) α)

set_option linter.unusedSectionVars false in
/-- **The per-chart `2`-jet frame-component atom at the chart centre.**

Specialising `abstractRHSFrameComponent_diff_abs_le_jet2` to the compact
singleton `K = {extChartAt I α α}` gives, for fixed `g_bg g₁ g₂` and chart
centre `α`, a constant `C > 0` such that the chart-`α`-frame scalar components of
the Ricci–DeTurck right-hand-side difference at the chart-centre image
`y = extChartAt I α α` are bounded by `C · chartMetricJet2DiffSup g₁ g₂ α y`. -/
theorem abstractRHSFrameComponent_diff_abs_le_jet2_chartCenter
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j : Fin (Module.finrank ℝ E),
      |(deTurckRicciRHS (I := I) g_bg g₁ ((extChartAt I α).symm (extChartAt I α α)) -
            deTurckRicciRHS (I := I) g_bg g₂ ((extChartAt I α).symm (extChartAt I α α)))
          (chartFrameVec (I := I) α i ((extChartAt I α).symm (extChartAt I α α)))
          (chartFrameVec (I := I) α j ((extChartAt I α).symm (extChartAt I α α)))| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α (extChartAt I α α) := by
  obtain ⟨C, hC_pos, hC⟩ :=
    abstractRHSFrameComponent_diff_abs_le_jet2 (I := I) g_bg g₁ g₂ α
      (K := {extChartAt I α α}) isCompact_singleton
      (singleton_chartCenter_subset_interior_target (I := I) α)
  exact ⟨C, hC_pos, fun i j => hC (extChartAt I α α) (Set.mem_singleton _) i j⟩

set_option linter.unusedSectionVars false in
/-- **Finite chart-source cover.**  On a compact manifold every point lies in its
own chart source, so the chart sources form an open cover; by compactness there
is a finite set of chart centres `s : Finset M` whose chart sources cover `M`. -/
theorem exists_finite_chartSource_cover :
    ∃ s : Finset M, (⋃ α ∈ s, (chartAt H α).source) = Set.univ := by
  classical
  have hcover : (⋃ α : M, (chartAt H α).source) = Set.univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source H x⟩
  have hopen : ∀ α : M, IsOpen ((chartAt H α).source) := fun α => (chartAt H α).open_source
  obtain ⟨s, hs⟩ :=
    IsCompact.elim_finite_subcover (isCompact_univ (X := M))
      (fun α : M => (chartAt H α).source) hopen
      (by rw [hcover])
  refine ⟨s, Set.eq_univ_of_univ_subset ?_⟩
  simpa using hs

set_option linter.unusedSectionVars false in
/-- **Manifold-uniform constant for the frame-component `2`-jet bound over a finite
chart family.**

Given a finite indexing `Finset ι`, a family of chart centres `α : ι → M`, and a
family of compact pieces `K : ι → Set E` with `K c ⊆ interior (extChartAt I (α c)).target`,
there is a *single* constant `C > 0` such that for every index `c`, every chart
point `y ∈ K c`, and all frame indices `(i, j)`, the chart-`(α c)`-frame scalar
component of the Ricci–DeTurck right-hand-side difference is bounded by
`C · chartMetricJet2DiffSup g₁ g₂ (α c) y`.

`C` is built as `1 + ∑_c C_c`, where `C_c > 0` is the per-chart atom constant from
`abstractRHSFrameComponent_diff_abs_le_jet2`; since each `C_c > 0` and the `2`-jet
seminorm is non-negative, the per-chart bound `≤ C_c · jet2` upgrades to
`≤ C · jet2` for the uniform `C ≥ C_c`. -/
theorem exists_uniform_const_RHSFrameComponent_diff_jet2_on_finset
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M)
    {ι : Type*} (t : Finset ι) (α : ι → M) (K : ι → Set E)
    (hK : ∀ c ∈ t, IsCompact (K c))
    (hKsub : ∀ c ∈ t, K c ⊆ interior ((extChartAt I (α c)).target : Set E)) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ t, ∀ y ∈ K c, ∀ i j : Fin (Module.finrank ℝ E),
      |(deTurckRicciRHS (I := I) g_bg g₁ ((extChartAt I (α c)).symm y) -
            deTurckRicciRHS (I := I) g_bg g₂ ((extChartAt I (α c)).symm y))
          (chartFrameVec (I := I) (α c) i ((extChartAt I (α c)).symm y))
          (chartFrameVec (I := I) (α c) j ((extChartAt I (α c)).symm y))| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ (α c) y := by
  classical
  choose C hC_pos hC using fun (c : ι) (hc : c ∈ t) =>
    abstractRHSFrameComponent_diff_abs_le_jet2 (I := I) g_bg g₁ g₂ (α c)
      (hK c hc) (hKsub c hc)
  refine ⟨1 + ∑ c ∈ t.attach, C c.1 c.2, ?_, ?_⟩
  · have hsum_nn : 0 ≤ ∑ c ∈ t.attach, C c.1 c.2 :=
      Finset.sum_nonneg (fun c _ => (hC_pos c.1 c.2).le)
    linarith
  intro c hc y hy i j
  have hbound := hC c hc y hy i j
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ (α c) y :=
    chartMetricJet2DiffSup_nonneg _ _ _ _
  have hCc_le : C c hc ≤ 1 + ∑ d ∈ t.attach, C d.1 d.2 := by
    have hmem : (⟨c, hc⟩ : {x // x ∈ t}) ∈ t.attach := Finset.mem_attach _ _
    have hsingle : C c hc ≤ ∑ d ∈ t.attach, C d.1 d.2 :=
      Finset.single_le_sum (f := fun d : {x // x ∈ t} => C d.1 d.2)
        (fun d _ => (hC_pos d.1 d.2).le) hmem
    linarith
  calc
    |(deTurckRicciRHS (I := I) g_bg g₁ ((extChartAt I (α c)).symm y) -
          deTurckRicciRHS (I := I) g_bg g₂ ((extChartAt I (α c)).symm y))
        (chartFrameVec (I := I) (α c) i ((extChartAt I (α c)).symm y))
        (chartFrameVec (I := I) (α c) j ((extChartAt I (α c)).symm y))|
      ≤ C c hc * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ (α c) y := hbound
    _ ≤ (1 + ∑ d ∈ t.attach, C d.1 d.2) *
          chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ (α c) y :=
        mul_le_mul_of_nonneg_right hCc_le hjet2_nn

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
