import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.Atlas
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Sobolev embedding `W^{1,p}_chart(M) ↪ L^q` on a closed manifold

For a closed (compact, boundaryless) smooth manifold `M` modelled on an
inner-product `E`, this file provides a chart-by-chart Sobolev-style continuous
embedding from the chart-based Sobolev space `W^{1,p}_chart(M)` (defined in
`Chart.lean`) into the chart-pushed `L^q` "norm".

The Hölder/finite-measure case (`q ≤ p`) is treated rigorously: on a compact
manifold, every chart-pushed function vanishes (within the chart target) outside
a compact set — the toEuclidean image of the chart-image of the
partition-of-unity tsupport — and Mathlib's
`MemLp.mono_exponent_of_measure_support_ne_top` then transfers `L^p` membership
to `L^q` for any lower exponent.

## Main results

* `eLpNorm_chartPushed_p_le_wkpNorm_one` : the order-zero L^p norm of the
  chart-pushed function is bounded by the order-one chart Sobolev norm
  (orderwise monotonicity).

* `chartPushed_memLp_of_memWkpChart_subexp` : for `q ≤ p`, the chart-pushed
  function lies in `L^q` of the chart target (as a subset of finite Euclidean
  measure carried by the compact image of the partition-of-unity support).

* `eLpNorm_chartPushed_q_le_wkpNorm_one_subexp` : the per-chart `q ≤ p` Hölder
  bound, with constant given by `(volume of compact chart-image)^{1/q - 1/p}`.

* `lqChartSum_le_wkpNormChart_subexp` : the **summed** chart-pushed `L^q` norm
  over the canonical partition of unity is bounded by a constant times the
  full chart-Sobolev `W^{1,p}` norm of `u`.

* `lpChartSum_le_wkpNormChart` : the same statement specialised to `q = p`
  (no rpow factor, valid for any boundaryless model with the canonical POU).

## Scope and future work

* **Bridge to the intrinsic `L^q`-norm under the Riemannian measure** is left
  for a follow-up module. That bridge requires uniform bounds on the metric
  volume density and on the Jacobian of `toEuclidean` over the (finitely-many)
  supports of the partition-of-unity weights on a compact manifold, plus a
  comparison of the canonical Haar measure on `E` with the standard volume
  measure on `EuclideanSpace ℝ (Fin (finrank ℝ E))`. The output is a constant
  `C(g, ρ)` such that
  `eLpNorm u q (riemannianMeasure g) ≤ C · lqChartSum`.

* **Sub-critical Sobolev `q = np/(n-p)` Sobolev conjugate embedding** (for
  `1 ≤ p < n` on closed `M`) is deferred to a follow-up module. The natural
  chart-by-chart route applies the vendored `sobolev_poincare_unitBall'` after
  a translation+scaling argument that maps the compact chart-image of the
  POU support into a unit ball, or uses the `MemW01p`-extension of an
  indicator-truncated chart-pushed function and the vendored
  `sobolev_of_memW01p_univ`. Both routes require additional infrastructure not
  yet in place.

* **Continuous embedding `W^{k,p}(M) ↪ C^0(M)` for `k > n/p`** is deferred.

* **Sobolev algebra `H^k · H^k → H^k` for `k > n/2`** is deferred.
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

/-- The order-zero `L^p` norm of a function is bounded by its order-`k`
Sobolev norm. -/
theorem Euclidean.wkpNorm_zero_le_wkpNorm
    {d : ℕ} {k : ℕ} {p : ℝ≥0∞} {u : EuclideanSpace ℝ (Fin d) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))} :
    eLpNorm u p (MeasureTheory.volume.restrict Ω) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm (d := d) k p u Ω := by
  classical
  let innerSum : ℕ → ℝ≥0∞ := fun j =>
    ∑ α : Fin j → Fin d,
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := d) p j α u Ω) p (MeasureTheory.volume.restrict Ω)
  have hWkp : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm (d := d) k p u Ω =
      ∑ j ∈ Finset.range (k + 1), innerSum j :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum k p u Ω
  have h_inner0 : innerSum 0 = eLpNorm u p (MeasureTheory.volume.restrict Ω) := by
    simp only [innerSum]
    have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
      funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin d) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α : Fin 0 → Fin d =>
            eLpNorm (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := d) p 0 α u Ω) p (MeasureTheory.volume.restrict Ω))]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  have h0 : (0 : ℕ) ∈ Finset.range (k + 1) := by
    rw [Finset.mem_range]; omega
  have h_le : innerSum 0 ≤ ∑ j ∈ Finset.range (k + 1), innerSum j :=
    Finset.single_le_sum (f := innerSum) (fun i _ => zero_le _) h0
  rw [hWkp]
  rw [← h_inner0]
  exact h_le

/-- The order-zero `L^p` norm of the chart-pushed function is bounded by the
chart Sobolev `W^{1,p}_chart` norm of `u`. -/
theorem eLpNorm_chartPushed_p_le_wkpNorm_one
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (u : M → ℝ) (α : M) :
    eLpNorm
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        p
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      ≤ wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  have h_per_α :
      eLpNorm
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          p
          (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
        ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) :=
    Euclidean.wkpNorm_zero_le_wkpNorm
  have h_le_tsum : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑' β : M,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β u)
            (chartTargetEuclid (I := I) (M := M) β) := by
    exact ENNReal.le_tsum α
  exact h_per_α.trans h_le_tsum

/-- For a compact manifold `M` and a chart-source-subordinate POU member `ρ_α`,
the `tsupport` of `ρ_α` is compact (subset of compact M). -/
private theorem tsupport_pou_isCompact
    [CompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    IsCompact (tsupport (ρ α : M → ℝ)) :=
  (isClosed_tsupport _).isCompact

/-- The image under `extChartAt I α` of the `tsupport` of a subordinate POU
member is compact in `E`. -/
private theorem image_extChartAt_tsupport_pou_isCompact
    [CompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    (α : M) :
    IsCompact ((extChartAt I α) '' (tsupport (ρ α : M → ℝ))) := by
  have hsub : tsupport (ρ α : M → ℝ) ⊆ (extChartAt I α).source := by
    intro x hx
    have h1 : x ∈ (chartAt H α).source := hρ α hx
    rwa [extChartAt_source]
  have hcont : ContinuousOn (extChartAt I α) (tsupport (ρ α : M → ℝ)) :=
    (continuousOn_extChartAt α).mono hsub
  exact (tsupport_pou_isCompact ρ α).image_of_continuousOn hcont

/-- The `toEuclidean` image of `extChartAt I α '' (tsupport ρ_α)` is compact in
`EuclideanSpace ℝ (Fin (finrank ℝ E))`, and lies inside `chartTargetEuclid α`. -/
private theorem image_chartPOU_subset_chartTargetEuclid
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    (α : M) :
    toEuclidean '' ((extChartAt I α) '' (tsupport (ρ α : M → ℝ))) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  intro y hy
  obtain ⟨z, hz_mem, hzy⟩ := hy
  obtain ⟨x, hx_mem, hxz⟩ := hz_mem
  have hx_source : x ∈ (extChartAt I α).source := by
    have : x ∈ (chartAt H α).source := hρ α hx_mem
    rwa [extChartAt_source]
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hxz]
    exact (extChartAt I α).map_source hx_source
  exact ⟨z, hz_target, hzy⟩

/-- The `toEuclidean`-image of the chart-image of `tsupport(ρ_α)` is compact. -/
private theorem chartImage_tsupport_isCompact_toEuclidean
    [CompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    (α : M) :
    IsCompact (toEuclidean '' ((extChartAt I α) '' (tsupport (ρ α : M → ℝ)))) :=
  (image_extChartAt_tsupport_pou_isCompact (I := I) (M := M) ρ hρ α).image
    toEuclidean.continuous

/-- The chart-pushed function is supported (in the genuine sense, where
nonzero) inside `toEuclidean '' (extChartAt I α) '' (tsupport ρ_α)`, RESTRICTED
to `chartTargetEuclid α`. That is, on `chartTargetEuclid α`, the chart-pushed
function vanishes outside the compact set
`toEuclidean '' (extChartAt I α) '' (tsupport ρ_α)`. -/
private theorem chartPushed_eq_zero_off_image_tsupport
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (α : M) (u : M → ℝ) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ toEuclidean '' ((extChartAt I α) '' (tsupport (ρ α : M → ℝ)))) :
    chartPushed (I := I) (M := M) ρ α u y = 0 := by
  obtain ⟨z, hz_target, hzy⟩ := hy_target
  have hsymm_source : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hz_target
  have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
    (extChartAt I α).right_inv hz_target
  by_contra hne
  apply hy_off
  refine ⟨z, ?_, hzy⟩
  refine ⟨(extChartAt I α).symm z, ?_, hz_eq⟩
  have hy_eq : toEuclidean.symm y = z := by
    rw [← hzy]
    exact toEuclidean.symm_apply_apply z
  unfold chartPushed at hne
  rw [hy_eq] at hne
  have hρ_ne : (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm z) ≠ 0 := by
    intro h0
    apply hne
    rw [h0]; ring
  exact subset_tsupport _ (Function.mem_support.mpr hρ_ne)

variable {u : M → ℝ}

/-- For a compact manifold and the canonical chart-atlas POU, the chart-pushed
function vanishes on `chartTargetEuclid α` outside a compact set, where the
compact set is the toEuclidean-image of the chart-image of `tsupport(ρ_α)`. -/
theorem chartPushed_support_subset_compact_in_target
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) (u : M → ℝ) :
    ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ toEuclidean ''
            ((extChartAt I α) ''
              (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ))) →
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y = 0 := by
  intro y hy_target hy_off
  exact chartPushed_eq_zero_off_image_tsupport (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u hy_target hy_off

/-- Volume (Euclidean) of the toEuclidean-image of the chart-image of
`tsupport(ρ_α)` is finite, since the set is compact. -/
theorem volume_chartImage_tsupport_lt_top
    [CompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    (α : M) :
    MeasureTheory.volume
        (toEuclidean '' ((extChartAt I α) '' (tsupport (ρ α : M → ℝ))))
      < (⊤ : ℝ≥0∞) := by
  have hK := chartImage_tsupport_isCompact_toEuclidean (I := I) (M := M) ρ hρ α
  exact hK.measure_lt_top

/-- For `q ≤ p` (with `1 ≤ q ≤ p < ∞`), and `MemWkpChart g 1 p u` (so each
chart-pushed function is in `MemW1p p`, which contains `MemLp p`), the
chart-pushed function is in `MemLp q` of the chart target image (under
`volume.restrict`).

The mechanism: the chart-pushed function is supported (within
`chartTargetEuclid α`, the only place that matters for `volume.restrict`) on a
compact set of finite measure. Apply `MemLp.mono_exponent_of_measure_support_ne_top`. -/
theorem chartPushed_memLp_of_memWkpChart_subexp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hqp : q ≤ p) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) (α : M) :
    MeasureTheory.MemLp
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      q
      (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_memLp : MeasureTheory.MemLp
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      p
      (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := hu α
    exact h.memLp
  set ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M
  set Sα : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    toEuclidean '' ((extChartAt I α) '' (tsupport (ρ α : M → ℝ)))
  have hSα_subset_target : Sα ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_chartPOU_subset_chartTargetEuclid (I := I) (M := M) ρ
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
  have hSα_compact : IsCompact Sα :=
    chartImage_tsupport_isCompact_toEuclidean (I := I) (M := M) ρ
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
  have hSα_meas : MeasurableSet Sα := hSα_compact.measurableSet
  set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushed (I := I) (M := M) ρ α u with hf_def
  let fclean : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    Set.indicator Sα f
  have hae : f =ᵐ[MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)] fclean := by
    have hae_in_target : ∀ᵐ y ∂(MeasureTheory.volume.restrict
          (chartTargetEuclid (I := I) (M := M) α)),
          y ∈ chartTargetEuclid (I := I) (M := M) α := by
      have hmeas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      exact MeasureTheory.ae_restrict_mem hmeas
    filter_upwards [hae_in_target] with y hy_in_target
    by_cases h_in_Sα : y ∈ Sα
    · simp [fclean, Set.indicator_of_mem h_in_Sα]
    · have hf_zero : f y = 0 :=
        chartPushed_eq_zero_off_image_tsupport (I := I) (M := M) ρ α u hy_in_target h_in_Sα
      have hfclean_zero : fclean y = 0 := Set.indicator_of_notMem h_in_Sα _
      rw [hf_zero, hfclean_zero]
  have h_fclean_memLp_p : MeasureTheory.MemLp fclean p
      (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
    (MeasureTheory.memLp_congr_ae hae).mp h_memLp
  have hfclean_zero_off : ∀ y, y ∉ Sα → fclean y = 0 := by
    intro y hy
    exact Set.indicator_of_notMem hy _
  have hSα_meas_lt_top : MeasureTheory.volume.restrict
        (chartTargetEuclid (I := I) (M := M) α) Sα < ⊤ := by
    have h1 : MeasureTheory.volume.restrict
        (chartTargetEuclid (I := I) (M := M) α) Sα ≤
      MeasureTheory.volume Sα :=
      MeasureTheory.Measure.restrict_le_self _
    exact lt_of_le_of_lt h1 (volume_chartImage_tsupport_lt_top (I := I) (M := M) ρ
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α)
  have h_fclean_memLp_q : MeasureTheory.MemLp fclean q
      (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
    h_fclean_memLp_p.mono_exponent_of_measure_support_ne_top
      (s := Sα) hfclean_zero_off (ne_of_lt hSα_meas_lt_top) hqp
  exact (MeasureTheory.memLp_congr_ae hae.symm).mp h_fclean_memLp_q

/-- The per-chart Hölder bound: for `q ≤ p`, the chart-pushed `L^q` norm is
controlled by `(volume of compact chart-image of tsupport(ρ_α))^{1/q - 1/p}`
times the chart-pushed `L^p` norm. -/
theorem eLpNorm_chartPushed_q_le_chartPushed_p_subexp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hq_pos : q ≠ 0) (hp_top : p ≠ (⊤ : ℝ≥0∞)) (hqp : q ≤ p) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) (α : M) :
    eLpNorm
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        q
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      ≤
        eLpNorm
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          p
          (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
        * (MeasureTheory.volume
            (toEuclidean ''
              ((extChartAt I α) ''
                (tsupport
                  ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)))))
            ^ (1 / q.toReal - 1 / p.toReal) := by
  classical
  set ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M
  set Sα : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    toEuclidean '' ((extChartAt I α) '' (tsupport (ρ α : M → ℝ)))
  set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushed (I := I) (M := M) ρ α u with hf_def
  let fclean : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    Set.indicator Sα f
  have hae : f =ᵐ[MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)] fclean := by
    have hae_in_target : ∀ᵐ y ∂(MeasureTheory.volume.restrict
          (chartTargetEuclid (I := I) (M := M) α)),
          y ∈ chartTargetEuclid (I := I) (M := M) α := by
      have hmeas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      exact MeasureTheory.ae_restrict_mem hmeas
    filter_upwards [hae_in_target] with y hy_in_target
    by_cases h_in_Sα : y ∈ Sα
    · simp [fclean, Set.indicator_of_mem h_in_Sα]
    · have hf_zero : f y = 0 :=
        chartPushed_eq_zero_off_image_tsupport (I := I) (M := M) ρ α u hy_in_target h_in_Sα
      have hfclean_zero : fclean y = 0 := Set.indicator_of_notMem h_in_Sα _
      rw [hf_zero, hfclean_zero]
  have heq_q : eLpNorm f q
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      = eLpNorm fclean q
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
    eLpNorm_congr_ae hae
  have heq_p : eLpNorm f p
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      = eLpNorm fclean p
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
    eLpNorm_congr_ae hae
  rw [heq_q, heq_p]
  set μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α) with hμ_def
  have hSα_meas : MeasurableSet Sα :=
    (chartImage_tsupport_isCompact_toEuclidean (I := I) (M := M) ρ
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α).measurableSet
  have heq_q' : eLpNorm fclean q μ = eLpNorm f q (μ.restrict Sα) := by
    rw [show fclean = Set.indicator Sα f from rfl]
    exact eLpNorm_indicator_eq_eLpNorm_restrict hSα_meas
  have heq_p' : eLpNorm fclean p μ = eLpNorm f p (μ.restrict Sα) := by
    rw [show fclean = Set.indicator Sα f from rfl]
    exact eLpNorm_indicator_eq_eLpNorm_restrict hSα_meas
  rw [heq_q', heq_p']
  have h_memLp_f_p_μ : MeasureTheory.MemLp f p μ := (hu α).memLp
  have h_aesm_f : MeasureTheory.AEStronglyMeasurable f μ :=
    h_memLp_f_p_μ.aestronglyMeasurable
  have h_aesm_f_restrict : MeasureTheory.AEStronglyMeasurable f (μ.restrict Sα) :=
    h_aesm_f.restrict
  have h_le : eLpNorm f q (μ.restrict Sα)
      ≤ eLpNorm f p (μ.restrict Sα) *
        (μ.restrict Sα Set.univ) ^ (1 / q.toReal - 1 / p.toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp h_aesm_f_restrict
  have hμSα_le : μ.restrict Sα Set.univ ≤ MeasureTheory.volume Sα := by
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact MeasureTheory.Measure.restrict_le_self _
  have hexp_nonneg : 0 ≤ 1 / q.toReal - 1 / p.toReal := by
    have hq_le_p_real : q.toReal ≤ p.toReal := ENNReal.toReal_mono hp_top hqp
    have hq_pos_real : 0 < q.toReal := by
      have hq_lt_top : q < ⊤ := lt_of_le_of_lt hqp (lt_top_iff_ne_top.mpr hp_top)
      exact ENNReal.toReal_pos hq_pos hq_lt_top.ne
    have hp_pos_real : 0 < p.toReal := lt_of_lt_of_le hq_pos_real hq_le_p_real
    rw [sub_nonneg]
    rw [one_div, one_div, inv_le_inv₀ hp_pos_real hq_pos_real]
    exact hq_le_p_real
  have h_rpow : (μ.restrict Sα Set.univ) ^ (1 / q.toReal - 1 / p.toReal) ≤
      MeasureTheory.volume Sα ^ (1 / q.toReal - 1 / p.toReal) :=
    ENNReal.rpow_le_rpow hμSα_le hexp_nonneg
  have h_step1 : eLpNorm f p (μ.restrict Sα) *
        ((μ.restrict Sα) Set.univ) ^ (1 / q.toReal - 1 / p.toReal) ≤
      eLpNorm f p (μ.restrict Sα) *
        MeasureTheory.volume Sα ^ (1 / q.toReal - 1 / p.toReal) := by
    gcongr
  exact h_le.trans h_step1

/-- Combined: per-chart `L^q` norm bounded by `(vol(compact))^{...}` times the
chart Sobolev `W^{1,p}` norm of `u`. -/
theorem eLpNorm_chartPushed_q_le_wkpNorm_one_subexp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hq_pos : q ≠ 0) (hp_top : p ≠ (⊤ : ℝ≥0∞)) (hqp : q ≤ p) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) (α : M) :
    eLpNorm
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        q
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      ≤ wkpNormChart (I := I) (M := M) g 1 p u
        * (MeasureTheory.volume
            (toEuclidean ''
              ((extChartAt I α) ''
                (tsupport
                  ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)))))
            ^ (1 / q.toReal - 1 / p.toReal) := by
  have h1 := eLpNorm_chartPushed_q_le_chartPushed_p_subexp (I := I) (M := M) g
    hq_pos hp_top hqp hu α
  have h2 := eLpNorm_chartPushed_p_le_wkpNorm_one (I := I) (M := M) g (p := p) u α
  have h3 : eLpNorm
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      p
      (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      * (MeasureTheory.volume
          (toEuclidean ''
            ((extChartAt I α) ''
              (tsupport
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)))))
          ^ (1 / q.toReal - 1 / p.toReal)
      ≤ wkpNormChart (I := I) (M := M) g 1 p u
        * (MeasureTheory.volume
            (toEuclidean ''
              ((extChartAt I α) ''
                (tsupport
                  ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)))))
            ^ (1 / q.toReal - 1 / p.toReal) :=
    mul_le_mul' h2 le_rfl
  exact h1.trans h3

/-- The sum of chart-pushed `L^q` norms over the canonical partition of unity
is bounded by `(sup over α with non-empty support of vol(K_α))^{1/q-1/p}` times
`(N : the count of α with nonempty support)` times the chart Sobolev norm. -/
theorem lqChartSum_le_wkpNormChart_subexp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hq_pos : q ≠ 0) (hp_top : p ≠ (⊤ : ℝ≥0∞)) (hqp : q ≤ p) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) :
    ∑' α : M,
      eLpNorm
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        q
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      ≤ ∑' α : M,
        (wkpNormChart (I := I) (M := M) g 1 p u
          * (MeasureTheory.volume
              (toEuclidean ''
                ((extChartAt I α) ''
                  (tsupport
                    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)))))
              ^ (1 / q.toReal - 1 / p.toReal)) := by
  apply ENNReal.tsum_le_tsum
  intro α
  exact eLpNorm_chartPushed_q_le_wkpNorm_one_subexp (I := I) (M := M) g
    hq_pos hp_top hqp hu α

/-- The sum of chart-pushed `L^p` norms is at most `N * wkpNormChart`, where
`N` counts charts with non-empty POU support — but more cleanly: the sum is
already bounded by `wkpNormChart` (since each per-chart `L^p` is bounded by
the per-chart `wkpNorm`, and the sum is bounded by `tsum wkpNorm` =
`wkpNormChart`). -/
theorem lpChartSum_le_wkpNormChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (u : M → ℝ) :
    ∑' α : M,
      eLpNorm
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        p
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      ≤ wkpNormChart (I := I) (M := M) g 1 p u := by
  have h_per : ∀ α : M,
      eLpNorm
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          p
          (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
        ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := by
    intro α
    exact Euclidean.wkpNorm_zero_le_wkpNorm
  have h_step1 : (∑' α : M,
        eLpNorm
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          p
          (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)))
        ≤ ∑' α : M,
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 p
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α) :=
    ENNReal.tsum_le_tsum h_per
  exact h_step1

/-- If `u ∈ W^{1,p}_chart(M)`, then for every chart `α`, the chart-pushed function
is in `L^p(volume.restrict (chartTargetEuclid α))`. Direct corollary of the
definition (since `MemWkp 1 p` includes the L^p part). -/
theorem chartPushed_memLp_p
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) (α : M) :
    MeasureTheory.MemLp
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      p
      (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  (hu α).memLp

/-- A more user-friendly version of `chartPushed_memLp_of_memWkpChart_subexp`,
restated with `1 ≤ q` and `q ≤ p`: on a closed manifold, every chart-pushed
function from a `W^{1,p}_chart` element lies in `L^q` for any `1 ≤ q ≤ p`,
because the function is supported on a compact set of finite Euclidean volume. -/
theorem chartPushed_memLq_le_p
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (_hq_one : 1 ≤ q) (hqp : q ≤ p) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) (α : M) :
    MeasureTheory.MemLp
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      q
      (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  chartPushed_memLp_of_memWkpChart_subexp (I := I) (M := M) g hqp hu α

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
