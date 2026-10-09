import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.GeneralHGI
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteOrder
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PartialDiffeomorph

open scoped Manifold ContDiff Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

private theorem metricDerivNorm_pullbackMetricOn_restrict
    (Φ : PartialDiffeomorph I I M N ∞) (U V : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Φ.source) (hVU : V ≤ U)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N) (a : ℕ) (x : V) :
    CheegerGromovCompactness.metricDerivNorm a
      (pullbackMetricOn Φ V (fun _ hx => hU (hVU hx)) h) (g.restrictOpen V) (g.restrictOpen V) x =
    CheegerGromovCompactness.metricDerivNorm a
      (pullbackMetricOn Φ U hU h) (g.restrictOpen U) (g.restrictOpen U)
      (TopologicalSpace.Opens.inclusion hVU x) := by
  have hpull : (pullbackMetricOn Φ U hU h).restrictOpenOfSubset hVU =
      pullbackMetricOn Φ V (fun _ hx => hU (hVU hx)) h := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [SmoothRiemannianMetric.restrictSubset_inner]
    exact (pullbackMetricOn_inner Φ U hU h (TopologicalSpace.Opens.inclusion hVU y) v w).trans
      (pullbackMetricOn_inner Φ V (fun _ hy => hU (hVU hy)) h y v w).symm
  have hg : (g.restrictOpen U).restrictOpenOfSubset hVU = g.restrictOpen V := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rfl
  simpa only [hpull, hg] using
    CheegerGromovCompactness.HGI.metricDerivNorm_flat hVU
      (pullbackMetricOn Φ U hU h) (g.restrictOpen U) (g.restrictOpen U) a x

theorem metricCkErrorOn_congr_of_eqOn_open
    (Φ Ψ : PartialDiffeomorph I I M N ∞) (U : TopologicalSpace.Opens M)
    (hΦ : closure (U : Set M) ⊆ Φ.source) (hΨ : closure (U : Set M) ⊆ Ψ.source)
    (heq : Set.EqOn (Φ : M → N) (Ψ : M → N) U)
    (p : ℕ) (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N) :
    metricCkErrorOn Φ (closure (U : Set M)) p g h =
      metricCkErrorOn Ψ (closure (U : Set M)) p g h := by
  let SΦ : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let SΨ : TopologicalSpace.Opens M := ⟨Ψ.source, Ψ.open_source⟩
  let W : TopologicalSpace.Opens M := SΦ ⊓ SΨ
  have hWΦ : (W : Set M) ⊆ Φ.source := fun _ hx => hx.1
  have hWΨ : (W : Set M) ⊆ Ψ.source := fun _ hx => hx.2
  let A := pullbackMetricOn Φ W hWΦ h
  let B := pullbackMetricOn Ψ W hWΨ h
  let R := g.restrictOpen W
  have hnorm (a : ℕ) : Set.EqOn
      (fun z : W => CheegerGromovCompactness.metricDerivNorm a A R R z)
      (fun z : W => CheegerGromovCompactness.metricDerivNorm a B R R z)
      (Subtype.val ⁻¹' (U : Set M)) := by
    intro x hx
    apply CheegerGromovCompactness.metricDerivNorm_eq_of_metric_eventuallyEq
    filter_upwards [(U.isOpen.preimage continuous_subtype_val).mem_nhds hx] with y hy v w
    have hmap : (Φ : M → N) =ᶠ[𝓝 (y : M)] (Ψ : M → N) :=
      Filter.Eventually.mono (U.isOpen.mem_nhds hy) fun z hz => heq hz
    change (pullbackMetricOn Φ W hWΦ h).inner y v w =
      (pullbackMetricOn Ψ W hWΨ h).inner y v w
    rw [pullbackMetricOn_inner, pullbackMetricOn_inner,
      hmap.eq_of_nhds, hmap.mfderiv_eq]
    rfl
  have hnormClosure (a : ℕ) : Set.EqOn
      (fun z : W => CheegerGromovCompactness.metricDerivNorm a A R R z)
      (fun z : W => CheegerGromovCompactness.metricDerivNorm a B R R z)
      (Subtype.val ⁻¹' closure (U : Set M)) := by
    have hcl : (Subtype.val : W → M) ⁻¹' closure (U : Set M) =
        closure ((Subtype.val : W → M) ⁻¹' (U : Set M)) :=
      W.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val (U : Set M)
    rw [hcl]
    exact (hnorm a).closure
      (CheegerGromovCompactness.metricDerivNorm_cont a A R R)
      (CheegerGromovCompactness.metricDerivNorm_cont a B R R)
  have hpoint (a : ℕ) (x : M) (hx : x ∈ closure (U : Set M)) :
      CheegerGromovCompactness.metricDerivNorm a
        (pullbackMetricOn Φ SΦ Set.Subset.rfl h) (g.restrictOpen SΦ) (g.restrictOpen SΦ)
        ⟨x, hΦ hx⟩ =
      CheegerGromovCompactness.metricDerivNorm a
        (pullbackMetricOn Ψ SΨ Set.Subset.rfl h) (g.restrictOpen SΨ) (g.restrictOpen SΨ)
        ⟨x, hΨ hx⟩ := by
    let z : W := ⟨x, hΦ hx, hΨ hx⟩
    exact (metricDerivNorm_pullbackMetricOn_restrict Φ SΦ W Set.Subset.rfl hWΦ g h a z).symm.trans
      ((hnormClosure a hx).trans
        (metricDerivNorm_pullbackMetricOn_restrict Ψ SΨ W Set.Subset.rfl hWΨ g h a z))
  unfold metricCkErrorOn CheegerGromovCompactness.metricCkENormOn
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    apply le_iSup_of_le (⟨x, hΨ hx⟩ : SΨ)
    apply le_iSup_of_le hx
    exact le_of_eq (congrArg ENNReal.ofReal (hpoint a x hx))
  · refine iSup_le fun x => iSup_le fun hx => ?_
    apply le_iSup_of_le (⟨x, hΦ hx⟩ : SΦ)
    apply le_iSup_of_le hx
    exact le_of_eq (congrArg ENNReal.ofReal (hpoint a x hx).symm)

theorem isMetricApproximationOn_congr_of_eqOn_open
    (Φ Ψ : PartialDiffeomorph I I M N ∞) (U : TopologicalSpace.Opens M)
    (hΦ : closure (U : Set M) ⊆ Φ.source) (hΨ : closure (U : Set M) ⊆ Ψ.source)
    (heq : Set.EqOn (Φ : M → N) (Ψ : M → N) U)
    (p : ℕ) (ε : ℝ) (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N) :
    isMetricApproximationOn Φ (closure (U : Set M)) p ε g h ↔
      isMetricApproximationOn Ψ (closure (U : Set M)) p ε g h := by
  simp only [isMetricApproximationOn, hΦ, hΨ, true_and,
    metricCkErrorOn_congr_of_eqOn_open Φ Ψ U hΦ hΨ heq p g h]

end DifferentialGeometry.PartialDiffeomorph
