import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.TimeRegularity
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Coordinates
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Bundle.PartialMfderiv.Basic

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem exists_local_metric_time_lipschitz_on_regular_interval
    {D : RealTimeInterval} (G : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn D G)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) (q : ℕ) (x : M) :
    ∃ (U : Set M) (L : ℝ), IsOpen U ∧ x ∈ U ∧ 0 ≤ L ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ y ∈ U,
        metricDerivNorm q (G s) (G t) R y ≤ L * |s - t| := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨basisE, V, C, hV, hxV, hVbase, hC, hnorm⟩ :=
    metricDerivNorm_le_compSq_uniform R q x
  let e := trivializationAt E (TangentSpace I) x
  let frame := e.localFrame basisE
  have hframe : IsLocalFrameOn I E ∞ frame e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I ∞ basisE
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  obtain ⟨sec, hsec⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet hxe
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hsec
  obtain ⟨K, hK, hxK, hKVW⟩ := exists_compact_between isCompact_singleton
    (hV.inter hW) (singleton_subset_iff.mpr ⟨hxV, hxW⟩)
  let F : (Fin (q + 2) → Fin (Module.finrank ℝ E)) → ℝ × M → ℝ :=
    fun slots z => metricCovDeriv (G z.1) R q z.2 (fun j => sec (slots j) z.2)
  have hF (slots : Fin (q + 2) → Fin (Module.finrank ℝ E))
      {t : ℝ} (ht : t ∈ D.regular) (y : M) :
      ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (F slots) (t, y) := by
    have hbase (V : Fin 2 → ContMDiffSection I E ∞ (TangentSpace I)) :
        ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
          (fun z : ℝ × M => metricTensorField (G z.1) z.2 (fun j => V j z.2)) (t, y) := by
      simpa only [metricTensorField_apply] using
        hG.pairSmoothAt (D.regular_isOpen.mem_nhds ht) V
    simpa only [F, metricCovDeriv_eq_covDerivOfField] using
      covDerivOfField_eval_contMDiffAt R (fun t => metricTensorField (G t)) hbase q
        (fun j => sec (slots j))
  let d : ℝ × M → ℝ := fun z => Real.sqrt
    (∑ slots : Fin (q + 2) → Fin (Module.finrank ℝ E),
      (deriv (fun r => F slots (r, z.2)) z.1) ^ 2)
  have hd : ContinuousOn d (Icc a b ×ˢ K) := by
    intro z hz
    apply ContinuousWithinAt.sqrt
    apply tendsto_finsetSum
    intro slots _
    exact ((DifferentialGeometry.timeDeriv_smoothAt (m := 0)
      (hF slots (hreg hz.1) z.2) (by simp)).continuousAt.continuousWithinAt).pow 2
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hd
  have hBnonneg : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨interior K, C * max B 0, isOpen_interior, hxK (mem_singleton x),
    mul_nonneg (zero_le_one.trans hC) hBnonneg, ?_⟩
  intro s hs t ht y hy
  have hyK : y ∈ K := interior_subset hy
  have hyV : y ∈ V := (hKVW hyK).1
  have hysec (i : Fin (Module.finrank ℝ E)) : sec i y = frame i y :=
    hWsub (hKVW hyK).2 i
  have hderiv (slots : Fin (q + 2) → Fin (Module.finrank ℝ E))
      (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivAt (fun v => F slots (v, y))
        (deriv (fun v => F slots (v, y)) r) r := by
    have hc : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun v => F slots (v, y)) r :=
      (hF slots (hreg hr) y).comp r (contMDiffAt_id.prodMk contMDiffAt_const)
    exact (contMDiffAt_iff_contDiffAt.mp hc).differentiableAt (by simp) |>.hasDerivAt
  have hdbound (r : ℝ) (hr : r ∈ Icc a b) : d (r, y) ≤ max B 0 :=
    (show d (r, y) ≤ ‖d (r, y)‖ by
      simpa only [Real.norm_eq_abs] using le_abs_self (d (r, y))).trans
        ((hB (r, y) ⟨hr, hyK⟩).trans (le_max_left _ _))
  have hdiff := sqrt_sum_sq_sub_le_of_hasDerivAt
    (fun slots r => F slots (r, y))
    (fun slots r => deriv (fun v => F slots (v, y)) r)
    hderiv hdbound hs ht
  have hn := hnorm (G s) (G t) y hyV (hVbase hyV)
  simp only [component0S_apply, IsLocalFrameOn.toBasisAt_coe] at hn
  have hcomponent (r : ℝ) (slots : Fin (q + 2) → Fin (Module.finrank ℝ E)) :
      metricCovDeriv (G r) R q y (fun j => frame (slots j) y) = F slots (r, y) := by
    dsimp only [F]
    congr 1
    funext j
    exact (hysec (slots j)).symm
  simp only [← show e = trivializationAt E (TangentSpace I) x from rfl,
    ← show frame = e.localFrame basisE from rfl, hcomponent] at hn
  calc
    metricDerivNorm q (G s) (G t) R y ≤
        C * Real.sqrt (∑ slots, (F slots (s, y) - F slots (t, y)) ^ 2) := hn
    _ ≤ C * (max B 0 * |s - t|) :=
      mul_le_mul_of_nonneg_left hdiff (zero_le_one.trans hC)
    _ = (C * max B 0) * |s - t| := (mul_assoc _ _ _).symm

theorem exists_metric_time_lipschitz_constant_on_compact_regular
    {D : RealTimeInterval} (G : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn D G)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) (p : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ≤ p, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ K,
      metricDerivNorm q (G s) (G t) R x ≤ L * |s - t| := by
  classical
  have horder (q : ℕ) : ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ K,
        metricDerivNorm q (G s) (G t) R x ≤ L * |s - t| := by
    choose U L hU hxU hL hlip using
      fun x : M => exists_local_metric_time_lipschitz_on_regular_interval G hG hreg R q x
    obtain ⟨F, _, hcover⟩ := hK.elim_nhds_subcover U
      (fun x _ => (hU x).mem_nhds (hxU x))
    refine ⟨∑ x ∈ F, L x, Finset.sum_nonneg (fun x _ => hL x), ?_⟩
    intro s hs t ht y hy
    obtain ⟨x, hxF, hyU⟩ := mem_iUnion₂.mp (hcover hy)
    exact (hlip x s hs t ht y hyU).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun z _ => hL z) hxF) (abs_nonneg _))
  choose L hL hlip using horder
  refine ⟨∑ q ∈ Finset.range (p + 1), L q,
    Finset.sum_nonneg (fun q _ => hL q), ?_⟩
  intro q hq s hs t ht x hx
  exact (hlip q s hs t ht x hx).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun r _ => hL r) (Finset.mem_range.mpr (by omega)))
    (abs_nonneg _))

end DifferentialGeometry.CheegerGromovCompactness
