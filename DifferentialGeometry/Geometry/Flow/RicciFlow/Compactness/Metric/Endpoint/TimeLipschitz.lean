import DifferentialGeometry.Geometry.Metric.Convergence.Time.CompactBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalMetricTimeControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantContinuity
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open Perelman.CanonicalNeighborhood.FiniteHorn
  (exists_local_metric_time_lipschitz_before_terminal)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private theorem metric_time_lipschitz_on_closed_of_halfOpen
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) (K : Set M) (p : ℕ) (L : ℝ)
    (hlip : ∀ q ≤ p, ∀ s ∈ Ico a b, ∀ t ∈ Ico a b, ∀ x ∈ K,
      metricDerivNorm q (S.base.metric s) (S.base.metric t) R x ≤ L * |s - t|) :
    ∀ q ≤ p, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ K,
      metricDerivNorm q (S.base.metric s) (S.base.metric t) R x ≤ L * |s - t| := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro q hq
  have hterminal (s : ℝ) (x : M) :
      ContinuousWithinAt
        (fun t => metricDerivNorm q (S.base.metric s) (S.base.metric t) R x) (Iic b) b := by
    classical
    obtain ⟨basis, horth⟩ := exists_orthonormal_basis R x
    have hinv := metricInverseInBasis_of_orthonormal R basis horth
    have hnorm (g : SmoothRiemannianMetric I M) :
        metricDerivNorm q (S.base.metric s) g R x = Real.sqrt
          (∑ slots : Fin (q + 2) → Fin (Module.finrank ℝ (TangentSpace I x)),
            (component0S basis (metricCovDeriv (S.base.metric s) R q x) slots -
              component0S basis (metricCovDeriv g R q x) slots) ^ 2) := by
      rw [metricDerivNorm, metricDiffCovDerivAt,
        normSq0S_identity_eq_sum_sq R x (q + 2) basis hinv]
      congr 1
    simp only [hnorm]
    apply ContinuousWithinAt.sqrt
    apply tendsto_finsetSum
    intro slots _
    exact (continuousWithinAt_const.sub
      (solution_metricCovDeriv_component_continuousWithinAt_terminal S hS hab hslab
        hreg R q x basis slots)).pow 2
  have hright (s : ℝ) (hs : s ∈ Ico a b) (x : M) (hx : x ∈ K) :
      metricDerivNorm q (S.base.metric s) (S.base.metric b) R x ≤ L * |s - b| := by
    have hleft := (hterminal s x).mono Iio_subset_Iic_self
    have hbound : Tendsto (fun t : ℝ => L * |s - t|) (𝓝[<] b) (𝓝 (L * |s - b|)) :=
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id).abs).tendsto.mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hleft hbound
    filter_upwards [Ico_mem_nhdsLT hab] with t ht
    exact hlip q hq s hs t ht x hx
  intro s hs t ht x hx
  rcases hs.2.lt_or_eq with hsb | hsb
  · rcases ht.2.lt_or_eq with htb | htb
    · exact hlip q hq s ⟨hs.1, hsb⟩ t ⟨ht.1, htb⟩ x hx
    · subst t
      exact hright s ⟨hs.1, hsb⟩ x hx
  · subst s
    rcases ht.2.lt_or_eq with htb | htb
    · rw [metricDerivNorm_symm, abs_sub_comm]
      exact hright t ⟨ht.1, htb⟩ x hx
    · subst t
      rw [metricDerivNorm_self, sub_self, abs_zero, mul_zero]

theorem exists_metric_time_lipschitz_constant_on_compact_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hregular : Ico a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) (p : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ≤ p, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ K,
      metricDerivNorm q (S.base.metric s) (S.base.metric t) R x ≤ L * |s - t| := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hlocal (x : M) : ∃ (U : Set M) (L : ℝ), IsOpen U ∧ x ∈ U ∧ 0 ≤ L ∧
      ∀ q ≤ p, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ y ∈ U,
        metricDerivNorm q (S.base.metric s) (S.base.metric t) R y ≤ L * |s - t| := by
    obtain ⟨U, c, L, hU, hxU, hUc, hac, hcb, hL, hlip⟩ :=
      exists_local_metric_time_lipschitz_before_terminal S hS hab hslab
        (Ioo_subset_Ico_self.trans hregular) x
    obtain ⟨Cref, hCref, href⟩ :=
      exists_metric_deriv_norm_reference_bound hUc (S.base.metric c) R p
    let Clate := Cref * ∑ r ∈ Finset.range (p + 1), L r
    have hClate : 0 ≤ Clate :=
      mul_nonneg hCref (Finset.sum_nonneg fun r _ => hL r)
    have hlateOpen : ∀ q ≤ p, ∀ s ∈ Ico c b, ∀ t ∈ Ico c b, ∀ y ∈ closure U,
        metricDerivNorm q (S.base.metric s) (S.base.metric t) R y ≤ Clate * |s - t| := by
      intro q hq s hs t ht y hy
      calc
        metricDerivNorm q (S.base.metric s) (S.base.metric t) R y ≤
            Cref * ∑ r ∈ Finset.range (p + 1),
              metricDerivNorm r (S.base.metric s) (S.base.metric t) (S.base.metric c) y :=
          href (S.base.metric s) (S.base.metric t) q hq y hy
        _ ≤ Cref * ∑ r ∈ Finset.range (p + 1), L r * |s - t| :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun r _ => hlip r s hs t ht y hy) hCref
        _ = Clate * |s - t| := by
          rw [← Finset.sum_mul]
          exact (mul_assoc _ _ _).symm
    have hlate := metric_time_lipschitz_on_closed_of_halfOpen S hS hcb
      (fun t ht => hslab ⟨hac.le.trans ht.1, ht.2⟩)
      (fun t ht => hregular ⟨hac.le.trans ht.1.le, ht.2⟩)
      R (closure U) p Clate hlateOpen
    have hearlyReg : Icc a c ⊆ D.regular :=
      fun t ht => hregular ⟨ht.1, ht.2.trans_lt hcb⟩
    obtain ⟨Cearly, hCearly, hearly⟩ := exists_metric_time_lipschitz_constant_on_compact_regular
      (fun t => S.base.metric t) hS.smoothMetric hearlyReg R hUc p
    have hordered (q : ℕ) (hq : q ≤ p) (s : ℝ) (hs : s ∈ Icc a b)
        (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t) (y : M) (hy : y ∈ U) :
        metricDerivNorm q (S.base.metric s) (S.base.metric t) R y ≤
          (Cearly + Clate) * |s - t| := by
      by_cases htc : t ≤ c
      · exact (hearly q hq s ⟨hs.1, hst.trans htc⟩ t ⟨ht.1, htc⟩ y
          (subset_closure hy)).trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
      by_cases hcs : c ≤ s
      · exact (hlate q hq s ⟨hcs, hs.2⟩ t ⟨hcs.trans hst, ht.2⟩ y
          (subset_closure hy)).trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
      have hsc : s < c := lt_of_not_ge hcs
      have hct : c < t := lt_of_not_ge htc
      calc
        metricDerivNorm q (S.base.metric s) (S.base.metric t) R y ≤
            metricDerivNorm q (S.base.metric s) (S.base.metric c) R y +
              metricDerivNorm q (S.base.metric c) (S.base.metric t) R y :=
          metricDerivNorm_triangle q (S.base.metric s) (S.base.metric c) (S.base.metric t) R y
        _ ≤ Cearly * |s - c| + Clate * |c - t| := add_le_add
          (hearly q hq s ⟨hs.1, hsc.le⟩ c ⟨hac.le, le_rfl⟩ y (subset_closure hy))
          (hlate q hq c ⟨le_rfl, hcb.le⟩ t ⟨hct.le, ht.2⟩ y (subset_closure hy))
        _ ≤ (Cearly + Clate) * |s - t| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hsc.le),
            abs_of_nonpos (sub_nonpos.mpr hct.le), abs_of_nonpos (sub_nonpos.mpr hst)]
          nlinarith [mul_nonneg hCearly (sub_nonneg.mpr hct.le),
            mul_nonneg hClate (sub_nonneg.mpr hsc.le)]
    refine ⟨U, Cearly + Clate, hU, hxU, add_nonneg hCearly hClate, ?_⟩
    intro q hq s hs t ht y hy
    rcases le_total s t with hst | hts
    · exact hordered q hq s hs t ht hst y hy
    · have h := hordered q hq t ht s hs hts y hy
      rwa [metricDerivNorm_symm, abs_sub_comm] at h
  choose U L hU hxU hL hlip using hlocal
  obtain ⟨F, _, hcover⟩ := hK.elim_nhds_subcover U
    (fun x _ => (hU x).mem_nhds (hxU x))
  refine ⟨∑ x ∈ F, L x, Finset.sum_nonneg (fun x _ => hL x), ?_⟩
  intro q hq s hs t ht y hy
  obtain ⟨x, hxF, hyU⟩ := mem_iUnion₂.mp (hcover hy)
  exact (hlip x q hq s hs t ht y hyU).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun z _ => hL z) hxF) (abs_nonneg _))

end DifferentialGeometry.PDE.RicciFlow
