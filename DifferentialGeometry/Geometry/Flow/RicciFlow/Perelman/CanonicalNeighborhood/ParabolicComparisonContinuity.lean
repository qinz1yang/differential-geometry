import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessLocalTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessMovingNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling

set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance parabolicContinuityC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem eventually_rescaledMetric_comparison_on_compact
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D) (hS : IsSolutionOn S)
    {a t depth Q : ℝ} (hdepth : 0 < depth) (hQ : 0 < Q)
    (hbuffer : a < t - depth / Q)
    (hslab : Icc a t ⊆ D.carrier) (hreg : Ioo a t ⊆ D.regular)
    {K : Set M} (hK : IsCompact K) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ c in 𝓝 Q, ∃ hc : 0 < c, Nonempty (MetricComparisonOn
      (rescaledMetric S t Q hQ) (rescaledMetric S t c hc)
      (id : M → M) K (Icc (-depth) 0) order eps) := by
  classical
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let start := (a + (t - depth / Q)) / 2
  have has : a < start := by dsimp only [start]; linarith
  have hstart : start < t - depth / Q := by dsimp only [start]; linarith
  have hst : start < t := lt_trans hstart (sub_lt_self _ (div_pos hdepth hQ))
  have htime (c : ℝ) (hc : 0 < c) (hsc : start < t - depth / c) :
      MapsTo (parabolicTime t c) (Icc (-depth) 0) (Icc start t) := by
    intro s hs
    change start ≤ t + s / c ∧ t + s / c ≤ t
    have hlow := (div_le_div_iff_of_pos_right hc).mpr hs.1
    have hupp := div_nonpos_of_nonpos_of_nonneg hs.2 hc.le
    rw [neg_div] at hlow
    constructor <;> linarith
  have hmapQ := htime Q hQ hstart
  obtain ⟨B, hB₀, hB⟩ := exists_closedWindow_metric_time_fields S hS has hst hslab hreg
  let U : TopologicalSpace.Opens M := ⊤
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let F := PartialDiffeomorph.refl (I := I3) M
  have hzero (s : ℝ) (y : M) (_hy : y ∈ U) (v : Fin 2 → TangentSpace I3 y) :
      B 0 s y v = (S.base.metric s).inner (F y)
        (mfderiv I3 I3 F y (v 0)) (mfderiv I3 I3 F y (v 1)) := by
    change B 0 s y v = (S.base.metric s).inner y
      (mfderiv I3 I3 (id : M → M) y (v 0))
      (mfderiv I3 I3 (id : M → M) y (v 1))
    simp only [hB₀, metricTensorField_apply, mfderiv_id, ContinuousLinearMap.id_apply]
  have hBreg := partial_pullback_time_tower_contDiffOn_closed S hS has hst hslab hreg
    F U (Set.subset_univ _) B hzero (fun q s hs y _hy => (hB q s hs y).2)
  have hvalid : ∀ᶠ c in 𝓝 Q, 0 < c ∧ start < t - depth / c := by
    have hcont : ContinuousAt (fun c : ℝ => t - depth / c) Q :=
      continuousAt_const.sub (continuousAt_const.div continuousAt_id hQ.ne')
    filter_upwards [eventually_gt_nhds hQ, hcont.eventually (eventually_gt_nhds hstart)] with c hc hs
    exact ⟨hc, hs⟩
  let Good (c : ℝ) := ∃ hc : 0 < c, Nonempty (MetricComparisonOn
    (rescaledMetric S t Q hQ) (rescaledMetric S t c hc)
    (id : M → M) K (Icc (-depth) 0) order eps)
  change ∀ᶠ c in 𝓝 Q, Good c
  by_contra hnot
  have hfreq : ∃ᶠ c in 𝓝 Q, ¬ Good c := by
    simpa only [Filter.Frequently, not_not] using hnot
  obtain ⟨c, hclim, hbad⟩ := Filter.exists_seq_forall_of_frequently (hfreq.and_eventually hvalid)
  have hc (n : ℕ) : 0 < c n := (hbad n).2.1
  have hmap (n : ℕ) := htime (c n) (hc n) (hbad n).2.2
  have hpair (i j : ℕ) : ∀ᶠ n in atTop, ∀ s ∈ Icc (-depth) 0, ∀ y ∈ K,
      tensor02CovDerivNormWith i
        (rescaledTensorTimeTower B t (c n) j s - rescaledTensorTimeTower B t Q j s)
        (rescaledMetric S t Q hQ s) (rescaledMetric S t Q hQ s) y < eps := by
    let f (n : ℕ) (s : ℝ) (y : M) := tensor02CovDerivNormWith i
      (rescaledTensorTimeTower B t (c n) j s - rescaledTensorTimeTower B t Q j s)
      (rescaledMetric S t Q hQ s) (rescaledMetric S t Q hQ s) y
    change ∀ᶠ n in atTop, ∀ s ∈ Icc (-depth) 0, ∀ y ∈ K, f n s y < eps
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop, ¬ (∀ s ∈ Icc (-depth) 0, ∀ y ∈ K, f n s y < eps) := by
      simpa only [Filter.Frequently, not_not] using hnot
    obtain ⟨ns, hns, hbad'⟩ := Filter.exists_seq_forall_of_frequently hfreq
    have hbad'' (n : ℕ) : ∃ s ∈ Icc (-depth) 0, ∃ y ∈ K, eps ≤ f (ns n) s y := by
      have hh := hbad' n
      push Not at hh
      exact hh
    choose s hs y hy hbadnorm using hbad''
    obtain ⟨w, hw, phi, hphi, hwlim⟩ := (isCompact_Icc.prod hK).tendsto_subseq
      (x := fun n => (s n, y n)) (fun n => ⟨hs n, hy n⟩)
    let pick := ns ∘ phi
    have hpick : Tendsto pick atTop atTop := hns.comp hphi.tendsto_atTop
    have hslim : Tendsto (fun n => s (phi n)) atTop (𝓝 w.1) :=
      (continuous_fst.tendsto w).comp hwlim
    have hylim : Tendsto (fun n => y (phi n)) atTop (𝓝 w.2) :=
      (continuous_snd.tendsto w).comp hwlim
    have htlim : Tendsto (fun n => t + s (phi n) / c (pick n)) atTop (𝓝 (t + w.1 / Q)) :=
      tendsto_const_nhds.add (hslim.div (hclim.comp hpick) hQ.ne')
    have hulim : Tendsto (fun n => t + s (phi n) / Q) atTop (𝓝 (t + w.1 / Q)) :=
      tendsto_const_nhds.add (hslim.div_const Q)
    have halim : Tendsto (fun n => c (pick n) * (c (pick n))⁻¹ ^ j) atTop
        (𝓝 (Q * Q⁻¹ ^ j)) :=
      (hclim.comp hpick).mul (((hclim.comp hpick).inv₀ hQ.ne').pow j)
    obtain ⟨V₁, hV₁, hp₁, ht₁, hBc⟩ := hBreg (⟨w.2, mem_univ _⟩ : U)
    obtain ⟨V₂, hV₂, hp₂, _ht₂, hgc⟩ :=
      solution_chartGram_contDiffOn_closed S hS has hst hslab hreg w.2
    have hnorm := weighted_error_covariant_norm_tendsto_at_point
      S.base.metric (B j) (B j) w.2 (hV₁.inter hV₂) ⟨hp₁, hp₂⟩
      (fun z hz => ht₁ hz.1)
      (fun r s => (hgc r s).mono (Set.prod_mono Subset.rfl (fun z hz => hz.2)))
      (fun slots => (hBc j slots).mono (Set.prod_mono Subset.rfl (fun z hz => hz.1)))
      (fun slots => (hBc j slots).mono (Set.prod_mono Subset.rfl (fun z hz => hz.1)))
      (fun n => t + s (phi n) / c (pick n)) (fun n => t + s (phi n) / Q)
      (fun n => hmap (pick n) (hs (phi n))) (fun n => hmapQ (hs (phi n)))
      (hmapQ hw.1) (hmapQ hw.1) htlim hulim
      (fun _ => Q) (fun n => c (pick n) * (c (pick n))⁻¹ ^ j) (fun _ => Q * Q⁻¹ ^ j)
      (fun _ => hQ) hQ tendsto_const_nhds halim tendsto_const_nhds
      (fun n => y (phi n)) hylim i
    have hzeroNorm (g : SmoothRiemannianMetric I3 M) (p : M) :
        tensor02CovDerivNormWith i 0 g g p = 0 := by
      have hh := tensor02CovDerivNormWith_smul g g 0 (B j t) i p
      simpa only [zero_smul, abs_zero, zero_mul] using hh
    simp only [sub_self, hzeroNorm] at hnorm
    have hge : eps ≤ 0 := ge_of_tendsto hnorm
      (Filter.Eventually.of_forall (fun n => hbadnorm (phi n)))
    exact (not_le_of_gt heps) hge
  have hfinite : {ij : ℕ × ℕ | ij.1 + 2 * ij.2 ≤ order}.Finite := by
    apply ((Finset.range (order + 1)).product (Finset.range (order + 1))).finite_toSet.subset
    intro ij hij
    change ij.1 + 2 * ij.2 ≤ order at hij
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hall := (Filter.eventually_all_finite hfinite).mpr (fun ij _hij => hpair ij.1 ij.2)
  obtain ⟨n, hn⟩ := hall.exists
  apply (hbad n).1
  refine ⟨hc n, ⟨metricComparisonOnOfGenuineTimeTowers
    (rescaledMetric S t Q hQ) (rescaledMetric S t (c n) (hc n))
    (id : M → M) K (Icc (-depth) 0) (uniqueDiffOn_Icc (by linarith)) order eps
    (rescaledTensorTimeTower B t (c n)) (rescaledTensorTimeTower B t Q) ?_ ?_ ?_ ?_ ?_⟩⟩
  · intro s y _hy v
    simp only [rescaledTensorTimeTower, pow_zero, mul_one, hB₀,
      ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
      metricTensorField_apply, rescaledMetric, scaleMetric_inner, mfderiv_id,
      ContinuousLinearMap.id_apply, id_eq]
  · intro s y v
    simp only [rescaledTensorTimeTower, pow_zero, mul_one, hB₀,
      ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
      metricTensorField_apply, rescaledMetric, scaleMetric_inner]
  · intro q s hs y _hy
    exact hasDerivWithinAt_rescaledTensorTimeTower B t (c n) (hmap n)
      (fun q s hs y => (hB q s hs y).2) q s hs y
  · intro q s hs y _hy
    exact hasDerivWithinAt_rescaledTensorTimeTower B t Q hmapQ
      (fun q s hs y => (hB q s hs y).2) q s hs y
  · intro i j hij s hs y hy
    exact (hn (i, j) hij s hs y hy).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
