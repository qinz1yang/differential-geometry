import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonDistanceConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalInnerRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalMetricSandwich
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.VolumeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeConsequences

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem tendsto_original_base_scalar_of_backward_comparisons
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval)
    (hscalar : Sm.scalar 0 P.basepoint = 1) (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric
        (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
        (Phi.map i) K (Icc (-1 : ℝ) 0) order delta)) :
    Tendsto (fun i => (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))) atTop (𝓝 1) := by
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace ThreeSpace P.M
  let _ : RegularSpace P.M := inferInstance
  obtain ⟨U, hUo, hpU, _hUuniv, hUc⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_singleton (x := P.basepoint))
      isOpen_univ (subset_univ _)
  let O : TopologicalSpace.Opens P.M := ⟨U, hUo⟩
  obtain ⟨N, hN⟩ := Phi.source_subset hUc
  have hsource : ∀ᶠ i in atTop, (O : Set P.M) ⊆ (Phi.partialDiffeomorph i).source :=
    (eventually_ge_atTop N).mono fun i hi => subset_closure.trans (hN i hi)
  let g i s := scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
    (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s))
  have hcmp : ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric (g i) (Phi.partialDiffeomorph i) O
        (Icc (-1 : ℝ) 0) 2 delta) := by
    intro delta hdelta
    filter_upwards [hcompare (closure U) hUc 2 delta hdelta] with i hi
    exact ⟨hi.some.mono subset_closure le_rfl le_rfl⟩
  have hlim := tendsto_metricScalarAt_of_comparisons Sm.base.metric g
    (fun i => Phi.partialDiffeomorph i) O (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 0)
    le_rfl (hpU (mem_singleton P.basepoint)) hsource hcmp
  have heq (i : ℕ) : metricScalarAt (g i 0) ((Phi.partialDiffeomorph i) P.basepoint) =
      (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i)) := by
    dsimp only [g]
    rw [mul_zero, add_zero, DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric, inv_inv, Phi.basepoint_map]
    rfl
  change metricScalarAt (Sm.base.metric 0) P.basepoint = 1 at hscalar
  simpa only [heq, hscalar] using hlim

theorem eventually_original_image_depth_of_backward_comparisons
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval)
    [PreconnectedSpace P.M] (hcomplete : RiemannianMetricComplete (Sm.base.metric 0))
    (hscalar : Sm.scalar 0 P.basepoint = 1) (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric
        (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
        (Phi.map i) K (Icc (-1 : ℝ) 0) order delta))
    {V : Set P.M} (hV : IsCompact V)
    (hdepth : ∀ y ∈ V, 40000 ≤ metricDistance (Sm.base.metric 0) P.basepoint y) :
    ∀ᶠ i in atTop, ∀ y ∈ Phi.map i '' V,
      10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
        metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y := by
  let g i s := scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
    (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s))
  have hcmp (K : Set P.M) (hK : IsCompact K) : ∀ᶠ i in atTop,
      K ⊆ (Phi.partialDiffeomorph i).source ∧
      Nonempty (MetricComparisonOn Sm.base.metric (g i) (Phi.partialDiffeomorph i) K
        (Icc (-1 : ℝ) 0) 0 (1 / 4)) := by
    obtain ⟨N, hN⟩ := Phi.source_subset hK
    filter_upwards [eventually_ge_atTop N, hcompare K hK 0 (1 / 4) (by norm_num)] with i hi hci
    exact ⟨hN i hi, hci⟩
  have hdist := eventually_metricDistance_bounds_on_compact_of_comparisons
    Sm.base.metric g (fun i => Phi.partialDiffeomorph i)
    (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 0) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hcomplete hcmp (hV.insert P.basepoint)
  have hlim := tendsto_original_base_scalar_of_backward_comparisons F tau htau q Phi Sm
    hscalar b hsigma hcompare
  have hhalf : ∀ᶠ i in atTop, (1 / 4 : ℝ) ≤ (tau (rho i) + b) *
      F.S.scalar (-tau (rho i)) (q (rho i)) :=
    ((tendsto_order.1 hlim).1 (1 / 4) (by norm_num)).mono fun _ hi => hi.le
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - (1 / 4 : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  filter_upwards [hdist, hhalf] with i hdi hqi
  rintro y ⟨z, hz, rfl⟩
  have hq : 0 < F.S.scalar (-tau (rho i)) (q (rho i)) :=
    ancientKappa_scalar_pos F hF (neg_nonpos.mpr (htau (rho i)).le) _
  have hlo := (hdi P.basepoint (mem_insert _ _) z (mem_insert_of_mem _ hz)).1
  have hbase : (Phi.partialDiffeomorph i) P.basepoint = q (rho i) := Phi.basepoint_map i
  have hnorm : 20000 ≤ metricDistance (g i 0) (q (rho i)) (Phi.map i z) := by
    rw [← hbase]
    exact (by linarith [hdepth z hz] : (20000 : ℝ) ≤ (1 / 2 : ℝ) * metricDistance (Sm.base.metric 0) P.basepoint z).trans
      ((mul_le_mul_of_nonneg_right hroot ENNReal.toReal_nonneg).trans hlo)
  have hscale : metricDistance (g i 0) (q (rho i)) (Phi.map i z) =
      (Real.sqrt (tau (rho i) + b))⁻¹ *
        metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) (Phi.map i z) := by
    dsimp only [g]
    rw [mul_zero, add_zero, metricDistance, edistOf_scale, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sqrt_inv]
    rfl
  have hnormalRoot : (1 / 2 : ℝ) ≤ Real.sqrt (tau (rho i) + b) *
      Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) := by
    rw [← Real.sqrt_mul (hsigma i).le]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  rw [hscale] at hnorm
  have hnorm' : 20000 * Real.sqrt (tau (rho i) + b) ≤
      metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) (Phi.map i z) := by
    have hh := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg (tau (rho i) + b))
    rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hsigma i)).ne', one_mul] at hh
    simpa only [mul_comm] using hh
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hq)).mpr
  calc
    (10000 : ℝ) = 20000 * (1 / 2 : ℝ) := by norm_num
    _ ≤ 20000 * (Real.sqrt (tau (rho i) + b) * Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i)))) :=
      mul_le_mul_of_nonneg_left hnormalRoot (by norm_num)
    _ = (20000 * Real.sqrt (tau (rho i) + b)) * Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm' (Real.sqrt_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem CanonicalWitness.eventually_image_ball_sandwich_of_backward_comparisons
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval)
    (hcomplete : RiemannianMetricComplete (Sm.base.metric 0))
    (hscalar : Sm.scalar 0 P.basepoint = 1) (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric
        (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
        (Phi.map i) K (Icc (-1 : ℝ) 0) order delta))
    {eps C1 C2 : ℝ} (K : CanonicalWitness Sm eps C1 C2 P.basepoint 0) :
    ∃ r : ℝ, 1 < r ∧ r ≤ max C1 2 ∧ ∀ᶠ i in atTop,
      (Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))))⁻¹ ≤ Real.sqrt (tau (rho i) + b) * r ∧
      Real.sqrt (tau (rho i) + b) * r ≤ (2 * max C1 2) / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ∧
      riemannianBallOf (F.S.base.metric (-tau (rho i))) (q (rho i)) (Real.sqrt (tau (rho i) + b) * r) ⊆
        Phi.map i '' K.domain.carrier ∧
      Phi.map i '' K.domain.carrier ⊆ riemannianBallOf (F.S.base.metric (-tau (rho i))) (q (rho i))
        (2 * (Real.sqrt (tau (rho i) + b) * r)) := by
  obtain ⟨a, c, margin, ha, haC, hm, hreserve, hinner, houter⟩ := K.exists_normalized_radial_reserve hscalar
  let eta := min (1 / 8 : ℝ) (margin / 8)
  have heta : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta8 : eta ≤ 1 / 8 := min_le_left _ _
  have hetam : eta ≤ margin / 8 := min_le_right _ _
  have ha0 : 0 < a := by linarith
  have hminus : 0 < 1 - eta := by linarith
  have hplus : 0 < 1 + eta := by linarith
  have hAcomp : 1 ≤ (1 - eta) * ((1 - eta)⁻¹) ^ 2 := by
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hminus.ne', one_mul]
    exact (one_le_inv₀ hminus).mpr (by linarith)
  have hLcomp : 1 + eta ≤ (1 + eta) ^ 2 := by nlinarith
  have htrans : (1 + eta) * c < 2 * (a / (1 - eta)⁻¹) := by
    have hratio : (1 + eta) * (2 - margin) < 2 * (1 - eta) := by
      nlinarith [mul_pos heta hm]
    rw [div_inv_eq_mul]
    calc
      _ < (1 + eta) * ((2 - margin) * a) := mul_lt_mul_of_pos_left hreserve hplus
      _ = ((1 + eta) * (2 - margin)) * a := by ring
      _ < (2 * (1 - eta)) * a := mul_lt_mul_of_pos_right hratio ha0
      _ = _ := by ring
  let r := a * (1 - eta)
  have hr : 1 < r := by dsimp only [r]; nlinarith
  have hrC : r ≤ max C1 2 :=
    (mul_le_of_le_one_right ha0.le (by linarith)).trans haC.le
  let g i s := scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
    (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s))
  have hlim := tendsto_original_base_scalar_of_backward_comparisons F tau htau q Phi Sm
    hscalar b hsigma hcompare
  have hrootlim : Tendsto (fun i => Real.sqrt ((tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))))
      atTop (𝓝 1) := by simpa only [Real.sqrt_one] using hlim.sqrt
  have hlow : ∀ᶠ i in atTop, 1 ≤ r * Real.sqrt ((tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))) := by
    have hh : Tendsto (fun i => r * Real.sqrt ((tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))))
        atTop (𝓝 r) := by simpa only [mul_one] using hrootlim.const_mul r
    exact ((tendsto_order.1 hh).1 1 hr).mono fun _ hi => hi.le
  have hup : ∀ᶠ i in atTop, Real.sqrt ((tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))) ≤ 2 :=
    ((tendsto_order.1 hrootlim).2 2 (by norm_num)).mono fun _ hi => hi.le
  have hcompact := hcomplete.closedEBall_isCompact P.basepoint c
  obtain ⟨N, hN⟩ := Phi.source_subset hcompact
  refine ⟨r, hr, hrC, ?_⟩
  filter_upwards [hlow, hup, eventually_ge_atTop N, hcompare _ hcompact 0 eta heta]
    with i hli hui hi hci
  obtain ⟨cmp⟩ := hci
  have hball : riemannianBallOf (Sm.base.metric 0) P.basepoint c ⊆
      riemannianClosedBallOf (Sm.base.metric 0) P.basepoint c := fun y hy =>
        (show riemannianEDistOf (Sm.base.metric 0) P.basepoint y < ENNReal.ofReal c from hy).le
  obtain ⟨_margin, _hmargin, _hmarginTrans, hin, hout⟩ := cmp.map_strict_ball_sandwich
    (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 0) K.domain P.basepoint
    ha0 (inv_pos.mpr hminus) hplus hinner houter (hball.trans (hN i hi)) hball htrans hAcomp hLcomp
  have hbase : (Phi.partialDiffeomorph i) P.basepoint = q (rho i) := Phi.basepoint_map i
  have hin' : riemannianBallOf (g i 0) (q (rho i)) r ⊆ Phi.map i '' K.domain.carrier := by
    change riemannianBallOf (g i 0) ((Phi.partialDiffeomorph i) P.basepoint) (a / (1 - eta)⁻¹) ⊆ _ at hin
    rw [hbase, div_inv_eq_mul] at hin
    exact hin
  have hout' : Phi.map i '' K.domain.carrier ⊆ riemannianBallOf (g i 0) (q (rho i)) (2 * r) := by
    change Phi.map i '' K.domain.carrier ⊆ riemannianBallOf (g i 0)
      ((Phi.partialDiffeomorph i) P.basepoint) ((1 + eta) * c) at hout
    rw [hbase] at hout
    exact hout.trans (riemannianBallOf_mono _ _ (by simpa only [div_inv_eq_mul] using htrans.le))
  have hscale (z : ℝ) : riemannianBallOf (g i 0) (q (rho i)) z =
      riemannianBallOf (F.S.base.metric (-tau (rho i))) (q (rho i))
        (Real.sqrt (tau (rho i) + b) * z) := by
    have heq := DifferentialGeometry.riemannianBallOf_scaleMetric (tau (rho i) + b)⁻¹
      (inv_pos.mpr (hsigma i)) (F.S.base.metric (-tau (rho i))) (q (rho i))
        (Real.sqrt (tau (rho i) + b) * z)
    rw [Real.sqrt_inv, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hsigma i)).ne', one_mul] at heq
    simpa only [g, mul_zero, add_zero] using heq
  have hQ : 0 < F.S.scalar (-tau (rho i)) (q (rho i)) :=
    ancientKappa_scalar_pos F hF (neg_nonpos.mpr (htau (rho i)).le) _
  rw [Real.sqrt_mul (hsigma i).le] at hli hui
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← one_div]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr
    nlinarith only [hli]
  · apply (le_div_iff₀ (Real.sqrt_pos.mpr hQ)).mpr
    have hh := mul_le_mul_of_nonneg_left hui (zero_lt_one.trans hr).le
    have hC := mul_le_mul_of_nonneg_left hrC (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hh, hC]
  · rwa [hscale] at hin'
  · rw [hscale] at hout'
    simpa only [mul_left_comm, mul_assoc] using hout'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem CanonicalWitness.eventually_image_scalar_bounds_of_backward_comparisons
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval)
    (hscalar : Sm.scalar 0 P.basepoint = 1) (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric
        (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
        (Phi.map i) K (Icc (-1 : ℝ) 0) order delta))
    {eps C1 C2 : ℝ} (K : CanonicalWitness Sm eps C1 C2 P.basepoint 0) :
    ∀ᶠ i in atTop, ∀ y ∈ K.domain.carrier,
      (4 * C2)⁻¹ * F.S.scalar (-tau (rho i)) (q (rho i)) ≤ F.S.scalar (-tau (rho i)) (Phi.map i y) ∧
      F.S.scalar (-tau (rho i)) (Phi.map i y) ≤ (4 * C2) * F.S.scalar (-tau (rho i)) (q (rho i)) := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  let E := 486 * C2 * (1 + 9 * C2)
  have hE : 0 < E := by dsimp only [E]; positivity
  let eta := min (1 / 4 : ℝ) E⁻¹
  have heta : 0 < eta := lt_min (by norm_num) (inv_pos.mpr hE)
  have heta4 : eta ≤ 1 / 4 := min_le_left _ _
  have hsmall : 486 * C2 * (1 + 9 * C2) * eta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 / 4 : ℝ) E⁻¹) hE.le
    rwa [mul_inv_cancel₀ hE.ne'] at hh
  have herr : 243 * (1 + 9 * C2) * eta ≤ (2 * C2)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * C2)).mpr
    nlinarith
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace ThreeSpace P.M
  let _ : RegularSpace P.M := inferInstance
  obtain ⟨U, hUopen, hKU, _, hUc⟩ :=
    exists_open_between_and_isCompact_closure K.domain.compact isOpen_univ (subset_univ _)
  let U' : TopologicalSpace.Opens P.M := ⟨U, hUopen⟩
  obtain ⟨N, hN⟩ := Phi.source_subset hUc
  let g i s := scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
    (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s))
  have hlim := tendsto_original_base_scalar_of_backward_comparisons F tau htau q Phi Sm
    hscalar b hsigma hcompare
  have hlow : ∀ᶠ i in atTop, (1 / 2 : ℝ) ≤ (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i)) :=
    ((tendsto_order.1 hlim).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have hup : ∀ᶠ i in atTop, (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i)) ≤ 2 :=
    ((tendsto_order.1 hlim).2 2 (by norm_num)).mono fun _ hi => hi.le
  filter_upwards [hlow, hup, eventually_ge_atTop N, hcompare _ hUc 2 eta heta] with i hli hui hi hci
  obtain ⟨cmp⟩ := hci
  let _ : IsManifold I3 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  intro y hy
  have hrm : normSq0S (Sm.base.metric 0) y 4 (metricRm04At (Sm.base.metric 0) y) ≤ C2 ^ 2 := by
    have hh := K.rm_bound y hy
    rw [hscalar, mul_one] at hh
    exact le_sq_of_sqrt_le (normSq0S_nonneg _ _ _ _) hh
  have hric := ricciSq_le_rm04 (Sm.base.metric 0) (Sm.base.metric 0) y
  change normSq0S (Sm.base.metric 0) y 2 (metricRicciAt (Sm.base.metric 0) y) ≤
    (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 *
      normSq0S (Sm.base.metric 0) y 4 (metricRm04At (Sm.base.metric 0) y) at hric
  have hricnorm : Real.sqrt (normSq0S (Sm.base.metric 0) y 2
      (metricRicciAt (Sm.base.metric 0) y)) ≤ 9 * C2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace]] at hric
    norm_num only at hric
    nlinarith
  have hRic (v w : TangentSpace I3 y) : |ricciTensor (Sm.base.metric 0) y v w| ≤
      (9 * C2) * Real.sqrt ((Sm.base.metric 0).inner y v v) *
        Real.sqrt ((Sm.base.metric 0).inner y w w) := by
    have hh := abs_apply_le_norm0S (Sm.base.metric 0) y 2
      (metricRicciAt (Sm.base.metric 0) y) (vec2 v w)
    rw [metricRicciAt_apply_eq_ricciTensor] at hh
    have hh' : |ricciTensor (Sm.base.metric 0) y v w| ≤
        Real.sqrt (normSq0S (Sm.base.metric 0) y 2 (metricRicciAt (Sm.base.metric 0) y)) *
          Real.sqrt ((Sm.base.metric 0).inner y v v) *
          Real.sqrt ((Sm.base.metric 0).inner y w w) := by
      simpa [vec2, Fin.prod_univ_two, mul_assoc] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hricnorm (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hdiff := MetricComparisonOn.scalar_sub_le_of_ricci_bound
    (N := P.M) (M := F.M) (h := Sm.base.metric) (g := g i) (F := Phi.partialDiffeomorph i)
    cmp U' (subset_closure.trans (hN i hi))
    subset_closure (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num) heta.le
    (by linarith) le_rfl (hKU hy) hRic
  have herror : |metricScalarAt (g i 0) (Phi.map i y) - Sm.scalar 0 y| ≤ (2 * C2)⁻¹ := by
    apply hdiff.trans
    have hh := scalarComparisonC_le (n := 3) heta.le heta4 (by positivity : 0 ≤ 9 * C2)
    norm_num only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, Nat.cast_add] at hh
    exact hh.trans (by nlinarith [herr])
  have hnorm : metricScalarAt (g i 0) (Phi.map i y) =
      (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (Phi.map i y) := by
    dsimp only [g]
    rw [mul_zero, add_zero, DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric, inv_inv]
    rfl
  rw [hnorm] at herror
  have hmod := K.scalar_bounds y hy
  rw [hscalar, mul_one, mul_one] at hmod
  have hinv : C2⁻¹ = 2 * (2 * C2)⁻¹ := by field_simp
  have hbound : (2 * C2)⁻¹ ≤ C2 := by
    have hh := inv_le_one_of_one_le₀ (by linarith [K.one_le_comparison_constant] : 1 ≤ 2 * C2)
    exact hh.trans K.one_le_comparison_constant
  have habs := abs_le.mp herror
  have hlo : (2 * C2)⁻¹ ≤ (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (Phi.map i y) := by
    rw [hinv] at hmod
    linarith
  have hhi : (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (Phi.map i y) ≤ 2 * C2 := by linarith
  have heq : (2 * C2)⁻¹ = 2 * (4 * C2)⁻¹ := by field_simp; ring
  have hn := inv_nonneg.mpr (show 0 ≤ 4 * C2 by positivity)
  constructor
  · apply (mul_le_mul_iff_right₀ (hsigma i)).mp
    have hh := mul_le_mul_of_nonneg_left hui hn
    rw [heq] at hlo
    nlinarith only [hh, hlo]
  · apply (mul_le_mul_iff_right₀ (hsigma i)).mp
    have hh := mul_le_mul_of_nonneg_left hli (show 0 ≤ 4 * C2 by positivity)
    nlinarith only [hh, hhi]

theorem CanonicalWitness.eventually_image_volume_lower_bound_of_backward_comparisons
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval)
    (hscalar : Sm.scalar 0 P.basepoint = 1) (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric
        (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
        (Phi.map i) K (Icc (-1 : ℝ) 0) order delta))
    {eps C1 C2 : ℝ} (K : CanonicalWitness Sm eps C1 C2 P.basepoint 0)
    (hv : K.alternative.requiresVolume) :
    ∀ᶠ i in atTop,
      ENNReal.ofReal ((16 * C2)⁻¹ / (F.S.scalar (-tau (rho i)) (q (rho i)) *
        Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))))) ≤
      riemannianVolumeMeasure I3 F.M (F.S.base.metric (-tau (rho i))) (Phi.map i '' K.domain.carrier) := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace ThreeSpace P.M
  let _ : RegularSpace P.M := inferInstance
  obtain ⟨U, hUopen, hKU, _, hUc⟩ :=
    exists_open_between_and_isCompact_closure K.domain.compact isOpen_univ (subset_univ _)
  obtain ⟨N, hN⟩ := Phi.source_subset hUc
  have hlim := tendsto_original_base_scalar_of_backward_comparisons F tau htau q Phi Sm
    hscalar b hsigma hcompare
  have hlow : ∀ᶠ i in atTop, (1 / 2 : ℝ) ≤ (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i)) :=
    ((tendsto_order.1 hlim).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have hmodel : ENNReal.ofReal (C2⁻¹ / ((1 : ℝ) * Real.sqrt 1)) ≤
      riemannianVolumeMeasure I3 P.M (Sm.base.metric 0) K.domain.carrier := by
    simpa only [hscalar] using K.volume hv
  filter_upwards [hlow, eventually_ge_atTop N, hcompare _ hUc 0 (1 / 2) (by norm_num)] with i hli hi hci
  obtain ⟨cmp⟩ := hci
  have cmp' : MetricComparisonOn (fun _ => Sm.base.metric 0)
      (fun _ => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
        (F.S.base.metric (-tau (rho i))))
      (Phi.map i) (closure U) ({0} : Set ℝ) 0 (1 / 2) := by
    simpa only [mul_zero, add_zero] using cmp.freezeTime
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) ({0} : Set ℝ)
  have hge := volume_reserve_image_of_scaled_comparison (Phi.partialDiffeomorph i)
    (inv_pos.mpr (hsigma i)) cmp' (show (0 : ℝ) ∈ ({0} : Set ℝ) from rfl)
    (by norm_num) (by norm_num) hUopen subset_closure (subset_closure.trans (hN i hi))
    K.domain.compact hKU hmodel
  have hroot : (1 / 4 : ℝ) ≤ Real.sqrt ((1 - 1 / 2 : ℝ) ^ 3) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hconst : (4 * C2)⁻¹ ≤
      (C2 * ((1 : ℝ) * Real.sqrt 1) / Real.sqrt ((1 - 1 / 2 : ℝ) ^ 3))⁻¹ := by
    simp only [Real.sqrt_one, mul_one]
    rw [inv_div, div_eq_mul_inv, mul_inv]
    simpa only [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num] using
      mul_le_mul_of_nonneg_right hroot (inv_nonneg.mpr hC2.le)
  have hge' : ENNReal.ofReal ((4 * C2)⁻¹ /
      ((tau (rho i) + b)⁻¹ * Real.sqrt (tau (rho i) + b)⁻¹)) ≤
      riemannianVolumeMeasure I3 F.M (F.S.base.metric (-tau (rho i))) (Phi.map i '' K.domain.carrier) :=
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hconst
      (mul_nonneg (inv_pos.mpr (hsigma i)).le (Real.sqrt_nonneg _)))).trans hge
  have hQ : 0 < F.S.scalar (-tau (rho i)) (q (rho i)) := by nlinarith [hsigma i]
  have hsig : (tau (rho i) + b)⁻¹ ≤ 2 * F.S.scalar (-tau (rho i)) (q (rho i)) := by
    rw [← one_div]
    apply (div_le_iff₀ (hsigma i)).mpr
    nlinarith only [hli]
  have hsqrt : Real.sqrt (tau (rho i) + b)⁻¹ ≤ 2 * Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hQ.le]
    nlinarith only [hsig, hQ]
  have hdenom : (tau (rho i) + b)⁻¹ * Real.sqrt (tau (rho i) + b)⁻¹ ≤
      4 * (F.S.scalar (-tau (rho i)) (q (rho i)) * Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i)))) := by
    have hh := mul_le_mul hsig hsqrt (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * F.S.scalar (-tau (rho i)) (q (rho i)))
    nlinarith only [hh]
  have hbound : (16 * C2)⁻¹ / (F.S.scalar (-tau (rho i)) (q (rho i)) *
      Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i)))) ≤
      (4 * C2)⁻¹ / ((tau (rho i) + b)⁻¹ * Real.sqrt (tau (rho i) + b)⁻¹) := by
    have hQden : 0 < F.S.scalar (-tau (rho i)) (q (rho i)) *
        Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) := by positivity
    have hsden : 0 < (tau (rho i) + b)⁻¹ * Real.sqrt (tau (rho i) + b)⁻¹ :=
      mul_pos (inv_pos.mpr (hsigma i)) (Real.sqrt_pos.mpr (inv_pos.mpr (hsigma i)))
    apply (div_le_div_iff₀ hQden hsden).mpr
    have hh := mul_le_mul_of_nonneg_left hdenom (show 0 ≤ (16 * C2)⁻¹ by positivity)
    have hconst' : (4 * C2)⁻¹ = 4 * (16 * C2)⁻¹ := by field_simp; ring
    rw [hconst']
    nlinarith only [hh]
  exact (ENNReal.ofReal_le_ofReal hbound).trans hge'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem CanonicalWitness.exists_eventually_image_cap_witness_of_backward_comparisons
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval)
    (hcomplete : RiemannianMetricComplete (Sm.base.metric 0))
    (hscalar : Sm.scalar 0 P.basepoint = 1) (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric
        (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
        (Phi.map i) K (Icc (-1 : ℝ) 0) order delta))
    {eps C1 C2 : ℝ} (K : CanonicalWitness Sm eps C1 C2 P.basepoint 0)
    (hv : K.alternative.requiresVolume) :
    ∃ r C : ℝ, 1 < r ∧ r ≤ max C1 2 ∧ 1 ≤ C ∧ ∀ᶠ i in atTop,
      ∀ eps' : ℝ, ∀ cap : LocalCap F.S eps' (q (rho i)) (-tau (rho i)) (Phi.map i '' K.domain.carrier),
        (∀ y ∈ cap.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
          metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y) →
        ∃ Ks : CanonicalWitness F.S eps' (2 * max C1 2) C (q (rho i)) (-tau (rho i)),
          Ks.domain.carrier = Phi.map i '' K.domain.carrier ∧
          Ks.radius = Real.sqrt (tau (rho i) + b) * r ∧
          ∃ cap' depth, Ks.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap := by
  obtain ⟨eta, heta, hb⟩ := exists_universal_scalarDifferentialBounds_unconditional.{u}
  have hB := hb kappa F hF
  let C := max eta (16 * C2)
  have hC : 1 ≤ C := heta.trans (le_max_left _ _)
  have hCeta : eta ≤ C := le_max_left _ _
  have hC16 : 16 * C2 ≤ C := le_max_right _ _
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hC4 : 4 * C2 ≤ C := by linarith
  have hC8 : 8 * C2 ≤ C := by linarith
  have hinv4 : C⁻¹ ≤ (4 * C2)⁻¹ := inv_anti₀ (by positivity) hC4
  have hinv16 : C⁻¹ ≤ (16 * C2)⁻¹ := inv_anti₀ (by positivity) hC16
  obtain ⟨r, hr, hrC, hrad⟩ := K.eventually_image_ball_sandwich_of_backward_comparisons
    F hF tau htau q Phi Sm hcomplete hscalar b hsigma hcompare
  have hsc := K.eventually_image_scalar_bounds_of_backward_comparisons F tau htau q Phi
    Sm hscalar b hsigma hcompare
  have hvol := K.eventually_image_volume_lower_bound_of_backward_comparisons F tau htau q Phi
    Sm hscalar b hsigma hcompare hv
  obtain ⟨N, hN⟩ := Phi.source_subset K.domain.compact
  refine ⟨r, C, hr, hrC, hC, ?_⟩
  filter_upwards [hrad, hsc, hvol, eventually_ge_atTop N] with i hri hsci hvi hi
  intro eps' cap hdepth
  have htime : -tau (rho i) ∈ ancientTimeInterval.carrier :=
    neg_nonpos.mpr (htau (rho i)).le
  have hQ : 0 < F.S.scalar (-tau (rho i)) (q (rho i)) :=
    ancientKappa_scalar_pos F hF htime _
  let D := K.domain.map (Phi.partialDiffeomorph i) (hN i hi)
  have hD : D.carrier = Phi.map i '' K.domain.carrier := rfl
  let cap' : LocalCap F.S eps' (q (rho i)) (-tau (rho i)) D.carrier := hD.symm ▸ cap
  have hcap : HEq cap' cap := by cases hD; rfl
  have hdepth' : ∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
      metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y := by
    cases hD
    exact hdepth
  let j : Fin cap.chain.count := ⟨0, cap.chain.count_pos⟩
  have hder := hB (-tau (rho i)) htime (q (rho i))
  have hdiff : DifferentiableWithinAt ℝ (fun s => F.S.scalar s (q (rho i)))
      ancientTimeInterval.carrier (-tau (rho i)) :=
    F.isSolution.scalarTime (K := ancientTimeInterval.carrier) htime (fun _ hs => hs) _
  have hleft : derivWithin (fun s => F.S.scalar s (q (rho i))) (Iic (-tau (rho i))) (-tau (rho i)) =
      derivWithin (fun s => F.S.scalar s (q (rho i))) ancientTimeInterval.carrier (-tau (rho i)) :=
    derivWithin_subset (Iic_subset_Iic.mpr htime) (uniqueDiffWithinAt_Iic _) hdiff
  let Ks : CanonicalWitness F.S eps' (2 * max C1 2) C (q (rho i)) (-tau (rho i)) := {
    Q_pos := hQ
    time_mem := htime
    eps_pos := (cap.chain.necks j).eps_pos
    eps_lt_one := (cap.chain.necks j).eps_small.trans (by norm_num)
    domain := D
    center_inside := by rw [hD]; exact cap.core_inside (interior_subset cap.center_inside)
    radius := Real.sqrt (tau (rho i) + b) * r
    radius_lower := hri.1
    radius_upper := hri.2.1
    ball_inside := by rw [hD]; exact hri.2.2.1
    inside_ball := by rw [hD]; exact hri.2.2.2
    scalar_bounds := by
      intro y hy
      rw [hD] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨(mul_le_mul_of_nonneg_right hinv4 hQ.le).trans (hsci z hz).1,
        (hsci z hz).2.trans (mul_le_mul_of_nonneg_right hC4 hQ.le)⟩
    rm_bound := by
      intro y hy
      rw [hD] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hRm := ancientKappa_rmNormLeScalar F (by simp [ThreeSpace]) hF (-tau (rho i)) htime (Phi.map i z)
      have hroot : Real.sqrt (3 : ℝ) ≤ 2 := by
        apply Real.sqrt_le_iff.mpr
        norm_num
      have hpos : 0 < F.S.scalar (-tau (rho i)) (Phi.map i z) :=
        ancientKappa_scalar_pos F hF htime _
      calc
        Real.sqrt (FlowMetricBall.rmNormSq F.S (-tau (rho i)) (Phi.map i z))
          ≤ Real.sqrt 3 * F.S.scalar (-tau (rho i)) (Phi.map i z) := hRm
        _ ≤ 2 * F.S.scalar (-tau (rho i)) (Phi.map i z) := mul_le_mul_of_nonneg_right hroot hpos.le
        _ ≤ 8 * C2 * F.S.scalar (-tau (rho i)) (q (rho i)) := by linarith [(hsci z hz).2]
        _ ≤ C * F.S.scalar (-tau (rho i)) (q (rho i)) := mul_le_mul_of_nonneg_right hC8 hQ.le
    alternative := CanonicalAlternative.cap cap' hdepth'
    volume := by
      intro _
      rw [hD]
      exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hinv16
        (mul_nonneg hQ.le (Real.sqrt_nonneg _)))).trans hvi
    gradient := by
      intro v
      exact (hder.1 v).trans (by
        gcongr)
    time_derivative := by
      rw [hleft, abs_of_nonneg hder.2.1]
      exact hder.2.2.trans (mul_le_mul_of_nonneg_right hCeta (sq_nonneg _)) }
  exact ⟨Ks, hD, rfl, cap', hdepth', rfl, hcap⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
