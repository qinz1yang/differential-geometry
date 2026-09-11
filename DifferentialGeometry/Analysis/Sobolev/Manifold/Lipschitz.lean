import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1
import DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Iterated
import DifferentialGeometry.Analysis.Integration.Measure.Family.Decomposition
import DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison
import DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import DifferentialGeometry.Geometry.Coordinates.Fields.Scalar
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.DivergenceTheorem


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma lip_mul_bdd
    {X : Type*} [PseudoMetricSpace X]
    {s : Set X} {ρ u : X → ℝ} {Kρ Ku B : ℝ≥0}
    (hρ : LipschitzOnWith Kρ ρ s)
    (hu : LipschitzOnWith Ku u s)
    (hρ0 : ∀ x ∈ s, dist (ρ x) 0 ≤ (1 : ℝ))
    (hu0 : ∀ x ∈ s, dist (u x) 0 ≤ (B : ℝ)) :
    LipschitzOnWith (Ku + Kρ * B) (fun x => ρ x * u x) s := by
  refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
  calc
    dist (ρ x * u x) (ρ y * u y)
        ≤ dist (ρ x * u x) (ρ x * u y) +
            dist (ρ x * u y) (ρ y * u y) :=
      dist_triangle _ _ _
    _ ≤ dist (ρ x) 0 * dist (u x) (u y) +
          dist (ρ x) (ρ y) * dist (u y) 0 := by
      exact add_le_add
        (by simpa only [smul_eq_mul] using
          (dist_smul_pair (ρ x) (u x) (u y)))
        (by simpa only [smul_eq_mul] using
          (dist_pair_smul (ρ x) (ρ y) (u y)))
    _ ≤ 1 * ((Ku : ℝ) * dist x y) +
          ((Kρ : ℝ) * dist x y) * (B : ℝ) := by
      exact add_le_add
        (mul_le_mul (hρ0 x hx) (hu.dist_le_mul x hx y hy)
          dist_nonneg zero_le_one)
        (mul_le_mul (hρ.dist_le_mul x hx y hy) (hu0 y hy)
          dist_nonneg (mul_nonneg (NNReal.coe_nonneg Kρ) dist_nonneg))
    _ = ((Ku + Kρ * B : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul, one_mul]
      ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem chart_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} {L B : ℝ≥0}
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    ∃ C : ℝ≥0, LipschitzWith C
      (chartPushedRaw (I := I) (M := M) α
        (fun x =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α :
            C^∞⟮I, M; ℝ⟯) x * u x)) := by
  classical
  let : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let ρ : M → ℝ := fun x =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α :
      C^∞⟮I, M; ℝ⟯) x
  let Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) α
  let raw : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw (I := I) (M := M) α u
  let ρE : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartSmoothExt (I := I) (M := M) α ρ
  let v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw (I := I) (M := M) α (fun x => ρ x * u x)
  have hρ_nonneg (x : M) : 0 ≤ ρ x := by
    simpa only [ρ] using
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α x
  have hρ_le_one (x : M) : ρ x ≤ 1 := by
    simpa only [ρ] using
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α x
  have hv_compact : HasCompactSupport v := by
    simpa only [v, ρ] using
      ChartTower.hasCompactSupport_chartPushedRaw_pou_mul
        (I := I) (M := M) α u
  have hv_support : tsupport v ⊆ Ω := by
    simpa only [v, ρ, Ω] using
      ChartTower.tsupport_chartPushedRaw_pou_mul_subset_target
        (I := I) (M := M) α u
  have hρE_smooth : ContDiff ℝ ∞ ρE := by
    have hone : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 : ℝ)) :=
      contMDiff_const
    have h := contDiff_chartSmoothExt_pou_mul
      (I := I) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M)
      hone
    simpa only [ρE, ρ, mul_one] using h
  have hρE_local : LocallyLipschitz ρE :=
    (hρE_smooth.of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).locallyLipschitz
  have hv_amp : ∀ y, edist (v y) 0 ≤ B := by
    intro y
    by_cases hy : y ∈ Ω
    · change edist
        (chartPushedRaw (I := I) (M := M) α (fun x => ρ x * u x) y) 0 ≤ B
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ (by simpa only [Ω] using hy),
        edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_le_coe]
      calc
        ‖ρ ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖₊
            = ‖ρ ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖₊ *
                ‖u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖₊ :=
              nnnorm_mul _ _
        _ ≤ 1 * B := by
          apply mul_le_mul'
          · rw [Real.nnnorm_of_nonneg (hρ_nonneg _)]
            exact_mod_cast hρ_le_one _
          · exact hB _
        _ = B := one_mul B
    · change edist
        (chartPushedRaw (I := I) (M := M) α (fun x => ρ x * u x) y) 0 ≤ B
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _
        (by simpa only [Ω] using hy), edist_self]
      exact bot_le
  have hv_local : LocallyLipschitz v := by
    intro y
    by_cases hy : y ∈ tsupport v
    · have hyΩ : y ∈ Ω := hv_support hy
      have hyE : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rw [show Ω = chartTargetEuclid (I := I) (M := M) α from rfl,
          chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hyΩ
        exact hyΩ
      obtain ⟨C, s, hs, hC⟩ :=
        DifferentialGeometry.Geometry.Riemannian.chart_inv_edist_le
          (I := I) α hyE
      obtain ⟨s₀, hs₀, hs₀s⟩ :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs
      have hs_full : s ∈ 𝓝 ((toEuclidean (E := E)).symm y) := by
        exact mem_of_superset
          (inter_mem hs₀ ((isOpen_extChartAt_target (I := I) α).mem_nhds hyE)) hs₀s
      let S : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
        (toEuclidean (E := E)).symm ⁻¹' s
      have hS : S ∈ 𝓝 y := by
        exact (toEuclidean (E := E)).symm.continuous.continuousAt.preimage_mem_nhds hs_full
      let D : ℝ≥0 := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖₊
      have hto : LipschitzWith D (toEuclidean (E := E)).symm := by
        simpa only [D] using (toEuclidean (E := E)).symm.lipschitz
      have hraw : LipschitzOnWith (L * C * D) raw (S ∩ Ω) := by
        intro a ha b hb
        rw [show raw a =
            u ((extChartAt I α).symm ((toEuclidean (E := E)).symm a)) by
          exact chartPushedRaw_apply_of_mem (I := I) (M := M) α u
            (by simpa only [Ω] using ha.2)]
        rw [show raw b =
            u ((extChartAt I α).symm ((toEuclidean (E := E)).symm b)) by
          exact chartPushedRaw_apply_of_mem (I := I) (M := M) α u
            (by simpa only [Ω] using hb.2)]
        have hCab : DifferentialGeometry.riemannianEDistOf (I := I) g
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm a))
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm b)) ≤
            C * edist ((toEuclidean (E := E)).symm a)
              ((toEuclidean (E := E)).symm b) := by
          simpa only [DifferentialGeometry.riemannianEDistOf] using
            hC _ ha.1 _ hb.1
        calc
          _ ≤ L * DifferentialGeometry.riemannianEDistOf (I := I) g
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm a))
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm b)) := hu _ _
          _ ≤ L * (C * edist ((toEuclidean (E := E)).symm a)
              ((toEuclidean (E := E)).symm b)) :=
            mul_le_mul_right hCab L
          _ ≤ L * (C * (D * edist a b)) :=
            mul_le_mul_right (mul_le_mul_right (hto a b) C) L
          _ = (L * C * D) * edist a b := by
            simp only [mul_assoc]
      obtain ⟨Kρ, t, ht, hρt⟩ := hρE_local y
      let w : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
        (S ∩ t) ∩ Ω
      have hw : w ∈ 𝓝 y := by
        exact inter_mem (inter_mem hS ht)
          ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds
            (by simpa only [Ω] using hyΩ))
      have hwSΩ : w ⊆ S ∩ Ω := fun _ hz => ⟨hz.1.1, hz.2⟩
      have hwt : w ⊆ t := fun _ hz => hz.1.2
      have hwΩ : w ⊆ Ω := fun _ hz => hz.2
      have hρw : LipschitzOnWith Kρ ρE w := hρt.mono hwt
      have hraw_w : LipschitzOnWith (L * C * D) raw w := hraw.mono hwSΩ
      have hρ0 : ∀ z ∈ w, dist (ρE z) 0 ≤ (1 : ℝ) := by
        intro z hz
        have hzΩ : z ∈ Ω := hwΩ hz
        have hzE : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
          rw [show Ω = chartTargetEuclid (I := I) (M := M) α from rfl,
            chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hzΩ
          exact hzΩ
        change dist
          (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
            ρ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) else 0) 0 ≤ 1
        rw [if_pos hzE, Real.dist_eq, sub_zero, abs_of_nonneg (hρ_nonneg _)]
        exact hρ_le_one _
      have hraw0 : ∀ z ∈ w, dist (raw z) 0 ≤ (B : ℝ) := by
        intro z hz
        rw [show raw z = u ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm z)) by
          exact chartPushedRaw_apply_of_mem (I := I) (M := M) α u
            (by simpa only [Ω] using hwΩ hz), Real.dist_eq, sub_zero,
          ← Real.norm_eq_abs, ← coe_nnnorm, NNReal.coe_le_coe]
        exact hB _
      have hprod : LipschitzOnWith ((L * C * D) + Kρ * B)
          (fun z => ρE z * raw z) w :=
        lip_mul_bdd hρw hraw_w hρ0 hraw0
      refine ⟨(L * C * D) + Kρ * B, w, hw, ?_⟩
      intro a ha b hb
      have hfac (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
          (hz : z ∈ w) : v z = ρE z * raw z := by
        have hzΩ : z ∈ Ω := hwΩ hz
        have hzE : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
          rw [show Ω = chartTargetEuclid (I := I) (M := M) α from rfl,
            chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hzΩ
          exact hzΩ
        rw [show v z = ρ ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm z)) *
              u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) by
          exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _
            (by simpa only [Ω] using hwΩ hz)]
        rw [show raw z = u ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm z)) by
          exact chartPushedRaw_apply_of_mem (I := I) (M := M) α u
            (by simpa only [Ω] using hwΩ hz)]
        change _ = (if (toEuclidean (E := E)).symm z ∈
            (extChartAt I α).target then
          ρ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) else 0) * _
        rw [if_pos hzE]
      rw [hfac a ha, hfac b hb]
      exact hprod ha hb
    · refine ⟨0, {z | v z = 0}, ?_, ?_⟩
      · exact notMem_tsupport_iff_eventuallyEq.mp hy
      · intro a ha b hb
        rw [ha, hb, edist_self]
        exact bot_le
  simpa only [v, ρ] using
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.lip_of_local_comp
      hv_local hv_compact hv_amp)
omit [IsManifold I ∞ M] in
private lemma chart_raw_zero
    (α : M) {a : M → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ toEuclidean '' ((extChartAt I α) '' tsupport a)) :
    chartPushedRaw (I := I) (M := M) α a y = 0 := by
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M) α hy_target hy
  · exact chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α a hy_target

omit [IsManifold I ∞ M] in
private lemma chart_raw_comp
    (α : M) {a : M → ℝ}
    (ha_cs : HasCompactSupport a)
    (ha_supp : tsupport a ⊆ (chartAt H α).source) :
    IsCompact (toEuclidean '' ((extChartAt I α) '' tsupport a)) := by
  have hsource : tsupport a ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source]
    exact ha_supp hx
  have hcont : ContinuousOn (extChartAt I α) (tsupport a) :=
    (continuousOn_extChartAt α).mono hsource
  exact (ha_cs.image_of_continuousOn hcont).image
    (toEuclidean (E := E)).continuous

private lemma chart_raw_smooth
    [I.Boundaryless]
    (α : M) {a : M → ℝ}
    (ha : ContMDiff I 𝓘(ℝ) ∞ a)
    (ha_cs : HasCompactSupport a)
    (ha_supp : tsupport a ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (chartPushedRaw (I := I) (M := M) α a) := by
  classical
  let K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    toEuclidean '' ((extChartAt I α) '' tsupport a)
  have hK_compact : IsCompact K := by
    simpa only [K] using chart_raw_comp (I := I) (M := M) α ha_cs ha_supp
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α := by
    simpa only [K] using
      image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
        (I := I) (M := M) (u := a) (α := α) ha_supp
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · have hyE : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      simpa only [chartTargetEuclid_eq_preimage_symm, Set.mem_preimage] using hy_target
    have hscalar : ContDiffAt ℝ ∞
        (scalarOnE (I := I) α a) ((toEuclidean (E := E)).symm y) :=
      (scalarOnE_contDiffWithinAt (I := I) α ha hyE).contDiffAt
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hyE)
    have hformula : ContDiffAt ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          scalarOnE (I := I) α a ((toEuclidean (E := E)).symm z)) y :=
      hscalar.comp y (toEuclidean (E := E)).symm.contDiff.contDiffAt
    apply hformula.congr_of_eventuallyEq
    filter_upwards [
      (chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy_target] with z hz
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α a hz]
    rfl
  · have hyK : y ∉ K := fun hy ↦ hy_target (hK_target hy)
    apply ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ))
      contDiffAt_const
    filter_upwards [hK_compact.isClosed.isOpen_compl.mem_nhds hyK] with z hz
    exact chart_raw_zero (I := I) (M := M) α hz

omit [IsManifold I ∞ M] in
private lemma chart_raw_cs
    (α : M) {a : M → ℝ}
    (ha_cs : HasCompactSupport a)
    (ha_supp : tsupport a ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α a) := by
  let K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    toEuclidean '' ((extChartAt I α) '' tsupport a)
  have hK_compact : IsCompact K := by
    simpa only [K] using chart_raw_comp (I := I) (M := M) α ha_cs ha_supp
  refine HasCompactSupport.of_support_subset_isCompact hK_compact ?_
  intro y hy
  by_contra hyK
  exact hy (chart_raw_zero (I := I) (M := M) α hyK)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma chart_raw_locLip
    [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} {L : ℝ≥0}
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y) :
    LocallyLipschitzOn (chartTargetEuclid (I := I) (M := M) α)
      (chartPushedRaw (I := I) (M := M) α u) := by
  let _ : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  intro y hy
  have hyE : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    simpa only [chartTargetEuclid_eq_preimage_symm, Set.mem_preimage] using hy
  obtain ⟨C, s, hs, hC⟩ :=
    DifferentialGeometry.Geometry.Riemannian.chart_inv_edist_le
      (I := I) α hyE
  obtain ⟨s₀, hs₀, hs₀s⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs
  have hs_full : s ∈ 𝓝 ((toEuclidean (E := E)).symm y) := by
    exact mem_of_superset
      (inter_mem hs₀ ((isOpen_extChartAt_target (I := I) α).mem_nhds hyE)) hs₀s
  let S : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (toEuclidean (E := E)).symm ⁻¹' s
  have hS : S ∈ 𝓝 y :=
    (toEuclidean (E := E)).symm.continuous.continuousAt.preimage_mem_nhds hs_full
  let D : ℝ≥0 := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖₊
  have hto : LipschitzWith D (toEuclidean (E := E)).symm := by
    simpa only [D] using (toEuclidean (E := E)).symm.lipschitz
  refine ⟨L * C * D, S ∩ chartTargetEuclid (I := I) (M := M) α,
    inter_mem (mem_nhdsWithin_of_mem_nhds hS) self_mem_nhdsWithin, ?_⟩
  intro z hz w hw
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hz.2]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hw.2]
  have hCzw : DifferentialGeometry.riemannianEDistOf (I := I) g
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm w)) ≤
      C * edist ((toEuclidean (E := E)).symm z)
        ((toEuclidean (E := E)).symm w) := by
    simpa only [DifferentialGeometry.riemannianEDistOf] using
      hC _ hz.1 _ hw.1
  calc
    _ ≤ L * DifferentialGeometry.riemannianEDistOf (I := I) g
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm w)) := hu _ _
    _ ≤ L * (C * edist ((toEuclidean (E := E)).symm z)
        ((toEuclidean (E := E)).symm w)) := mul_le_mul_right hCzw L
    _ ≤ L * (C * (D * edist z w)) :=
      mul_le_mul_right (mul_le_mul_right (hto z w) C) L
    _ = (L * C * D) * edist z w := by simp only [mul_assoc]

theorem exists_lipschitzWith_chartPullZero_mul
    [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) {a u : M → ℝ} {L : ℝ≥0}
    (ha : ContMDiff I 𝓘(ℝ) ∞ a)
    (ha_cs : HasCompactSupport a)
    (ha_supp : tsupport a ⊆ (chartAt H α).source)
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y) :
    ∃ C : ℝ≥0, LipschitzWith C
      (chartPullZero (I := I) α (fun x => a x * u x)) := by
  classical
  let rawA := chartPushedRaw (I := I) (M := M) α a
  let rawU := chartPushedRaw (I := I) (M := M) α u
  let raw := chartPushedRaw (I := I) (M := M) α (fun x => a x * u x)
  have hraw_eq : raw = fun y => rawA y * rawU y := by
    funext y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [show raw y = a ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y)) *
          u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) by
        exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
      rw [show rawA y = a ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y)) by
        exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
      rw [show rawU y = u ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y)) by
        exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    · rw [show raw y = 0 by
        exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
      rw [show rawA y = 0 by
        exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
      simp only [zero_mul]
  have hrawA_smooth : ContDiff ℝ ∞ rawA := by
    simpa only [rawA] using chart_raw_smooth (I := I) (M := M) α ha ha_cs ha_supp
  have hrawA_cs : HasCompactSupport rawA := by
    simpa only [rawA] using chart_raw_cs (I := I) (M := M) α ha_cs ha_supp
  obtain ⟨K, hrawA_lip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hrawA_cs hrawA_smooth (by simp)
  have hrawU_local := chart_raw_locLip (I := I) (M := M) g α hu
  have hmul_local : LocallyLipschitz
      (fun p : ℝ × ℝ => p.1 * p.2) := by
    have hmul_smooth : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) :=
      contDiff_fst.mul contDiff_snd
    exact hmul_smooth.locallyLipschitz
  have hprod_on : LocallyLipschitzOn
      (chartTargetEuclid (I := I) (M := M) α) (fun y => rawA y * rawU y) := by
    rw [locallyLipschitzOn_iff_restrict]
    have hA : LocallyLipschitz
        ((chartTargetEuclid (I := I) (M := M) α).domRestrict rawA) :=
      locallyLipschitzOn_iff_restrict.mp hrawA_lip.locallyLipschitz.locallyLipschitzOn
    have hU : LocallyLipschitz
        ((chartTargetEuclid (I := I) (M := M) α).domRestrict rawU) :=
      locallyLipschitzOn_iff_restrict.mp hrawU_local
    exact hmul_local.comp (hA.prodMk hU)
  have hrawA_tsupport : tsupport rawA ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    let K₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
      toEuclidean '' ((extChartAt I α) '' tsupport a)
    have hK₀_closed : IsClosed K₀ :=
      (chart_raw_comp (I := I) (M := M) α ha_cs ha_supp).isClosed
    have hsupp : Function.support rawA ⊆ K₀ := by
      intro y hy
      by_contra hyK
      exact hy (chart_raw_zero (I := I) (M := M) α hyK)
    have hts : tsupport rawA ⊆ K₀ := closure_minimal hsupp hK₀_closed
    exact hts.trans (by
      simpa only [K₀] using
        image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
          (I := I) (M := M) (u := a) (α := α) ha_supp)
  have hraw_local : LocallyLipschitz raw := by
    rw [hraw_eq]
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · obtain ⟨C, s, hs, hCs⟩ := hprod_on hy
      obtain ⟨t, ht, hts⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs
      refine ⟨C, s, mem_of_superset
        (inter_mem ht ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy))
        hts, hCs⟩
    · have hyA : y ∉ tsupport rawA := fun h ↦ hy (hrawA_tsupport h)
      obtain ⟨s, hs, hsA⟩ := Filter.eventually_iff_exists_mem.mp
        (notMem_tsupport_iff_eventuallyEq.mp hyA)
      refine ⟨0, s, hs, ?_⟩
      intro z hz w hw
      change edist (rawA z * rawU z) (rawA w * rawU w) ≤ _
      have hzA : rawA z = 0 := by simpa using hsA z hz
      have hwA : rawA w = 0 := by simpa using hsA w hw
      rw [hzA, hwA, zero_mul, zero_mul, edist_self]
      exact bot_le
  have hraw_cs : HasCompactSupport raw := by
    rw [hraw_eq]
    exact hrawA_cs.mul_right
  obtain ⟨B₀, hB₀⟩ := hraw_cs.exists_bound_of_continuous hraw_local.continuous
  let B : ℝ≥0 := ⟨max B₀ 0, le_max_right _ _⟩
  have hraw_amp : ∀ y, edist (raw y) 0 ≤ B := by
    intro y
    rw [edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_le_coe]
    exact_mod_cast (hB₀ y).trans (le_max_left _ _)
  obtain ⟨C, hC⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.lip_of_local_comp
      hraw_local hraw_cs hraw_amp
  have heq : chartPullZero (I := I) α (fun x => a x * u x) =
      raw ∘ toEuclidean (E := E) := by
    funext y
    by_cases hy : y ∈ (extChartAt I α).target
    · rw [chartPullZero_mem (I := I) α _ hy, Function.comp_apply]
      rw [show raw (toEuclidean (E := E) y) =
          (a * u) ((extChartAt I α).symm y) by
        have hy' : toEuclidean (E := E) y ∈
            chartTargetEuclid (I := I) (M := M) α := by
          rw [chartTargetEuclid_eq_preimage_symm]
          change (toEuclidean (E := E)).symm (toEuclidean (E := E) y) ∈
            (extChartAt I α).target
          simpa only [(toEuclidean (E := E)).symm_apply_apply] using hy
        change chartPushedRaw (I := I) (M := M) α
            (fun x => a x * u x) (toEuclidean (E := E) y) = _
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy']
        simp only [(toEuclidean (E := E)).symm_apply_apply]
        rfl]
      rfl
    · rw [chartPullZero_nmem (I := I) α _ hy, Function.comp_apply]
      symm
      exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ (by
        rw [chartTargetEuclid_eq_preimage_symm]
        change (toEuclidean (E := E)).symm (toEuclidean (E := E) y) ∉
          (extChartAt I α).target
        simpa only [(toEuclidean (E := E)).symm_apply_apply] using hy)
  refine ⟨C * ‖(toEuclidean (E := E)).toContinuousLinearMap‖₊, ?_⟩
  rw [heq]
  exact hC.comp (toEuclidean (E := E)).lipschitz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_chartPushedRaw_memW1p_on_ball_of_lipschitz
    [T2Space M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ≥0∞} {u : M → ℝ} {L : ℝ≥0}
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y) :
    ∃ r : ℝ, 0 < r ∧
      DeGiorgi.MemW1p p
        (chartPushedRaw (I := I) (M := M) α u)
        (Metric.ball
          (toEuclidean (E := E) (extChartAt I α α)) r) := by
  obtain ⟨χ, -, hχ_supp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) α).mem_iff.mp
      ((chartAt H α).open_source.mem_nhds (mem_chart_source H α))
  let cut : M → ℝ := fun x ↦ χ x * u x
  obtain ⟨C, hcut_pull⟩ := exists_lipschitzWith_chartPullZero_mul
    (I := I) g α χ.contMDiff χ.hasCompactSupport hχ_supp hu
  have hcut_pull' : LipschitzWith C
      (chartPullZero (I := I) α cut) := by
    simpa only [cut] using hcut_pull
  let cutRaw : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw (I := I) (M := M) α cut
  have hraw_eq : cutRaw =
      chartPullZero (I := I) α cut ∘ (toEuclidean (E := E)).symm := by
    funext y
    change chartPushedRaw (I := I) (M := M) α cut y = _
    by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
    · have hy' : y ∈ chartTargetEuclid (I := I) (M := M) α := by
        rw [chartTargetEuclid_eq_preimage_symm]
        exact hy
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α cut hy',
        Function.comp_apply, chartPullZero_mem (I := I) α cut hy,
        scalarOnE_def]
    · have hy' : y ∉ chartTargetEuclid (I := I) (M := M) α := by
        rw [chartTargetEuclid_eq_preimage_symm]
        exact hy
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α cut hy',
        Function.comp_apply, chartPullZero_nmem (I := I) α cut hy]
  have hcutRaw : LipschitzWith
      (C * ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖₊) cutRaw := by
    rw [hraw_eq]
    exact hcut_pull'.comp (toEuclidean (E := E)).symm.lipschitz
  have hcut_support : Function.support cut ⊆ tsupport (χ : M → ℝ) := by
    intro x hx
    apply subset_tsupport
    intro hχ
    exact hx (by simp only [cut, hχ, zero_mul])
  have hcut_cs : HasCompactSupport cut :=
    HasCompactSupport.of_support_subset_isCompact χ.hasCompactSupport hcut_support
  have hcut_supp : tsupport cut ⊆ (chartAt H α).source :=
    (closure_minimal hcut_support (isClosed_tsupport _)).trans hχ_supp
  have hcutRaw_cs : HasCompactSupport cutRaw := by
    simpa only [cutRaw] using
      chart_raw_cs (I := I) (M := M) α hcut_cs hcut_supp
  let c : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (E := E) (extChartAt I α α)
  have hchart_tendsto : Tendsto
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ↦
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (nhds c) (nhds α) := by
    have hto : Tendsto (toEuclidean (E := E)).symm (nhds c)
        (nhds (extChartAt I α α)) := by
      have hto' := (toEuclidean (E := E)).symm.continuousAt (x := c)
      change Tendsto (toEuclidean (E := E)).symm (nhds c)
        (nhds ((toEuclidean (E := E)).symm c)) at hto'
      simpa only [c, (toEuclidean (E := E)).symm_apply_apply] using hto'
    have hinv : Tendsto (extChartAt I α).symm
        (nhds (extChartAt I α α)) (nhds α) := by
      have hinv' := continuousAt_extChartAt_symm (I := I) α
      change Tendsto (extChartAt I α).symm
        (nhds (extChartAt I α α))
        (nhds ((extChartAt I α).symm (extChartAt I α α))) at hinv'
      rw [(extChartAt I α).left_inv
        (mem_extChartAt_source (I := I) α)] at hinv'
      exact hinv'
    exact hinv.comp hto
  have hχ_one :
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ↦ χ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =ᶠ[nhds c]
        fun _ ↦ (1 : ℝ) :=
    hchart_tendsto.eventually χ.eventuallyEq_one
  have hone_nhds : {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) | χ
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 1} ∈ nhds c :=
    hχ_one
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hone_nhds
  refine ⟨r, hr, ?_⟩
  have hcut_mem : DeGiorgi.MemW1p p cutRaw (Metric.ball c r) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_lip
      hcutRaw hcutRaw_cs
  have hcut_eq : cutRaw =ᵐ[volume.restrict (Metric.ball c r)]
      chartPushedRaw (I := I) (M := M) α u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    change chartPushedRaw (I := I) (M := M) α cut y =
      chartPushedRaw (I := I) (M := M) α u y
    have hχ_y := hball hy
    change χ ((extChartAt I α).symm
      ((toEuclidean (E := E)).symm y)) = 1 at hχ_y
    by_cases hy' : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α cut hy']
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy']
      simp only [cut, hχ_y, one_mul]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α cut hy']
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α u hy']
  exact
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      Metric.isOpen_ball hcut_eq).mp hcut_mem

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma pou_ae_diff
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} {L B : ℝ≥0}
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    ∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α),
      x ∈ (chartAt H α).source →
        DifferentiableAt ℝ
          (chartPushedRaw (I := I) (M := M) α
            (fun y =>
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α :
                C^∞⟮I, M; ℝ⟯) y * u y))
          ((toEuclidean (E := E)) (extChartAt I α x)) := by
  obtain ⟨C, hC⟩ := chart_pou_lip (I := I) g α hu hB
  exact ae_chart_of_volume (I := I) (M := M) g α
    (measurableSet_of_differentiableAt ℝ _) hC.ae_differentiableAt

private lemma pou_ae_mdiff
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} {L B : ℝ≥0}
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    ∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α),
      x ∈ (chartAt H α).source →
        MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α :
              C^∞⟮I, M; ℝ⟯) y * u y) x := by
  filter_upwards [pou_ae_diff (I := I) g α hu hB] with x hx
  exact fun hx_source => mdifferentiableAt_of_chartPushedRaw_differentiableAt (I := I) α hx_source (hx hx_source)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem ae_mdiff_of_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {u : M → ℝ} {L B : ℝ≥0}
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    ∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
      (I := I) (M := M) g), MDifferentiableAt I 𝓘(ℝ, ℝ) u x := by
  rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_eq_finset_sum
    (I := I) (M := M) g, MeasureTheory.ae_finsetSum_measure_iff]
  intro α _
  let ρ : M → ℝ := fun x =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α :
      C^∞⟮I, M; ℝ⟯) x
  rw [MeasureTheory.ae_withDensity_iff
    (DifferentialGeometry.Integral.Measure.measurable_ofReal_pou_weight
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α)]
  filter_upwards [pou_ae_mdiff (I := I) g α hu hB] with x hx
  intro hweight
  have hρ_ne : ρ x ≠ 0 := by
    intro hρ_zero
    apply hweight
    simp only [ρ, hρ_zero, ENNReal.ofReal_zero]
  have hx_tsupport : x ∈ tsupport ρ := by
    apply subset_closure
    simpa only [Function.mem_support] using hρ_ne
  have hx_source : x ∈ (chartAt H α).source := by
    apply (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
    simpa only [ρ] using hx_tsupport
  have hprod : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ρ y * u y) x := by
    simpa only [ρ] using hx hx_source
  have hρ_smooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρ x := by
    simpa only [ρ] using
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α :
        C^∞⟮I, M; ℝ⟯).contMDiff.contMDiffAt
  have hinv : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (ρ y)⁻¹) x :=
    (hρ_smooth.inv₀ hρ_ne).mdifferentiableAt (by simp)
  have hrecover : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => (ρ y)⁻¹ * (ρ y * u y)) x :=
    hinv.mul hprod
  refine hrecover.congr_of_eventuallyEq ?_
  filter_upwards [hρ_smooth.continuousAt.eventually_ne hρ_ne] with y hy
  rw [← mul_assoc, inv_mul_cancel₀ hy, one_mul]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_chart_one_of_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : M → ℝ} {L B : ℝ≥0}
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    MemWkpChart (I := I) (M := M) 1 p u := by
  classical
  intro α
  let ρ : M → ℝ := fun x =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α :
      C^∞⟮I, M; ℝ⟯) x
  let Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) α
  let v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw (I := I) (M := M) α (fun x => ρ x * u x)
  have hv_compact : HasCompactSupport v := by
    simpa only [v, ρ] using
      ChartTower.hasCompactSupport_chartPushedRaw_pou_mul
        (I := I) (M := M) α u
  obtain ⟨C, hCv⟩ := chart_pou_lip (I := I) g α hu hB
  have hCv' : LipschitzWith C v := by
    simpa only [v, ρ] using hCv
  have hraw_mem :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_one_of_lip
      (p := p) (Omega := Ω) hCv' hv_compact
  exact
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)).mpr
      (by simpa only [v, ρ, Ω] using hraw_mem)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
