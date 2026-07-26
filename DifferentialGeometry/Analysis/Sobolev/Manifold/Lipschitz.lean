import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Geometry.Metric.DistanceScaling

/-!
# Intrinsically Lipschitz functions in chart Sobolev spaces

This file gives the qualitative first-order Sobolev entrance for bounded
functions that are Lipschitz with respect to an explicitly supplied smooth
Riemannian metric.
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The partition-of-unity localization of a bounded function that is
Lipschitz for an explicit Riemannian distance is globally Lipschitz in the
Euclidean chart model. -/
theorem chart_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
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
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
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
  have hv_supp : tsupport v ⊆ Ω := by
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
    · have hyΩ : y ∈ Ω := hv_supp hy
      have hyE : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        simpa only [Ω, chartTargetEuclid_eq_preimage_symm] using hyΩ
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
          simpa only [Ω, chartTargetEuclid_eq_preimage_symm] using hzΩ
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
          simpa only [Ω, chartTargetEuclid_eq_preimage_symm] using hzΩ
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

private lemma pou_ae_diff
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
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
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
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
  exact fun hx_source => mdiff_of_raw (I := I) α hx_source (hx hx_source)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A bounded function that is Lipschitz for an explicit Riemannian distance
is manifold-differentiable almost everywhere for the Riemannian volume. -/
theorem ae_mdiff_of_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A bounded function that is Lipschitz for the extended distance of a
smooth Riemannian metric belongs to every first-order chart Sobolev space. -/
theorem mem_chart_one_of_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : M → ℝ} {L B : ℝ≥0}
    (hu : ∀ x y, edist (u x) (u y) ≤ L *
      DifferentialGeometry.riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    MemWkpChart (I := I) (M := M) g 1 p u := by
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
