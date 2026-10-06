import DifferentialGeometry.Geometry.MinimalSurface.Variation.FoldFirstVariation
import DifferentialGeometry.Geometry.Measure.Area.RegionCongruence
import Mathlib.Analysis.Calculus.Deriv.Slope
import DifferentialGeometry.Analysis.Calculus.Interpolation.FiniteClosedCover
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicReplacement

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] in
private theorem exists_lipschitz_disk_comp_smooth
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    {F : M → M} (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 F) :
    ∃ K : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (F (u z)) (F (u w)) ≤ (K : ℝ≥0∞) * edist z w := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hmetric (x y : M) : edist x y = riemannianEDistOf g x y := rfl
  let U := diskExtension u
  have hU : LipschitzWith L U := diskExtension_riemannian_lipschitz g hu
  have hlocal (x : closedDisk) : ∃ (C : ℝ≥0) (V : Set ℂ),
      IsOpen V ∧ (x : ℂ) ∈ V ∧ LipschitzOnWith C (F ∘ U) V := by
    obtain ⟨C, A, hA, hCA⟩ := (hF.contMDiffAt (x := U x)).exists_lipschitzOnWith
    have hpre : U ⁻¹' A ∈ 𝓝 (x : ℂ) := hU.continuous.continuousAt hA
    obtain ⟨V, hVA, hV, hxV⟩ := mem_nhds_iff.mp hpre
    refine ⟨C * L, V, hV, hxV, ?_⟩
    intro z hz w hw
    exact (hCA (hVA hz) (hVA hw)).trans
      ((mul_le_mul_right (hU z w) (C : ℝ≥0∞)).trans_eq (by
        rw [ENNReal.coe_mul, mul_assoc]))
  choose C V hV hxV hCV using hlocal
  obtain ⟨s, hs⟩ := (isCompact_closedBall (0 : ℂ) 1).elim_finite_subcover V hV
    (fun z hz => mem_iUnion_of_mem (⟨z, hz⟩ : closedDisk) (hxV ⟨z, hz⟩))
  have hcomp : LipschitzOnWith (s.sup C) (F ∘ U) (Metric.closedBall (0 : ℂ) 1) := by
    apply Analysis.lipschitzOnWith_of_eventually_edist_le (convex_closedBall (0 : ℂ) 1)
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hs hz)
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((hV i).mem_nhds hzi)] with w hwi
    exact (hCV i hwi hzi).trans (mul_le_mul_left
      (ENNReal.coe_le_coe.mpr (Finset.le_sup hi)) _)
  refine ⟨s.sup C, fun z w => ?_⟩
  simpa only [Function.comp_apply, U, diskExtension_coe, hmetric, Subtype.edist_eq] using
    hcomp z.property w.property

/-- Apply a smooth ambient map only on an interior source ball. The actual map
fixes the image of the patch circle. The replacement is constructed with its
metric Lipschitz bound, original boundary trace, and exterior range. No ambient
connectedness or smoothness across a fold of the original disk is assumed. -/
theorem exists_disk_replacement_of_smooth_map
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    {F : M → M} (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 F)
    {p : ℂ} {r : ℝ} (hpr : ‖p‖ + r < 1)
    (hfix : ∀ z ∈ Metric.sphere p r, F (diskExtension u z) = diskExtension u z)
    {W : Set M} (huW : Set.range u ⊆ W) (hFW : MapsTo F W W) :
    ∃ (v : C(closedDisk, M)) (K : ℝ≥0),
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      (∀ z : closedDisk, dist (z : ℂ) p ≤ r → v z = F (u z)) ∧
      (∀ z : closedDisk, r ≤ dist (z : ℂ) p → v z = u z) := by
  let f : C(closedDisk, M) := ⟨fun z => F (u z), hF.continuous.comp u.continuous⟩
  obtain ⟨K, hK⟩ := exists_lipschitz_disk_comp_smooth g u hu hF
  have hf : ∀ z w, riemannianEDistOf g (f z) (f w) ≤
      (K : ℝ≥0∞) * edist z w := hK
  have heq : ∀ z ∈ Metric.sphere p r, diskExtension f z = diskExtension u z := hfix
  obtain ⟨v, hv, hinner, houter, htrace, _⟩ :=
    exists_disk_replacement_of_eq_on_sphere g u hu
      (diskExtension_riemannian_lipschitz g hf) hpr heq
  refine ⟨v, K + L, hv, htrace, ?_, ?_, houter⟩
  · rintro _ ⟨z, rfl⟩
    by_cases hz : dist (z : ℂ) p ≤ r
    · rw [hinner z hz, diskExtension_coe]
      exact hFW (huW ⟨z, rfl⟩)
    · rw [houter z (le_of_not_ge hz)]
      exact huW ⟨z, rfl⟩
  · intro z hz
    exact (hinner z hz).trans (diskExtension_coe f z)


open MeasureTheory _root_.Metric
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped ComplexConjugate

private theorem riemannianDiskArea_replacement_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u w : C(closedDisk, M)) {K L : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤
      (K : ℝ≥0∞) * edist z z')
    (hw : ∀ z z', riemannianEDistOf g (w z) (w z') ≤
      (L : ℝ≥0∞) * edist z z')
    {v : ℂ → M} {p : ℂ} {r : ℝ}
    (hball : closedBall p r ⊆ ball (0 : ℂ) 1)
    (hinner : ∀ z : closedDisk, dist (z : ℂ) p ≤ r → w z = v z)
    (houter : ∀ z : closedDisk, r ≤ dist (z : ℂ) p → w z = u z) :
    riemannianDiskArea g w = riemannianDiskArea g u -
      riemannianArea g (diskExtension u) (closedBall p r) +
      riemannianArea g v (closedBall p r) := by
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hiu : IntegrableOn (riemannianAreaDensity g (diskExtension u))
      (closedBall (0 : ℂ) 1) :=
    integrableOn_riemannianAreaDensity_of_lipschitz g
      (diskExtension_riemannian_lipschitz g hu) _
  have hiw : IntegrableOn (riemannianAreaDensity g (diskExtension w))
      (closedBall (0 : ℂ) 1) :=
    integrableOn_riemannianAreaDensity_of_lipschitz g
      (diskExtension_riemannian_lipschitz g hw) _
  have hsub : closedBall p r ⊆ closedBall (0 : ℂ) 1 :=
    hball.trans ball_subset_closedBall
  have hinside : riemannianArea g (diskExtension w) (closedBall p r) =
      riemannianArea g v (closedBall p r) := by
    apply riemannianArea_congr_on_closedBall g
    intro z hz
    exact (diskExtension_coe w ⟨z, hsub hz⟩).trans
      (hinner ⟨z, hsub hz⟩ (mem_closedBall.mp hz))
  have houtside :
      (∫ z in closedBall (0 : ℂ) 1 \ closedBall p r,
        riemannianAreaDensity g (diskExtension w) z) =
      ∫ z in closedBall (0 : ℂ) 1 \ closedBall p r,
        riemannianAreaDensity g (diskExtension u) z := by
    have hzint : ∀ᵐ z ∂volume.restrict (closedBall (0 : ℂ) 1 \ closedBall p r),
        z ∈ ball (0 : ℂ) 1 :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
    apply integral_congr_ae
    filter_upwards [hzint, ae_restrict_mem
      (measurableSet_closedBall.diff measurableSet_closedBall)] with z hz hzd
    apply riemannianAreaDensity_congr g
    filter_upwards [(isOpen_ball.inter isClosed_closedBall.isOpen_compl).mem_nhds
      ⟨hz, hzd.2⟩] with y hy
    let q : closedDisk := ⟨y, ball_subset_closedBall hy.1⟩
    have hdist : r ≤ dist y p := (not_le.mp (show ¬ dist y p ≤ r from hy.2)).le
    exact (diskExtension_coe w q).trans
      ((houter q hdist).trans (diskExtension_coe u q).symm)
  have hsu := setIntegral_sdiff measurableSet_closedBall hiu hsub
  have hsw := setIntegral_sdiff measurableSet_closedBall hiw hsub
  change (∫ z in closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension w) z) =
    (∫ z in closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension u) z) -
      (∫ z in closedBall p r, riemannianAreaDensity g (diskExtension u) z) +
        ∫ z in closedBall p r, riemannianAreaDensity g v z
  change (∫ z in closedBall p r, riemannianAreaDensity g (diskExtension w) z) =
    (∫ z in closedBall p r, riemannianAreaDensity g v z) at hinside
  rw [houtside, hinside, hsu] at hsw
  linarith


/-- A genuine folded disk with strictly negative paired ambient divergence has
an admissible fixed-boundary competitor of strictly smaller area in the original
metric. The moving patch is pasted into the same disk, preserving its exact trace
and its image in the supplied exterior set. The lower sheet is the literal
reflection of this disk, not a separately chosen source sheet. -/
theorem exists_disk_area_lt_of_fold_divergence_neg
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΦzero : ∀ x, Φ 0 x = x)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    (hvelocity : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x)
    (p r : ℝ)
    (hpr : ‖(p : ℂ)‖ + r < 1)
    (hfix : ∀ t z, z ∈ Metric.sphere (p : ℂ) r →
      Φ t (diskExtension u z) = diskExtension u z)
    {W : Set M} (huW : Set.range u ⊆ W)
    (hΦW : ∀ t, MapsTo (Φ t) W W)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hi : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hir : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) z))
    (hnegative :
      (∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
        ambientDivergenceWithin g (diskExtension u) (closedHalfDisk p r) Y z) +
      (∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
        ambientDivergenceWithin g (diskExtension u ∘ conj) (closedHalfDisk p r) Y z) < 0) :
    ∃ (v : C(closedDisk, M)) (K : ℝ≥0),
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      riemannianDiskArea g v < riemannianDiskArea g u := by
  have hdecrease : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      riemannianArea g ((Φ t) ∘ diskExtension u) (Metric.closedBall (p : ℂ) r) <
        riemannianArea g (diskExtension u) (Metric.closedBall (p : ℂ) r) := by
    obtain ⟨_, _, hd⟩ := hasDerivAt_riemannianArea_isotopy_of_fold
      g u huLip Φ hΦ hΦzero Y hY hvelocity p r hU hUr hi hir
    have hs := hd.tendsto_slope_zero_right.eventually_lt_const hnegative
    filter_upwards [hs, self_mem_nhdsWithin] with t ht hpos
    have hinitial : (Φ 0) ∘ diskExtension u = diskExtension u := by
      funext z
      exact hΦzero _
    simp only [zero_add, smul_eq_mul, hinitial] at ht
    rcases mul_neg_iff.mp ht with ⟨_, hdiff⟩ | ⟨hneg, _⟩
    · exact sub_neg.mp hdiff
    · exact ((not_lt_of_ge (inv_pos.mpr hpos).le) hneg).elim
  obtain ⟨t, ht⟩ := hdecrease.exists
  obtain ⟨v, K, hvLip, hvtrace, hvW, hinner, houter⟩ :=
    exists_disk_replacement_of_smooth_map g u huLip ((Φ t).contMDiff.of_le (by simp))
      hpr (hfix t) huW (hΦW t)
  have hball : Metric.closedBall (p : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have hn : ‖z‖ ≤ dist z (p : ℂ) + ‖(p : ℂ)‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - (p : ℂ)) (p : ℂ)
    exact hn.trans_lt (by have hd := Metric.mem_closedBall.mp hz; linarith)
  have hin : ∀ z : closedDisk, dist (z : ℂ) (p : ℂ) ≤ r →
      v z = ((Φ t) ∘ diskExtension u) z := by
    intro z hz
    exact (hinner z hz).trans (congrArg (Φ t) (diskExtension_coe u z).symm)
  have harea := riemannianDiskArea_replacement_eq g u v huLip hvLip hball hin houter
  refine ⟨v, K, hvLip, hvtrace, hvW, ?_⟩
  linarith

end DifferentialGeometry.Geometry
