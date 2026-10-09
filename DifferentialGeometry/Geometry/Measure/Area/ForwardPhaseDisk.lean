/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Measure.Area.ForwardPhaseAnnulus
import DifferentialGeometry.Analysis.Calculus.Interpolation.FiniteClosedCover
import Mathlib.Tactic.FinCases

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Paste the actual alternate filling into the original disk through the
forward phase annulus. The original metric, literal trace and both images
are retained; no inverse bound for the boundary phase is required. -/
theorem exists_forwardPhase_pastedDisk
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q a : C(closedDisk, M))
    {Lq La : ℝ≥0}
    (hqLip : ∀ z w : closedDisk, riemannianEDistOf G (q z) (q w) ≤
      (Lq : ℝ≥0∞) * edist z w)
    (haLip : ∀ z w : closedDisk, riemannianEDistOf G (a z) (a w) ≤
      (La : ℝ≥0∞) * edist z w)
    (hqSmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q)
      (Metric.ball (0 : ℂ) 1))
    {r b : ℝ} (hr : 0 < r) (hrb : r < b) (hb : b < 1)
    (φ : ℝ ≃ₜ ℝ) (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
    (hm : StrictMono φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    (htrace : ∀ t : ℝ, diskTrace a (t : loopCircle) =
      diskExtension q (r • (AddCircle.toCircle (φ t : loopCircle) : ℂ))) :
    let H := ForwardPhaseAnnulus.map r b hφ hp
    ∃ (F : C(closedDisk, M)) (KF : ℝ≥0),
      (∀ z : closedDisk, F z =
        if ‖(z : ℂ)‖ ≤ r then diskExtension a (r⁻¹ • (z : ℂ))
        else if ‖(z : ℂ)‖ ≤ b then diskExtension q (H z)
        else diskExtension q z) ∧
      (∀ z w : closedDisk, riemannianEDistOf G (F z) (F w) ≤
        (KF : ℝ≥0∞) * edist z w) ∧
      (∀ z : ℂ, ‖z‖ ≤ r →
        diskExtension F z = diskExtension a (r⁻¹ • z)) ∧
      (∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ b →
        diskExtension F z = diskExtension q (H z)) ∧
      (∀ z : ℂ, (r + b) / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
        diskExtension F z = diskExtension q z) ∧
      diskTrace F = diskTrace q ∧
      Set.range F = Set.range a ∪
        diskExtension q '' {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ 1} ∧
      riemannianDiskArea G F =
        riemannianArea G (diskExtension q)
          (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) r) +
        riemannianDiskArea G a ∧
      riemannianDiskArea G F = riemannianDiskArea G q -
        riemannianArea G (diskExtension q) (Metric.closedBall (0 : ℂ) r) +
        riemannianDiskArea G a := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let H := ForwardPhaseAnnulus.map r b hφ hp
  let U := diskExtension q
  let A := diskExtension a
  let S : ℂ →L[ℝ] ℂ := r⁻¹ • ContinuousLinearMap.id ℝ ℂ
  let T : ℂ →L[ℝ] ℂ := r • ContinuousLinearMap.id ℝ ℂ
  have hr1 : r < 1 := hrb.trans hb
  have hrc : r < (r + b) / 2 := by linarith
  have hcb : (r + b) / 2 < b := by linarith
  have hST (z : ℂ) : S (T z) = z := by
    change r⁻¹ • (r • z) = z
    exact inv_smul_smul₀ hr.ne' z
  have hTS (z : ℂ) : T (S z) = z := by
    change r • (r⁻¹ • z) = z
    exact smul_inv_smul₀ hr.ne' z
  have hU : LipschitzWith Lq U := diskExtension_riemannian_lipschitz G hqLip
  have hA : LipschitzWith La A := diskExtension_riemannian_lipschitz G haLip
  obtain ⟨KH, hKH⟩ := ForwardPhaseAnnulus.exists_lipschitzOnWith_map hr hφ hp (b := b)
  have hHself {z : ℂ} (hz : (r + b) / 2 ≤ ‖z‖) : H z = z :=
    ForwardPhaseAnnulus.map_eq_self hrb hφ hp hz
  have hseam (z : ℂ) (hz : ‖z‖ = r) : A (S z) = U (H z) := by
    have hw : ‖S z‖ = 1 := by
      change ‖r⁻¹ • z‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hz,
        inv_mul_cancel₀ hr.ne']
    let w : Circle := ⟨S z, mem_sphere_zero_iff_norm.mpr hw⟩
    obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective w
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective θ
    have hst : S z = (AddCircle.toCircle (t : loopCircle) : ℂ) := by
      have hv := congrArg (fun v : Circle => (v : ℂ)) hθ
      simpa only [AddCircle.homeomorphCircle_apply, ← ht] using hv.symm
    have hzt : z = r • (AddCircle.toCircle (t : loopCircle) : ℂ) := by
      calc
        z = T (S z) := (hTS z).symm
        _ = r • (AddCircle.toCircle (t : loopCircle) : ℂ) := by rw [hst]; rfl
    calc
      A (S z) = diskTrace a (t : loopCircle) := by
        rw [hst]
        exact diskExtension_coe a (diskBoundary (t : loopCircle))
      _ = U (r • (AddCircle.toCircle (φ t : loopCircle) : ℂ)) := htrace t
      _ = U (H z) := by
        rw [hzt]
        change U _ = U (ForwardPhaseAnnulus.map r b hφ hp _)
        rw [ForwardPhaseAnnulus.map_pos_smul_toCircle r b hφ hp hr]
        simp only [ForwardPhaseAnnulus.phaseLift,
          ForwardPhaseAnnulus.cutoff_eq_one hrb le_rfl, sub_self, zero_mul,
          one_mul, zero_add]
  let D : ℂ → M := fun z =>
    if ‖z‖ ≤ r then A (S z) else if ‖z‖ ≤ b then U (H z) else U z
  have hDinner {z : ℂ} (hz : ‖z‖ ≤ r) : D z = A (S z) := by
    simp only [D, ite_eq_left hz]
  have hDmiddle {z : ℂ} (hrz : r ≤ ‖z‖) (hzb : ‖z‖ ≤ b) : D z = U (H z) := by
    by_cases hzr : ‖z‖ ≤ r
    · exact (hDinner hzr).trans (hseam z (le_antisymm hzr hrz))
    · simp only [D, ite_eq_right hzr, ite_eq_left hzb]
  have hDouter {z : ℂ} (hz : (r + b) / 2 ≤ ‖z‖) : D z = U z := by
    have hzr : ¬ ‖z‖ ≤ r := not_le.mpr (hrc.trans_le hz)
    by_cases hzb : ‖z‖ ≤ b
    · simp only [D, ite_eq_right hzr, ite_eq_left hzb, hHself hz]
    · simp only [D, ite_eq_right hzr, ite_eq_right hzb]
  let cells : Fin 3 → Set ℂ := ![
    Metric.closedBall 0 r,
    {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ b},
    {z : ℂ | b ≤ ‖z‖}]
  let constants : Fin 3 → ℝ≥0 := ![La * ‖S‖₊, Lq * KH, Lq]
  have hmiddleClosed : IsClosed {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ b} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have houterClosed : IsClosed {z : ℂ | b ≤ ‖z‖} :=
    isClosed_le continuous_const continuous_norm
  have hclosed : ∀ i, IsClosed ((Subtype.val : closedDisk → ℂ) ⁻¹' cells i) := by
    intro i
    fin_cases i
    · simpa [cells] using
        (Metric.isClosed_closedBall.preimage continuous_subtype_val :
          IsClosed ((Subtype.val : closedDisk → ℂ) ⁻¹' Metric.closedBall (0 : ℂ) r))
    · simpa [cells] using hmiddleClosed.preimage
        (continuous_subtype_val : Continuous (Subtype.val : closedDisk → ℂ))
    · simpa [cells] using houterClosed.preimage
        (continuous_subtype_val : Continuous (Subtype.val : closedDisk → ℂ))
  have hcover : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∃ i, z ∈ cells i := by
    intro z _
    by_cases hzr : ‖z‖ ≤ r
    · exact ⟨0, by simpa [cells, Metric.mem_closedBall, dist_zero_right] using hzr⟩
    · by_cases hzb : ‖z‖ ≤ b
      · exact ⟨1, by simpa [cells] using And.intro (le_of_lt (lt_of_not_ge hzr)) hzb⟩
      · exact ⟨2, by simpa [cells] using le_of_lt (lt_of_not_ge hzb)⟩
  have hcellLip : ∀ i, LipschitzOnWith (constants i) D
      (Metric.closedBall (0 : ℂ) 1 ∩ cells i) := by
    intro i
    fin_cases i
    · intro x hx y hy
      have hxr : ‖x‖ ≤ r := by simpa [cells, Metric.mem_closedBall, dist_zero_right] using hx.2
      have hyr : ‖y‖ ≤ r := by simpa [cells, Metric.mem_closedBall, dist_zero_right] using hy.2
      rw [hDinner hxr, hDinner hyr]
      exact (hA.comp S.lipschitzWith) x y
    · intro x hx y hy
      have hxA : r ≤ ‖x‖ ∧ ‖x‖ ≤ b := by simpa [cells] using hx.2
      have hyA : r ≤ ‖y‖ ∧ ‖y‖ ≤ b := by simpa [cells] using hy.2
      rw [hDmiddle hxA.1 hxA.2, hDmiddle hyA.1 hyA.2]
      exact (hU.comp_lipschitzOnWith hKH) hxA hyA
    · intro x hx y hy
      have hxb : b ≤ ‖x‖ := by simpa [cells] using hx.2
      have hyb : b ≤ ‖y‖ := by simpa [cells] using hy.2
      rw [hDouter (hcb.le.trans hxb), hDouter (hcb.le.trans hyb)]
      exact hU x y
  have hDLip : LipschitzOnWith (Finset.univ.sup constants) D
      (Metric.closedBall (0 : ℂ) 1) :=
    lipschitzOnWith_of_finite_closed_cover (convex_closedBall (0 : ℂ) 1)
      cells hclosed hcover constants hcellLip
  let F : C(closedDisk, M) := ⟨fun z => D z, hDLip.to_restrict.continuous⟩
  have hFLip : ∀ z w : closedDisk, riemannianEDistOf G (F z) (F w) ≤
      ((Finset.univ.sup constants : ℝ≥0) : ℝ≥0∞) * edist z w :=
    fun z w => hDLip z.property w.property
  have hFvalue {z : ℂ} (hz : ‖z‖ ≤ 1) : diskExtension F z = D z :=
    diskExtension_coe F ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz⟩
  have hFinner (z : ℂ) (hz : ‖z‖ ≤ r) : diskExtension F z = A (S z) :=
    (hFvalue (hz.trans hr1.le)).trans (hDinner hz)
  have hFmiddle (z : ℂ) (hrz : r ≤ ‖z‖) (hzb : ‖z‖ ≤ b) :
      diskExtension F z = U (H z) :=
    (hFvalue (hzb.trans hb.le)).trans (hDmiddle hrz hzb)
  have hFouter (z : ℂ) (hcz : (r + b) / 2 ≤ ‖z‖) (hz : ‖z‖ ≤ 1) :
      diskExtension F z = U z := (hFvalue hz).trans (hDouter hcz)
  have hFtrace : diskTrace F = diskTrace q := by
    ext θ
    change F (diskBoundary θ) = q (diskBoundary θ)
    have hz : ‖(diskBoundary θ : ℂ)‖ = 1 := Circle.norm_coe _
    exact (diskExtension_coe F (diskBoundary θ)).symm.trans
      ((hFouter _ (by rw [hz]; exact hcb.le.trans hb.le) hz.le).trans
        (diskExtension_coe q (diskBoundary θ)))
  have hFrange : Set.range F = Set.range a ∪
      U '' {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
    apply Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      have hz : ‖(z : ℂ)‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      by_cases hzr : ‖(z : ℂ)‖ ≤ r
      · apply Or.inl
        have hsz : ‖S z‖ ≤ 1 := by
          change ‖r⁻¹ • (z : ℂ)‖ ≤ 1
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
          calc
            r⁻¹ * ‖(z : ℂ)‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hzr (inv_nonneg.mpr hr.le)
            _ = 1 := inv_mul_cancel₀ hr.ne'
        let w : closedDisk := ⟨S z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hsz⟩
        refine ⟨w, ?_⟩
        exact (diskExtension_coe a w).symm.trans (hDinner hzr).symm
      · apply Or.inr
        have hrz : r ≤ ‖(z : ℂ)‖ := (lt_of_not_ge hzr).le
        by_cases hzb : ‖(z : ℂ)‖ ≤ b
        · refine ⟨H z, ?_, (hDmiddle hrz hzb).symm⟩
          simpa only [Set.mem_ofPred_eq, H, ForwardPhaseAnnulus.norm_map] using And.intro hrz hz
        · exact ⟨z, ⟨hrz, hz⟩,
            (hDouter (hcb.le.trans (lt_of_not_ge hzb).le)).symm⟩
    · rintro y (⟨w, rfl⟩ | ⟨z, ⟨hrz, hz⟩, rfl⟩)
      · have hw : ‖(w : ℂ)‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
        have htw : ‖T w‖ ≤ r := by
          change ‖r • (w : ℂ)‖ ≤ r
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
          nlinarith
        let z : closedDisk := ⟨T w, by
          simpa only [Metric.mem_closedBall, dist_zero_right] using htw.trans hr1.le⟩
        refine ⟨z, ?_⟩
        calc
          F z = A (S (T w)) := hDinner htw
          _ = A w := by rw [hST]
          _ = a w := diskExtension_coe a w
      · by_cases hzb : ‖z‖ ≤ b
        · have hbij := ForwardPhaseAnnulus.bijOn_map_radial r b φ hφ hm hp (Icc r b)
          obtain ⟨w, hw, heq⟩ := hbij.surjOn (show z ∈ {z : ℂ | ‖z‖ ∈ Icc r b} from ⟨hrz, hzb⟩)
          let wD : closedDisk := ⟨w, by
            simpa only [Metric.mem_closedBall, dist_zero_right] using hw.2.trans hb.le⟩
          refine ⟨wD, ?_⟩
          exact (hDmiddle hw.1 hw.2).trans (congrArg U heq)
        · let zD : closedDisk := ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz⟩
          exact ⟨zD, hDouter (hcb.le.trans (lt_of_not_ge hzb).le)⟩
  have hSimage : S '' Metric.closedBall (0 : ℂ) r = Metric.closedBall (0 : ℂ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖r⁻¹ • z‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      calc
        r⁻¹ * ‖z‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hz' (inv_nonneg.mpr hr.le)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · intro z hz
      have hz' : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      refine ⟨T z, ?_, hST z⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖r • z‖ ≤ r
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
  have hinnerArea : riemannianArea G (diskExtension F) (Metric.closedBall (0 : ℂ) r) =
      riemannianDiskArea G a := by
    calc
      _ = riemannianArea G (A ∘ S) (Metric.closedBall (0 : ℂ) r) :=
        riemannianArea_congr_on_closedBall G (fun z hz => hFinner z
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))
      _ = riemannianArea G A (S '' Metric.closedBall (0 : ℂ) r) :=
        riemannianArea_precomp G hA S.lipschitzWith T.lipschitzWith
          measurableSet_closedBall (fun z _ => hTS z)
      _ = _ := by rw [hSimage]; rfl
  let annulus : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < b}
  have hannulus : IsOpen annulus :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hbandAE : Metric.closedBall (0 : ℂ) b \ Metric.closedBall (0 : ℂ) r =ᵐ[volume]
      annulus := by
    have hnull : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere (0 : ℂ) b := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) b
    filter_upwards [hnull] with z hz
    have hne : ‖z‖ ≠ b := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    apply propext
    simp only [Set.mem_sdiff, Metric.mem_closedBall, dist_zero_right, annulus, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzb, hzr⟩
      exact ⟨lt_of_not_ge hzr, lt_of_le_of_ne hzb hne⟩
    · rintro ⟨hrz, hzb⟩
      exact ⟨hzb.le, not_le.mpr hrz⟩
  have hbandArea :
      riemannianArea G (diskExtension F)
        (Metric.closedBall (0 : ℂ) b \ Metric.closedBall (0 : ℂ) r) =
      riemannianArea G U (Metric.closedBall (0 : ℂ) b \ Metric.closedBall (0 : ℂ) r) := by
    calc
      _ = riemannianArea G (diskExtension F) annulus := setIntegral_congr_set hbandAE
      _ = riemannianArea G (U ∘ H) annulus :=
        riemannianArea_congr_on_open G hannulus (fun z hz => hFmiddle z hz.1.le hz.2.le)
      _ = riemannianArea G U annulus :=
        riemannianArea_forwardPhaseAnnulus G q hqSmooth hr hb φ hφ hm hp
      _ = _ := setIntegral_congr_set hbandAE.symm
  have hqInt := integrable_riemannianDiskAreaDensity G hqLip
  have hFInt := integrable_riemannianDiskAreaDensity G hFLip
  have hbsub : Metric.closedBall (0 : ℂ) b ⊆ Metric.closedBall (0 : ℂ) 1 :=
    Metric.closedBall_subset_closedBall hb.le
  have hrsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.closedBall (0 : ℂ) b :=
    Metric.closedBall_subset_closedBall hrb.le
  have houterArea :
      riemannianArea G (diskExtension F)
        (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) b) =
      riemannianArea G U (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) b) := by
    have hzint : ∀ᵐ z ∂volume.restrict
        (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) b),
        z ∈ Metric.ball (0 : ℂ) 1 :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
    apply integral_congr_ae
    filter_upwards [hzint,
      ae_restrict_mem (measurableSet_closedBall.diff measurableSet_closedBall)] with z hz hzd
    apply riemannianAreaDensity_congr G
    filter_upwards [(Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl).mem_nhds
      ⟨hz, hzd.2⟩] with w hw
    have hw1 : ‖w‖ ≤ 1 := (show ‖w‖ < 1 by
      simpa only [Metric.mem_ball, dist_zero_right] using hw.1).le
    have hwb : b < ‖w‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hw.2
    exact hFouter w (hcb.le.trans hwb.le) hw1
  have hFband :
      riemannianArea G (diskExtension F)
        (Metric.closedBall (0 : ℂ) b \ Metric.closedBall (0 : ℂ) r) =
      riemannianArea G (diskExtension F) (Metric.closedBall (0 : ℂ) b) -
        riemannianArea G (diskExtension F) (Metric.closedBall (0 : ℂ) r) :=
    setIntegral_sdiff measurableSet_closedBall (hFInt.mono_set hbsub) hrsub
  have hqband :
      riemannianArea G U (Metric.closedBall (0 : ℂ) b \ Metric.closedBall (0 : ℂ) r) =
      riemannianArea G U (Metric.closedBall (0 : ℂ) b) -
        riemannianArea G U (Metric.closedBall (0 : ℂ) r) :=
    setIntegral_sdiff measurableSet_closedBall (hqInt.mono_set hbsub) hrsub
  have hFout :
      riemannianArea G (diskExtension F)
        (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) b) =
      riemannianDiskArea G F -
        riemannianArea G (diskExtension F) (Metric.closedBall (0 : ℂ) b) :=
    setIntegral_sdiff measurableSet_closedBall hFInt hbsub
  have hqout :
      riemannianArea G U (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) b) =
      riemannianDiskArea G q - riemannianArea G U (Metric.closedBall (0 : ℂ) b) :=
    setIntegral_sdiff measurableSet_closedBall hqInt hbsub
  have hsubtract : riemannianDiskArea G F = riemannianDiskArea G q -
      riemannianArea G U (Metric.closedBall (0 : ℂ) r) + riemannianDiskArea G a := by
    linarith only [hinnerArea, hbandArea, houterArea, hFband, hqband, hFout, hqout]
  have hqremove :
      riemannianArea G U (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) r) =
      riemannianDiskArea G q - riemannianArea G U (Metric.closedBall (0 : ℂ) r) :=
    setIntegral_sdiff measurableSet_closedBall hqInt (hrsub.trans hbsub)
  refine ⟨F, Finset.univ.sup constants, (fun _ => rfl), hFLip,
    hFinner, hFmiddle, hFouter, hFtrace, hFrange, ?_, hsubtract⟩
  rw [hqremove]
  exact hsubtract

end DifferentialGeometry.Geometry
