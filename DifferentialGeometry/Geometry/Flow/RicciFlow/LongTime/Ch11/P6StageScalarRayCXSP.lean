import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateTimeCoreDefP6TC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LastCrossingCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageVolumeFromJetsCXSP
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

/-!
# CX-SPINE：原 stage 最短段的 scalar limit 在逃逸端点爆破

公共 Curves.exists_isometric_segment_subseq_limit_with_missing_endpoint 负责产生实际 ray；
pointedScalar_tendsto_of_inverse_tendsto 负责下面的逐点 scalar 收敛。
本文件只补 terminal scalar blowup 的实质步骤，不重做 metric curve compactness。

若段起点 scalar < Lambda，而终点 scalar > C2*Lambda，则 IVT 找到 scalar=Lambda 的点。
该点的实际 canonical witness 在半径 Lambda^(-1/2) 内控制 scalar。
最短段的剩余长度若更短，就与终点的高 scalar 矛盾。
该步不需要 gradient 或 time derivative。
TimeCore 在原 F/history、原 terminal time 上实际支付 witness，包括 birth/horizon。
Awork 是本次 TimeCore/seed volume 参数；显式保留同 Awork 的整段几何包含。
这里不消费或扩大 hspine 的 kappa window(A)，也不把 Awork 与该 A 混同。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

private theorem segment_scalar_le_of_canonical_level_CXSP
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) {ε C1 C2 a b Λ : ℝ}
    {γ : ℝ → M} (hab : a ≤ b) (hΛ : 0 < Λ)
    (hγ : ContinuousOn γ (Icc a b))
    (hmin : ∀ v ∈ Icc a b, ∀ w ∈ Icc a b,
      riemannianEDistOf g (γ v) (γ w) = ENNReal.ofReal |v - w|)
    (hleft : metricScalarAt g (γ a) < Λ)
    (hright : Λ < metricScalarAt g (γ b))
    (hcan : ∀ v ∈ Icc a b, metricScalarAt g (γ v) = Λ →
      Nonempty (SpatialCanonicalWitness g ε C1 C2 (γ v)))
    (hlen : b - a < (Real.sqrt Λ)⁻¹) :
    metricScalarAt g (γ b) ≤ C2 * Λ := by
  have hf : ContinuousOn (fun v => metricScalarAt g (γ v)) (Icc a b) :=
    (metricScalar_smooth g).continuous.comp_continuousOn hγ
  obtain ⟨v, hv, hRv, _hlast, _hclosed, _hopen⟩ :=
    exists_last_threshold_CXSP hf hab hleft hright
  obtain ⟨W⟩ := hcan v ⟨hv.1.le, hv.2.le⟩ hRv
  have hball : γ b ∈ riemannianBallOf g (γ v)
      (Real.sqrt (metricScalarAt g (γ v)))⁻¹ := by
    change riemannianEDistOf g (γ v) (γ b) < ENNReal.ofReal _
    rw [hmin v ⟨hv.1.le, hv.2.le⟩ b ⟨hab, le_rfl⟩, hRv,
      abs_of_nonpos (sub_nonpos.mpr hv.2.le), neg_sub]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (inv_pos.mpr (Real.sqrt_pos.mpr hΛ))).mpr
        ((sub_le_sub_left hv.1.le b).trans_lt hlen)
  have hbound := (W.scalar_bounds (γ b)
    (W.ball_inside (riemannianBallOf_mono g (γ v) W.radius_lower hball))).2
  simpa only [hRv] using hbound

/-- 实际同 Awork 的 seed segments 与 TimeCore 给 pointwise limit 的 scalar blowup；
scalar convergence 接 canonical metric convergence，不从 Good/Dt 取得。 -/
theorem scalar_limit_tendsto_atTop_of_timeCore_segments_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcore : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime)
    (Awork : ℝ) (hA : 0 < Awork) (idx : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (idx n)).horizon)
    (p : ∀ n, ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier)
    (r : ℕ → ℝ)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (idx n)).toHistory
      (t n) (p n) (r n))
    (hvol : ∀ n, ENNReal.ofReal (Awork⁻¹ * r n ^ 3) ≤ ballVolume
      ((F.tower.history (idx n)).toHistory.stageMetric
        ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (htlim : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (Hbase : ℝ) (hHbase : 0 < Hbase) (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (hscale : ∀ n, Q n * r n ^ 2 = Hbase)
    (rho : ℝ) (hrho : 0 < rho) (ell : ℕ → ℝ)
    (hell : Tendsto ell atTop (𝓝 rho))
    (γ : ∀ n, ℝ → ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier)
    (hγ : ∀ n, ContinuousOn (γ n) (Icc (0 : ℝ) (ell n)))
    (hmin : ∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
      riemannianEDistOf
        (scaleMetric (Q n) (hQ n) ((F.tower.history (idx n)).toHistory.stageMetric
          ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)))
        (γ n v) (γ n w) = ENNReal.ofReal |v - w|)
    (hsegment : ∀ᶠ n in atTop, ∀ v ∈ Icc (0 : ℝ) (ell n),
      γ n v ∈ riemannianBallOf
        ((F.tower.history (idx n)).toHistory.stageMetric
          ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))
        (p n) (Awork * r n))
    (hhigh : Tendsto (fun n => metricScalarAt
      ((F.tower.history (idx n)).toHistory.stageMetric
        ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))
      (γ n (ell n)) / Q n) atTop atTop)
    (f : Ico (0 : ℝ) rho → ℝ)
    (hscalar : ∀ u : Ico (0 : ℝ) rho, Tendsto (fun n => metricScalarAt
      ((F.tower.history (idx n)).toHistory.stageMetric
        ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))
      (γ n u) / Q n) atTop (𝓝 (f u))) :
    Tendsto f (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop := by
  obtain ⟨Kcan, Tcan, _hKcan, _hTcan, hcanonical⟩ := hcore Awork hA
  let gm := fun n => (F.tower.history (idx n)).toHistory.stageMetric
    ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)
  have hnorm (n : ℕ) (v : ℝ) :
      metricScalarAt (scaleMetric (Q n) (hQ n) (gm n)) (γ n v) =
        metricScalarAt (gm n) (γ n v) / Q n := by
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div]
  apply tendsto_atTop.mpr
  intro B
  let Λ : ℝ := max (Kcan / Hbase) (max B 0) + 1
  have hΛ : 0 < Λ := by
    have h0 : 0 ≤ max (Kcan / Hbase) (max B 0) :=
      (le_max_right B 0).trans (le_max_right _ _)
    dsimp only [Λ]
    linarith
  have hBΛ : B < Λ := by
    have h := (le_max_left B 0).trans (le_max_right (Kcan / Hbase) (max B 0))
    dsimp only [Λ]
    linarith
  have hKΛ : Kcan ≤ Λ * Hbase := by
    apply (div_le_iff₀ hHbase).mp
    have h := le_max_left (Kcan / Hbase) (max B 0)
    dsimp only [Λ]
    linarith
  let d : ℝ := min (rho / 2) (Real.sqrt Λ)⁻¹
  have hd : 0 < d := lt_min (half_pos hrho) (inv_pos.mpr (Real.sqrt_pos.mpr hΛ))
  have hgap : Tendsto (fun u : Ico (0 : ℝ) rho => rho - (u : ℝ))
      (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := rho)).sub
      (tendsto_comap : Tendsto (Subtype.val : Ico (0 : ℝ) rho → ℝ) _ (𝓝 rho))
  filter_upwards [hgap.eventually (Iio_mem_nhds hd)] with u hu
  by_contra hnot
  have hlow : f u < Λ := (lt_of_not_ge hnot).trans hBΛ
  have hev : ∀ᶠ n in atTop,
      (u : ℝ) < ell n ∧ ell n - u < d ∧
      metricScalarAt (gm n) (γ n u) / Q n < Λ ∧
      max Λ (C2 * Λ) < metricScalarAt (gm n) (γ n (ell n)) / Q n ∧
      Tcan ≤ (t n : ℝ) ∧
      (∀ v ∈ Icc (0 : ℝ) (ell n), γ n v ∈ riemannianBallOf (gm n) (p n)
        (Awork * r n)) := by
    filter_upwards [hell.eventually_const_lt u.property.2,
      (hell.sub_const (u : ℝ)).eventually (Iio_mem_nhds hu),
      (hscalar u).eventually (Iio_mem_nhds hlow),
      hhigh.eventually_gt_atTop (max Λ (C2 * Λ)),
      htlim.eventually_ge_atTop Tcan, hsegment] with n hn hlen hlo hhi hlate hseg
    exact ⟨hn, hlen, hlo, hhi, hlate, hseg⟩
  obtain ⟨n, hun, hlen, hlo, hhi, hlate, hseg⟩ := hev.exists
  have hsub : Icc (u : ℝ) (ell n) ⊆ Icc (0 : ℝ) (ell n) :=
    Icc_subset_Icc u.property.1 le_rfl
  have hcanNorm : ∀ v ∈ Icc (u : ℝ) (ell n),
      metricScalarAt (scaleMetric (Q n) (hQ n) (gm n)) (γ n v) = Λ →
      Nonempty (SpatialCanonicalWitness (scaleMetric (Q n) (hQ n) (gm n))
        ε C1 C2 (γ n v)) := by
    intro v hv hlevel
    have hlevelRaw : metricScalarAt (gm n) (γ n v) = Λ * Q n := by
      rw [hnorm] at hlevel
      exact (div_eq_iff (hQ n).ne').mp hlevel
    have hthreshold : Kcan * (r n ^ 2)⁻¹ ≤ metricScalarAt (gm n) (γ n v) := by
      rw [hlevelRaw, ← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos (hsmall n).1)]
      simpa only [mul_assoc, hscale n] using hKΛ
    obtain ⟨W, _hchart⟩ := (hcanonical (idx n) (t n) (p n) (r n)
      hlate (htime n) (hsmall n) (hvol n) (γ n v) (hseg v (hsub hv)) hthreshold).1
    exact ⟨W.scaleMetric (Q n) (hQ n)⟩
  have hbound := segment_scalar_le_of_canonical_level_CXSP
    (scaleMetric (Q n) (hQ n) (gm n)) hun.le hΛ ((hγ n).mono hsub)
    (fun v hv w hw => hmin n v (hsub hv) w (hsub hw))
    (by rwa [hnorm])
    (by rw [hnorm]; exact (le_max_left _ _).trans_lt hhi) hcanNorm
    (hlen.trans_le (min_le_right _ _))
  rw [hnorm] at hbound
  exact (not_lt_of_ge hbound) ((le_max_right _ _).trans_lt hhi)

end GC.LongTime.Ch11

end
