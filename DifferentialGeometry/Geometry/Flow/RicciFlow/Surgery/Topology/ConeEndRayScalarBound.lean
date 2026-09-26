import DifferentialGeometry.Geometry.Neck.FiniteEnd
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem ray_scalar_mul_sq_le_of_spatialNeck_sequence
    {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (metric : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf metric x y)
    {b alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000)
    (g : C(Ico 0 b, M)) (hg : Isometry g) (t : ℕ → Ico 0 b)
    (htstrict : StrictMono (fun n => (t n : ℝ))) (htend : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 b))
    (nk : ∀ n, SpatialNeck metric (2 * alpha) (g (t n)))
    (hspacing : ∀ n, (t (n + 1) : ℝ) - t n =
      ((2 * alpha)⁻¹ / 40) / Real.sqrt (metricScalarAt metric (g (t n))))
    {N : ℕ} {C : ℝ}
    (hupper : ∀ n, N ≤ n → metricScalarAt metric (g (t n)) * (b - (t n : ℝ)) ^ 2 ≤ C) :
    ∀ s : Ico 0 b, (t N : ℝ) ≤ s →
      metricScalarAt metric (g s) * (b - (s : ℝ)) ^ 2 ≤ 2 * C := by
  classical
  intro s hs
  have hex : ∃ k, (s : ℝ) < t (k + 1) := by
    obtain ⟨k, hk⟩ := (htend.eventually (eventually_gt_nhds s.2.2)).exists
    exact ⟨k, hk.trans (htstrict (Nat.lt_succ_self k))⟩
  set k := Nat.find hex with hkdef
  have hk1 : (s : ℝ) < t (k + 1) := Nat.find_spec hex
  have hNk : N ≤ k := by
    by_contra hlt
    push Not at hlt
    have := htstrict.monotone (show k + 1 ≤ N by omega)
    linarith
  have hk0 : (t k : ℝ) ≤ s := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]
      exact (htstrict.monotone (Nat.zero_le N)).trans hs
    · have hmin := Nat.find_min hex (show k - 1 < k by omega)
      push Not at hmin
      rwa [show k - 1 + 1 = k by omega] at hmin
  have hRk := (nk k).Q_pos
  have hsqk : 0 < Real.sqrt (metricScalarAt metric (g (t k))) := Real.sqrt_pos.mpr hRk
  have h2a : 2 * alpha < 1 / 1000000 := by linarith
  let r : ℝ := (2 * alpha)⁻¹ / 20
  have hr : 0 < r := by positivity
  have hrsmall : r < (2 * alpha)⁻¹ := by
    have : 0 < (2 * alpha)⁻¹ := by positivity
    dsimp only [r]
    linarith
  have hsq1 : 1 / 2 ≤ Real.sqrt (1 - 2 * alpha) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hball : g s ∈ riemannianBallOf metric (g (t k))
      (r * Real.sqrt (1 - 2 * alpha) / Real.sqrt (metricScalarAt metric (g (t k)))) := by
    change riemannianEDistOf metric (g (t k)) (g s) < _
    rw [← hmetric, hg.edist_eq, edist_dist, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith)]
    apply ENNReal.ofReal_lt_ofReal_iff'.mpr
    refine ⟨?_, by positivity⟩
    have hsp := hspacing k
    have hlt : (s : ℝ) - t k <
        ((2 * alpha)⁻¹ / 40) / Real.sqrt (metricScalarAt metric (g (t k))) := by
      linarith
    have hle : ((2 * alpha)⁻¹ / 40) / Real.sqrt (metricScalarAt metric (g (t k))) ≤
        r * Real.sqrt (1 - 2 * alpha) / Real.sqrt (metricScalarAt metric (g (t k))) := by
      apply div_le_div_of_nonneg_right _ hsqk.le
      have : 0 < (2 * alpha)⁻¹ := by positivity
      dsimp only [r]
      nlinarith
    linarith
  have himg := (nk k).ball_subset_image_slab hr hrsmall hball
  have hwin : g s ∈ (nk k).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) := by
    obtain ⟨z, hz, hzs⟩ := himg
    exact ⟨z, ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩, hzs⟩
  have hbd := ((nk k).scalar_bounds_on_image_window hwin).2
  have h2 : metricScalarAt metric (g s) ≤ 2 * metricScalarAt metric (g (t k)) := by
    have : 1 + 4323 * (2 * alpha) ≤ 2 := by linarith
    nlinarith
  have hup := hupper k hNk
  have hbt : 0 ≤ b - (s : ℝ) := (sub_pos.mpr s.2.2).le
  have hbk : b - (s : ℝ) ≤ b - (t k : ℝ) := by linarith
  have hsq : (b - (s : ℝ)) ^ 2 ≤ (b - (t k : ℝ)) ^ 2 := pow_le_pow_left₀ hbt hbk 2
  have hR0 : 0 ≤ metricScalarAt metric (g s) := by
    have := ((nk k).scalar_bounds_on_image_window hwin).1
    have : 0 ≤ 1 - 4323 * (2 * alpha) := by linarith
    nlinarith
  calc metricScalarAt metric (g s) * (b - (s : ℝ)) ^ 2
      ≤ (2 * metricScalarAt metric (g (t k))) * (b - (t k : ℝ)) ^ 2 :=
        mul_le_mul h2 hsq (sq_nonneg _) (by positivity)
    _ ≤ 2 * C := by nlinarith

theorem exists_punctured_cone_end_of_spatial_necks_with_ray_scalar_bound
    {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (metric : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf metric x y)
    {b alpha : ℝ} (hb : 0 < b) (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000)
    (hsec : ∀ (x : M) (v w : TangentSpace I3 x),
      0 ≤ metricRm04StandardAt metric x v w w v)
    (g : C(Ico 0 b, M)) (hg : Isometry g)
    (hblow : Tendsto (fun t => metricScalarAt metric (g t))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) atTop)
    (q : UniformSpace.Completion M)
    (hq : Tendsto (fun t => (g t : UniformSpace.Completion M))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) (𝓝 q))
    (hnecks : ∀ᶠ tau : Ico 0 b in comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b),
      Nonempty (SpatialNeck metric alpha (g tau))) :
    ∃ W : TopologicalSpace.Opens M, ∃ hW : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hW
      let mW : MetricSpace W :=
        let _ : PseudoMetricSpace W := (metric.restrictOpen W).toPseudoMetricSpace
        MetricSpace.ofT0PseudoMetricSpace W
      let _ : MetricSpace W := mW
      let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
      let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
      let eW : PseudoEMetricSpace W :=
        @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
      let _ : WeakPseudoEMetricSpace W :=
        @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
      ∃ qW : UniformSpace.Completion W, ∃ delta : ℝ, 0 < delta ∧
        qW ∉ range (fun x : W => (x : UniformSpace.Completion W)) ∧
        UniformSpace.Completion.map (Subtype.val : W → M) qW = q ∧
        IsCompact (Metric.closedBall qW delta) ∧
        Metric.closedBall qW delta ⊆ insert qW
          (range (fun x : W => (x : UniformSpace.Completion W))) ∧
        ∃ x : ℕ → W, ∃ times : ℕ → Ico 0 b,
          (∀ n, (x n : M) = g (times n)) ∧
          Tendsto (fun n => (times n : ℝ)) atTop (𝓝 b) ∧
          Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 qW) ∧
          (∀ n, dist (x n : UniformSpace.Completion W) qW = b - times n) ∧
          Tendsto (fun n => metricScalarAt (metric.restrictOpen W) (x n)) atTop atTop ∧
          (∀ n, ((2 * alpha)⁻¹) ^ 2 / 8 ≤
            metricScalarAt (metric.restrictOpen W) (x n) *
              dist (x n : UniformSpace.Completion W) qW ^ 2) ∧
          (∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
            metricScalarAt (metric.restrictOpen W) (x n) *
              dist (x n : UniformSpace.Completion W) qW ^ 2 ≤ B) ∧
          Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
          ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n in atTop, ∀ s : Ico 0 b, (s : ℝ) ≤ times n →
            metricScalarAt metric (g s) ≤ K * metricScalarAt metric (g (times n)) := by
  obtain ⟨t, nk, htstrict, htend, hspacing, _, _, _, eta, Ψ, hann, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, E, theta, _, _, _, _, D, _, hrest⟩ :=
    exists_spatialNeck_sequence_with_punctured_completion metric hmetric hb ha hsmall
      hsec g hg hblow q hq hnecks
  let W : TopologicalSpace.Opens M :=
    ⟨interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)), isOpen_interior⟩
  obtain ⟨gW, hgW, _, _, hW, hrest⟩ := hrest
  let _ : PathConnectedSpace W := hW
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, hqW, hdistW, hmissing, hmap, _, _, _, _, _, hquantW, _, hupper,
    delta, hdelta, hcompact, hcover, happrox, _, _⟩ := hrest
  let u : ℕ → Ico (t 2 : ℝ) b := fun n =>
    ⟨t (n + 2), htstrict.monotone (by omega), (t (n + 2)).property.2⟩
  let x : ℕ → W := fun n => gW (u n)
  let times : ℕ → Ico 0 b := fun n => t (n + 2)
  have hux : ∀ n, (x n : M) = g (times n) := fun n => hgW (u n)
  have htimes : Tendsto (fun n => (times n : ℝ)) atTop (𝓝 b) :=
    htend.comp (tendsto_add_atTop_nat 2)
  have hu : Tendsto u atTop
      (comap (Subtype.val : Ico (t 2 : ℝ) b → ℝ) (𝓝 b)) :=
    tendsto_comap_iff.mpr htimes
  have hx : Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 qW) :=
    hqW.comp hu
  have hxdist (n : ℕ) : dist (x n : UniformSpace.Completion W) qW = b - times n := by
    rw [dist_comm]
    exact hdistW (u n)
  have hQ : Tendsto (fun n => metricScalarAt (metric.restrictOpen W) (x n))
      atTop atTop := by
    simp only [metricScalarAt_restrictOpen, hux]
    exact hblow.comp (tendsto_comap_iff.mpr htimes)
  have hlower (n : ℕ) : ((2 * alpha)⁻¹) ^ 2 / 8 ≤
      metricScalarAt (metric.restrictOpen W) (x n) *
        dist (x n : UniformSpace.Completion W) qW ^ 2 := by
    have hmem : (x n : M) ∈ Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1) := by
      rw [hux]
      refine ⟨((nk (n + 2)).center, 0), ⟨mem_univ _, le_rfl, zero_le_one⟩, ?_⟩
      exact ((hann (n + 2)).2.1 _).trans (nk (n + 2)).center_eq
    simpa only [dist_comm qW] using hquantW n (x n) hmem
  have hupper' : ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      metricScalarAt (metric.restrictOpen W) (x n) *
        dist (x n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, hBpos, hB⟩ := hupper
    refine ⟨B, hBpos, ?_⟩
    simpa only [metricScalarAt_restrictOpen, hux, hxdist, times] using hB
  obtain ⟨C, hCpos, hC⟩ := hupper
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hC
  have hcone := ray_scalar_mul_sq_le_of_spatialNeck_sequence metric hmetric ha hsmall g hg t
    htstrict htend nk hspacing (N := N₁ + 2) (C := C) (fun n hn => by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      exact hN₁ k (by omega))
  have hK0 : IsCompact (g '' {s : Ico 0 b | (s : ℝ) ≤ t (N₁ + 2)}) := by
    refine (IsCompact.image ?_ g.continuous)
    have hcl : {s : Ico 0 b | (s : ℝ) ≤ t (N₁ + 2)} =
        (Subtype.val : Ico 0 b → ℝ) ⁻¹' Icc 0 (t (N₁ + 2)) := by
      ext s
      simp only [mem_ofPred_eq, mem_preimage, mem_Icc]
      exact ⟨fun h => ⟨s.2.1, h⟩, fun h => h.2⟩
    rw [hcl]
    apply (Topology.IsInducing.subtypeVal).isCompact_preimage' isCompact_Icc
    intro r hr
    exact ⟨⟨r, hr.1, hr.2.trans_lt (t (N₁ + 2)).2.2⟩, rfl⟩
  obtain ⟨C₀, hC₀⟩ := (hK0.image (metricScalar_smooth metric).continuous).bddAbove
  have hc₀ : (0 : ℝ) < ((2 * alpha)⁻¹) ^ 2 / 8 := by positivity
  refine ⟨W, hW, qW, delta, hdelta, hmissing, hmap, hcompact, hcover, x, times,
    hux, htimes, hx, hxdist, hQ, hlower, hupper', happrox,
    max 1 (2 * C / (((2 * alpha)⁻¹) ^ 2 / 8)), le_max_left _ _, ?_⟩
  filter_upwards [hQ.eventually_ge_atTop (max C₀ 0)] with n hn
  intro s hs
  have hRn : metricScalarAt metric (g (times n)) =
      metricScalarAt (metric.restrictOpen W) (x n) := by
    rw [metricScalarAt_restrictOpen, hux]
  have hRpos : 0 ≤ metricScalarAt metric (g (times n)) := by
    rw [hRn]; exact (le_max_right _ _).trans hn
  rcases le_or_gt (s : ℝ) (t (N₁ + 2)) with hsN | hsN
  · have h1 : metricScalarAt metric (g s) ≤ C₀ := hC₀ ⟨g s, ⟨s, hsN, rfl⟩, rfl⟩
    have h2 : C₀ ≤ metricScalarAt metric (g (times n)) := by
      rw [hRn]; exact (le_max_left _ _).trans hn
    calc metricScalarAt metric (g s) ≤ metricScalarAt metric (g (times n)) := h1.trans h2
      _ ≤ max 1 (2 * C / (((2 * alpha)⁻¹) ^ 2 / 8)) * metricScalarAt metric (g (times n)) :=
        le_mul_of_one_le_left hRpos (le_max_left _ _)
  · have hs1 := hcone s hsN.le
    have hbs : 0 < b - (s : ℝ) := sub_pos.mpr s.2.2
    have hbt : b - (times n : ℝ) ≤ b - (s : ℝ) := by linarith
    have hbt0 : 0 < b - (times n : ℝ) := sub_pos.mpr (times n).2.2
    have hlow := hlower n
    rw [hxdist, ← hRn] at hlow
    have hsq : (b - (times n : ℝ)) ^ 2 ≤ (b - (s : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hbt0.le hbt 2
    have hA : metricScalarAt metric (g s) * (b - (times n : ℝ)) ^ 2 ≤ 2 * C := by
      rcases le_or_gt 0 (metricScalarAt metric (g s)) with hR0 | hR0
      · exact (mul_le_mul_of_nonneg_left hsq hR0).trans hs1
      · nlinarith [sq_nonneg (b - (times n : ℝ))]
    have hB : 2 * C ≤ (2 * C / (((2 * alpha)⁻¹) ^ 2 / 8)) *
        (metricScalarAt metric (g (times n)) * (b - (times n : ℝ)) ^ 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
      nlinarith [hlow]
    have hpos : 0 < (b - (times n : ℝ)) ^ 2 := by positivity
    have hC : metricScalarAt metric (g s) ≤ 2 * C / (((2 * alpha)⁻¹) ^ 2 / 8) *
        metricScalarAt metric (g (times n)) := by
      have := hA.trans hB
      rw [← mul_assoc] at this
      exact le_of_mul_le_mul_right this hpos
    exact hC.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hRpos)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
