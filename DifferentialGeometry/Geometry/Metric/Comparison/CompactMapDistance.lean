import DifferentialGeometry.Geometry.Metric.Comparison.PathLength
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Topology.EMetricSpace.Convergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Riemannian

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

noncomputable section IntrinsicDistanceLimit
open Filter MeasureTheory Set
open scoped _root_.Topology

private theorem le_of_tendsto_of_eventually_le_mul
    {ι : Type*} {l : Filter ι} [l.NeBot] {d : ℝ≥0∞} {a : ι → ℝ≥0∞} {b : ℝ≥0∞}
    (ha : Tendsto a l (𝓝 d))
    (hb : ∀ L : ℝ, 1 < L → ∀ᶠ i in l, a i ≤ ENNReal.ofReal L * b) :
    d ≤ b := by
  have hL (L : ℝ) (hL : 1 < L) : d ≤ ENNReal.ofReal L * b :=
    le_of_tendsto ha (hb L hL)
  have hlim : Tendsto (fun L : ℝ => ENNReal.ofReal L * b)
      (𝓝[>] 1) (𝓝 b) := by
    have hreal : Tendsto (fun L : ℝ => L) (𝓝[>] 1) (𝓝 1) := nhdsWithin_le_nhds
    have hof : Tendsto (fun L : ℝ => ENNReal.ofReal L) (𝓝[>] 1) (𝓝 (1 : ℝ≥0∞)) :=
      by simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hreal
    simpa only [ENNReal.coe_one, one_mul] using ENNReal.Tendsto.mul_const hof
      (Or.inl (by simp : (1 : ℝ≥0∞) ≠ 0))
  have hev : ∀ᶠ L : ℝ in 𝓝[>] 1, 1 < L := self_mem_nhdsWithin
  exact ge_of_tendsto hlim (hev.mono fun L h => hL L h)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [∀ x : N, ENorm (TangentSpace I x)]
  {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
  [∀ n (x : M n), ENorm (TangentSpace I x)]
  [∀ n (x : M n), ENormSMulClass ℝ (TangentSpace I x)]

theorem le_riemannianEDist_of_tendsto_map_distance
    (F : ∀ n, N → M n)
    (hupper : ∀ K : Set N, IsCompact K → ∀ L : ℝ, 1 < L →
      ∀ᶠ n in atTop,
        (∀ x ∈ K, ContMDiffAt I I 1 (F n) x) ∧
        ∀ x ∈ K, ∀ v : TangentSpace I x,
          ‖mfderiv I I (F n) x v‖ₑ ≤ ENNReal.ofReal L * ‖v‖ₑ)
    (x y : N) {d : ℝ≥0∞}
    (hdist : Tendsto (fun n => riemannianEDist I (F n x) (F n y)) atTop (𝓝 d)) :
    d ≤ riemannianEDist I x y := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  obtain ⟨gamma, hzero, hone, hgamma, hlength⟩ := exists_lt_of_riemannianEDist_lt hr
  let K : Set N := gamma '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hgamma.continuousOn
  have hbound : d ≤ pathELength I gamma 0 1 := by
    apply le_of_tendsto_of_eventually_le_mul hdist
    intro L hL
    filter_upwards [hupper K hK L hL] with n hn
    have hmem : ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K := fun s hs => ⟨s, hs, rfl⟩
    have hmap : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (F n ∘ gamma) (Icc 0 1) := by
      intro s hs
      exact (hn.1 (gamma s) (hmem s hs)).comp_contMDiffWithinAt s (hgamma s hs)
    have hle := riemannianEDist_le_pathELength (x := F n x) (y := F n y) hmap
      (by simp only [Function.comp_apply, hzero])
      (by simp only [Function.comp_apply, hone]) (by norm_num : (0 : ℝ) ≤ 1)
    apply hle.trans
    rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Ioo
    intro s hs
    have hFm := (hn.1 (gamma s) (hmem s ⟨hs.1.le, hs.2.le⟩)).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hgm := (hgamma.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    rw [mfderiv_comp_apply s hFm hgm]
    exact hn.2 (gamma s) (hmem s ⟨hs.1.le, hs.2.le⟩) _
  exact hbound.trans hlength.le

end IntrinsicDistanceLimit

noncomputable section CompactMapDistance

open Filter MeasureTheory Set
open scoped NNReal _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [PseudoEMetricSpace N] [ChartedSpace H N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [WeaklyLocallyCompactSpace N]
  {ι : Type*} {l : Filter ι}
  {M : ι → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
  [∀ n (x : M n), ENorm (TangentSpace I x)]
  [∀ n (x : M n), ENormSMulClass ℝ (TangentSpace I x)]

theorem tendsto_riemannianEDist_map_of_tendsto_of_compact_mfderiv_bound
    (F : ∀ n, N → M n)
    (hupper : ∀ K : Set N, IsCompact K → ∃ C : ℝ≥0, ∀ᶠ n in l,
      (∀ x ∈ K, ContMDiffAt I I 1 (F n) x) ∧
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        ‖mfderiv I I (F n) x v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ)
    {x : N} {xn : ι → N} (hx : Tendsto xn l (𝓝 x)) :
    Tendsto (fun n => riemannianEDist I (F n x) (F n (xn n))) l (𝓝 0) := by
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨r, hr, hrK⟩ := EMetric.mem_nhds_iff.mp hxK
  obtain ⟨C, hC⟩ := hupper K hK
  let B : ℝ≥0 := C + 1
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by simp [B]
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hmin : 0 < min r (ε / (B : ℝ≥0∞)) := lt_min hr (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
  have hxsmall : ∀ᶠ n in l, edist x (xn n) < min r (ε / (B : ℝ≥0∞)) := by
    have hball := hx.eventually (Metric.eball_mem_nhds x hmin)
    simpa only [Metric.mem_eball, edist_comm] using hball
  filter_upwards [hC, hxsmall] with n hn hxn
  rw [IsRiemannianManifold.out (I := I)] at hxn
  obtain ⟨gamma, hzero, hone, hgamma, hlength⟩ := exists_lt_of_riemannianEDist_lt hxn
  have hmem : MapsTo gamma (Icc 0 1) K := by
    intro t ht
    apply hrK
    rw [Metric.mem_eball, edist_comm, IsRiemannianManifold.out (I := I)]
    calc
      riemannianEDist I x (gamma t) ≤ pathELength I gamma 0 t :=
        riemannianEDist_le_pathELength
          (hgamma.mono (Icc_subset_Icc le_rfl ht.2)) hzero rfl ht.1
      _ ≤ pathELength I gamma 0 1 := pathELength_mono le_rfl ht.2
      _ < min r (ε / (B : ℝ≥0∞)) := hlength
      _ ≤ r := min_le_left _ _
  have hbound : ∀ z ∈ K, ∀ v : TangentSpace I z,
      ‖mfderiv I I (F n) z v‖ₑ ≤ (B : ℝ≥0∞) * ‖v‖ₑ := by
    intro z hz v
    exact (hn.2 z hz v).trans (mul_le_mul_left (by exact_mod_cast le_add_of_nonneg_right zero_le_one :
      (C : ℝ≥0∞) ≤ (B : ℝ≥0∞)) _)
  have hmap : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (F n ∘ gamma) (Icc 0 1) := by
    intro s hs
    exact (hn.1 (gamma s) (hmem hs)).comp_contMDiffWithinAt s (hgamma s hs)
  have hlengthmap : pathELength I (F n ∘ gamma) 0 1 ≤
      (B : ℝ≥0∞) * pathELength I gamma 0 1 := by
    apply pathELength_comp_le_of_enorm_mfderiv_le (F n) B
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hgamma.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt one_ne_zero
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hn.1 (gamma s) (hmem ⟨hs.1.le, hs.2.le⟩)).mdifferentiableAt one_ne_zero
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hbound (gamma s) (hmem ⟨hs.1.le, hs.2.le⟩) _
  have hle := (riemannianEDist_le_pathELength hmap rfl rfl zero_le_one).trans hlengthmap
  change riemannianEDist I (F n (gamma 0)) (F n (gamma 1)) ≤ _ at hle
  rw [hzero, hone] at hle
  calc
    riemannianEDist I (F n x) (F n (xn n)) ≤
        (B : ℝ≥0∞) * pathELength I gamma 0 1 := hle
    _ ≤ (B : ℝ≥0∞) * (ε / (B : ℝ≥0∞)) :=
      mul_le_mul_right (hlength.le.trans (min_le_right _ _)) _
    _ = ε := by
      rw [ENNReal.mul_div_cancel hB0 ENNReal.coe_ne_top]

end CompactMapDistance

noncomputable section MovingDistanceLimit

open Filter Set
open scoped NNReal _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [PseudoEMetricSpace N] [ChartedSpace H N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [WeaklyLocallyCompactSpace N]
  {M : ℕ → Type*} [∀ n, PseudoEMetricSpace (M n)] [∀ n, ChartedSpace H (M n)]
  [∀ n, RiemannianBundle (fun x : M n => TangentSpace I x)]
  [∀ n, IsRiemannianManifold I (M n)]

theorem le_riemannianEDist_of_tendsto_moving_map_distance
    (F : ∀ n, N → M n)
    (hupper : ∀ K : Set N, IsCompact K → ∀ L : ℝ, 1 < L →
      ∀ᶠ n in atTop,
        (∀ x ∈ K, ContMDiffAt I I 1 (F n) x) ∧
        ∀ x ∈ K, ∀ v : TangentSpace I x,
          ‖mfderiv I I (F n) x v‖ₑ ≤ ENNReal.ofReal L * ‖v‖ₑ)
    {x y : N} {xn yn : ℕ → N}
    (hx : Tendsto xn atTop (𝓝 x)) (hy : Tendsto yn atTop (𝓝 y)) {d : ℝ≥0∞}
    (hdist : Tendsto (fun n => riemannianEDist I (F n (xn n)) (F n (yn n)))
      atTop (𝓝 d)) :
    d ≤ riemannianEDist I x y := by
  have hbound : ∀ K : Set N, IsCompact K → ∃ C : ℝ≥0, ∀ᶠ n in atTop,
      (∀ z ∈ K, ContMDiffAt I I 1 (F n) z) ∧
      ∀ z ∈ K, ∀ v : TangentSpace I z,
        ‖mfderiv I I (F n) z v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ := by
    intro K hK
    exact ⟨2, by simpa only [ENNReal.ofReal_ofNat, ENNReal.coe_ofNat] using
        (hupper K hK 2 (by norm_num))⟩
  have hxmap := tendsto_riemannianEDist_map_of_tendsto_of_compact_mfderiv_bound F hbound hx
  have hymap := tendsto_riemannianEDist_map_of_tendsto_of_compact_mfderiv_bound F hbound hy
  have hxmap' : Tendsto (fun n => edist (F n (xn n)) (F n x)) atTop (𝓝 0) := by
    simpa only [edist_comm, IsRiemannianManifold.out (I := I)] using hxmap
  have hymap' : Tendsto (fun n => edist (F n (yn n)) (F n y)) atTop (𝓝 0) := by
    simpa only [edist_comm, IsRiemannianManifold.out (I := I)] using hymap
  have hdist' : Tendsto (fun n => edist (F n (xn n)) (F n (yn n))) atTop (𝓝 d) := by
    simpa only [IsRiemannianManifold.out (I := I)] using hdist
  have hfixed := DifferentialGeometry.Topology.tendsto_edist_of_tendsto_edist_zero
    hxmap' hymap' hdist'
  apply le_riemannianEDist_of_tendsto_map_distance F hupper x y
  simpa only [IsRiemannianManifold.out (I := I)] using hfixed

end MovingDistanceLimit

noncomputable section CompactDistanceLimit

open Filter Set
open scoped _root_.Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [WeaklyLocallyCompactSpace M]
  {N : ℕ → Type*} [∀ n, PseudoMetricSpace (N n)]
  [∀ n, ChartedSpace H (N n)]
  [∀ n, RiemannianBundle (fun y : N n => TangentSpace I y)]
  [∀ n, IsRiemannianManifold I (N n)]

theorem tendsto_dist_of_compact_map_distance_convergence
    (F : ∀ n, M → N n)
    (hupper : ∀ K : Set M, IsCompact K → ∀ L : ℝ, 1 < L → ∀ᶠ n in atTop,
      (∀ x ∈ K, ContMDiffAt I I 1 (F n) x) ∧
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        ‖mfderiv I I (F n) x v‖ₑ ≤ ENNReal.ofReal L * ‖v‖ₑ)
    (x y : ℕ → M)
    (hcompact : ∃ K : Set M, IsCompact K ∧ ∀ᶠ n in atTop, x n ∈ K ∧ y n ∈ K)
    {d : ℝ} (hdist : Tendsto (fun n => dist (F n (x n)) (F n (y n))) atTop (𝓝 d))
    (hbound : ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop, dist (x n) (y n) ≤ C * d) :
    Tendsto (fun n => dist (x n) (y n)) atTop (𝓝 d) := by
  have hd0 : 0 ≤ d := ge_of_tendsto hdist (Eventually.of_forall fun n => dist_nonneg)
  obtain ⟨K, hK, htrap⟩ := hcompact
  apply tendsto_order.mpr
  constructor
  · intro a had
    by_contra! hbad
    let P : Set (M × M) := (K ×ˢ K) ∩ {p | dist p.1 p.2 ≤ a}
    have hP : IsCompact P := (hK.prod hK).inter_right (isClosed_le continuous_dist continuous_const)
    have hfreq : ∃ᶠ n in atTop, (x n, y n) ∈ P := by
      apply (hbad.and_eventually htrap).mono
      intro n hn
      exact ⟨hn.2, hn.1⟩
    obtain ⟨p, hp, φ, hφ, hlim⟩ := hP.tendsto_subseq' hfreq
    have hu : ∀ C : Set M, IsCompact C → ∀ L : ℝ, 1 < L → ∀ᶠ n in atTop,
        (∀ z ∈ C, ContMDiffAt I I 1 (F (φ n)) z) ∧
        ∀ z ∈ C, ∀ v : TangentSpace I z,
          ‖mfderiv I I (F (φ n)) z v‖ₑ ≤ ENNReal.ofReal L * ‖v‖ₑ :=
      fun C hC L hL => hφ.tendsto_atTop.eventually (hupper C hC L hL)
    have hd : Tendsto (fun n => riemannianEDist I
        (F (φ n) (x (φ n))) (F (φ n) (y (φ n)))) atTop (𝓝 (ENNReal.ofReal d)) := by
      simpa only [← IsRiemannianManifold.out, edist_dist, Function.comp_def] using
        ENNReal.tendsto_ofReal (hdist.comp hφ.tendsto_atTop)
    have hxlim : Tendsto (fun n => x (φ n)) atTop (𝓝 p.1) :=
      (continuous_fst.tendsto p).comp hlim
    have hylim : Tendsto (fun n => y (φ n)) atTop (𝓝 p.2) :=
      (continuous_snd.tendsto p).comp hlim
    have hb := le_riemannianEDist_of_tendsto_moving_map_distance
      (fun n => F (φ n)) hu hxlim hylim hd
    rw [← IsRiemannianManifold.out, edist_dist] at hb
    have hbd : d ≤ dist p.1 p.2 := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hb
    exact (not_le_of_gt had) (hbd.trans hp.2)
  · intro b hdb
    by_cases hd : d = 0
    · filter_upwards [hbound 2 (by norm_num)] with n hn
      rw [hd, mul_zero] at hn
      exact hn.trans_lt (by simpa only [hd] using hdb)
    · have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
      let C : ℝ := (b / d + 1) / 2
      have hC : 1 < C := by
        have hratio : 1 < b / d := (lt_div_iff₀ hdpos).mpr (by simpa using hdb)
        dsimp only [C]
        linarith
      have hCb : C * d < b := by
        dsimp only [C]
        rw [div_mul_eq_mul_div, add_mul, div_mul_cancel₀ _ hd, one_mul]
        linarith
      filter_upwards [hbound C hC] with n hn
      exact hn.trans_lt hCb


end CompactDistanceLimit

end DifferentialGeometry.Geometry.Riemannian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open Bundle Manifold Filter MeasureTheory Set
open scoped Manifold ContDiff ENNReal _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [∀ x : N, ENorm (TangentSpace I x)]
  {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
  [∀ n (x : M n), ENorm (TangentSpace I x)]
  [∀ n (x : M n), ENormSMulClass ℝ (TangentSpace I x)]

theorem eventually_riemannianEDist_map_lt
    (F : ∀ n, N → M n)
    (hupper : ∀ K : Set N, IsCompact K → ∀ L : ℝ, 1 < L →
      ∀ᶠ n in atTop,
        (∀ x ∈ K, ContMDiffAt I I 1 (F n) x) ∧
        ∀ x ∈ K, ∀ v : TangentSpace I x,
          ‖mfderiv I I (F n) x v‖ₑ ≤ ENNReal.ofReal L * ‖v‖ₑ)
    (x y : N) {r : ℝ}
    (hdist : riemannianEDist I x y < ENNReal.ofReal r) :
    ∀ᶠ n in atTop, riemannianEDist I (F n x) (F n y) < ENNReal.ofReal r := by
  have hr : 0 < r := ENNReal.ofReal_pos.mp ((show (0 : ℝ≥0∞) ≤ riemannianEDist I x y from bot_le).trans_lt hdist)
  obtain ⟨s, hds, hsr⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hdist)
  have hs : 0 < s := ENNReal.toReal_nonneg.trans_lt hds
  have hdist' : riemannianEDist I x y < ENNReal.ofReal s :=
    (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hdist)).mpr hds
  have hratio : (1 : ℝ) < r / s :=
    (lt_div_iff₀ hs).mpr (by simpa only [one_mul] using hsr)
  obtain ⟨L, hL, hLr⟩ := exists_between hratio
  have hLpos : 0 < L := zero_lt_one.trans hL
  have hLs : L * s < r := (lt_div_iff₀ hs).mp hLr
  obtain ⟨gamma, hzero, hone, hgamma, hlength⟩ := exists_lt_of_riemannianEDist_lt hdist'
  let K : Set N := gamma '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hgamma.continuousOn
  filter_upwards [hupper K hK L hL] with n hn
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, gamma t ∈ K := fun t ht => ⟨t, ht, rfl⟩
  have hmap : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (F n ∘ gamma) (Icc 0 1) := by
    intro t ht
    exact (hn.1 (gamma t) (hmem t ht)).comp_contMDiffWithinAt t (hgamma t ht)
  have hlengthmap : pathELength I (F n ∘ gamma) 0 1 ≤
      ENNReal.ofReal L * pathELength I gamma 0 1 := by
    rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Ioo
    intro t ht
    have hFm := (hn.1 (gamma t) (hmem t ⟨ht.1.le, ht.2.le⟩)).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hgm := (hgamma.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    rw [mfderiv_comp_apply t hFm hgm]
    exact hn.2 (gamma t) (hmem t ⟨ht.1.le, ht.2.le⟩) _
  calc
    riemannianEDist I (F n x) (F n y) ≤ pathELength I (F n ∘ gamma) 0 1 :=
      riemannianEDist_le_pathELength hmap
        (by simp only [Function.comp_apply, hzero])
        (by simp only [Function.comp_apply, hone]) zero_le_one
    _ ≤ ENNReal.ofReal L * pathELength I gamma 0 1 := hlengthmap
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal s := mul_le_mul_right hlength.le _
    _ = ENNReal.ofReal (L * s) := (ENNReal.ofReal_mul hLpos.le).symm
    _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).mpr hLs

end DifferentialGeometry.Geometry.Riemannian
