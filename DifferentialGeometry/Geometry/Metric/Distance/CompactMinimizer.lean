import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Geodesic.Naturality.MetricLocality
import DifferentialGeometry.Topology.MetricSpace.CompactBall
import DifferentialGeometry.Geometry.Exponential.RadialPath
import DifferentialGeometry.Geometry.Comparison.HopfRinow.RadialSurjectivity
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_eq_of_near_minimizer_trapping
    (g g' : SmoothRiemannianMetric I M) {K : Set M} {p q : M} {delta : ℝ}
    (hdelta : 0 < delta) (hfinite : riemannianEDistOf g p q ≠ ⊤)
    (heq : ∀ x ∈ K, g'.inner x = g.inner x)
    (hle : ∀ x (v : TangentSpace I x), g.inner x v v ≤ g'.inner x v v)
    (htrap : ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = p → gamma 1 = q →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal delta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) :
    riemannianEDistOf g' p q = riemannianEDistOf g p q := by
  refine le_antisymm ?_ (edistOf_mono g g' hle p q)
  by_contra hnot
  have hgap : riemannianEDistOf g p q < riemannianEDistOf g p q + ENNReal.ofReal delta :=
    ENNReal.lt_add_right hfinite (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  obtain ⟨c, hc, hupper⟩ := exists_between (lt_min (not_le.mp hnot) hgap)
  obtain ⟨gamma, hstart, hend, hsmooth, hlength⟩ := exists_lt_of_edistOf_lt g hc
  have hmem := htrap gamma hsmooth hstart hend
    (hlength.le.trans (hupper.trans_le (min_le_right _ _)).le)
  have heqlength : metricPathELength g' gamma 0 1 = metricPathELength g gamma 0 1 :=
    metricPathELength_congr g g' (fun s hs => heq _ (hmem s ⟨hs.1.le, hs.2.le⟩))
  have hdist := edistOf_le_metricPathELength g' (by norm_num : (0 : ℝ) ≤ 1) hsmooth
  rw [hstart, hend, heqlength] at hdist
  exact (not_lt_of_ge hdist)
    (hlength.trans (hupper.trans_le (min_le_left _ _)))

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smooth_geodesic_minimizer_of_compact_trapping
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {p q : M} {delta : ℝ} (hdelta : 0 < delta) (hfinite : riemannianEDistOf g p q ≠ ⊤)
    (htrap : ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = p → gamma 1 = q →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal delta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) :
    ∃ gamma : ℝ → M, gamma 0 = p ∧ gamma 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) ∧
      metricPathELength g gamma 0 1 = riemannianEDistOf g p q ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        metricPathELength g gamma a b = ENNReal.ofReal (b - a) * riemannianEDistOf g p q) ∧
      Riemannian.Geodesic.IsGeodesicOn (I := I) g gamma (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        g.inner (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1)
          (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) = (riemannianEDistOf g p q).toReal ^ 2 := by
  classical
  obtain ⟨g', U, hcomplete, hUopen, hKU, heqU, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g hK
  have heqdist : riemannianEDistOf g' p q = riemannianEDistOf g p q :=
    riemannianEDistOf_eq_of_near_minimizer_trapping g g' hdelta hfinite
      (fun x hx => heqU x (hKU hx)) hle htrap
  let : IsManifold I 1 M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g'.inner, g'.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g' :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g' x v
  have hdist' : riemannianEDistOf g' p q = Manifold.riemannianEDist I p q :=
    riemannianEDistOf_eq_riemannianEDist g' hEnorm p q
  have hfinite' : Manifold.riemannianEDist I p q ≠ ⊤ := by
    rw [← hdist', heqdist]
    exact hfinite
  obtain ⟨v, hv, hspeed⟩ := minExp_of_ne_top g' hEnorm p q hfinite'
  let gamma : ℝ → M := intrinsicGeodesic g' hEnorm p v
  have hstart : gamma 0 = p := intrinsicGeodesic_zero g' hEnorm p v
  have hend : gamma 1 = q := hv
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    isGeodesic_contMDiff g' (intrinsicGeodesic_isGeodesic g' hEnorm p v)
      (intrinsicGeodesic_continuous g' hEnorm p v)
  have hspeedAll (s : ℝ) :
      g'.inner (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) = g'.inner p v v :=
    intrinsicGeodesic_speedSq_eq g' hEnorm p v s
  have hlen' : metricPathELength g' gamma 0 1 = riemannianEDistOf g p q := by
    rw [metricPathELength_eq]
    simp_rw [hspeedAll]
    rw [setLIntegral_const, Real.volume_Ioo]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    rw [hspeed, ENNReal.ofReal_toReal hfinite', ← hdist', heqdist]
  have hlen : metricPathELength g gamma 0 1 ≤ metricPathELength g' gamma 0 1 := by
    rw [metricPathELength_eq, metricPathELength_eq]
    exact setLIntegral_mono' measurableSet_Ioo fun s _hs =>
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hle (gamma s) _))
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K := by
    apply htrap gamma (hsmooth.of_le (by simp)).contMDiffOn hstart hend
    exact (hlen.trans_eq hlen').trans
      (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal delta from bot_le))
  refine ⟨gamma, hstart, hend, hsmooth, hmem, ?_, ?_, ?_, ?_⟩
  · calc
      _ = metricPathELength g' gamma 0 1 :=
        (metricPathELength_congr g g' (fun s hs => heqU _ (hKU (hmem s ⟨hs.1.le, hs.2.le⟩)))).symm
      _ = _ := hlen'
  · intro a ha b hb
    calc
      _ = metricPathELength g' gamma a b :=
        (metricPathELength_congr g g' (fun s hs => heqU _
          (hKU (hmem s ⟨ha.1.trans hs.1.le, hs.2.le.trans hb.2⟩)))).symm
      _ = _ := by
        rw [metricPathELength_eq]
        simp_rw [hspeedAll]
        rw [setLIntegral_const, Real.volume_Ioo, hspeed, ENNReal.ofReal_toReal hfinite',
          ← hdist', heqdist, mul_comm]
  · apply (Riemannian.Geodesic.isGeodesicOn_iff_of_metric_eventuallyEq g g' ?_).mpr
      ((intrinsicGeodesic_isGeodesic g' hEnorm p v).isGeodesicOn _)
    intro t ht
    filter_upwards [hUopen.mem_nhds (hKU (hmem t ht))] with y hy
    intro v w
    rw [heqU y hy]
  · intro t ht
    rw [← heqU (gamma t) (hKU (hmem t ht)), hspeedAll]
    calc
      _ = (Real.sqrt (g'.inner p v v)) ^ 2 := (Real.sq_sqrt (metric_inner_self_nonneg g' p v)).symm
      _ = _ := by rw [hspeed, ← hdist', heqdist]

theorem exists_smooth_minimizer_with_subinterval_lengths
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {p q : M} {delta : ℝ} (hdelta : 0 < delta) (hfinite : riemannianEDistOf g p q ≠ ⊤)
    (htrap : ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = p → gamma 1 = q →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal delta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) :
    ∃ gamma : ℝ → M, gamma 0 = p ∧ gamma 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) ∧
      metricPathELength g gamma 0 1 = riemannianEDistOf g p q ∧
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        metricPathELength g gamma a b = ENNReal.ofReal (b - a) * riemannianEDistOf g p q := by
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength, hsub, _, _⟩ :=
    exists_smooth_geodesic_minimizer_of_compact_trapping g hK hdelta hfinite htrap
  exact ⟨gamma, hstart, hend, hsmooth, hmem, hlength, hsub⟩

theorem exists_smooth_minimizer_of_compact_trapping
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {p q : M} {delta : ℝ} (hdelta : 0 < delta) (hfinite : riemannianEDistOf g p q ≠ ⊤)
    (htrap : ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = p → gamma 1 = q →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal delta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) :
    ∃ gamma : ℝ → M, gamma 0 = p ∧ gamma 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) ∧
      metricPathELength g gamma 0 1 = riemannianEDistOf g p q := by
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength, _hsub⟩ :=
    exists_smooth_minimizer_with_subinterval_lengths g hK hdelta hfinite htrap
  exact ⟨gamma, hstart, hend, hsmooth, hmem, hlength⟩

variable {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace N]

theorem exists_smooth_geodesic_minimizer_of_isCompact_closedBall
    (g : SmoothRiemannianMetric I N)
    (hmetric : ∀ x y : N, edist x y = riemannianEDistOf g x y)
    {p q : N} {R : ℝ} (hK : IsCompact (Metric.closedBall p R)) (hR : dist p q < R) :
    ∃ gamma : ℝ → N, gamma 0 = p ∧ gamma 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ Metric.closedBall p R) ∧
      metricPathELength g gamma 0 1 = ENNReal.ofReal (dist p q) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        metricPathELength g gamma a b = ENNReal.ofReal (b - a) * ENNReal.ofReal (dist p q)) ∧
      Riemannian.Geodesic.IsGeodesicOn (I := I) g gamma (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        g.inner (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1)
          (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) = dist p q ^ 2 := by
  let _ : IsManifold I 1 N := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let _ : T2Space (TangentBundle I N) := inferInstance
  have hdist (x y : N) : riemannianEDistOf g x y = ENNReal.ofReal (dist x y) :=
    (hmetric x y).symm.trans (edist_dist x y)
  let eta : ℝ := (R - dist p q) / 2
  have heta : 0 < eta := half_pos (sub_pos.mpr hR)
  have hfinite : riemannianEDistOf g p q ≠ ⊤ := by
    rw [hdist]
    exact ENNReal.ofReal_ne_top
  have htrap : ∀ gamma : ℝ → N,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) →
      gamma 0 = p → gamma 1 = q →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal eta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ Metric.closedBall p R := by
    intro gamma hsmooth hstart _hend hnear s hs
    have hprefix := edistOf_le_metricPathELength g hs.1
      (hsmooth.mono (Icc_subset_Icc le_rfl hs.2))
    rw [hstart] at hprefix
    have hbound := (hprefix.trans (metricPathELength_mono g gamma le_rfl hs.2)).trans hnear
    rw [hdist, hdist, ← ENNReal.ofReal_add dist_nonneg heta.le] at hbound
    have hreal : dist p (gamma s) ≤ dist p q + eta :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
    change dist (gamma s) p ≤ R
    rw [dist_comm]
    dsimp only [eta] at hreal
    linarith only [hreal, hR]
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength, hsub, hgeo, hspeed⟩ :=
    exists_smooth_geodesic_minimizer_of_compact_trapping g hK heta hfinite htrap
  refine ⟨gamma, hstart, hend, hsmooth, hmem, ?_, ?_, hgeo, ?_⟩
  · simpa only [hdist] using hlength
  · intro a ha b hb
    simpa only [hdist] using hsub a ha b hb
  · intro s hs
    simpa only [hdist, ENNReal.toReal_ofReal dist_nonneg] using hspeed s hs


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smooth_geodesic_minimizer_of_punctured_compact_ball
    {X : Type*} [MetricSpace X] (g : SmoothRiemannianMetric I N)
    (hmetric : ∀ x y : N, edist x y = riemannianEDistOf g x y)
    {e : N → X} (he : Isometry e) {z : X} {r : ℝ}
    (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range e))
    {p q : N} (hgap : dist p q < dist (e p) z + dist (e q) z)
    (hbuffer : dist (e p) z + dist p q < r) :
    ∃ gamma : ℝ → N, gamma 0 = p ∧ gamma 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      (∀ s ∈ Icc (0 : ℝ) 1, e (gamma s) ∈ Metric.closedBall z r) ∧
      metricPathELength g gamma 0 1 = ENNReal.ofReal (dist p q) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        metricPathELength g gamma a b = ENNReal.ofReal (b - a) * ENNReal.ofReal (dist p q)) ∧
      Riemannian.Geodesic.IsGeodesicOn (I := I) g gamma (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        g.inner (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1)
          (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) = dist p q ^ 2 := by
  let _ : IsManifold I 1 N := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let _ : T2Space (TangentBundle I N) := inferInstance
  obtain ⟨eta, heta, hetab⟩ := exists_between
    (lt_min (sub_pos.mpr hgap) (sub_pos.mpr hbuffer))
  have hetaGap := hetab.trans_le (min_le_left _ _)
  have hetaBuffer := hetab.trans_le (min_le_right _ _)
  let rho := (dist (e p) z + dist (e q) z - dist p q - eta) / 2
  have hrho : 0 < rho := by dsimp only [rho]; linarith only [hetaGap]
  let K : Set X := Metric.closedBall z r ∩ {w : X | rho ≤ dist w z}
  have hK : IsCompact K := hcompact.inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hKr : K ⊆ range e := by
    intro w hw
    rcases hcover hw.1 with heq | heq
    · have hlow : rho ≤ dist w z := hw.2
      rw [heq, dist_self] at hlow
      exact False.elim (hrho.not_ge hlow)
    · exact heq
  have hKpre : IsCompact (e ⁻¹' K) := he.isEmbedding.isInducing.isCompact_preimage' hK hKr
  have hdist (x y : N) : riemannianEDistOf g x y = ENNReal.ofReal (dist x y) :=
    (hmetric x y).symm.trans (edist_dist x y)
  have hfinite : riemannianEDistOf g p q ≠ ⊤ := by rw [hdist]; exact ENNReal.ofReal_ne_top
  have htrap (gamma : ℝ → N) (hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1))
      (hstart : gamma 0 = p) (hend : gamma 1 = q)
      (hlength : metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal eta)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : gamma t ∈ e ⁻¹' K := by
    have hleft := edistOf_le_metricPathELength g ht.1
      (hsmooth.mono (Icc_subset_Icc le_rfl ht.2))
    have hright := edistOf_le_metricPathELength g ht.2
      (hsmooth.mono (Icc_subset_Icc ht.1 le_rfl))
    rw [hstart, hdist] at hleft
    rw [hend, hdist] at hright
    have hadd : metricPathELength g gamma 0 t + metricPathELength g gamma t 1 =
        metricPathELength g gamma 0 1 := by
      let _ : RiemannianBundle (fun u : N => TangentSpace I u) := ⟨g.toRiemannianMetric⟩
      exact Manifold.pathELength_add (I := I) (γ := gamma) ht.1 ht.2
    have hsum := ((add_le_add hleft hright).trans_eq hadd).trans hlength
    rw [hdist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
      ← ENNReal.ofReal_add dist_nonneg heta.le] at hsum
    have hreal : dist p (gamma t) + dist (gamma t) q ≤ dist p q + eta :=
      (ENNReal.ofReal_le_ofReal_iff (add_nonneg dist_nonneg heta.le)).mp hsum
    have houter := dist_triangle (e (gamma t)) (e p) z
    rw [he.dist_eq, dist_comm (gamma t) p] at houter
    have hp := dist_triangle (e p) (e (gamma t)) z
    have hq := dist_triangle (e q) (e (gamma t)) z
    rw [he.dist_eq] at hp
    rw [he.dist_eq, dist_comm q (gamma t)] at hq
    constructor
    · change dist (e (gamma t)) z ≤ r
      linarith only [houter, hreal, hetaBuffer, dist_nonneg (x := gamma t) (y := q)]
    · change rho ≤ dist (e (gamma t)) z
      dsimp only [rho]
      linarith only [hp, hq, hreal]
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength, hsub, hgeo, hspeed⟩ :=
    exists_smooth_geodesic_minimizer_of_compact_trapping g hKpre heta hfinite htrap
  refine ⟨gamma, hstart, hend, hsmooth, fun t ht => (hmem t ht).1, ?_, ?_, hgeo, ?_⟩
  · simpa only [hdist] using hlength
  · intro a ha b hb
    simpa only [hdist] using hsub a ha b hb
  · intro t ht
    simpa only [hdist, ENNReal.toReal_ofReal dist_nonneg] using hspeed t ht


end DifferentialGeometry.Geometry

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

open Exponential
open HopfRinow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_distance_parametrized_minimizer_of_isCompact_riemannianClosedBall
    (g : SmoothRiemannianMetric I M) (p q : M) {R : ℝ}
    (hR : riemannianEDistOf g p q < ENNReal.ofReal R)
    (hcompact : IsCompact (riemannianClosedBallOf g p R)) :
    ∃ gamma : ℝ → M,
      gamma 0 = p ∧ gamma (riemannianEDistOf g p q).toReal = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ gamma (Icc 0 (riemannianEDistOf g p q).toReal) ∧
      ∀ s ∈ Icc 0 (riemannianEDistOf g p q).toReal,
        ∀ t ∈ Icc 0 (riemannianEDistOf g p q).toReal,
          riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
  by_cases hpq : p = q
  · subst q
    refine ⟨fun _ => p, rfl, rfl, contMDiffOn_const, ?_⟩
    intro s hs t ht
    rw [riemannianEDistOf_self, ENNReal.toReal_zero] at hs ht
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    rw [hs0, ht0, sub_self, abs_zero, ENNReal.ofReal_zero, riemannianEDistOf_self]
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hdist (x y : M) : riemannianEDistOf g x y = riemannianEDist I x y :=
    riemannianEDistOf_eq_riemannianEDist g hEnorm x y
  have hball : IsCompact (Metric.closedEBall p (ENNReal.ofReal R)) := by
    convert hcompact using 1
    ext y
    change edist y p ≤ ENNReal.ofReal R ↔ riemannianEDistOf g p y ≤ ENNReal.ofReal R
    rw [edist_comm, IsRiemannianManifold.out (I := I), hdist]
  obtain ⟨v, hv, hvq, hvlen⟩ := RadialSurjectivity.minExp_of_cptBall g hEnorm p q
    (by simpa only [hdist] using hR) hball
  let L : ℝ := (riemannianEDistOf g p q).toReal
  have hfinite : riemannianEDistOf g p q ≠ ⊤ := ne_top_of_lt hR
  have hnonzero : riemannianEDistOf g p q ≠ 0 := by
    intro hz
    exact hpq (riemannianEDist_eq_zero_imp_eq (I := I) p q ((hdist p q).symm ▸ hz))
  have hL : 0 < L := ENNReal.toReal_pos hnonzero hfinite
  have hvnorm : Real.sqrt (g.inner p v v) = L := by
    have h := congrArg ENNReal.toReal hvlen
    rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ← hdist p q] at h
    exact h
  have hvv : g.inner p v v = L ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg g p v), hvnorm]
  let u : TangentSpace I p := L⁻¹ • v
  have hunit : g.inner p u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self g p, hvv, ← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]
  have hLv : L • u = v := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hdom (t : ℝ) (ht : t ∈ Icc 0 L) : t • u ∈ expDomain g p := by
    have heq : t • u = (t / L) • v := by
      dsimp only [u]
      rw [smul_smul, div_eq_mul_inv]
    rw [heq]
    exact smul_mem_expDomain hv ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
  let gamma : ℝ → M := fun t => expMap g p (t • u)
  have hzero : gamma 0 = p := by dsimp only [gamma]; rw [zero_smul, expMap_zero]
  have hend : gamma L = q := by dsimp only [gamma]; rw [hLv, hvq]
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ gamma (Icc 0 L) := by
    intro t ht
    have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => s • (show E from u)) :=
      contMDiff_id.smul contMDiff_const
    exact ((contMDiffAt_expMap g p (hdom t ht)).comp t
      hline.contMDiffAt).contMDiffWithinAt
  have hspeed : ∀ t ∈ Icc 0 L,
      ‖mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)‖ₑ ≤ ENNReal.ofReal 1 := by
    intro t ht
    rw [hEnorm]
    have hi := inner_curveVelocity_expMap_smul g p (show E from u) (hdom t ht)
    change g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
      (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) = g.inner p u u at hi
    have hiEq := congrArg (fun r : ℝ => ENNReal.ofReal (Real.sqrt r)) (hi.trans hunit)
    simpa only [Real.sqrt_one] using! hiEq.le
  have hupper (s t : ℝ) (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) (hst : s ≤ t) :
      riemannianEDistOf g (gamma s) (gamma t) ≤ ENNReal.ofReal (t - s) := by
    rw [hdist]
    simpa only [one_mul] using curve_edist_le_speed_mul_time (I := I)
      (c := (1 : ℝ)) zero_le_one hst
      ((hsmooth.of_le (by norm_num)).mono (Icc_subset_Icc hs.1 ht.2))
      (fun z hz => hspeed z ⟨hs.1.trans hz.1, hz.2.trans ht.2⟩)
  have hordered (s t : ℝ) (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) (hst : s ≤ t) :
      riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal (t - s) := by
    have hstfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper s t hs ht hst)
    have h0s := hupper 0 s ⟨le_rfl, hL.le⟩ hs hs.1
    have htL := hupper t L ht ⟨hL.le, le_rfl⟩ ht.2
    have htri := (riemannianEDistOf_triangle g (gamma 0) (gamma s) (gamma L)).trans
      (add_le_add le_rfl (riemannianEDistOf_triangle g (gamma s) (gamma t) (gamma L)))
    have hbound := htri.trans (add_le_add h0s (add_le_add le_rfl htL))
    rw [hzero, hend, sub_zero] at hbound
    have hre := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.add_ne_top.mpr ⟨hstfin, ENNReal.ofReal_ne_top⟩⟩) hbound
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hstfin, ENNReal.ofReal_ne_top⟩),
      ENNReal.toReal_add hstfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hs.1, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)] at hre
    have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupper s t hs ht hst)
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] at hu
    have heq : (riemannianEDistOf g (gamma s) (gamma t)).toReal = t - s := by
      change L ≤ s + ((riemannianEDistOf g (gamma s) (gamma t)).toReal + (L - t)) at hre
      linarith
    exact (ENNReal.ofReal_toReal hstfin).symm.trans (congrArg ENNReal.ofReal heq)
  refine ⟨gamma, hzero, hend, hsmooth, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · rw [hordered s t hs ht hst, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  · rw [riemannianEDistOf_comm g (gamma s) (gamma t), hordered t s ht hs hts,
      abs_of_nonneg (sub_nonneg.mpr hts)]

theorem exists_distance_parametrized_minimizer_in_closedBall
    (g : SmoothRiemannianMetric I M) (o p q : M) {R : ℝ} (hR : 0 ≤ R)
    (hp : riemannianEDistOf g o p ≤ ENNReal.ofReal R)
    (hq : riemannianEDistOf g o q ≤ ENNReal.ofReal R)
    (hcompact : IsCompact (riemannianClosedBallOf g o (3 * R + 1))) :
    ∃ gamma : ℝ → M,
      gamma 0 = p ∧ gamma (riemannianEDistOf g p q).toReal = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ gamma (Icc 0 (riemannianEDistOf g p q).toReal) ∧
      (∀ t ∈ Icc 0 (riemannianEDistOf g p q).toReal,
        gamma t ∈ riemannianClosedBallOf g o (3 * R)) ∧
      ∀ s ∈ Icc 0 (riemannianEDistOf g p q).toReal,
        ∀ t ∈ Icc 0 (riemannianEDistOf g p q).toReal,
          riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
  have hdist : riemannianEDistOf g p q ≤ ENNReal.ofReal (2 * R) := by
    have h := (riemannianEDistOf_triangle g p o q).trans
      (add_le_add (by simpa only [riemannianEDistOf_comm g p o] using hp) hq)
    rw [← ENNReal.ofReal_add hR hR] at h
    simpa only [two_mul] using h
  have hclosed : IsClosed (riemannianClosedBallOf g p (2 * R + 1)) :=
    isClosed_le (continuous_riemannianEDist g p) continuous_const
  have hsub : riemannianClosedBallOf g p (2 * R + 1) ⊆
      riemannianClosedBallOf g o (3 * R + 1) := by
    intro z hz
    have h := (riemannianEDistOf_triangle g o p z).trans (add_le_add hp hz)
    rw [← ENNReal.ofReal_add hR (by linarith : 0 ≤ 2 * R + 1)] at h
    change riemannianEDistOf g o z ≤ ENNReal.ofReal (3 * R + 1)
    have heq : R + (2 * R + 1) = 3 * R + 1 := by ring
    rwa [heq] at h
  have hK : IsCompact (riemannianClosedBallOf g p (2 * R + 1)) :=
    hcompact.of_isClosed_subset hclosed hsub
  have hlt : riemannianEDistOf g p q < ENNReal.ofReal (2 * R + 1) :=
    hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 2 * R + 1)).mpr (by linarith))
  obtain ⟨gamma, hzero, hend, hsmooth, hmin⟩ :=
    exists_distance_parametrized_minimizer_of_isCompact_riemannianClosedBall g p q hlt hK
  have hlength : (riemannianEDistOf g p q).toReal ≤ 2 * R := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist).trans_eq
      (ENNReal.toReal_ofReal (by linarith))
  refine ⟨gamma, hzero, hend, hsmooth, ?_, hmin⟩
  intro t ht
  have hseg := hmin 0 ⟨le_rfl, ENNReal.toReal_nonneg⟩ t ht
  rw [hzero, zero_sub, abs_neg, abs_of_nonneg ht.1] at hseg
  have h := (riemannianEDistOf_triangle g o p (gamma t)).trans
    (add_le_add hp hseg.le)
  rw [← ENNReal.ofReal_add hR ht.1] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by linarith [ht.2]))

end DifferentialGeometry.Geometry.Riemannian
