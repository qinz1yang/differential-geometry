import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Line
import DifferentialGeometry.Topology.SphereSeparation.PathCrossing
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence

set_option autoImplicit false
noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature
open DifferentialGeometry.Topology.SphereSeparation
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I}
  {subseq : ℕ → ℕ} {Phi : PointedRiemannianConvergenceMaps X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth

theorem exists_pointed_metric_line_of_minimizing_segments_intersecting_bounded_sets
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (S : ∀ k, Set (X.obj (subseq k)).M)
    {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ k, S k ⊆ riemannianClosedBallOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint B)
    (gamma : ∀ k, ℝ → (X.obj (subseq k)).M) (length : ℕ → ℝ)
    (hlength : ∀ k, 0 ≤ length k)
    (hmin : ∀ k, ∀ s ∈ Icc 0 (length k), ∀ t ∈ Icc 0 (length k),
      riemannianEDistOf (X.obj (subseq k)).metric (gamma k s) (gamma k t) =
        ENNReal.ofReal |s - t|)
    (hinter : ∀ k, ∃ t ∈ Icc 0 (length k), gamma k t ∈ S k)
    (hleft : Tendsto (fun k => (riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k 0)).toReal) atTop atTop)
    (hright : Tendsto (fun k => (riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k (length k))).toReal) atTop atTop) :
    ∃ line : ℝ → L.M, ∀ s t : ℝ,
      riemannianEDistOf L.metric (line s) (line t) = ENNReal.ofReal |s - t| := by
  classical
  choose cut hcut hcutS using hinter
  have hcutI (k : ℕ) : cut k ∈ Icc 0 (length k) := hcut k
  have hbase (k : ℕ) : riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k (cut k)) ≤ ENNReal.ofReal B := hS k (hcutS k)
  have hboundLeft (k : ℕ) :
      (riemannianEDistOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint (gamma k 0)).toReal ≤ B + cut k := by
    have htri := riemannianEDistOf_triangle (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k (cut k)) (gamma k 0)
    have hdist := hmin k (cut k) (hcutI k) 0 ⟨le_rfl, hlength k⟩
    rw [sub_zero, abs_of_nonneg (hcut k).1] at hdist
    rw [hdist] at htri
    have hle := htri.trans (add_le_add (hbase k) le_rfl)
    rw [← ENNReal.ofReal_add hB (hcut k).1] at hle
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
      (ENNReal.toReal_ofReal (add_nonneg hB (hcut k).1))
  have hboundRight (k : ℕ) :
      (riemannianEDistOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint (gamma k (length k))).toReal ≤
        B + (length k - cut k) := by
    have htri := riemannianEDistOf_triangle (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k (cut k)) (gamma k (length k))
    have hdist := hmin k (cut k) (hcutI k) (length k) ⟨hlength k, le_rfl⟩
    rw [abs_of_nonpos (sub_nonpos.mpr (hcut k).2), neg_sub] at hdist
    rw [hdist] at htri
    have hle := htri.trans (add_le_add (hbase k) le_rfl)
    rw [← ENNReal.ofReal_add hB (sub_nonneg.mpr (hcut k).2)] at hle
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
      (ENNReal.toReal_ofReal (add_nonneg hB (sub_nonneg.mpr (hcut k).2)))
  have hcutTop : Tendsto cut atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [hleft.eventually_ge_atTop (B + r)] with k hk
    linarith [hboundLeft k]
  have hrestTop : Tendsto (fun k => length k - cut k) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [hright.eventually_ge_atTop (B + r)] with k hk
    linarith [hboundRight k]
  let radius : ℕ → ℝ := fun k => min (cut k) (length k - cut k)
  have hradius : Tendsto radius atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [hcutTop.eventually_ge_atTop r, hrestTop.eventually_ge_atTop r] with k hk hl
    exact le_min hk hl
  let centered := fun k t => gamma k (t + cut k)
  have hcentered (k : ℕ) : riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (centered k 0) ≤ ENNReal.ofReal B := by
    simpa only [centered, zero_add] using hbase k
  have hsegment : ∀ k, ∀ s ∈ Icc (-radius k) (radius k),
      ∀ t ∈ Icc (-radius k) (radius k),
      ENNReal.ofReal ((1 - (0 : ℝ)) * |s - t|) ≤
        riemannianEDistOf (X.obj (subseq k)).metric (centered k s) (centered k t) ∧
      riemannianEDistOf (X.obj (subseq k)).metric (centered k s) (centered k t) ≤
        ENNReal.ofReal ((1 + (0 : ℝ)) * |s - t|) := by
    intro k s hs t ht
    have hin (z : ℝ) (hz : z ∈ Icc (-radius k) (radius k)) :
        z + cut k ∈ Icc 0 (length k) := by
      have hrad₁ : radius k ≤ cut k := min_le_left _ _
      have hrad₂ : radius k ≤ length k - cut k := min_le_right _ _
      constructor <;> linarith [hz.1, hz.2]
    have heq := hmin k _ (hin s hs) _ (hin t ht)
    have hsub : s + cut k - (t + cut k) = s - t := by ring
    simp only [centered, sub_zero, add_zero, one_mul]
    rw [heq, hsub]
    exact ⟨le_rfl, le_rfl⟩
  obtain ⟨line, _, hline⟩ := exists_pointed_line_of_growing_almost_isometric_segments_with_bounded_centers
    C href hcomplete hconnected centered hB hcentered radius hradius
    (fun _ => 0) tendsto_const_nhds hsegment
  exact ⟨line, hline⟩


theorem exists_pointed_metric_line_of_separating_minimizing_segments
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (S : ∀ k, Set (X.obj (subseq k)).M)
    (sep : ∀ k, TwoSidedSeparation (S k))
    {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ k, S k ⊆ riemannianClosedBallOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint B)
    (gamma : ∀ k, ℝ → (X.obj (subseq k)).M) (length : ℕ → ℝ)
    (hlength : ∀ k, 0 ≤ length k)
    (hcont : ∀ k, ContinuousOn (gamma k) (Icc 0 (length k)))
    (hmin : ∀ k, ∀ s ∈ Icc 0 (length k), ∀ t ∈ Icc 0 (length k),
      riemannianEDistOf (X.obj (subseq k)).metric (gamma k s) (gamma k t) =
        ENNReal.ofReal |s - t|)
    (hneg : ∀ k, gamma k 0 ∈ (sep k).negativeSide)
    (hpos : ∀ k, gamma k (length k) ∈ (sep k).positiveSide)
    (hleft : Tendsto (fun k => (riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k 0)).toReal) atTop atTop)
    (hright : Tendsto (fun k => (riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k (length k))).toReal) atTop atTop) :
    ∃ line : ℝ → L.M, ∀ s t : ℝ,
      riemannianEDistOf L.metric (line s) (line t) = ENNReal.ofReal |s - t| := by
  apply exists_pointed_metric_line_of_minimizing_segments_intersecting_bounded_sets
    C href hcomplete hconnected S hB hS gamma length hlength hmin _ hleft hright
  intro k
  obtain ⟨t, ht, htS⟩ :=
    (sep k).exists_mem_Ioo_of_continuousOn (hlength k) (hcont k) (hneg k) (hpos k)
  exact ⟨t, ⟨ht.1.le, ht.2.le⟩, htS⟩

theorem exists_pointed_metric_line_of_minimizing_segments_in_separated_open_sets
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (U : ∀ k, TopologicalSpace.Opens (X.obj (subseq k)).M)
    (S : ∀ k, Set (U k)) (sep : ∀ k, TwoSidedSeparation (S k))
    {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ k z, z ∈ S k → riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (z : (X.obj (subseq k)).M) ≤ ENNReal.ofReal B)
    (gamma : ∀ k, ℝ → U k) (length : ℕ → ℝ)
    (hlength : ∀ k, 0 ≤ length k)
    (hcont : ∀ k, ContinuousOn (gamma k) (Icc 0 (length k)))
    (hmin : ∀ k, ∀ s ∈ Icc 0 (length k), ∀ t ∈ Icc 0 (length k),
      riemannianEDistOf (X.obj (subseq k)).metric (gamma k s) (gamma k t) =
        ENNReal.ofReal |s - t|)
    (hneg : ∀ k, gamma k 0 ∈ (sep k).negativeSide)
    (hpos : ∀ k, gamma k (length k) ∈ (sep k).positiveSide)
    (hleft : Tendsto (fun k => (riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k 0)).toReal) atTop atTop)
    (hright : Tendsto (fun k => (riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (gamma k (length k))).toReal) atTop atTop) :
    ∃ line : ℝ → L.M, ∀ s t : ℝ,
      riemannianEDistOf L.metric (line s) (line t) = ENNReal.ofReal |s - t| := by
  apply exists_pointed_metric_line_of_minimizing_segments_intersecting_bounded_sets
    C href hcomplete hconnected (fun k => Subtype.val '' S k) hB
    (fun k z hz => by obtain ⟨w, hw, rfl⟩ := hz; exact hS k w hw)
    (fun k t => (gamma k t : (X.obj (subseq k)).M)) length hlength hmin _ hleft hright
  intro k
  obtain ⟨t, ht, htS⟩ :=
    (sep k).exists_mem_Ioo_of_continuousOn (hlength k) (hcont k) (hneg k) (hpos k)
  exact ⟨t, ⟨ht.1.le, ht.2.le⟩, ⟨gamma k t, htS, rfl⟩⟩

end DifferentialGeometry.CheegerGromovCompactness

set_option autoImplicit false
noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature
open Geometry.Riemannian
open DifferentialGeometry.Topology.SphereSeparation

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I}
  {subseq : ℕ → ℕ} {Phi : PointedRiemannianConvergenceMaps X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_pointed_metric_line_of_separated_points_in_compact_balls
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (U : ∀ k, TopologicalSpace.Opens (X.obj (subseq k)).M)
    (S : ∀ k, Set (U k)) (sep : ∀ k, TwoSidedSeparation (S k))
    {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ k z, z ∈ S k → riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (z : (X.obj (subseq k)).M) ≤ ENNReal.ofReal B)
    (p q : ∀ k, U k)
    (hp : ∀ k, p k ∈ (sep k).negativeSide)
    (hq : ∀ k, q k ∈ (sep k).positiveSide)
    (R : ℕ → ℝ) (hR : ∀ k, 0 ≤ R k) (hRlim : Tendsto R atTop atTop)
    (hpR : ∀ k, riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (p k) = ENNReal.ofReal (R k))
    (hqR : ∀ k, riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (q k) = ENNReal.ofReal (R k))
    (hcompact : ∀ k, IsCompact (riemannianClosedBallOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (3 * R k + 1)))
    (hcapture : ∀ k, riemannianClosedBallOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (3 * R k) ⊆ U k) :
    ∃ line : ℝ → L.M, ∀ s t : ℝ,
      riemannianEDistOf L.metric (line s) (line t) = ENNReal.ofReal |s - t| := by
  classical
  let length (k : ℕ) := (riemannianEDistOf (X.obj (subseq k)).metric (p k) (q k)).toReal
  have hlength (k : ℕ) : 0 ≤ length k := ENNReal.toReal_nonneg
  choose gamma hzero hend hsmooth hmem hmin using fun k =>
    exists_distance_parametrized_minimizer_in_closedBall (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (p k) (q k) (hR k) (hpR k).le (hqR k).le (hcompact k)
  let lifted (k : ℕ) (t : ℝ) : U k :=
    ⟨gamma k (projIcc 0 (length k) (hlength k) t),
      hcapture k (hmem k _ (projIcc 0 (length k) (hlength k) t).property)⟩
  have heq (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (length k)) :
      (lifted k t : (X.obj (subseq k)).M) = gamma k t := by
    dsimp only [lifted]
    rw [projIcc_of_mem (hlength k) ht]
  have hcont (k : ℕ) : ContinuousOn (lifted k) (Icc 0 (length k)) := by
    have hmap : Continuous (fun t : ℝ => gamma k (projIcc 0 (length k) (hlength k) t)) :=
      ((hsmooth k).continuousOn.domRestrict).comp continuous_projIcc
    exact (hmap.subtype_mk _).continuousOn
  have hminLift : ∀ k, ∀ s ∈ Icc 0 (length k), ∀ t ∈ Icc 0 (length k),
      riemannianEDistOf (X.obj (subseq k)).metric (lifted k s) (lifted k t) =
        ENNReal.ofReal |s - t| := by
    intro k s hs t ht
    rw [heq k s hs, heq k t ht]
    exact hmin k s hs t ht
  have hstart (k : ℕ) : lifted k 0 = p k := by
    apply Subtype.ext
    rw [heq k 0 ⟨le_rfl, hlength k⟩, hzero k]
  have hfinish (k : ℕ) : lifted k (length k) = q k := by
    apply Subtype.ext
    rw [heq k (length k) ⟨hlength k, le_rfl⟩, hend k]
  apply exists_pointed_metric_line_of_minimizing_segments_in_separated_open_sets
    C href hcomplete hconnected U S sep hB hS lifted length hlength hcont hminLift
    (fun k => hstart k ▸ hp k) (fun k => hfinish k ▸ hq k) ?_ ?_
  · have hdist (k : ℕ) : (riemannianEDistOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint (lifted k 0)).toReal = R k := by
      rw [hstart, hpR, ENNReal.toReal_ofReal (hR k)]
    simpa only [hdist] using hRlim
  · have hdist (k : ℕ) : (riemannianEDistOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint (lifted k (length k))).toReal = R k := by
      rw [hfinish, hqR, ENNReal.toReal_ofReal (hR k)]
    simpa only [hdist] using hRlim

end DifferentialGeometry.CheegerGromovCompactness

set_option autoImplicit false
noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature
open DifferentialGeometry.Topology.SphereSeparation

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I}
  {subseq : ℕ → ℕ} {Phi : PointedRiemannianConvergenceMaps X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_pointed_metric_line_of_eventual_separated_points_in_compact_balls
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (U : ∀ k, TopologicalSpace.Opens (X.obj (subseq k)).M)
    (S : ∀ k, Set (U k)) (sep : ∀ k, TwoSidedSeparation (S k))
    {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ k z, z ∈ S k → riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (z : (X.obj (subseq k)).M) ≤ ENNReal.ofReal B)
    (hpoints : ∀ R : ℝ, B < R → ∀ᶠ k in atTop,
      IsCompact (riemannianClosedBallOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint (3 * R + 1)) ∧
      riemannianClosedBallOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint (3 * R) ⊆ U k ∧
      ∃ p q : U k, p ∈ (sep k).negativeSide ∧ q ∈ (sep k).positiveSide ∧
        riemannianEDistOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint p =
          ENNReal.ofReal R ∧
        riemannianEDistOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint q =
          ENNReal.ofReal R) :
    ∃ line : ℝ → L.M, ∀ s t : ℝ,
      riemannianEDistOf L.metric (line s) (line t) = ENNReal.ofReal |s - t| := by
  classical
  let radius (n : ℕ) : ℝ := B + n + 1
  have hradius (n : ℕ) : B < radius n := by dsimp only [radius]; linarith [Nat.cast_nonneg (α := ℝ) n]
  choose threshold hthreshold using fun n => eventually_atTop.mp (hpoints (radius n) (hradius n))
  let index : ℕ → ℕ := fun n => max n (threshold n)
  obtain ⟨phi, hphi, hindex⟩ := strictMono_subseq_of_id_le (u := index) (fun n => le_max_left _ _)
  let f := index ∘ phi
  have hf : StrictMono f := hindex
  choose p q hp hq hpR hqR using fun n =>
    (hthreshold (phi n) (f n) (le_max_right _ _)).2.2
  have hlim : Tendsto (fun n => radius (phi n)) atTop atTop := by
    have hcast : Tendsto (fun n => (phi n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hphi.tendsto_atTop
    simpa only [radius, add_comm B, add_assoc] using
      tendsto_atTop_add_const_right atTop (B + 1) hcast
  have href' : ∀ n, ((C.compSubseq f hf).domain n).referenceMetric =
      ((C.compSubseq f hf).domain n).limitMetric := fun n => href (f n)
  apply exists_pointed_metric_line_of_separated_points_in_compact_balls
    (C.compSubseq f hf) href' hcomplete hconnected
    (fun n => U (f n)) (fun n => S (f n)) (fun n => sep (f n)) hB
    (fun n => hS (f n)) p q hp hq (fun n => radius (phi n))
    (fun n => hB.trans (hradius (phi n)).le) hlim hpR hqR
    (fun n => (hthreshold (phi n) (f n) (le_max_right _ _)).1)
    (fun n => (hthreshold (phi n) (f n) (le_max_right _ _)).2.1)

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature
open DifferentialGeometry.Topology.SphereSeparation

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I}
  {subseq : ℕ → ℕ} {Phi : PointedRiemannianConvergenceMaps X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_pointed_metric_line_of_eventual_minimizing_segments_intersecting_bounded_sets
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (S : ∀ k, Set (X.obj (subseq k)).M) {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ k, S k ⊆ riemannianClosedBallOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint B)
    (hsegments : ∀ R : ℝ, B < R → ∀ᶠ k in atTop,
      ∃ (gamma : ℝ → (X.obj (subseq k)).M) (length : ℝ), 0 ≤ length ∧
        (∀ s ∈ Icc 0 length, ∀ t ∈ Icc 0 length,
          riemannianEDistOf (X.obj (subseq k)).metric (gamma s) (gamma t) =
            ENNReal.ofReal |s - t|) ∧
        (∃ t ∈ Icc 0 length, gamma t ∈ S k) ∧
        (riemannianEDistOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint
          (gamma 0)).toReal = R ∧
        (riemannianEDistOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint
          (gamma length)).toReal = R) :
    ∃ line : ℝ → L.M, ∀ s t : ℝ,
      riemannianEDistOf L.metric (line s) (line t) = ENNReal.ofReal |s - t| := by
  classical
  let radius (n : ℕ) : ℝ := B + n + 1
  have hradius (n : ℕ) : B < radius n := by
    dsimp only [radius]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose threshold hthreshold using fun n => eventually_atTop.mp (hsegments (radius n) (hradius n))
  let index : ℕ → ℕ := fun n => max n (threshold n)
  obtain ⟨phi, hphi, hindex⟩ := strictMono_subseq_of_id_le (u := index) (fun n => le_max_left _ _)
  let f := index ∘ phi
  have hf : StrictMono f := hindex
  choose gamma length hlength hmin hinter hleft hright using fun n =>
    hthreshold (phi n) (f n) (le_max_right _ _)
  have hlim : Tendsto (fun n => radius (phi n)) atTop atTop := by
    have hcast : Tendsto (fun n => (phi n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hphi.tendsto_atTop
    simpa only [radius, add_comm B, add_assoc] using
      tendsto_atTop_add_const_right atTop (B + 1) hcast
  have href' : ∀ n, ((C.compSubseq f hf).domain n).referenceMetric =
      ((C.compSubseq f hf).domain n).limitMetric := fun n => href (f n)
  apply exists_pointed_metric_line_of_minimizing_segments_intersecting_bounded_sets
    (C.compSubseq f hf) href' hcomplete hconnected (fun n => S (f n)) hB
    (fun n => hS (f n)) gamma length hlength hmin hinter
  · simpa only [Function.comp_apply, hleft] using hlim
  · simpa only [Function.comp_apply, hright] using hlim

end DifferentialGeometry.CheegerGromovCompactness
