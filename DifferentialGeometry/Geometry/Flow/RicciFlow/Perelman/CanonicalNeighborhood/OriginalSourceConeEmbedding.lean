import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.LocalDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalConeRange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalConeEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AnnularRepresentatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

theorem RealizedFiniteHorn.exists_original_source_forward_inverse_capture
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (H : RealizedFiniteHorn X.toFlowSequence)
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (N : ℕ)
    (j psi nseq : ℕ → ℕ) (hpsi : StrictMono psi)
    (hQ : ∀ n, 0 < metricScalarAt H.metric (ray.point (d (N + n))))
    {R : ℝ} (hR : 0 < R)
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R))
    (hdiagonal : ∀ i n : ℕ, n ≤ i →
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + n))) R
      ball ⊆ (H.maps (j i)).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled)
        (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
          ((X.term (H.subseq (j i))).S.base.metric 0)) (H.maps (j i)) ball {0} i
            (1 / ((i : ℝ) + 2))))
    {Q : Type v} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q] [IsManifold I3 ∞ Q]
    [T2Space Q] [SigmaCompactSpace Q]
    (g : SmoothRiemannianMetric I3 Q) (V U : TopologicalSpace.Opens Q)
    (hVU : V ≤ U) (q : Q) (hq : q ∈ V)
    (f : ∀ k, PartialDiffeomorph I3 I3 Q (X.term (H.subseq (j (psi (nseq k))))).M ∞)
    (G : ℕ → SmoothRiemannianMetric I3 U)
    (hG : MetricCInfConvergenceOnCompacts G (g.restrictOpen U) (g.restrictOpen U))
    (hsource : ∀ᶠ k in atTop, (U : Set Q) ⊆ (f k).source)
    (hmetric : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G k).inner x v w =
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
          ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)).inner (f k x)
            (mfderiv I3 I3 (f k) x v) (mfderiv I3 I3 (f k) x w))
    (hbase : ∀ k, f k q = H.maps (j (psi (nseq k))) (ray.point (d (N + nseq k)))) :
    ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf g q r) ∧
      riemannianClosedBallOf g q r ⊆ V ∧
      ∀ᶠ k in atTop, ∀ p ∈ riemannianClosedBallOf g q r,
        f k p ∈ (H.maps (j (psi (nseq k)))).target ∧
        (H.maps (j (psi (nseq k)))).symm (f k p) ∈
          riemannianClosedBallOf
            (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
              H.metric) (ray.point (d (N + nseq k))) (R / 32) ∧
        riemannianEDistOf
          (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
            H.metric) (ray.point (d (N + nseq k)))
            ((H.maps (j (psi (nseq k)))).symm (f k p)) < ENNReal.ofReal (R / 16) ∧
        H.maps (j (psi (nseq k))) ((H.maps (j (psi (nseq k)))).symm (f k p)) = f k p := by
  let target := fun k => scaleMetric
    (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
      ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)
  obtain ⟨R0, hR0, hR0compact, hR0V, hKcompact, hKV, _, hdist, _⟩ :=
    exists_uniform_local_distance_convergence_and_inverse_capture g V U hVU q hq
      target f G hG hsource hmetric
  let r : ℝ := min (R0 / 16) (R / 512)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR0 : r ≤ R0 / 16 := min_le_left _ _
  have hrR : r ≤ R / 512 := min_le_right _ _
  have hsub : riemannianClosedBallOf g q r ⊆ riemannianClosedBallOf g q (R0 / 16) :=
    riemannianClosedBallOf_mono g q hrR0
  have hqc : q ∈ riemannianClosedBallOf g q (R0 / 16) := by
    change riemannianEDistOf g q q ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  refine ⟨r, hr, hKcompact.of_isClosed_subset
    (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist g q) continuous_const) hsub,
    hsub.trans hKV, ?_⟩
  filter_upwards [hdist (R / 512) (by positivity)] with k hk
  intro p hp
  have hpair := hk q hqc p (hsub hp)
  have hdp : (riemannianEDistOf g q p).toReal ≤ r :=
    ENNReal.toReal_le_of_le_ofReal hr.le hp
  have hsourceDist : riemannianEDistOf (target k) (f k q) (f k p) ≤
      ENNReal.ofReal (R / 128) := by
    let _ : ConnectedSpace (X.term (H.subseq (j (psi (nseq k))))).M :=
      X.connected (H.subseq (j (psi (nseq k))))
    have hfinite := riemannianEDistOf_ne_top (target k) (f k q) (f k p)
    rw [← ENNReal.ofReal_toReal hfinite]
    apply ENNReal.ofReal_le_ofReal
    have hu := (abs_lt.mp hpair).2
    linarith
  let hornMetric := scaleMetric
    (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k)) H.metric
  let center := ray.point (d (N + nseq k))
  let Hmap := H.maps (j (psi (nseq k)))
  have hsmallsub : riemannianClosedBallOf hornMetric center (R / 32) ⊆
      riemannianClosedBallOf hornMetric center R := riemannianClosedBallOf_mono _ _ (by linarith)
  have hcpt : IsCompact (riemannianClosedBallOf hornMetric center (R / 32)) :=
    (hcompact (nseq k)).of_isClosed_subset
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist hornMetric center)
        continuous_const) hsmallsub
  obtain ⟨hHsource, ⟨cmp⟩⟩ := hdiagonal (psi (nseq k)) (nseq k) (hpsi.id_le _)
  have hHsource' : riemannianClosedBallOf hornMetric center (R / 32) ⊆ Hmap.source :=
    hsmallsub.trans hHsource
  have heps : 1 / ((psi (nseq k) : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    linarith [Nat.cast_nonneg (α := ℝ) (psi (nseq k))]
  have hlower : ∀ z ∈ riemannianClosedBallOf hornMetric center (R / 32),
      ∀ v : TangentSpace I3 z, hornMetric.inner z v v ≤
        (2 : ℝ) ^ 2 * (target k).inner (Hmap z)
          (mfderiv I3 I3 Hmap z v) (mfderiv I3 I3 Hmap z v) := by
    intro z hz v
    have hzbig := hsmallsub hz
    have hcmp := (cmp.equivalence 0 (by simp) z hzbig v).1
    rw [cmp.pullback_eq 0 z hzbig (fun _ => v)] at hcmp
    have hv := inner_self_nonneg hornMetric z v
    have htarget := inner_self_nonneg (target k) (Hmap z) (mfderiv I3 I3 Hmap z v)
    change (1 - 1 / ((psi (nseq k) : ℝ) + 2)) * hornMetric.inner z v v ≤
      (target k).inner (Hmap z) (mfderiv I3 I3 Hmap z v) (mfderiv I3 I3 Hmap z v) at hcmp
    nlinarith
  have hcapture := closedBall_subset_image_of_metric_lower_crossModel hornMetric (target k)
    Hmap center (R := R / 32) (L := 2) (r := R / 128) (by positivity) (by norm_num)
      (by linarith) hcpt hHsource' hlower
  have hsourceDist' : f k p ∈ riemannianClosedBallOf (target k) (Hmap center) (R / 128) := by
    change riemannianEDistOf (target k) (Hmap center) (f k p) ≤ _
    simpa only [Hmap, center, hbase k] using hsourceDist
  obtain ⟨w, hw, hwp⟩ := hcapture hsourceDist'
  have hwsource := hHsource' hw
  have htarget : f k p ∈ Hmap.target := hwp ▸ Hmap.map_source hwsource
  have hinv : Hmap.symm (f k p) = w := by
    rw [← hwp]
    exact Hmap.left_inv hwsource
  refine ⟨htarget, hinv ▸ hw, ?_, Hmap.right_inv htarget⟩
  change riemannianEDistOf hornMetric center (Hmap.symm (f k p)) < _
  rw [hinv]
  exact hw.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact EndAngles.metric

theorem RealizedFiniteHorn.range_mem_nhds_of_marked_original_source_inverse_family
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (H : RealizedFiniteHorn X.toFlowSequence)
    (angles : EndAngles H.horn) [CompactSpace (UniformSpace.Completion angles.quotient)]
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (N : ℕ)
    (C : AnnularConvergence H.horn angles ray d)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (j psi nseq : ℕ → ℕ) (hpsi : StrictMono psi) (hnseq : StrictMono nseq)
    (hQ : ∀ n, 0 < metricScalarAt H.metric (ray.point (d (N + n))))
    {a b lambda R : ℝ} (ha : 0 < a) (hlambda : 0 < lambda)
    (ha1 : a < 1) (h1b : 1 < b) (hR : 0 < R)
    (hscale : Tendsto (fun k => Real.sqrt
      (metricScalarAt H.metric (ray.point (d (N + nseq k))) * d (N + nseq k) ^ 2))
      atTop (𝓝 lambda))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R))
    (hdiagonal : ∀ i n : ℕ, n ≤ i →
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + n))) R
      ball ⊆ (H.maps (j i)).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled)
        (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
          ((X.term (H.subseq (j i))).S.base.metric 0)) (H.maps (j i)) ball {0} i
            (1 / ((i : ℝ) + 2))))
    {Q : Type v} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q] [IsManifold I3 ∞ Q]
    [T2Space Q] [SigmaCompactSpace Q]
    (g : SmoothRiemannianMetric I3 Q) (V U : TopologicalSpace.Opens Q)
    (hVU : V ≤ U) (q : Q) (hq : q ∈ V)
    (f : ∀ k, PartialDiffeomorph I3 I3 Q (X.term (H.subseq (j (psi (nseq k))))).M ∞)
    (G : ℕ → SmoothRiemannianMetric I3 U)
    (hG : MetricCInfConvergenceOnCompacts G (g.restrictOpen U) (g.restrictOpen U))
    (hsource : ∀ᶠ k in atTop, (U : Set Q) ⊆ (f k).source)
    (hmetric : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G k).inner x v w =
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
          ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)).inner (f k x)
            (mfderiv I3 I3 (f k) x v) (mfderiv I3 I3 (f k) x w))
    (hbase : ∀ k, f k q = H.maps (j (psi (nseq k))) (ray.point (d (N + nseq k))))
    (rK : ℝ) (hrK : 0 < rK) (hKV : riemannianClosedBallOf g q rK ⊆ V)
    (herror : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
      ∀ p ∈ riemannianClosedBallOf g q rK, ∀ z ∈ riemannianClosedBallOf g q rK,
        |(riemannianEDistOf
          (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
            ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)) (f k p) (f k z)).toReal -
            (riemannianEDistOf g p z).toReal| < epsilon)
    (D : Set (ℝ × UniformSpace.Completion angles.quotient)) (hD : IsOpen D)
    (hoD : (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) ∈ D)
    (Psi : D → V) (u : ℕ → D → V) (hcluster : MapClusterPt Psi atTop u)
    (huK : ∀ k (x : D), (u k x : Q) ∈ riemannianClosedBallOf g q rK)
    (y : D → ℕ → ℝ × UniformSpace.Completion angles.quotient) (w : D → ℕ → H.space)
    (hy : ∀ x : D, Tendsto (y x) atTop (𝓝 (x : ℝ × UniformSpace.Completion angles.quotient)))
    (hw : ∀ x : D, ∀ᶠ k in atTop,
      (y x k, w x k) ∈ C.relation a b (N + nseq k) ∧
      metricDistance (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k))))
        (hQ (nseq k)) H.metric) (ray.point (d (N + nseq k))) (w x k) ≤ R / 16 ∧
      f k (u k x) = H.maps (j (psi (nseq k))) (w x k)) :
    range (fun x => (Psi x : Q)) ∈ 𝓝 q := by
  let index : ℕ → ℕ := fun k => N + nseq k
  have hindex : StrictMono index := fun k l hkl => Nat.add_lt_add_left (hnseq hkl) N
  let Cs := C.compSubseq index hindex
  let target := fun k => scaleMetric
    (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
      ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)
  have hcompare : ∀ᶠ k in atTop,
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k))))
        (hQ (nseq k)) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + nseq k))) R
      ball ⊆ (H.maps (j (psi (nseq k)))).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled) (fun _ => target k)
        (H.maps (j (psi (nseq k)))) ball {0} 0 (1 / ((k : ℝ) + 2))) := by
    apply Eventually.of_forall
    intro k
    obtain ⟨hsrc, ⟨cmp⟩⟩ := hdiagonal (psi (nseq k)) (nseq k) (hpsi.id_le _)
    refine ⟨hsrc, ⟨cmp.mono (subset_refl _) (Nat.zero_le _) ?_⟩⟩
    apply one_div_le_one_div_of_le (by positivity)
    have hik : k ≤ psi (nseq k) := (hnseq.id_le k).trans (hpsi.id_le _)
    exact_mod_cast Nat.add_le_add_right hik 2
  obtain ⟨delta, hdelta, _, honto⟩ := Cs.exists_capture_radius_subset_range ha hlambda ha1 h1b hR
    (fun k => hd (N + nseq k)) (fun k => hQ (nseq k)) hscale target
    (fun k => H.maps (j (psi (nseq k)))) hcompare g V q rK f herror D hD hoD
    Psi u hcluster huK y w hy hw
  let R' := min R (16 * delta)
  have hR' : 0 < R' := lt_min hR (by positivity)
  have hsub (n : ℕ) : riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R' ⊆ riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R := riemannianClosedBallOf_mono _ _ (min_le_left _ _)
  have hcompact' (n : ℕ) : IsCompact (riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R') :=
    (hcompact n).of_isClosed_subset
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const) (hsub n)
  have hdiagonal' : ∀ i n : ℕ, n ≤ i →
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + n))) R'
      ball ⊆ (H.maps (j i)).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled)
        (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
          ((X.term (H.subseq (j i))).S.base.metric 0)) (H.maps (j i)) ball {0} i
            (1 / ((i : ℝ) + 2))) := by
    intro i n hni
    obtain ⟨hsrc, ⟨cmp⟩⟩ := hdiagonal i n hni
    exact ⟨(hsub n).trans hsrc, ⟨cmp.mono (hsub n) le_rfl le_rfl⟩⟩
  obtain ⟨r0, hr0, _, _, hforward⟩ := H.exists_original_source_forward_inverse_capture X ray d N
    j psi nseq hpsi hQ hR' hcompact' hdiagonal' g V U hVU q hq f G hG hsource hmetric hbase
  let r := min r0 rK
  have hr : 0 < r := lt_min hr0 hrK
  have hballopen : IsOpen (riemannianBallOf g q r) :=
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist g q) continuous_const
  have hqball : q ∈ riemannianBallOf g q r := by
    change riemannianEDistOf g q q < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  apply Filter.mem_of_superset (hballopen.mem_nhds hqball)
  intro p hp
  have hpr : p ∈ riemannianClosedBallOf g q r := by
    change riemannianEDistOf g q p ≤ ENNReal.ofReal r
    exact (show riemannianEDistOf g q p < ENNReal.ofReal r from hp).le
  have hp0 : p ∈ riemannianClosedBallOf g q r0 :=
    riemannianClosedBallOf_mono g q (min_le_left r0 rK) hpr
  have hpK : p ∈ riemannianClosedBallOf g q rK :=
    riemannianClosedBallOf_mono g q (min_le_right r0 rK) hpr
  let pV : V := ⟨p, hKV hpK⟩
  let v : ℕ → H.space := fun k => (H.maps (j (psi (nseq k)))).symm (f k p)
  have hv : ∀ᶠ k in atTop,
      metricDistance (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k))))
        (hQ (nseq k)) H.metric) (ray.point (d (N + nseq k))) (v k) ≤ delta ∧
        H.maps (j (psi (nseq k))) (v k) = f k pV := by
    filter_upwards [hforward] with k hk
    have hkp := hk p hp0
    have hb : metricDistance
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k)) H.metric)
          (ray.point (d (N + nseq k))) (v k) ≤ R' / 32 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hkp.2.1
    refine ⟨hb.trans ?_, hkp.2.2.2⟩
    have hh : R' ≤ 16 * delta := min_le_right _ _
    linarith
  obtain ⟨x, hx⟩ := honto pV hpK v hv
  exact ⟨x, congrArg (fun z : V => (z : Q)) hx⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact EndAngles.metric

theorem RealizedFiniteHorn.exists_marked_original_source_local_cone_embedding
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (H : RealizedFiniteHorn X.toFlowSequence)
    (angles : EndAngles H.horn) [CompactSpace (UniformSpace.Completion angles.quotient)]
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (N : ℕ)
    (C : AnnularConvergence H.horn angles ray d)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (j psi nseq : ℕ → ℕ) (hpsi : StrictMono psi) (hnseq : StrictMono nseq)
    (hQ : ∀ n, 0 < metricScalarAt H.metric (ray.point (d (N + n))))
    {a b lambda R : ℝ} (ha : 0 < a) (hlambda : 0 < lambda)
    (ha1 : a < 1) (h1b : 1 < b) (hR : 0 < R)
    (hscale : Tendsto (fun k => Real.sqrt
      (metricScalarAt H.metric (ray.point (d (N + nseq k))) * d (N + nseq k) ^ 2))
      atTop (𝓝 lambda))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R))
    (hdiagonal : ∀ i n : ℕ, n ≤ i →
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + n))) R
      ball ⊆ (H.maps (j i)).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled)
        (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
          ((X.term (H.subseq (j i))).S.base.metric 0)) (H.maps (j i)) ball {0} i
            (1 / ((i : ℝ) + 2))))
    {Q : Type v} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q] [IsManifold I3 ∞ Q]
    [T2Space Q] [SigmaCompactSpace Q]
    (g : SmoothRiemannianMetric I3 Q) (V U : TopologicalSpace.Opens Q)
    (hVU : V ≤ U) (q : Q) (hq : q ∈ V)
    (f : ∀ k, PartialDiffeomorph I3 I3 Q (X.term (H.subseq (j (psi (nseq k))))).M ∞)
    (G : ℕ → SmoothRiemannianMetric I3 U)
    (hG : MetricCInfConvergenceOnCompacts G (g.restrictOpen U) (g.restrictOpen U))
    (hsource : ∀ᶠ k in atTop, (U : Set Q) ⊆ (f k).source)
    (hmetric : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G k).inner x v w =
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
          ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)).inner (f k x)
            (mfderiv I3 I3 (f k) x v) (mfderiv I3 I3 (f k) x w))
    (hbase : ∀ k, f k q = H.maps (j (psi (nseq k))) (ray.point (d (N + nseq k))))
 :
    ∃ D : Set (ℝ × UniformSpace.Completion angles.quotient), IsOpen D ∧
      (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) ∈ D ∧
      (∀ x ∈ D, x.1 ∈ Ioo a b) ∧
      ∃ Psi : D → V, Topology.IsEmbedding Psi ∧
        range (fun x => (Psi x : Q)) ∈ 𝓝 q ∧
        (∀ x : D, (x : ℝ × UniformSpace.Completion angles.quotient) =
          (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) → (Psi x : Q) = q) ∧
        (∀ x z : D, (riemannianEDistOf (g.restrictOpen V) (Psi x) (Psi z)).toReal =
          lambda * Metric.coneDistance (x : ℝ × UniformSpace.Completion angles.quotient)
            (z : ℝ × UniformSpace.Completion angles.quotient)) ∧
        ∃ (u : ℕ → D → V)
          (y : D → ℕ → ℝ × UniformSpace.Completion angles.quotient) (w : D → ℕ → H.space),
          MapClusterPt Psi atTop u ∧
          (∀ x : D, Tendsto (y x) atTop (𝓝 (x : ℝ × UniformSpace.Completion angles.quotient))) ∧
          ∀ x : D, ∀ᶠ k in atTop,
            (y x k, w x k) ∈ C.relation a b (N + nseq k) ∧
            (u k x : Q) = (f k).symm (H.maps (j (psi (nseq k))) (w x k)) ∧
            f k (u k x) = H.maps (j (psi (nseq k))) (w x k) := by
  let index : ℕ → ℕ := fun k => N + nseq k
  have hindex : StrictMono index := fun k l hkl => Nat.add_lt_add_left (hnseq hkl) N
  let Cs := C.compSubseq index hindex
  let target := fun k => scaleMetric
    (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
      ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)
  have hcompare : ∀ᶠ k in atTop,
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k))))
        (hQ (nseq k)) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + nseq k))) R
      IsCompact ball ∧ ball ⊆ (H.maps (j (psi (nseq k)))).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled) (fun _ => target k)
        (H.maps (j (psi (nseq k)))) ball {0} 0 (1 / ((k : ℝ) + 2))) := by
    apply Eventually.of_forall
    intro k
    obtain ⟨hsrc, ⟨cmp⟩⟩ := hdiagonal (psi (nseq k)) (nseq k) (hpsi.id_le _)
    refine ⟨hcompact (nseq k), hsrc, ⟨cmp.mono (subset_refl _) (Nat.zero_le _) ?_⟩⟩
    apply one_div_le_one_div_of_le (by positivity)
    have hik : k ≤ psi (nseq k) := (hnseq.id_le k).trans (hpsi.id_le _)
    exact_mod_cast Nat.add_le_add_right hik 2
  obtain ⟨A, _, hAR, K, _, hKV, ⟨rK, hrK, hKrK⟩, herror,
    D, hD, hoD, hradial, Psi, u, y, w, hemb, hcluster, _, huK, hbasepoint, hdist, hy, hw⟩ :=
    Cs.exists_marked_local_cone_embedding_of_local_metric_limit ha hlambda ha1 h1b hR
      (fun k => hd (N + nseq k)) (fun k => hQ (nseq k)) hscale target
      (fun k => H.maps (j (psi (nseq k)))) hcompare g V U hVU q hq f G hG hsource hmetric hbase
  subst K
  have hrange := H.range_mem_nhds_of_marked_original_source_inverse_family X angles ray d N C hd
    j psi nseq hpsi hnseq hQ ha hlambda ha1 h1b hR hscale hcompact hdiagonal
    g V U hVU q hq f G hG hsource hmetric hbase rK hrK hKV herror D hD hoD
    Psi u hcluster huK y w hy (fun x => (hw x).mono fun _ hi =>
      ⟨hi.1, hi.2.1.le.trans hAR, hi.2.2.2⟩)
  refine ⟨D, hD, hoD, hradial, Psi, hemb, hrange, hbasepoint, hdist, u, y, w,
    hcluster, hy, ?_⟩
  intro x
  filter_upwards [hw x] with k hk
  exact ⟨hk.1, hk.2.2.1, hk.2.2.2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
