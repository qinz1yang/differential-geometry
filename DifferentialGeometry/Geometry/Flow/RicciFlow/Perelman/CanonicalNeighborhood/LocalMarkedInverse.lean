import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AnnularRepresentatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.LocalDistance
import DifferentialGeometry.Topology.Compactness.MapLimits

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v q

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W]
  {M : ℕ → Type v} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)]
  {Q : Type q} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q]

attribute [local instance] EndAngles.metric

theorem AnnularConvergence.exists_marked_inverse_representatives_of_metric_comparison
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
    [CompactSpace (UniformSpace.Completion angles.quotient)]
    {ray : EndRay H.endpoint} {d : ℕ → ℝ} (C : AnnularConvergence H angles ray d)
    {a b lambda R s : ℝ} (ha : 0 < a) (ha1 : a < 1) (h1b : 1 < b)
    (hR : 0 < R) (hs : 0 < s)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    (target : ∀ i, SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 W (M i) ∞)
    (f : ∀ i, PartialDiffeomorph I3 I3 Q (M i) ∞) (K : Set Q)
    (hcompare : ∀ᶠ i in atTop,
      let scaled := scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
      let ball := riemannianClosedBallOf scaled (ray.point (d i)) R
      ball ⊆ (F i).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled) (fun _ => target i) (F i)
        ball {0} 0 (1 / ((i : ℝ) + 2))))
    (hcapture : ∀ᶠ i in atTop, K ⊆ (f i).source ∧
      riemannianClosedBallOf (target i) (F i (ray.point (d i))) s ⊆ (f i) '' K) :
    ∃ A : ℝ, 0 < A ∧ A ≤ R / 16 ∧ 2 * A ≤ s ∧
      ∀ x : ℝ × UniformSpace.Completion angles.quotient, x.1 ∈ Icc a b →
        lambda * Metric.coneDistance
          (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) x < A →
        ∃ (y : ℕ → ℝ × UniformSpace.Completion angles.quotient) (w : ℕ → W),
          Tendsto y atTop (𝓝 x) ∧
          (∀ᶠ i in atTop, (y i, w i) ∈ C.relation a b i ∧
            Metric.coneDistance x (y i) < C.error a b i) ∧
          ∀ᶠ i in atTop,
            metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
              (ray.point (d i)) (w i) < A ∧
            w i ∈ (F i).source ∧ F i (w i) ∈ (f i).target ∧
            (f i).symm (F i (w i)) ∈ K ∧
            f i ((f i).symm (F i (w i))) = F i (w i) := by
  let A := min (R / 16) (s / 2)
  have hA : 0 < A := lt_min (by positivity) (by positivity)
  have hAR : A ≤ R / 16 := min_le_left _ _
  have hAs : 2 * A ≤ s := by have := min_le_right (R / 16) (s / 2); dsimp only [A]; linarith
  refine ⟨A, hA, hAR, hAs, ?_⟩
  intro x hx hxA
  obtain ⟨y, w, hy, hrel, _hlim, hnear⟩ :=
    C.exists_curvature_rescaled_marked_representatives ha ha1 h1b hd hQ hscale x hx hxA
  refine ⟨y, w, hy, hrel, ?_⟩
  filter_upwards [hcompare, hcapture, hnear] with i hcmp hcap hwi
  let scaled := scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
  let ball := riemannianClosedBallOf scaled (ray.point (d i)) R
  have hfinite (z z' : W) : riemannianEDistOf scaled z z' ≠ ⊤ := by
    dsimp only [scaled]
    rw [edistOf_scale, H.edist_eq_ofReal_dist]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hwA : w i ∈ riemannianClosedBallOf scaled (ray.point (d i)) A := by
    change riemannianEDistOf scaled (ray.point (d i)) (w i) ≤ ENNReal.ofReal A
    apply (ENNReal.toReal_le_toReal (hfinite _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hA.le]
    exact hwi.le
  have hwR : w i ∈ ball := riemannianClosedBallOf_mono scaled (ray.point (d i))
    (show A ≤ R by linarith) hwA
  obtain ⟨hsource, ⟨cmp⟩⟩ := hcmp
  have heps : 1 / ((i : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hup : ∀ z ∈ ball, ∀ v : TangentSpace I3 z,
      (target i).inner (F i z) (mfderiv I3 I3 (F i) z v) (mfderiv I3 I3 (F i) z v) ≤
        (2 : ℝ) ^ 2 * scaled.inner z v v := by
    intro z hz v
    have hh := (cmp.equivalence 0 (by simp) z hz v).2
    rw [cmp.pullback_eq 0 z hz (fun _ => v)] at hh
    have hn := metric_inner_self_nonneg scaled z v
    change (target i).inner (F i z) (mfderiv I3 I3 (F i) z v) (mfderiv I3 I3 (F i) z v) ≤
      (1 + 1 / ((i : ℝ) + 2)) * scaled.inner z v v at hh
    nlinarith
  have hcenter : ray.point (d i) ∈ riemannianClosedBallOf scaled (ray.point (d i)) A := by
    change riemannianEDistOf scaled _ _ ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hdist := crossModel_edist_le_of_metric_upper scaled (target i) (F i)
    (ray.point (d i)) (L := 2) (by norm_num) hA.le
    (show 3 * A < R by linarith) hsource hup hcenter hwA
  have htball : F i (w i) ∈ riemannianClosedBallOf (target i) (F i (ray.point (d i))) s := by
    refine hdist.trans ?_
    calc ENNReal.ofReal 2 * riemannianEDistOf scaled (ray.point (d i)) (w i)
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal A := mul_le_mul' le_rfl hwA
      _ = ENNReal.ofReal (2 * A) := (ENNReal.ofReal_mul (by norm_num)).symm
      _ ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal hAs
  obtain ⟨p, hp, heq⟩ := hcap.2 htball
  have hptarget : F i (w i) ∈ (f i).target := heq ▸ (f i).map_source (hcap.1 hp)
  have hinverse : (f i).symm (F i (w i)) = p := by
    rw [← heq]
    exact (f i).left_inv (hcap.1 hp)
  exact ⟨hwi, hsource hwR, hptarget, hinverse.symm ▸ hp, (f i).right_inv hptarget⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {W : Type*} [TopologicalSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [T2Space W]
  {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]

theorem tendsto_metricDistance_map_of_local_comparison
    (g : ℕ → SmoothRiemannianMetric I3 W) (h : ∀ i, SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 W (M i) ∞) (p : ℕ → W)
    {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hsmall : r ≤ R / 16)
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0))
    (hnonneg : ∀ᶠ i in atTop, 0 ≤ eps i)
    (hcmp : ∀ᶠ i in atTop,
      IsCompact (riemannianClosedBallOf (g i) (p i) R) ∧
      riemannianClosedBallOf (g i) (p i) R ⊆ (F i).source ∧
      ∀ y ∈ riemannianClosedBallOf (g i) (p i) R, ∀ v : TangentSpace I3 y,
        (1 - eps i) * (g i).inner y v v ≤
            (h i).inner (F i y) (mfderiv I3 I3 (F i) y v) (mfderiv I3 I3 (F i) y v) ∧
        (h i).inner (F i y) (mfderiv I3 I3 (F i) y v) (mfderiv I3 I3 (F i) y v) ≤
            (1 + eps i) * (g i).inner y v v)
    (w z : ℕ → W)
    (hpoints : ∀ᶠ i in atTop, w i ∈ riemannianClosedBallOf (g i) (p i) r ∧
      z i ∈ riemannianClosedBallOf (g i) (p i) r)
    {D : ℝ} (hdist : Tendsto (fun i => metricDistance (g i) (w i) (z i)) atTop (𝓝 D)) :
    Tendsto (fun i => metricDistance (h i) (F i (w i)) (F i (z i))) atTop (𝓝 D) := by
  have hlo : Tendsto (fun i => Real.sqrt (1 - eps i)) atTop (𝓝 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (1 : ℝ))).sub heps)
    simp only [sub_zero, Real.sqrt_one] at h
    exact h
  have hup : Tendsto (fun i => Real.sqrt (1 + eps i)) atTop (𝓝 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (1 : ℝ))).add heps)
    simp only [add_zero, Real.sqrt_one] at h
    exact h
  have hbounds : ∀ᶠ i in atTop,
      Real.sqrt (1 - eps i) * metricDistance (g i) (w i) (z i) ≤
        metricDistance (h i) (F i (w i)) (F i (z i)) ∧
      metricDistance (h i) (F i (w i)) (F i (z i)) ≤
        Real.sqrt (1 + eps i) * metricDistance (g i) (w i) (z i) := by
    filter_upwards [hcmp, hpoints, hnonneg,
      heps.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with i hc hp he hhalf
    have hm : 1 / 2 < Real.sqrt (1 - eps i) := by
      have hpos : 0 ≤ 1 - eps i := by linarith
      have hs := Real.sq_sqrt hpos
      nlinarith [Real.sqrt_nonneg (1 - eps i)]
    have hM : Real.sqrt (1 + eps i) < 2 := by
      have hpos : 0 ≤ 1 + eps i := by linarith
      have hs := Real.sq_sqrt hpos
      nlinarith [Real.sqrt_nonneg (1 + eps i)]
    have hroom : Real.sqrt (1 + eps i) * (3 * r) < Real.sqrt (1 - eps i) * R := by
      have h1 : Real.sqrt (1 + eps i) * (3 * r) ≤ 2 * (3 * r) :=
        mul_le_mul_of_nonneg_right hM.le (by positivity)
      have h2 : R / 2 < Real.sqrt (1 - eps i) * R := by nlinarith
      linarith
    exact crossModel_metricDistance_transfer (g i) (h i) (F i) (p i) hR he
      (by linarith) hr hc.1 hc.2.1 hc.2.2 hroom (w i) hp.1 (z i) hp.2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [one_mul] using hlo.mul hdist)
    (by simpa only [one_mul] using hup.mul hdist)
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {W : Type*} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
  [SigmaCompactSpace W]
  {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]
  {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
  {ray : EndRay H.endpoint} {d : ℕ → ℝ}

attribute [local instance] EndAngles.metric

theorem AnnularConvergence.tendsto_source_distance_of_marked_representatives
    (C : AnnularConvergence H angles ray d) {a b lambda R r : ℝ}
    (ha : 0 < a) (hab : a < b) (hR : 0 < R) (hr : 0 ≤ r) (hsmall : r ≤ R / 16)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    (target : ∀ i, SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 W (M i) ∞)
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0))
    (hnonneg : ∀ᶠ i in atTop, 0 ≤ eps i)
    (hcompare : ∀ᶠ i in atTop,
      let scaled := scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
      let ball := riemannianClosedBallOf scaled (ray.point (d i)) R
      IsCompact ball ∧ ball ⊆ (F i).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled) (fun _ => target i) (F i) ball {0} 0 (eps i)))
    (x y : ℕ → ℝ × UniformSpace.Completion angles.quotient) (w z : ℕ → W)
    {x₀ y₀ : ℝ × UniformSpace.Completion angles.quotient}
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀))
    (hw : ∀ᶠ i in atTop, (x i, w i) ∈ C.relation a b i)
    (hz : ∀ᶠ i in atTop, (y i, z i) ∈ C.relation a b i)
    (hnear : ∀ᶠ i in atTop,
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) (w i) ≤ r ∧
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) (z i) ≤ r) :
    Tendsto (fun i => metricDistance (target i) (F i (w i)) (F i (z i))) atTop
      (𝓝 (lambda * Metric.coneDistance x₀ y₀)) := by
  let scaled := fun i => scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
  apply tendsto_metricDistance_map_of_local_comparison scaled target F (fun i => ray.point (d i))
    hR hr hsmall eps heps hnonneg
  · filter_upwards [hcompare] with i hi
    obtain ⟨cmp⟩ := hi.2.2
    refine ⟨hi.1, hi.2.1, ?_⟩
    intro y hy v
    have h := cmp.equivalence 0 (by simp) y hy v
    rw [cmp.pullback_eq 0 y hy (fun _ => v)] at h
    exact h
  · filter_upwards [hnear] with i hi
    have hfinite (v : W) : riemannianEDistOf (scaled i) (ray.point (d i)) v ≠ ⊤ := by
      dsimp only [scaled]
      rw [edistOf_scale, H.edist_eq_ofReal_dist]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    constructor
    · apply (ENNReal.toReal_le_toReal (hfinite _) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal hr]
      exact hi.1
    · apply (ENNReal.toReal_le_toReal (hfinite _) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal hr]
      exact hi.2
  · exact C.tendsto_curvature_scaled_distance_of_representatives ha hab hd hQ hscale x y w z
      hx hy hw hz

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {W : Type*} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
  [SigmaCompactSpace W]
  {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q]
  [IsManifold I3 ∞ Q] [T2Space Q] [SigmaCompactSpace Q]
  {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
  {ray : EndRay H.endpoint} {d : ℕ → ℝ}

attribute [local instance] EndAngles.metric

theorem AnnularConvergence.exists_local_marked_inverse_distance_family_in_ball
    [CompactSpace (UniformSpace.Completion angles.quotient)]
    (C : AnnularConvergence H angles ray d) {a b lambda R : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (h1b : 1 < b) (hR : 0 < R)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    (target : ∀ i, SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 W (M i) ∞)
    (hcompare : ∀ᶠ i in atTop,
      let scaled := scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
      let ball := riemannianClosedBallOf scaled (ray.point (d i)) R
      IsCompact ball ∧ ball ⊆ (F i).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled) (fun _ => target i) (F i)
        ball {0} 0 (1 / ((i : ℝ) + 2))))
    (gQ : SmoothRiemannianMetric I3 Q) (V U : TopologicalSpace.Opens Q)
    (hVU : V ≤ U) (q : Q) (hq : q ∈ V)
    (f : ∀ i, PartialDiffeomorph I3 I3 Q (M i) ∞)
    (G : ℕ → SmoothRiemannianMetric I3 U)
    (hG : MetricCInfConvergenceOnCompacts G (gQ.restrictOpen U) (gQ.restrictOpen U))
    (hfsource : ∀ᶠ i in atTop, (U : Set Q) ⊆ (f i).source)
    (hmetric : ∀ᶠ i in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G i).inner x v w = (target i).inner (f i x)
        (mfderiv I3 I3 (f i) x v) (mfderiv I3 I3 (f i) x w))
    (hbase : ∀ i, f i q = F i (ray.point (d i))) :
    ∃ A : ℝ, 0 < A ∧ A ≤ R / 16 ∧
      ∃ K : Set Q, IsCompact K ∧ K ⊆ V ∧ q ∈ K ∧
      (∃ rK : ℝ, 0 < rK ∧ K = riemannianClosedBallOf gQ q rK) ∧
      (∀ x y : V, (x : Q) ∈ K → (y : Q) ∈ K →
        riemannianEDistOf (gQ.restrictOpen V) x y = riemannianEDistOf gQ x y) ∧
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ i in atTop, ∀ p ∈ K, ∀ z ∈ K,
        |(riemannianEDistOf (target i) (f i p) (f i z)).toReal -
          (riemannianEDistOf gQ p z).toReal| < epsilon) ∧
      let D := {x : ℝ × UniformSpace.Completion angles.quotient |
        x.1 ∈ Icc a b ∧ lambda * Metric.coneDistance
          (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) x < A}
      ∃ (y : D → ℕ → ℝ × UniformSpace.Completion angles.quotient) (w : D → ℕ → W),
        (∀ x : D, Tendsto (y x) atTop (𝓝 (x : ℝ × UniformSpace.Completion angles.quotient))) ∧
        (∀ x : D, ∀ᶠ i in atTop, (y x i, w x i) ∈ C.relation a b i ∧
          Metric.coneDistance x (y x i) < C.error a b i) ∧
        (∀ x : D, ∀ᶠ i in atTop,
          metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
            (ray.point (d i)) (w x i) < A ∧
          (f i).symm (F i (w x i)) ∈ K ∧
          f i ((f i).symm (F i (w x i))) = F i (w x i)) ∧
        (∀ x z : D, Tendsto (fun i =>
          (riemannianEDistOf gQ ((f i).symm (F i (w x i))) ((f i).symm (F i (w z i)))).toReal)
          atTop (𝓝 (lambda * Metric.coneDistance (x : ℝ × UniformSpace.Completion angles.quotient)
            (z : ℝ × UniformSpace.Completion angles.quotient)))) ∧
        ∀ x : D, (x : ℝ × UniformSpace.Completion angles.quotient) =
          (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) →
          Tendsto (fun i => (riemannianEDistOf gQ ((f i).symm (F i (w x i))) q).toReal)
            atTop (𝓝 0) := by
  classical
  obtain ⟨L, hL, _hLcompact, _hLV, hKcompact, hKV, hrestricted, herror, hcapture⟩ :=
    exists_uniform_local_distance_convergence_and_inverse_capture gQ V U hVU q hq target f G hG
      hfsource hmetric
  let K := riemannianClosedBallOf gQ q (L / 16)
  have hcap : ∀ᶠ i in atTop, K ⊆ (f i).source ∧
      riemannianClosedBallOf (target i) (F i (ray.point (d i))) (L / 64) ⊆ (f i) '' K := by
    filter_upwards [hcapture] with i hi
    refine ⟨hi.1, ?_⟩
    intro z hz
    have hz' : z ∈ riemannianClosedBallOf (target i) (f i q) (L / 64) := by rwa [hbase i]
    obtain ⟨_, hmem, heq⟩ := hi.2 z hz'
    exact ⟨(f i).symm z, hmem, heq⟩
  obtain ⟨A, hA, hAR, _hAs, hselect⟩ :=
    C.exists_marked_inverse_representatives_of_metric_comparison ha ha1 h1b hR (by positivity : 0 < L / 64)
      hd hQ hscale target F f K (hcompare.mono fun i hi => hi.2) hcap
  have hqK : q ∈ K := by
    change riemannianEDistOf gQ q q ≤ ENNReal.ofReal (L / 16)
    rw [riemannianEDistOf_self]
    exact bot_le
  refine ⟨A, hA, hAR, K, hKcompact, hKV, hqK, ⟨L / 16, by positivity, rfl⟩,
    hrestricted, herror, ?_⟩
  let D := {x : ℝ × UniformSpace.Completion angles.quotient |
    x.1 ∈ Icc a b ∧ lambda * Metric.coneDistance
      (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) x < A}
  have hchoose := fun x : D => hselect x x.property.1 x.property.2
  choose y w hy hrel hinv using hchoose
  have heps : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 2)) atTop (𝓝 0) := by
    have hc : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have h : Tendsto (fun i : ℕ => ((i : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hc
    simpa only [one_div] using h
  refine ⟨y, w, hy, hrel, ?_, ?_, ?_⟩
  · intro x
    filter_upwards [hinv x] with i hi
    exact ⟨hi.1, hi.2.2.2.1, hi.2.2.2.2⟩
  · intro x z
    have hsourceDist := C.tendsto_source_distance_of_marked_representatives ha (ha1.trans h1b)
      hR hA.le hAR hd hQ hscale target F (fun i => 1 / ((i : ℝ) + 2)) heps
      (Eventually.of_forall fun _ => by positivity) hcompare (y x) (y z) (w x) (w z)
      (hy x) (hy z) ((hrel x).mono fun _ h => h.1) ((hrel z).mono fun _ h => h.1)
      (by filter_upwards [hinv x, hinv z] with i hx hz; exact ⟨hx.1.le, hz.1.le⟩)
    exact Topology.tendsto_inverse_pair_distance_of_uniform_distance_error
      (fun p q => (riemannianEDistOf gQ p q).toReal)
      (fun i p q => (riemannianEDistOf (target i) p q).toReal) (fun i => f i) K herror
      (fun i => F i (w x i)) (fun i => F i (w z i))
      (fun i => (f i).symm (F i (w x i))) (fun i => (f i).symm (F i (w z i)))
      ((hinv x).mono fun _ h => ⟨h.2.2.2.1, h.2.2.2.2⟩)
      ((hinv z).mono fun _ h => ⟨h.2.2.2.1, h.2.2.2.2⟩) hsourceDist
  · intro x hxbase
    let o : ℝ × UniformSpace.Completion angles.quotient :=
      (1, (angles.classOf ray : UniformSpace.Completion angles.quotient))
    have hbaseRel : ∀ᶠ i in atTop, (o, ray.point (d i)) ∈ C.relation a b i := by
      filter_upwards [C.annuli a b ha (ha1.trans h1b)] with i hi
      exact hi.2.2.2.2.2.2 ha1 h1b
    have hsourceDist := C.tendsto_source_distance_of_marked_representatives ha (ha1.trans h1b)
      hR hA.le hAR hd hQ hscale target F (fun i => 1 / ((i : ℝ) + 2)) heps
      (Eventually.of_forall fun _ => by positivity) hcompare (y x) (fun _ => o)
      (w x) (fun i => ray.point (d i)) (hy x) tendsto_const_nhds
      ((hrel x).mono fun _ h => h.1) hbaseRel
      (by
        filter_upwards [hinv x] with i hi
        refine ⟨hi.1.le, ?_⟩
        simpa only [metricDistance, riemannianEDistOf_self, ENNReal.toReal_zero] using hA.le)
    have hzero : Metric.coneDistance (x : ℝ × UniformSpace.Completion angles.quotient) o = 0 := by
      rw [hxbase]
      change Metric.coneDistance (1, _) (1, _) = 0
      norm_num [Metric.coneDistance, min_eq_right Real.pi_pos.le]
    rw [hzero, mul_zero] at hsourceDist
    exact Topology.tendsto_inverse_pair_distance_of_uniform_distance_error
      (fun p q => (riemannianEDistOf gQ p q).toReal)
      (fun i p q => (riemannianEDistOf (target i) p q).toReal) (fun i => f i) K herror
      (fun i => F i (w x i)) (fun i => F i (ray.point (d i)))
      (fun i => (f i).symm (F i (w x i))) (fun _ => q)
      ((hinv x).mono fun _ h => ⟨h.2.2.2.1, h.2.2.2.2⟩)
      (Eventually.of_forall fun i => ⟨hqK, hbase i⟩) hsourceDist

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
