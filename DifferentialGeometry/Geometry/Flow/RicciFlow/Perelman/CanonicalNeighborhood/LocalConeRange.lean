import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AnnularRepresentatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalMarkedInverse
import DifferentialGeometry.Topology.Compactness.MapLimits
import DifferentialGeometry.Geometry.Metric.Distance.ClosedBall
import DifferentialGeometry.Topology.Compactness.ExtremumNeighborhood

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
  [∀ i, IsManifold I3 ∞ (M i)]
  {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
  {ray : EndRay H.endpoint} {d : ℕ → ℝ}

attribute [local instance] EndAngles.metric

theorem tendsto_source_distance_zero_of_rescaled_distance_zero
    (H : FiniteHorn g) (ray : EndRay H.endpoint) {R : ℝ} (hR : 0 < R)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (target : ∀ i, SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 W (M i) ∞)
    (hcompare : ∀ᶠ i in atTop,
      let scaled := scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
      let ball := riemannianClosedBallOf scaled (ray.point (d i)) R
      ball ⊆ (F i).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled) (fun _ => target i) (F i)
        ball {0} 0 (1 / ((i : ℝ) + 2))))
    {l : Filter ℕ} (hl : l ≤ atTop) (w v : ℕ → W)
    (hpoints : ∀ᶠ i in l,
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) (w i) ≤ R / 16 ∧
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) (v i) ≤ R / 16)
    (hzero : Tendsto (fun i => metricDistance
      (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g) (w i) (v i)) l (𝓝 0)) :
    Tendsto (fun i => metricDistance (target i) (F i (w i)) (F i (v i))) l (𝓝 0) := by
  let scaled := fun i => scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
  have hfinite (i : ℕ) (x y : W) : riemannianEDistOf (scaled i) x y ≠ ⊤ := by
    dsimp only [scaled]
    rw [edistOf_scale, H.edist_eq_ofReal_dist]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (show Tendsto (fun i => 2 * metricDistance (scaled i) (w i) (v i)) l (𝓝 0) by
      simpa only [mul_zero] using tendsto_const_nhds.mul hzero)
  filter_upwards [hl hcompare, hpoints] with i hc hp
  obtain ⟨cmp⟩ := hc.2
  have hupper : ∀ z ∈ riemannianClosedBallOf (scaled i) (ray.point (d i)) R,
      ∀ v : TangentSpace I3 z, (target i).inner (F i z)
        (mfderiv I3 I3 (F i) z v) (mfderiv I3 I3 (F i) z v) ≤
        (2 : ℝ) ^ 2 * (scaled i).inner z v v := by
    intro z hz v
    have hu := (cmp.equivalence 0 (by simp) z hz v).2
    rw [cmp.pullback_eq 0 z hz (fun _ => v)] at hu
    have heps : 1 / ((i : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hv := inner_self_nonneg (scaled i) z v
    change (target i).inner (F i z) (mfderiv I3 I3 (F i) z v) (mfderiv I3 I3 (F i) z v) ≤
      (1 + 1 / ((i : ℝ) + 2)) * (scaled i).inner z v v at hu
    nlinarith
  have hmem (z : W) (hz : metricDistance (scaled i) (ray.point (d i)) z ≤ R / 16) :
      z ∈ riemannianClosedBallOf (scaled i) (ray.point (d i)) (R / 16) := by
    apply (ENNReal.toReal_le_toReal (hfinite i _ _) ENNReal.ofReal_ne_top).mp
    simpa only [metricDistance, ENNReal.toReal_ofReal (by positivity : 0 ≤ R / 16)] using hz
  have hu := crossModel_edist_le_of_metric_upper (scaled i) (target i) (F i)
    (ray.point (d i)) (L := 2) (by norm_num) (by positivity : 0 ≤ R / 16)
    (by linarith : 3 * (R / 16) < R) hc.1 hupper (hmem _ hp.1) (hmem _ hp.2)
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite i (w i) (v i))) hu
  simpa only [metricDistance, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using hr

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
  [∀ i, IsManifold I3 ∞ (M i)]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q]
  [IsManifold I3 ∞ Q] [T2Space Q]
  {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
  {ray : EndRay H.endpoint} {d : ℕ → ℝ}

attribute [local instance] EndAngles.metric

theorem AnnularConvergence.exists_capture_radius_subset_range
    [CompactSpace (UniformSpace.Completion angles.quotient)]
    (C : AnnularConvergence H angles ray d) {a b lambda R : ℝ}
    (ha : 0 < a) (hlambda : 0 < lambda) (ha1 : a < 1) (h1b : 1 < b) (hR : 0 < R)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    (target : ∀ i, SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 W (M i) ∞)
    (hcompare : ∀ᶠ i in atTop,
      let scaled := scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
      let ball := riemannianClosedBallOf scaled (ray.point (d i)) R
      ball ⊆ (F i).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled) (fun _ => target i) (F i)
        ball {0} 0 (1 / ((i : ℝ) + 2))))
    (gQ : SmoothRiemannianMetric I3 Q) (V : TopologicalSpace.Opens Q) (q : Q) (rK : ℝ)
    (f : ∀ i, PartialDiffeomorph I3 I3 Q (M i) ∞)
    (herror : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ i in atTop,
      ∀ p ∈ riemannianClosedBallOf gQ q rK, ∀ z ∈ riemannianClosedBallOf gQ q rK,
        |(riemannianEDistOf (target i) (f i p) (f i z)).toReal -
          (riemannianEDistOf gQ p z).toReal| < epsilon)
    (D : Set (ℝ × UniformSpace.Completion angles.quotient)) (hD : IsOpen D)
    (hoD : (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) ∈ D)
    (Psi : D → V) (u : ℕ → D → V)
    (hcluster : MapClusterPt Psi atTop u)
    (huK : ∀ i (x : D), (u i x : Q) ∈ riemannianClosedBallOf gQ q rK)
    (y : D → ℕ → ℝ × UniformSpace.Completion angles.quotient) (w : D → ℕ → W)
    (hy : ∀ x : D, Tendsto (y x) atTop (𝓝 (x : ℝ × UniformSpace.Completion angles.quotient)))
    (hw : ∀ x : D, ∀ᶠ i in atTop,
      (y x i, w x i) ∈ C.relation a b i ∧
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) (w x i) ≤ R / 16 ∧ f i (u i x) = F i (w x i)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ R / 16 ∧
      ∀ (p : V), (p : Q) ∈ riemannianClosedBallOf gQ q rK → ∀ v : ℕ → W,
        (∀ᶠ i in atTop,
          metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
            (ray.point (d i)) (v i) ≤ delta ∧ F i (v i) = f i p) →
        p ∈ range Psi := by
  classical
  let B := Icc a b × UniformSpace.Completion angles.quotient
  let P : B → ℝ × UniformSpace.Completion angles.quotient := fun z => (z.1.1, z.2)
  let o : ℝ × UniformSpace.Completion angles.quotient :=
    (1, (angles.classOf ray : UniformSpace.Completion angles.quotient))
  let oB : B :=
    (⟨1, ha1.le, h1b.le⟩, (angles.classOf ray : UniformSpace.Completion angles.quotient))
  have hP : Continuous P := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  let rho : B → ℝ := fun z => lambda * Metric.coneDistance o (P z)
  have hrho : Continuous rho := continuous_const.mul
    (Metric.continuous_coneDistance.comp (continuous_const.prodMk hP))
  obtain ⟨eta, heta, hetaD⟩ := hrho.exists_pos_sublevel_subset_of_unique_zero
    (fun _ => mul_nonneg hlambda.le (Real.sqrt_nonneg _)) (o := oB) (by
      intro z hz
      have heq := (Metric.coneDistance_eq_zero_iff zero_lt_one (ha.trans_le z.1.2.1)).mp
        ((mul_eq_zero.mp hz).resolve_left hlambda.ne')
      exact Prod.ext (Subtype.ext (congrArg Prod.fst heq).symm) (congrArg Prod.snd heq).symm)
    ((hD.preimage hP).mem_nhds hoD)
  let delta := min (eta / 2) (min (R / 32)
    (min (lambda / 4 * (1 - a)) (lambda / 4 * (b - 1))))
  have hdelta : 0 < delta := lt_min (by positivity)
    (lt_min (by positivity) (lt_min (mul_pos (by positivity) (by linarith))
      (mul_pos (by positivity) (by linarith))))
  have hdeta : delta < eta := (min_le_left _ _).trans_lt (by linarith)
  have hdR : delta ≤ R / 16 :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans (by linarith)
  have hda : delta < lambda / 2 * (1 - a) :=
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (by nlinarith)
  have hdb : delta < lambda / 2 * (b - 1) :=
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by nlinarith)
  refine ⟨delta, hdelta, hdR, ?_⟩
  intro p hpK v hv
  have hmem : ∀ᶠ i in atTop, ∀ _p : Unit,
      dist (v i : UniformSpace.Completion W) H.endpoint / d i ∈ Icc a b := by
    filter_upwards [eventually_radial_mem_of_rescaled_distance_le H ray ha1 h1b hlambda hda hdb
      hd hQ hscale, hv] with i hi hvi
    exact fun _ => ⟨(hi (v i) hvi.1).1.le, (hi (v i) hvi.1).2.le⟩
  obtain ⟨s, z, hsz⟩ := C.exists_annular_selection ha (ha1.trans h1b) (fun i (_ : Unit) => v i) hmem
  let c : ℕ → ℝ × UniformSpace.Completion angles.quotient := fun i => P (s i ())
  let zc : ℕ → W := fun i => z i ()
  have hrel : ∀ᶠ i in atTop, (c i, zc i) ∈ C.relation a b i :=
    hsz.mono fun _ hi => (hi ()).1
  have hnear : Tendsto (fun i => dist (v i) (zc i) / d i) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i => div_nonneg dist_nonneg (hd i).1.le)
      (hsz.mono fun _ hi => (hi ()).2.le) (C.error_zero a b ha (ha1.trans h1b))
  let Kc : Set (ℝ × UniformSpace.Completion angles.quotient) := Icc a b ×ˢ univ
  have hKc : IsCompact Kc := isCompact_Icc.prod isCompact_univ
  refine hcluster.mem_range_of_compact hKc c
    (Eventually.of_forall fun i => ⟨(s i ()).1.2, mem_univ _⟩) ?_ p ?_
  · intro x hxK hxcluster
    let l : Filter ℕ := atTop ⊓ comap c (𝓝 x)
    have hl : l ≤ atTop := inf_le_left
    have hlne : l.NeBot := neBot_inf_comap_iff_map.mpr (by
      simpa only [inf_comm] using hxcluster.clusterPt.neBot)
    let : l.NeBot := hlne
    have hcx : Tendsto c l (𝓝 x) := tendsto_iff_comap.mpr inf_le_right
    have hbound := C.rescaled_cone_distance_le_of_captured_limit ha ha1 h1b hd hQ hscale hl
      c zc v hcx (hl hrel) (hnear.mono_left hl) (hl (hv.mono fun _ hi => hi.1))
    exact hetaD (⟨x.1, hxK.1⟩, x.2) (hbound.trans_lt hdeta)
  · intro l hl hlne x hx hcx
    let : l.NeBot := hlne
    let xD : D := ⟨x, hx⟩
    have hxpos : 0 < x.1 := by
      have hxK : x ∈ Kc := hKc.isClosed.mem_of_tendsto hcx
        (hl (Eventually.of_forall fun i => ⟨(s i ()).1.2, mem_univ _⟩))
      exact ha.trans_le hxK.1.1
    have hzero := C.tendsto_rescaled_distance_of_approximated_representatives ha (ha1.trans h1b)
      hd hQ hscale hl (y xD) c (w xD) zc v ((hy xD).mono_left hl) hcx
      (hl ((hw xD).mono fun _ hi => hi.1)) (hl hrel) (hnear.mono_left hl)
    rw [(Metric.coneDistance_eq_zero_iff hxpos hxpos).mpr rfl, mul_zero] at hzero
    have hsource := tendsto_source_distance_zero_of_rescaled_distance_zero H ray hR hQ target F
      hcompare hl (w xD) v (by
        filter_upwards [hl (hw xD), hl hv] with i hi hvi
        exact ⟨hi.2.1, hvi.1.trans hdR⟩) hzero
    have hlimit := Topology.tendsto_inverse_pair_distance_of_uniform_distance_error
      (fun p z : Q => (riemannianEDistOf gQ p z).toReal)
      (fun i p z => (riemannianEDistOf (target i) p z).toReal)
      (fun i => f i) (riemannianClosedBallOf gQ q rK)
      (fun epsilon hepsilon => hl (herror epsilon hepsilon))
      (fun i => F i (w xD i)) (fun i => F i (v i))
      (fun i => (u i xD : Q)) (fun _ => (p : Q))
      (hl ((hw xD).mono fun i hi => ⟨huK i xD, hi.2.2⟩))
      (hl (hv.mono fun _ hi => ⟨hpK, hi.2.symm⟩)) hsource
    obtain ⟨m, hm, hmdist⟩ := Geometry.Riemannian.exists_metricSpace_closedBall gQ q (r := rK)
    let : MetricSpace (riemannianClosedBallOf gQ q rK) := m.replaceTopology hm.symm
    let uk : ℕ → riemannianClosedBallOf gQ q rK := fun i => ⟨u i xD, huK i xD⟩
    let pk : riemannianClosedBallOf gQ q rK := ⟨p, hpK⟩
    have huk : Tendsto uk l (𝓝 pk) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact hlimit.congr' (Eventually.of_forall fun i => (hmdist (uk i) pk).symm)
    have hQlim := continuous_subtype_val.continuousAt.tendsto.comp huk
    exact tendsto_subtype_rng.mpr hQlim

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
