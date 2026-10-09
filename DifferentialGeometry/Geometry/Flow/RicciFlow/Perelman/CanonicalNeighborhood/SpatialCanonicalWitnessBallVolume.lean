import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialRoundComponentBallVolume
import DifferentialGeometry.Geometry.Neck.BallVolume
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

open _root_.Manifold Bundle in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_riemannianEDistOf_eq_of_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {x w : M} {a b : ℝ} (ha : 0 ≤ a)
    (haw : ENNReal.ofReal a ≤ riemannianEDistOf g x w)
    (hwb : riemannianEDistOf g x w < ENNReal.ofReal b) :
    ∃ y, riemannianEDistOf g x y = ENNReal.ofReal a ∧
      riemannianEDistOf g y w < ENNReal.ofReal (b - a) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  change riemannianEDist I x w < ENNReal.ofReal b at hwb
  change ENNReal.ofReal a ≤ riemannianEDist I x w at haw
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hwb
  have hcont : ContinuousOn (fun t => riemannianEDist I x (γ t)) (Icc 0 1) :=
    (Geometry.Riemannian.continuous_riemannianEDist g x).comp_continuousOn hγ.continuousOn
  have hmem : ENNReal.ofReal a ∈ Icc (riemannianEDist I x (γ 0))
      (riemannianEDist I x (γ 1)) := by
    rw [h0, h1, riemannianEDist_self]
    exact ⟨bot_le, haw⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hcont hmem
  refine ⟨γ t, hft, ?_⟩
  have hfirst : riemannianEDist I x (γ t) ≤ pathELength I γ 0 t :=
    riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2)) h0 rfl ht.1
  have hsecond : riemannianEDist I (γ t) w ≤ pathELength I γ t 1 :=
    riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc ht.1 le_rfl)) rfl h1 ht.2
  have hadd := pathELength_add (I := I) (γ := γ) ht.1 ht.2
  have hsum : ENNReal.ofReal a + riemannianEDist I (γ t) w < ENNReal.ofReal b := by
    rw [← hft]
    calc riemannianEDist I x (γ t) + riemannianEDist I (γ t) w
        ≤ pathELength I γ 0 t + pathELength I γ t 1 := add_le_add hfirst hsecond
      _ = pathELength I γ 0 1 := hadd
      _ < ENNReal.ofReal b := hlen
  change riemannianEDist I (γ t) w < ENNReal.ofReal (b - a)
  rw [ENNReal.ofReal_sub b ha]
  exact lt_tsub_iff_left.mpr hsum

private theorem ball_subset_image_closedBall_of_spatialNeck {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {v : M} (nk : SpatialNeck g eps v)
    (z : Cylinder) {R : ℝ} (hR : 0 < R) (hz : |z.2| + R < eps⁻¹) :
    riemannianBallOf (scaleMetric (metricScalarAt g v) nk.Q_pos g) (nk.map z)
        (R * Real.sqrt (1 - eps)) ⊆
      nk.map '' riemannianClosedBallOf (nk.cylinder.metric 0) z R := by
  have hminus : 0 < 1 - eps := by linarith [nk.eps_small]
  have hsqrt : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr hminus
  have hball : riemannianClosedBallOf (nk.cylinder.metric 0) z R ⊆
      univ ×ˢ Icc (z.2 - R) (z.2 + R) := nk.cylinder.closedBall_subset_slab z hR.le
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (z.2 - R) (z.2 + R) ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro y hy
    exact ⟨hy.1, by
      constructor <;> linarith [hy.2.1, hy.2.2, neg_abs_le z.2, le_abs_self z.2]⟩
  have hcapture := ball_subset_image_of_metric_lower_crossModel (nk.cylinder.metric 0)
    (scaleMetric (metricScalarAt g v) nk.Q_pos g) nk.map z
    (L := (Real.sqrt (1 - eps))⁻¹) hR (inv_pos.mpr hsqrt)
    (nk.cylinder.isCompact_closedBall z hR.le)
    (hball.trans (hslab.trans nk.domain)) (by
      intro y hy w
      have he := (nk.comparison.equivalence 0 (by norm_num) y (hslab (hball hy)) w).1
      rw [nk.comparison.pullback_eq 0 y (hslab (hball hy)) (fun _ => w)] at he
      have hh := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hminus.le)
      rw [← mul_assoc, inv_mul_cancel₀ hminus.ne', one_mul] at hh
      simpa only [inv_pow, Real.sq_sqrt hminus.le] using hh)
  rwa [div_inv_eq_mul] at hcapture

private theorem ball_volume_of_positive {P : OrientedThreeStage.{u}} {g : P.Metric}
    {x : P.Carrier} {eps C1 C2 : ℝ} (W : SpatialCanonicalWitness g eps C1 C2 x)
    (whole : W.domain.carrier = connectedComponent x)
    (sec : SecLower g (C2⁻¹ * metricScalarAt g x) W.domain.carrier)
    (hvolU : ENNReal.ofReal (C2⁻¹ / (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
      riemannianVolumeMeasure I3 P.Carrier g W.domain.carrier)
    {r : ℝ} (hr : 0 < r) (hcurv : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) :
    ENNReal.ofReal (1 / (27 * max C1 1 ^ 3 * max C2 1) * r ^ 3) ≤
      riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r) := by
  set A := max C1 1 with hAdef
  set B := max C2 1 with hBdef
  have hA : 1 ≤ A := le_max_right _ _
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hB : C2 ≤ B := le_max_left _ _
  set Q := metricScalarAt g x with hQdef
  have hQ : 0 < Q := W.Q_pos
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsQsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  set L := 3 * A / Real.sqrt Q with hLdef
  have hrL : r ≤ L := by
    have h3 := sqrt_scalarAt_mul_le_three_of_rm_le g x hcurv
    rw [hLdef, le_div_iff₀ hsQ]
    nlinarith
  have hball : riemannianBallOf g x L ⊆ W.domain.carrier := by
    rw [whole]
    exact DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen
      (I := I3) g x L
  have hdomain : W.domain.carrier ⊆ riemannianBallOf g x L := by
    refine W.inside_ball.trans (riemannianBallOf_mono g x ?_)
    have hrad : W.radius ≤ A / Real.sqrt Q :=
      W.radius_upper.trans (div_le_div_of_nonneg_right (le_max_left _ _) hsQ.le)
    have hApos : 0 ≤ A / Real.sqrt Q := by positivity
    rw [hLdef, mul_div_assoc]
    linarith
  have hRic : ∀ y ∈ riemannianBallOf g x L, ∀ v : TangentSpace I3 y,
      0 ≤ ricciTensor (I := I3) g y v v := by
    intro y hy v
    have hs : Geometry.Riemannian.SectionalBoundedBelowAt (I := I3) g y (C2⁻¹ * Q) :=
      fun a b => sec y (hball hy) a b
    have hlow := Geometry.Riemannian.ricci_lower_of_sectionalBoundedBelowAt g y hs v
    have hinner : 0 ≤ g.inner y v v := by
      rcases eq_or_ne v 0 with hv | hv
      · subst v
        simp
      · exact (g.pos y v hv).le
    have hK : 0 ≤ C2⁻¹ * Q := by
      have : 0 ≤ C2⁻¹ := inv_nonneg.mpr (zero_le_one.trans hC2)
      positivity
    exact le_trans (by positivity) hlow
  have hmain :=
    Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_ratio_ge_of_ricci_nonneg g
      (RiemannianMetricComplete.of_compact g) x hr hrL hRic
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hmain
  have hinv : B⁻¹ ≤ C2⁻¹ := inv_anti₀ (zero_lt_one.trans_le hC2) hB
  have hQs : 0 < Q * Real.sqrt Q := mul_pos hQ hsQ
  have hU : ENNReal.ofReal (B⁻¹ / (Q * Real.sqrt Q)) ≤
      riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x L) :=
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hinv hQs.le)).trans
      (hvolU.trans (measure_mono hdomain))
  have hcoef : 1 / (27 * A ^ 3 * B) * r ^ 3 = (r / L) ^ 3 * (B⁻¹ / (Q * Real.sqrt Q)) := by
    rw [hLdef]
    have hQ3 : Q * Real.sqrt Q = Real.sqrt Q ^ 3 := by rw [pow_succ, hsQsq]
    rw [hQ3]
    field_simp
    ring
  rw [hcoef, ENNReal.ofReal_mul (by positivity)]
  exact (mul_le_mul' le_rfl hU).trans hmain

private theorem ricci_lower_on_domain {P : OrientedThreeStage.{u}} {g : P.Metric}
    {x : P.Carrier} {eps C1 C2 : ℝ} (W : SpatialCanonicalWitness g eps C1 C2 x) {B : ℝ}
    (hB : C2 ≤ B) (hBpos : 0 < B) :
    ∀ y ∈ W.domain.carrier, ∀ v : TangentSpace I3 y,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) *
          (3 * Real.sqrt (B * metricScalarAt g x)) ^ 2) * g.inner y v v ≤
        ricciTensor (I := I3) g y v v := by
  intro y hy v
  have hQ : 0 < metricScalarAt g x := W.Q_pos
  have hrm : Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ B * metricScalarAt g x :=
    (W.rm_bound y hy).trans (mul_le_mul_of_nonneg_right hB hQ.le)
  have hlow := Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm (I := I3) g hrm v
  have hinner : 0 ≤ g.inner y v v := by
    rcases eq_or_ne v 0 with hv | hv
    · subst v
      simp
    · exact (g.pos y v hv).le
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hlow ⊢
  have hq2 : (3 * Real.sqrt (B * metricScalarAt g x)) ^ 2 = 9 * (B * metricScalarAt g x) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hBpos.le hQ.le)]
    norm_num
  have hcoef : -(((3 - 1 : ℕ) : ℝ) * (3 * Real.sqrt (B * metricScalarAt g x)) ^ 2) ≤
      -(((3 : ℕ) : ℝ) ^ 2 * (B * metricScalarAt g x)) := by
    rw [hq2]
    have hBQ : 0 ≤ B * metricScalarAt g x := mul_nonneg hBpos.le hQ.le
    norm_num
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef hinner).trans hlow

private theorem exists_tube_distance {P : OrientedThreeStage.{u}} {g : P.Metric}
    {x : P.Carrier} {eps C1 C2 : ℝ} (W : SpatialCanonicalWitness g eps C1 C2 x)
    (cap : SpatialLocalCap g eps x W.domain.carrier)
    (deep : ∀ y ∈ cap.tube, 10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y)
    {v : P.Carrier} (hvT : v ∈ cap.tube) :
    ∃ D : ℝ, 10000 / Real.sqrt (metricScalarAt g x) ≤ D ∧ D ≤ 2 * W.radius ∧
      riemannianBallOf g x D ⊆ W.domain.carrier ∧
      (∀ y ∈ cap.tube, ENNReal.ofReal D ≤ riemannianEDistOf g x y) ∧
      ∀ δ : ℝ, 0 < δ → ∃ w ∈ cap.tube, riemannianEDistOf g x w < ENNReal.ofReal (D + δ) := by
  have hsQ : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr W.Q_pos
  have htubeU : cap.tube ⊆ W.domain.carrier := by
    intro y hy
    have hy' : y ∈ cap.core.carrier ∪ cap.tube := Or.inr hy
    rwa [← cap.union_eq] at hy'
  have hfrontier : frontier W.domain.carrier ⊆ cap.tube := by
    intro y hy
    have hout := cap.outer_boundary
    have htube := cap.tube_eq
    rw [← hout] at hy
    rw [← htube]
    have h1 : ({1} : Set ℝ) ⊆ Icc 0 1 := by
      intro t ht
      rw [mem_singleton_iff.mp ht]
      exact ⟨zero_le_one, le_rfl⟩
    exact image_mono (Set.prod_mono subset_rfl h1) hy
  obtain ⟨De, hDedef⟩ : ∃ De : ℝ≥0∞, De = ⨅ y ∈ cap.tube, riemannianEDistOf g x y :=
    ⟨_, rfl⟩
  have hDle : ∀ y ∈ cap.tube, De ≤ riemannianEDistOf g x y := fun y hy => by
    rw [hDedef]
    exact iInf₂_le y hy
  have hDlow : ENNReal.ofReal (10000 / Real.sqrt (metricScalarAt g x)) ≤ De := by
    rw [hDedef]
    exact le_iInf₂ fun y hy =>
      (ENNReal.ofReal_le_ofReal (deep y hy)).trans ENNReal.ofReal_toReal_le
  have hxv : riemannianEDistOf g x v < ENNReal.ofReal (2 * W.radius) :=
    W.inside_ball (htubeU hvT)
  have hDfin : De ≠ ⊤ := ((hDle v hvT).trans_lt (hxv.trans ENNReal.ofReal_lt_top)).ne
  have hrad : 0 ≤ W.radius :=
    (inv_nonneg.mpr (Real.sqrt_nonneg _)).trans W.radius_lower
  refine ⟨De.toReal, (ENNReal.ofReal_le_iff_le_toReal hDfin).mp hDlow,
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg zero_le_two hrad) ((hDle v hvT).trans hxv.le),
    ?_, fun y hy => (ENNReal.ofReal_toReal hDfin).symm ▸ hDle y hy, ?_⟩
  · have hDpos : 0 < De.toReal := lt_of_lt_of_le (div_pos (by norm_num) hsQ)
      ((ENNReal.ofReal_le_iff_le_toReal hDfin).mp hDlow)
    have hDeq : ENNReal.ofReal De.toReal = De := ENNReal.ofReal_toReal hDfin
    have hconn := (DifferentialGeometry.isPathConnected_riemannianBallOf g x hDpos).isConnected
      |>.isPreconnected
    have hxB : x ∈ riemannianBallOf g x De.toReal := by
      change riemannianEDistOf g x x < _
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hDpos
    have hsplit : riemannianBallOf g x De.toReal ⊆
        interior W.domain.carrier ∪ (closure W.domain.carrier)ᶜ := by
      intro y hy
      by_cases hc : y ∈ closure W.domain.carrier
      · left
        by_contra hi
        have h1 := hDle y (hfrontier ⟨hc, hi⟩)
        have h2 : riemannianEDistOf g x y < ENNReal.ofReal De.toReal := hy
        rw [hDeq] at h2
        exact absurd (h1.trans_lt h2) (lt_irrefl _)
      · right
        exact hc
    have hsub := hconn.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset_closure) hsplit
      ⟨x, hxB, W.center_inside⟩
    exact hsub.trans interior_subset
  · intro δ hδ
    have hlt : De < ENNReal.ofReal (De.toReal + δ) := by
      rw [← ENNReal.ofReal_toReal hDfin]
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    have hlt' : (⨅ y ∈ cap.tube, riemannianEDistOf g x y) <
        ENNReal.ofReal (De.toReal + δ) := by
      rw [← hDedef]
      exact hlt
    obtain ⟨w, hw⟩ := iInf_lt_iff.mp hlt'
    obtain ⟨hwT, hwlt⟩ := iInf_lt_iff.mp hw
    exact ⟨w, hwT, hwlt⟩

private theorem ball_volume_near_tube {P : OrientedThreeStage.{u}} {g : P.Metric}
    {x : P.Carrier} {eps : ℝ} {U : Set P.Carrier} (cap : SpatialLocalCap g eps x U)
    {v : P.Carrier} (nk : SpatialNeck g eps v) (hmap : ∀ z, cap.tubeMap z = nk.map z)
    {ν : ℝ}
    (hvol : ∀ (z : Cylinder) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → |z.2| + ρ < eps⁻¹ →
      ENNReal.ofReal (ν * ρ ^ 3) ≤ riemannianVolumeMeasure I3 P.Carrier
        (scaleMetric (metricScalarAt g v) nk.Q_pos g)
        (riemannianBallOf (scaleMetric (metricScalarAt g v) nk.Q_pos g) (nk.map z) ρ))
    {w w' : P.Carrier} (hwT : w ∈ cap.tube) {s : ℝ} (hs : 0 < s)
    (hsle : s ≤ 1 / (4 * Real.sqrt (metricScalarAt g v)))
    (hww' : riemannianEDistOf g w w' < ENNReal.ofReal (1 / (2 * Real.sqrt (metricScalarAt g v)))) :
    ENNReal.ofReal (ν * s ^ 3) ≤
      riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g w' s) := by
  have hsQv : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr nk.Q_pos
  obtain ⟨z₀, hz₀, hz₀eq⟩ : ∃ z₀ ∈ (univ : Set (Sphere 2)) ×ˢ Icc (0 : ℝ) 1,
      cap.tubeMap z₀ = w := by
    rw [← cap.tube_eq] at hwT
    exact hwT
  have heps : eps < 1 / 11 := nk.eps_small
  have hepsinv : 11 < eps⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) nk.eps_pos]
    linarith
  have hz₀abs : |z₀.2| ≤ 1 := abs_le.mpr ⟨by linarith [hz₀.2.1], hz₀.2.2⟩
  have hcapture := ball_subset_image_closedBall_of_spatialNeck nk z₀ one_pos
    (by linarith : |z₀.2| + 1 < eps⁻¹)
  have hminus : 0 < 1 - eps := by linarith [nk.eps_pos]
  have hsqrt1 : 1 / 2 ≤ Real.sqrt (1 - eps) := by
    rw [Real.le_sqrt (by norm_num) hminus.le]
    linarith
  have hw'mem : w' ∈ riemannianBallOf (scaleMetric (metricScalarAt g v) nk.Q_pos g) (nk.map z₀)
      (1 * Real.sqrt (1 - eps)) := by
    have hscale := riemannianBallOf_scaleMetric (metricScalarAt g v) nk.Q_pos g (nk.map z₀)
      (Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g v))
    rw [mul_div_cancel₀ _ hsQv.ne'] at hscale
    rw [one_mul, hscale]
    change riemannianEDistOf g (nk.map z₀) w' < _
    rw [← hmap, hz₀eq]
    refine hww'.trans_le (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ (mul_pos two_pos hsQv) hsQv]
    nlinarith
  obtain ⟨z', hz'ball, hz'eq⟩ := hcapture hw'mem
  have hz'slab := nk.cylinder.closedBall_subset_slab z₀ zero_le_one hz'ball
  have hz'abs : |z'.2| ≤ 2 := abs_le.mpr ⟨by linarith [hz'slab.2.1, hz₀.2.1],
    by linarith [hz'slab.2.2, hz₀.2.2]⟩
  have hρ : 0 < Real.sqrt (metricScalarAt g v) * s := mul_pos hsQv hs
  have hρle : Real.sqrt (metricScalarAt g v) * s ≤ 1 / 4 := by
    calc Real.sqrt (metricScalarAt g v) * s ≤
          Real.sqrt (metricScalarAt g v) * (1 / (4 * Real.sqrt (metricScalarAt g v))) :=
          mul_le_mul_of_nonneg_left hsle hsQv.le
      _ = 1 / 4 := by field_simp
  have hvolw := hvol z' (Real.sqrt (metricScalarAt g v) * s) hρ (by linarith) (by linarith)
  rw [hz'eq, riemannianBallOf_scaleMetric, volume_scale_apply] at hvolw
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hvolw
  have hc0 : ENNReal.ofReal (Real.sqrt (metricScalarAt g v)) ^ 3 ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_pos.mpr hsQv).ne'
  have hct : ENNReal.ofReal (Real.sqrt (metricScalarAt g v)) ^ 3 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hc0 hct).mp
  calc ENNReal.ofReal (Real.sqrt (metricScalarAt g v)) ^ 3 * ENNReal.ofReal (ν * s ^ 3)
      = ENNReal.ofReal (ν * (Real.sqrt (metricScalarAt g v) * s) ^ 3) := by
        rw [← ENNReal.ofReal_pow hsQv.le, ← ENNReal.ofReal_mul (pow_nonneg hsQv.le 3)]
        congr 1
        ring
    _ ≤ _ := hvolw

private theorem cap_constant_le {A B σ Q D s r ν : ℝ} (hApos : 0 < A) (hBpos : 0 < B)
    (hQ : 0 < Q) (hν : 0 < ν) (hr : 0 < r) (hDpos : 0 < D) (hσ : 0 < σ)
    (hDQ : D * Real.sqrt Q ≤ 2 * A) (hsσ : σ / Real.sqrt Q ≤ s) :
    Real.exp (-(12 * A * Real.sqrt B)) * ν * σ ^ 3 / (64 * A ^ 3) * r ^ 3 ≤
      Real.exp (-(3 * Real.sqrt (B * Q) * ((3 - 1 : ℕ) : ℝ) * D)) * (r / (2 * D)) ^ 3 *
        (ν * s ^ 3) := by
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
  have hexp : Real.exp (-(12 * A * Real.sqrt B)) ≤
      Real.exp (-(3 * Real.sqrt (B * Q) * ((3 - 1 : ℕ) : ℝ) * D)) := by
    apply Real.exp_le_exp.mpr
    have h2 : ((3 - 1 : ℕ) : ℝ) = 2 := by norm_num
    have hqD : 3 * Real.sqrt (B * Q) * ((3 - 1 : ℕ) : ℝ) * D ≤ 12 * A * Real.sqrt B := by
      rw [h2, Real.sqrt_mul hBpos.le]
      calc 3 * (Real.sqrt B * Real.sqrt Q) * 2 * D = 6 * Real.sqrt B * (D * Real.sqrt Q) := by
            ring
        _ ≤ 6 * Real.sqrt B * (2 * A) :=
            mul_le_mul_of_nonneg_left hDQ (mul_nonneg (by norm_num) hsB.le)
        _ = 12 * A * Real.sqrt B := by ring
    linarith
  have hrat : r * Real.sqrt Q / (4 * A) ≤ r / (2 * D) := by
    rw [div_le_div_iff₀ (mul_pos four_pos hApos) (mul_pos two_pos hDpos)]
    calc r * Real.sqrt Q * (2 * D) = 2 * r * (D * Real.sqrt Q) := by ring
      _ ≤ 2 * r * (2 * A) := mul_le_mul_of_nonneg_left hDQ (mul_nonneg zero_le_two hr.le)
      _ = r * (4 * A) := by ring
  have hσQ : 0 ≤ σ / Real.sqrt Q := div_nonneg hσ.le hsQ.le
  have hrQ : 0 ≤ r * Real.sqrt Q / (4 * A) :=
    div_nonneg (mul_nonneg hr.le hsQ.le) (mul_nonneg (by norm_num) hApos.le)
  have hr2D : 0 ≤ r / (2 * D) := div_nonneg hr.le (mul_nonneg two_pos.le hDpos.le)
  calc Real.exp (-(12 * A * Real.sqrt B)) * ν * σ ^ 3 / (64 * A ^ 3) * r ^ 3
      = Real.exp (-(12 * A * Real.sqrt B)) * (r * Real.sqrt Q / (4 * A)) ^ 3 *
          (ν * (σ / Real.sqrt Q) ^ 3) := by
        field_simp
        ring
    _ ≤ _ := mul_le_mul (mul_le_mul hexp (pow_le_pow_left₀ hrQ hrat 3)
          (pow_nonneg hrQ 3) (Real.exp_pos _).le)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσQ hsσ 3) hν.le)
          (mul_nonneg hν.le (pow_nonneg hσQ 3))
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg hr2D 3))

private theorem ball_volume_of_cap {P : OrientedThreeStage.{u}} {g : P.Metric}
    {x : P.Carrier} {eps C1 C2 : ℝ} (W : SpatialCanonicalWitness g eps C1 C2 x)
    (cap : SpatialLocalCap g eps x W.domain.carrier)
    (deep : ∀ y ∈ cap.tube, 10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y)
    {v : P.Carrier} (nk : SpatialNeck g eps v) (hmap : ∀ z, cap.tubeMap z = nk.map z)
    {ν : ℝ} (hν : 0 < ν)
    (hvol : ∀ (z : Cylinder) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → |z.2| + ρ < eps⁻¹ →
      ENNReal.ofReal (ν * ρ ^ 3) ≤ riemannianVolumeMeasure I3 P.Carrier
        (scaleMetric (metricScalarAt g v) nk.Q_pos g)
        (riemannianBallOf (scaleMetric (metricScalarAt g v) nk.Q_pos g) (nk.map z) ρ))
    {r : ℝ} (hr : 0 < r) (hcurv : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) :
    ENNReal.ofReal (Real.exp (-(12 * max C1 1 * Real.sqrt (max C2 1))) * ν *
        min (1 / (4 * Real.sqrt (max C2 1))) 5000 ^ 3 / (64 * max C1 1 ^ 3) * r ^ 3) ≤
      riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r) := by
  have hApos : 0 < max C1 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hBpos : 0 < max C2 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB : C2 ≤ max C2 1 := le_max_left _ _
  have hσ : 0 < min (1 / (4 * Real.sqrt (max C2 1))) 5000 :=
    lt_min (div_pos one_pos (mul_pos four_pos (Real.sqrt_pos.mpr hBpos))) (by norm_num)
  have hQ : 0 < metricScalarAt g x := W.Q_pos
  have hsQ : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hQ
  have hvT : v ∈ cap.tube := by
    rw [← cap.tube_eq, ← nk.center_eq, ← hmap]
    exact mem_image_of_mem _ ⟨mem_univ _, le_rfl, zero_le_one⟩
  have hvU : v ∈ W.domain.carrier := by
    have hy' : v ∈ cap.core.carrier ∪ cap.tube := Or.inr hvT
    rwa [← cap.union_eq] at hy'
  have hsQv : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr nk.Q_pos
  have hQvB : metricScalarAt g v ≤ max C2 1 * metricScalarAt g x :=
    (W.scalar_bounds v hvU).2.trans (mul_le_mul_of_nonneg_right hB hQ.le)
  obtain ⟨D, hDge, hDrad, hBx, hDtube, hnear⟩ := exists_tube_distance W cap deep hvT
  have hDpos : 0 < D := lt_of_lt_of_le (div_pos (by norm_num) hsQ) hDge
  have hDQ : D * Real.sqrt (metricScalarAt g x) ≤ 2 * max C1 1 := by
    have hrad : W.radius ≤ max C1 1 / Real.sqrt (metricScalarAt g x) :=
      W.radius_upper.trans (div_le_div_of_nonneg_right (le_max_left _ _) hsQ.le)
    have h2 : D ≤ 2 * max C1 1 / Real.sqrt (metricScalarAt g x) := by
      rw [mul_div_assoc]
      linarith
    rwa [← le_div_iff₀ hsQ]
  have h3 := sqrt_scalarAt_mul_le_three_of_rm_le g x hcurv
  have hrD : r ≤ D := by
    refine le_trans ?_ hDge
    rw [le_div_iff₀ hsQ]
    nlinarith
  set δ := 1 / (4 * Real.sqrt (metricScalarAt g v)) with hδdef
  have hδ : 0 < δ := div_pos one_pos (mul_pos four_pos hsQv)
  obtain ⟨w, hwT, hwlt⟩ := hnear δ hδ
  set s := min δ (D / 2) with hsdef
  have hs : 0 < s := lt_min hδ (half_pos hDpos)
  have hsD : s ≤ D / 2 := min_le_right _ _
  have hsle : s ≤ δ := min_le_left _ _
  have hDw : ENNReal.ofReal D ≤ riemannianEDistOf g x w := hDtube w hwT
  obtain ⟨w', hxw', hw'w⟩ := exists_riemannianEDistOf_eq_of_lt g (x := x) (w := w)
    (a := D - s) (b := D + δ) (by linarith)
    ((ENNReal.ofReal_le_ofReal (by linarith)).trans hDw) hwlt
  have hsub : riemannianBallOf g w' s ⊆ riemannianBallOf g x D := by
    intro y hy
    change riemannianEDistOf g x y < ENNReal.ofReal D
    have hy' : riemannianEDistOf g w' y < ENNReal.ofReal s := hy
    calc riemannianEDistOf g x y ≤ riemannianEDistOf g x w' + riemannianEDistOf g w' y :=
          riemannianEDistOf_triangle g x w' y
      _ < ENNReal.ofReal (D - s) + ENNReal.ofReal s := by
          rw [hxw']
          exact ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hy'
      _ = ENNReal.ofReal D := by
          rw [← ENNReal.ofReal_add (by linarith) hs.le]
          congr 1
          ring
  have hww' : riemannianEDistOf g w w' <
      ENNReal.ofReal (1 / (2 * Real.sqrt (metricScalarAt g v))) := by
    rw [riemannianEDistOf_comm]
    refine hw'w.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have hsum : δ + δ = 1 / (2 * Real.sqrt (metricScalarAt g v)) := by
      rw [hδdef]
      field_simp
      ring
    linarith
  have hvolw := ball_volume_near_tube cap nk hmap hvol hwT hs hsle hww'
  have hRic : ∀ y ∈ riemannianBallOf g x D, ∀ v : TangentSpace I3 y,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) *
          (3 * Real.sqrt (max C2 1 * metricScalarAt g x)) ^ 2) * g.inner y v v ≤
        ricciTensor (I := I3) g y v v := fun y hy =>
    ricci_lower_on_domain W hB hBpos y (hBx hy)
  have hmain :=
    Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_ratio_ge_of_ricci_lower g
      (RiemannianMetricComplete.of_compact g) x (by positivity) hr hrD hRic
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hmain
  have hsσ : min (1 / (4 * Real.sqrt (max C2 1))) 5000 / Real.sqrt (metricScalarAt g x) ≤ s := by
    apply le_min
    · calc min (1 / (4 * Real.sqrt (max C2 1))) 5000 / Real.sqrt (metricScalarAt g x) ≤
            1 / (4 * Real.sqrt (max C2 1)) / Real.sqrt (metricScalarAt g x) :=
            div_le_div_of_nonneg_right (min_le_left _ _) hsQ.le
        _ = 1 / (4 * Real.sqrt (max C2 1 * metricScalarAt g x)) := by
            rw [Real.sqrt_mul hBpos.le]
            field_simp
        _ ≤ δ := by
            apply one_div_le_one_div_of_le (mul_pos four_pos hsQv)
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQvB) (by norm_num)
    · calc min (1 / (4 * Real.sqrt (max C2 1))) 5000 / Real.sqrt (metricScalarAt g x) ≤
            5000 / Real.sqrt (metricScalarAt g x) :=
            div_le_div_of_nonneg_right (min_le_right _ _) hsQ.le
        _ ≤ D / 2 := by
            have h2 : 10000 / Real.sqrt (metricScalarAt g x) =
                2 * (5000 / Real.sqrt (metricScalarAt g x)) := by ring
            linarith
  have hreal := cap_constant_le hApos hBpos hQ hν hr hDpos hσ hDQ hsσ
  have hc0 : 0 ≤ Real.exp (-(3 * Real.sqrt (max C2 1 * metricScalarAt g x) *
      ((3 - 1 : ℕ) : ℝ) * D)) * (r / (2 * D)) ^ 3 :=
    mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (div_nonneg hr.le (mul_nonneg two_pos.le hDpos.le)) 3)
  calc _ ≤ ENNReal.ofReal (Real.exp (-(3 * Real.sqrt (max C2 1 * metricScalarAt g x) *
          ((3 - 1 : ℕ) : ℝ) * D)) * (r / (2 * D)) ^ 3) * ENNReal.ofReal (ν * s ^ 3) := by
        rw [← ENNReal.ofReal_mul hc0]
        exact ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (Real.exp (-(3 * Real.sqrt (max C2 1 * metricScalarAt g x) *
          ((3 - 1 : ℕ) : ℝ) * D)) * (r / (2 * D)) ^ 3) *
          riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x D) :=
        mul_le_mul' le_rfl (hvolw.trans (measure_mono hsub))
    _ ≤ _ := hmain

theorem exists_ball_volume_of_spatialCanonicalWitness (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      W.alternative.requiresVolume → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x r) := by
  obtain ⟨κn, hκn, hneck⟩ := exists_pos_mul_cube_le_spatialNeck_ball_volume_of_curvature_bound.{u}
  obtain ⟨ν, hν, hvol⟩ := exists_pos_mul_cube_le_spatialNeck_normalized_ball_volume.{u}
  set κp := 1 / (27 * max C1 1 ^ 3 * max C2 1) with hκpdef
  set κc := Real.exp (-(12 * max C1 1 * Real.sqrt (max C2 1))) * ν *
    min (1 / (4 * Real.sqrt (max C2 1))) 5000 ^ 3 / (64 * max C1 1 ^ 3) with hκcdef
  have hA : 0 < max C1 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB : 0 < max C2 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hκp : 0 < κp := by positivity
  have hσ : 0 < min (1 / (4 * Real.sqrt (max C2 1))) 5000 := lt_min (by positivity) (by norm_num)
  have hκc : 0 < κc := by positivity
  refine ⟨min κn (min κp κc), lt_min hκn (lt_min hκp hκc), ?_⟩
  intro P g x W hchart hreq r hr hcurv
  have hmono : ∀ {a : ℝ}, min κn (min κp κc) ≤ a →
      ENNReal.ofReal (min κn (min κp κc) * r ^ 3) ≤ ENNReal.ofReal (a * r ^ 3) := fun h =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h (by positivity))
  cases hA' : W.alternative with
  | neck data =>
    exact (hmono (min_le_left _ _)).trans (hneck data.neck r hr hcurv)
  | cap cap deep =>
    obtain ⟨v, nk, hmap⟩ := hchart cap deep hA'
    exact (hmono ((min_le_right _ _).trans (min_le_right _ _))).trans
      (ball_volume_of_cap W cap deep nk hmap hν (fun z ρ h1 h2 h3 => hvol nk z ρ h1 h2 h3) hr
        hcurv)
  | positive whole data sec =>
    exact (hmono ((min_le_right _ _).trans (min_le_left _ _))).trans
      (ball_volume_of_positive W whole sec (W.volume (by rw [hA']; trivial)) hr hcurv)
  | round whole data =>
    rw [hA'] at hreq
    exact hreq.elim

theorem exists_ball_volume_of_spatialCanonicalWitness_of_simplyConnected (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      SimplyConnectedSpace (connectedComponent x) → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r) := by
  obtain ⟨κ₄, hκ₄, h₄⟩ := exists_ball_volume_of_spatialCanonicalWitness.{u} ε C1 C2
  obtain ⟨κr, hκr, hround⟩ := exists_ball_volume_of_spatialRoundComponent.{u} C1 C2
  refine ⟨min κ₄ κr, lt_min hκ₄ hκr, ?_⟩
  intro P g x W hchart hsc r hr hcurv
  cases hA' : W.alternative with
  | round whole data =>
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (by positivity))).trans (hround W whole data hsc r hr hcurv)
  | neck data =>
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (by positivity))).trans (h₄ W hchart (by rw [hA']; trivial) r hr hcurv)
  | cap cap deep =>
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (by positivity))).trans (h₄ W hchart (by rw [hA']; trivial) r hr hcurv)
  | positive whole data sec =>
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (by positivity))).trans (h₄ W hchart (by rw [hA']; trivial) r hr hcurv)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
