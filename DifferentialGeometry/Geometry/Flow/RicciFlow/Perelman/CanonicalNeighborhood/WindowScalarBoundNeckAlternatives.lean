import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitTransfer

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_scalar_bound_far_of_neck_alternatives :
    ∃ εfar : ℝ, 0 < εfar ∧ ∀ {P : PointedRiemannianManifold.{u, 0, 0} I3} [ConnectedSpace P.M]
      [NoncompactSpace P.M], RiemannianMetricComplete P.metric →
      (∀ x : P.M, metricAlgebraicCurvatureTensorAt P.metric x ∈
        algebraicCurvatureOperatorNonnegativeCone) →
      ∀ {κ K : ℝ}, 0 < κ → MetricNoncollapsed P κ (Ioc 0 1) →
      (∀ x : P.M, Tensor0SBundle.normSq0S P.metric x 4 (metricRm04At P.metric x) ≤ K) →
      ∀ {ε C q A : ℝ}, ε ≤ εfar → 0 ≤ A → ∀ p : P.M,
      ∃ Rf Cf : ℝ, ∀ g : SmoothRiemannianMetric I3 P.M, RiemannianMetricComplete g →
        (∀ x : P.M, metricAlgebraicCurvatureTensorAt g x ∈
          algebraicCurvatureOperatorNonnegativeCone) →
        (∀ x : P.M, q < metricScalarAt g x →
          Nonempty (SpatialNeck g ε x) ∨
          (∃ w : P.M, Nonempty (SpatialNeck g ε w) ∧
            metricScalarAt g x ≤ C * metricScalarAt g w ∧
            riemannianEDistOf g x w < ENNReal.ofReal 2) ∨
          CompactSpace P.M) →
        (∀ x y : P.M, metricDistance P.metric x y ≤ metricDistance g x y ∧
          metricDistance g x y ≤ metricDistance P.metric x y + A) →
        ∀ y : P.M, Rf < metricDistance P.metric p y → metricScalarAt g y ≤ Cf := by
  obtain ⟨eta0, heta0, hsep⟩ :=
    exists_far_spatialNeck_unbounded_separated_component_of_nonnegative.{u}
  refine ⟨eta0, heta0, ?_⟩
  intro P _ _ hcomplete0 hcone0 κ K hκ hnc hK ε C q A heps hA p
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hsecOf : ∀ g : SmoothRiemannianMetric I3 P.M, (∀ x : P.M,
      metricAlgebraicCurvatureTensorAt g x ∈ algebraicCurvatureOperatorNonnegativeCone) →
      DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g := fun g hc =>
    (DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff g).mpr fun x v w =>
      (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
        g x hdim).mp (hc x) v w
  let _ : EMetricSpace P.M := P.emetricSpace
  have hfinite (x y : P.M) : edist x y ≠ ⊤ := riemannianEDistOf_ne_top P.metric x y
  let _ : MetricSpace P.M := EMetricSpace.toMetricSpace hfinite
  have hdist (x y : P.M) : dist x y = metricDistance P.metric x y := rfl
  have hPc : MetricComplete P := hcomplete0.complete
  obtain ⟨r, hr, hball⟩ := exists_uniform_pathConnected_ball_complement_of_metricNoncollapsed
    hκ (le_max_right K 0) P hPc ‹_› hnc (fun x => (hK x).trans (le_max_left K 0))
  obtain ⟨D0, C0, hD0, hC0, hseparate⟩ :=
    hsep P.M P.metric hcomplete0 (hsecOf P.metric hcone0) p A hA
  obtain ⟨Cd, hCd, hdiam⟩ := exists_uniform_spatial_neck_core_diameter (M := P.M)
  set C2 := max C 1 with hC2def
  have hC2 : 1 ≤ C2 := le_max_right _ _
  refine ⟨max D0 r + 3, max q (C2 * max C0 ((Cd / r) ^ 2)) + 1, ?_⟩
  intro g hg hcone hW herror y hy
  by_contra hnot
  push Not at hnot
  set Ry := metricScalarAt g y with hRy
  have hqy : q < Ry := by linarith [le_max_left q (C2 * max C0 ((Cd / r) ^ 2))]
  have hC2y : C2 * max C0 ((Cd / r) ^ 2) < Ry := by
    linarith [le_max_right q (C2 * max C0 ((Cd / r) ^ 2))]
  have hRypos : 0 < Ry := by
    have : 0 ≤ C2 * max C0 ((Cd / r) ^ 2) :=
      mul_nonneg (by linarith) ((sq_nonneg _).trans (le_max_right _ _))
    linarith
  obtain ⟨v, nk, hRvlow, hyv⟩ : ∃ (v : P.M) (_ : SpatialNeck g ε v),
      Ry ≤ C2 * metricScalarAt g v ∧ metricDistance g y v < 2 := by
    rcases hW y hqy with ⟨⟨nk⟩⟩ | ⟨w, ⟨nk⟩, hyw, hdw⟩ | hcpt
    · refine ⟨y, nk, ?_, ?_⟩
      · nlinarith
      · change (riemannianEDistOf g y y).toReal < 2
        rw [riemannianEDistOf_self]
        norm_num
    · refine ⟨w, nk, ?_, ?_⟩
      · have hw0 := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative g w (hcone w)
        exact hyw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0)
      · exact ENNReal.toReal_lt_of_lt_ofReal hdw
    · exact (noncompact_univ P.M (isCompact_univ_iff.mpr hcpt)).elim
  set Rv := metricScalarAt g v with hRv
  have hRvbig : max C0 ((Cd / r) ^ 2) < Rv := by
    have hC2pos : 0 < C2 := by linarith
    by_contra hle
    push Not at hle
    nlinarith
  have hC0v : C0 < Rv := (le_max_left _ _).trans_lt hRvbig
  have hscalev : (Cd / r) ^ 2 < Rv := (le_max_right _ _).trans_lt hRvbig
  have hyv0 : dist y v < 2 := by
    rw [hdist]
    exact (herror y v).1.trans_lt hyv
  have hpv : max D0 r + 1 < metricDistance P.metric p v := by
    have htri := dist_triangle p v y
    rw [dist_comm v y] at htri
    rw [hdist, hdist] at htri
    linarith
  have hD0v : D0 < metricDistance P.metric p v := by
    linarith [le_max_left D0 r]
  have hrv : r < metricDistance P.metric p v := by
    linarith [le_max_right D0 r]
  have habs : ∀ x z : P.M, |metricDistance g x z - metricDistance P.metric x z| ≤ A := by
    intro x z
    rw [abs_of_nonneg (sub_nonneg.mpr (herror x z).1)]
    linarith [(herror x z).2]
  obtain ⟨z, hzfar, hzcomp⟩ := hseparate g hg (hsecOf g hcone) ε v nk heps habs hD0v hC0v
    (metricDistance P.metric p v + r)
  have hdiamr : Cd / Real.sqrt Rv < r := by
    have hq : 0 < Rv := by linarith [sq_nonneg (Cd / r)]
    have hdiv : 0 ≤ Cd / r := div_nonneg hCd.le hr.le
    have hlt : Cd / r < Real.sqrt Rv := by
      rw [show Cd / r = Real.sqrt ((Cd / r) ^ 2) from (Real.sqrt_sq hdiv).symm]
      exact Real.sqrt_lt_sqrt (by positivity) hscalev
    have hcross := (div_lt_iff₀ hr).mp hlt
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr hq)).mpr
    nlinarith
  let S := nk.map '' (univ ×ˢ ({0} : Set ℝ))
  have hcentral : S ⊆ riemannianBallOf P.metric v r := by
    intro w hw
    have hvcore : v ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) :=
      ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩
    have hwcore : w ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) := by
      obtain ⟨u, hu, rfl⟩ := hw
      exact ⟨u, ⟨hu.1, by rw [show u.2 = 0 from hu.2]; norm_num⟩, rfl⟩
    have hd := (herror v w).1.trans_lt ((hdiam g ε v nk v hvcore w hwcore).trans_lt hdiamr)
    change riemannianEDistOf P.metric v w < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top _ _ _)]
    exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr hd
  have hp : p ∈ (riemannianBallOf P.metric v r)ᶜ := by
    intro hmem
    have hsmall := ENNReal.toReal_lt_of_lt_ofReal hmem
    change metricDistance P.metric v p < r at hsmall
    rw [show metricDistance P.metric v p = metricDistance P.metric p v from
      by simp only [metricDistance, riemannianEDistOf_comm]] at hsmall
    linarith
  have hz : z ∈ (riemannianBallOf P.metric v r)ᶜ := by
    intro hmem
    have hsmall := ENNReal.toReal_lt_of_lt_ofReal hmem
    change metricDistance P.metric v z < r at hsmall
    have htri := dist_triangle p v z
    rw [hdist, hdist, hdist] at htri
    linarith
  have hcomponent : (riemannianBallOf P.metric v r)ᶜ ⊆ connectedComponentIn Sᶜ p :=
    (hball v).isConnected.isPreconnected.subset_connectedComponentIn hp
      (compl_subset_compl.mpr hcentral)
  exact hzcomp (hcomponent hz)


theorem exists_uniform_scalar_bound_on_openClosed_window_of_neck_alternatives :
    ∃ εfar : ℝ, 0 < εfar ∧ ∀ {P : PointedRiemannianManifold.{u, 0, 0} I3} [ConnectedSpace P.M]
      {Tstar : ℝ} (hT : 0 < Tstar) (G : ℝ → SmoothRiemannianMetric I3 P.M),
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.openClosed (-Tstar) 0 0 ⟨by linarith, le_rfl⟩)) →
      G 0 = P.metric →
      (∀ τ ∈ Ioc (-Tstar) 0, RiemannianMetricComplete (G τ)) →
      (∀ τ ∈ Ioc (-Tstar) 0, ∀ x : P.M,
        metricAlgebraicCurvatureTensorAt (G τ) x ∈ algebraicCurvatureOperatorNonnegativeCone) →
      (∃ κ : ℝ, 0 < κ ∧ MetricNoncollapsed P κ (Ioc 0 1)) →
      ∀ {ε C q : ℝ} {Ctime : ℝ≥0}, ε ≤ εfar →
      (∀ τ ∈ Ioc (-Tstar) 0, ∀ x : P.M, q < metricScalarAt (G τ) x →
        Nonempty (SpatialNeck (G τ) ε x) ∨
        (∃ w : P.M, Nonempty (SpatialNeck (G τ) ε w) ∧
          metricScalarAt (G τ) x ≤ C * metricScalarAt (G τ) w ∧
          riemannianEDistOf (G τ) x w < ENNReal.ofReal 2) ∨
        CompactSpace P.M) →
      (∀ τ ∈ Ioo (-Tstar) 0, ∀ x : P.M, q < metricScalarAt (G τ) x →
        |derivWithin (fun v => metricScalarAt (G v) x) (Iic τ) τ| ≤
          Ctime * metricScalarAt (G τ) x ^ 2) →
      (∀ A Dd : ℝ, ∃ C : ℝ, ∀ τ ∈ Ioo (-Tstar) 0, ∀ z x : P.M,
        metricScalarAt (G τ) z ≤ A → riemannianEDistOf (G τ) z x < ENNReal.ofReal Dd →
          metricScalarAt (G τ) x ≤ C) →
      ∃ C : ℝ, ∀ τ ∈ Ioc (-Tstar) 0, ∀ x : P.M, metricScalarAt (G τ) x ≤ C := by
  obtain ⟨eps₀, heps₀, hslice⟩ :=
    exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives.{u}
  obtain ⟨εF, hεF, hfar⟩ := exists_scalar_bound_far_of_neck_alternatives.{u}
  refine ⟨min eps₀ εF, lt_min heps₀ hεF, ?_⟩
  intro P _ Tstar hT G hS hG0 hcomplete hcone hnc ε C q Ctime heps hW hderiv hRP
  let D := RealTimeInterval.openClosed (-Tstar) 0 0 ⟨by linarith, le_rfl⟩
  let S : SolutionOn (I := I3) (M := P.M) D := { base.metric := G }
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have h0mem : (0 : ℝ) ∈ Ioc (-Tstar) 0 := ⟨by linarith, le_rfl⟩
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : ℝ, ∀ x : P.M, metricScalarAt (G 0) x ≤ Q₀ := by
    by_cases hcpt0 : CompactSpace P.M
    · obtain ⟨C0, hC0⟩ := (isCompact_univ.image (metricScalar_smooth (G 0)).continuous).bddAbove
      exact ⟨C0, fun x => hC0 ⟨x, mem_univ x, rfl⟩⟩
    · refine hslice (G 0) (hcomplete 0 h0mem) (hcone 0 h0mem) (C := C) (q := q)
        (heps.trans (min_le_left _ _)) fun x hx => ?_
      rcases hW 0 h0mem x hx with h1 | ⟨w, hw, hxw, -⟩ | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨w, hw, hxw⟩)
      · exact (hcpt0 h3).elim
  set Q := max Q₀ 0 with hQdef
  have hQ : 0 ≤ Q := le_max_right _ _
  have hterminal : ∀ x : P.M, metricScalarAt (G 0) x ≤ Q :=
    fun x => (hQ₀ x).trans (le_max_left _ _)
  have hcone0 : ∀ x : P.M, metricAlgebraicCurvatureTensorAt P.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone := by
    rw [← hG0]
    exact hcone 0 h0mem
  have hterminal0 : ∀ x : P.M, metricScalarAt P.metric x ≤ Q := by
    rw [← hG0]
    exact hterminal
  set c₀ := (20 / 3 : ℝ) * Real.sqrt (2 * Tstar * Q) * Real.sqrt Tstar with hc₀def
  have hc₀ : 0 ≤ c₀ := by positivity
  have hdistance : ∀ s ∈ Ioc (-Tstar) 0,
      (∃ K : ℝ, ∀ τ ∈ Icc s 0, ∀ x : P.M, metricScalarAt (G τ) x ≤ K) →
      ∀ x y : P.M, metricDistance P.metric x y ≤ metricDistance (G s) x y ∧
        metricDistance (G s) x y ≤ metricDistance P.metric x y + c₀ := by
    intro s hs hKs x y
    obtain ⟨K, hK⟩ := hKs
    rcases hs.2.eq_or_lt with h | h
    · subst h
      rw [hG0]
      exact ⟨le_rfl, le_add_of_nonneg_right hc₀⟩
    · have hsub : Icc s 0 ⊆ Ioc (-Tstar) 0 := fun r hr => ⟨hs.1.trans_le hr.1, hr.2⟩
      have hbound : ∃ C : ℝ, ∀ r ∈ Icc s 0, ∀ z : P.M,
          Tensor0SBundle.normSq0S (S.base.metric r) z 4 (S.base.rm04 r z) ≤ C := by
        refine ⟨100 ^ 2 * (max K 0) ^ 2, fun r hr z => ?_⟩
        have hnorm := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
          (G r) z hdim (hcone r (hsub hr) z)
        have hR0 := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative (G r) z
          (hcone r (hsub hr) z)
        change Tensor0SBundle.normSq0S (G r) z 4 (metricRm04 (G r) z) ≤ _
        exact hnorm.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hR0 ((hK r hr z).trans (le_max_left _ _)) 2) (by norm_num))
      have hd := ricciFlow_additive_distance_bound_of_terminal_scalar S hS
        (by simp [ThreeSpace]) ‹_› h hsub (fun r hr => ⟨hs.1.trans hr.1, hr.2⟩)
        (fun r hr => hcomplete r (hsub hr)) hbound (fun r hr => hcone r (hsub hr)) hQ
        hterminal ⟨le_rfl, h.le⟩ x y
      rw [show S.base.metric 0 = P.metric from hG0] at hd
      have hd' : 0 ≤ metricDistance (G s) x y - metricDistance P.metric x y ∧
          metricDistance (G s) x y - metricDistance P.metric x y ≤
            (20 / 3 : ℝ) * Real.sqrt (2 * (0 - s) * Q) *
              (Real.sqrt (0 - s) - Real.sqrt (s - s)) := by
        simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
          show (3 : ℝ) - 1 = 2 by norm_num, metricDistance] using hd
      have hcoeff : (20 / 3 : ℝ) * Real.sqrt (2 * (0 - s) * Q) ≤
          (20 / 3 : ℝ) * Real.sqrt (2 * Tstar * Q) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith [hs.1])) (by norm_num)
      have hroot : Real.sqrt (0 - s) ≤ Real.sqrt Tstar :=
        Real.sqrt_le_sqrt (by linarith [hs.1])
      have hfinal : (20 / 3 : ℝ) * Real.sqrt (2 * (0 - s) * Q) *
          (Real.sqrt (0 - s) - Real.sqrt (s - s)) ≤ c₀ := by
        rw [sub_self, Real.sqrt_zero, sub_zero]
        exact mul_le_mul hcoeff hroot (Real.sqrt_nonneg _) (by positivity)
      constructor <;> linarith [hd'.1, hd'.2]
  let _ : EMetricSpace P.M := P.emetricSpace
  have hfinite (x y : P.M) : edist x y ≠ ⊤ := riemannianEDistOf_ne_top P.metric x y
  let _ : MetricSpace P.M := EMetricSpace.toMetricSpace hfinite
  have hdist (x y : P.M) : dist x y = metricDistance P.metric x y := rfl
  have hedist : ∀ (s Dd : ℝ) (z x : P.M), metricDistance (G s) z x < Dd →
      riemannianEDistOf (G s) z x < ENNReal.ofReal Dd := by
    intro s Dd z x hlt
    rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top _ _ _)]
    exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_nonneg.trans_lt hlt)).mpr hlt
  have hanchor : ∃ Cs : ℝ, Q ≤ Cs ∧ ∀ s ∈ Ioc (-Tstar) 0,
      (∃ K : ℝ, ∀ τ ∈ Icc s 0, ∀ x : P.M, metricScalarAt (G τ) x ≤ K) →
      ∀ x : P.M, metricScalarAt (G s) x ≤ Cs := by
    by_cases hcpt : CompactSpace P.M
    · obtain ⟨R, _hR, hballR⟩ :=
        (isCompact_univ : IsCompact (univ : Set P.M)).isBounded.subset_closedBall_lt
          0 P.basepoint
      have hdiam (x y : P.M) : metricDistance P.metric x y ≤ 2 * R := by
        have hx := hballR (mem_univ x)
        have hy := hballR (mem_univ y)
        rw [Metric.mem_closedBall] at hx hy
        have htri := dist_triangle x P.basepoint y
        rw [dist_comm P.basepoint y] at htri
        rw [← hdist]
        linarith
      obtain ⟨C', hC'⟩ := hRP Q (2 * R + c₀ + 1)
      refine ⟨max Q C', le_max_left _ _, ?_⟩
      intro s hs hKs x
      rcases hs.2.eq_or_lt with h | h
      · subst h
        exact (hterminal x).trans (le_max_left _ _)
      · obtain ⟨z, hz⟩ := exists_scalar_le_at_earlier_time_of_compact S hS hs.2
          (fun r hr => ⟨hs.1.trans_le hr.1, hr.2⟩) (fun r hr => ⟨hs.1.trans hr.1, hr.2⟩)
          P.basepoint
        have hzQ : metricScalarAt (G s) z ≤ Q := hz.trans (hterminal _)
        have hd := (hdistance s hs hKs z x).2
        have hlt := hedist s (2 * R + c₀ + 1) z x (by linarith [hdiam z x])
        exact (hC' s ⟨hs.1, h⟩ z x hzQ hlt).trans (le_max_right _ _)
    · let _ : NoncompactSpace P.M := ⟨fun h => hcpt (isCompact_univ_iff.mp h)⟩
      obtain ⟨κ, hκ, hncκ⟩ := hnc
      have hK0 : ∀ x : P.M, Tensor0SBundle.normSq0S P.metric x 4 (metricRm04At P.metric x) ≤
          100 ^ 2 * Q ^ 2 := by
        intro x
        have hnorm := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
          P.metric x hdim (hcone0 x)
        have hR0 := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative P.metric x
          (hcone0 x)
        exact hnorm.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hR0 (hterminal0 x) 2) (by norm_num))
      have hcomplete0 : RiemannianMetricComplete P.metric := by
        rw [← hG0]
        exact hcomplete 0 h0mem
      obtain ⟨Rf, Cf, hfarb⟩ := hfar (P := P) hcomplete0 hcone0 hκ hncκ hK0
        (heps.trans (min_le_right _ _)) hc₀ P.basepoint
      have hescape : ∃ z : P.M, max Rf 0 < metricDistance P.metric P.basepoint z := by
        by_contra! hbound
        have hball : (univ : Set P.M) ⊆
            riemannianClosedBallOf P.metric P.basepoint (max Rf 0) := by
          intro z _
          exact (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top _ _ _)
            (le_max_right _ _)).mpr (hbound z)
        have hcomp := (RiemannianMetricComplete.closedEBall_isCompact hcomplete0 P.basepoint
          (max Rf 0)).of_isClosed_subset isClosed_univ hball
        exact hcpt (isCompact_univ_iff.mp hcomp)
      obtain ⟨z, hz⟩ := hescape
      have hzf : Rf < metricDistance P.metric P.basepoint z :=
        (le_max_left _ _).trans_lt hz
      set Dd := metricDistance P.metric z P.basepoint + Rf + c₀ + 1 with hDd
      obtain ⟨C', hC'⟩ := hRP Cf Dd
      refine ⟨max Q (max Cf C'), le_max_left _ _, ?_⟩
      intro s hs hKs x
      rcases hs.2.eq_or_lt with h | h
      · subst h
        exact (hterminal x).trans (le_max_left _ _)
      · have herror := hdistance s hs hKs
        have hfs := hfarb (G s) (hcomplete s hs) (hcone s hs) (hW s hs) herror
        by_cases hx : Rf < metricDistance P.metric P.basepoint x
        · exact (hfs x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
        · have hRx : metricDistance P.metric P.basepoint x ≤ Rf := le_of_not_gt hx
          have hzx : metricDistance (G s) z x < Dd := by
            have htri := dist_triangle z P.basepoint x
            rw [hdist, hdist, hdist] at htri
            have hd := (herror z x).2
            rw [hDd]
            linarith
          exact (hC' s ⟨hs.1, h⟩ z x (hfs z hzf) (hedist s Dd z x hzx)).trans
            ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨Cs, hQCs, hCs⟩ := hanchor
  set B := max Cs (max q 1) with hBdef
  have hB : 0 < B := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_right _ _))
  have hqB : q ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hCsB : Cs ≤ B := le_max_left _ _
  set δ := 1 / (2 * ((Ctime : ℝ) + 1) * B) with hδdef
  have hδ : 0 < δ := by positivity
  have hKδ : (Ctime : ℝ) * δ ≤ 1 / (2 * B) := by
    have h1 : (Ctime : ℝ) * δ ≤ ((Ctime : ℝ) + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have h2 : ((Ctime : ℝ) + 1) * δ = 1 / (2 * B) := by
      rw [hδdef]
      field_simp
    linarith
  have hdiffAt : ∀ v ∈ Ioo (-Tstar) 0, ∀ x : P.M,
      DifferentiableAt ℝ (fun w => metricScalarAt (G w) x) v := by
    intro v hv x
    have h := hS.scalarTime (K := Ioo (-Tstar) 0) (t := v) hv (fun w hw => ⟨hw.1, hw.2.le⟩) x
    exact h.differentiableAt (Ioo_mem_nhds hv.1 hv.2)
  have hcontx : ∀ x : P.M, ContinuousOn (fun w => metricScalarAt (G w) x) (Ioc (-Tstar) 0) := by
    intro x
    have hc : ContinuousOn (fun w : ℝ => S.scalar w x) (Ioc (-Tstar) 0) :=
      hS.scalarCont.comp (f := fun w : ℝ => (w, x))
        (continuousOn_id.prodMk continuousOn_const) (fun w hw => ⟨hw, mem_univ x⟩)
    exact hc
  have hstep : ∀ s₀ ∈ Ioc (-Tstar) 0, ∀ n : ℕ, ∀ τ ∈ Icc (max s₀ (-((n : ℝ) * δ))) 0,
      ∀ x : P.M, metricScalarAt (G τ) x ≤ Cs := by
    intro s₀ hs₀ n
    induction n with
    | zero =>
      intro τ hτ x
      have hτ0 : τ = 0 := by
        have h1 := hτ.1
        simp only [Nat.cast_zero, zero_mul, neg_zero] at h1
        exact le_antisymm hτ.2 ((le_max_right _ _).trans h1)
      rw [hτ0]
      exact (hterminal x).trans hQCs
    | succ n ih =>
      set a := max s₀ (-((n : ℝ) * δ)) with hadef
      set a' := max s₀ (-(((n + 1 : ℕ) : ℝ) * δ)) with ha'def
      have haa' : a - a' ≤ δ := by
        have h1 : s₀ ≤ a' := le_max_left _ _
        have h2 : -(((n + 1 : ℕ) : ℝ) * δ) ≤ a' := le_max_right _ _
        push_cast at h2
        rcases le_total s₀ (-((n : ℝ) * δ)) with h | h
        · rw [hadef, max_eq_right h]
          linarith
        · rw [hadef, max_eq_left h]
          linarith
      have ha'mem : -Tstar < a' := hs₀.1.trans_le (le_max_left _ _)
      have ha0 : a ≤ 0 := max_le hs₀.2 (neg_nonpos.mpr (by positivity))
      have hwin : ∀ τ ∈ Icc a' 0, ∀ x : P.M, metricScalarAt (G τ) x ≤ 2 * B := by
        intro τ hτ x
        rcases le_total τ a with hτa | hτa
        · refine le_two_mul_of_abs_deriv_le_mul_sq_of_continuousOn_of_right_le
            (u := fun w => metricScalarAt (G w) x) hB (NNReal.coe_nonneg Ctime)
            ((hcontx x).mono fun w hw => ⟨ha'mem.trans_le hw.1, hw.2.trans ha0⟩)
            (fun v hv => hdiffAt v ⟨ha'mem.trans hv.1, hv.2.trans_le ha0⟩ x) ?_
            ((ih a ⟨le_rfl, ha0⟩ x).trans hCsB)
            ((mul_le_mul_of_nonneg_left haa' (NNReal.coe_nonneg Ctime)).trans hKδ) τ ⟨hτ.1, hτa⟩
          intro v hv hBv
          have hvmem : v ∈ Ioo (-Tstar) 0 := ⟨ha'mem.trans hv.1, hv.2.trans_le ha0⟩
          have h := hderiv v hvmem x (hqB.trans_lt hBv)
          rwa [(hdiffAt v hvmem x).derivWithin (uniqueDiffWithinAt_Iic v)] at h
        · exact (ih τ ⟨hτa, hτ.2⟩ x).trans (by linarith)
      intro τ hτ x
      exact hCs τ ⟨ha'mem.trans_le hτ.1, hτ.2⟩
        ⟨2 * B, fun w hw => hwin w ⟨hτ.1.trans hw.1, hw.2⟩⟩ x
  refine ⟨Cs, fun τ hτ x => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (-τ / δ)
  have hmax : max τ (-((n : ℝ) * δ)) = τ := by
    apply max_eq_left
    have h1 := (div_le_iff₀ hδ).mp hn
    linarith
  exact hstep τ hτ n τ (by rw [hmax]; exact ⟨le_rfl, hτ.2⟩) x

def windowNeckAccuracy : ℝ :=
  exists_uniform_scalar_bound_on_openClosed_window_of_neck_alternatives.{u}.choose

theorem windowNeckAccuracy_pos : 0 < windowNeckAccuracy.{u} :=
  exists_uniform_scalar_bound_on_openClosed_window_of_neck_alternatives.{u}.choose_spec.1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
