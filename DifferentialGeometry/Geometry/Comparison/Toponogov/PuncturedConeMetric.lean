import DifferentialGeometry.Geometry.Comparison.Toponogov.PuncturedConeApproximation
import DifferentialGeometry.Geometry.Metric.ConeAnnulus

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.Toponogov
universe u
variable {M : Type u} [MetricSpace M]
  {q : UniformSpace.Completion M} {r : ℝ}

private theorem coneDistance_triangle_of_approximation
    (C : PuncturedConeApproximation q r)
    (i j k : {x : M // dist (x : UniformSpace.Completion M) q ∈ Ioo 0 (r / 3)})
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    let _ := C.angles.metricSpace
    Metric.coneDistance (a, (C.angles.classOf i : UniformSpace.Completion (Quotient C.angles.setoid)))
        (c, (C.angles.classOf k : UniformSpace.Completion (Quotient C.angles.setoid))) ≤
      Metric.coneDistance (a, (C.angles.classOf i : UniformSpace.Completion (Quotient C.angles.setoid)))
        (b, (C.angles.classOf j : UniformSpace.Completion (Quotient C.angles.setoid))) +
      Metric.coneDistance (b, (C.angles.classOf j : UniformSpace.Completion (Quotient C.angles.setoid)))
        (c, (C.angles.classOf k : UniformSpace.Completion (Quotient C.angles.setoid))) := by
  classical
  let _ := C.angles.metricSpace
  dsimp only
  let A := min a (min b c)
  let B := max a (max b c)
  have hA : 0 < A := lt_min ha (lt_min hb hc)
  have haAB : a ∈ Icc A B := ⟨min_le_left _ _, le_max_left _ _⟩
  have hbAB : b ∈ Icc A B := ⟨(min_le_right _ _).trans (min_le_left _ _),
    (le_max_left _ _).trans (le_max_right _ _)⟩
  have hcAB : c ∈ Icc A B := ⟨(min_le_right _ _).trans (min_le_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩
  by_contra h
  let D := Metric.coneDistance (a, (C.angles.classOf i : UniformSpace.Completion (Quotient C.angles.setoid)))
    (c, (C.angles.classOf k : UniformSpace.Completion (Quotient C.angles.setoid))) -
    (Metric.coneDistance (a, (C.angles.classOf i : UniformSpace.Completion (Quotient C.angles.setoid)))
      (b, (C.angles.classOf j : UniformSpace.Completion (Quotient C.angles.setoid))) +
    Metric.coneDistance (b, (C.angles.classOf j : UniformSpace.Completion (Quotient C.angles.setoid)))
      (c, (C.angles.classOf k : UniformSpace.Completion (Quotient C.angles.setoid))))
  have hD : 0 < D := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨S, hFS, _, _, happrox⟩ := C.approximation A B (D / 4) hA
    (haAB.1.trans haAB.2) (by positivity) {(i, a), (j, b), (k, c)} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact haAB
      · exact hbAB
      · exact hcAB)
  have hi : (i, a) ∈ S := hFS (by simp)
  have hj : (j, b) ∈ S := hFS (by simp)
  have hk : (k, c) ∈ S := hFS (by simp)
  have hpositive : ∀ᶠ rho : ℝ in 𝓝[>] 0, 0 < rho := self_mem_nhdsWithin
  obtain ⟨rho, hpos, _, _, _, hpair⟩ := (hpositive.and happrox).exists
  have htri := div_le_div_of_nonneg_right
    (dist_triangle (C.ray i (rho * a)) (C.ray j (rho * b)) (C.ray k (rho * c))) hpos.le
  rw [add_div] at htri
  have hac := abs_lt.mp (hpair (i, a) hi (k, c) hk)
  have hab := abs_lt.mp (hpair (i, a) hi (j, b) hj)
  have hbc := abs_lt.mp (hpair (j, b) hj (k, c) hk)
  dsimp only [Prod.fst, Prod.snd] at hac hab hbc
  dsimp only [D] at hD
  dsimp only [D] at hac hab hbc
  linarith only [hD, htri, hac.2, hab.1, hbc.1]

private theorem coneDistance_triangle_on_completed_directions
    (C : PuncturedConeApproximation q r) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    let _ := C.angles.metricSpace
    ∀ x y z : UniformSpace.Completion (Quotient C.angles.setoid),
      Metric.coneDistance (a, x) (c, z) ≤
        Metric.coneDistance (a, x) (b, y) + Metric.coneDistance (b, y) (c, z) := by
  let _ := C.angles.metricSpace
  dsimp only
  intro x y z
  refine UniformSpace.Completion.induction_on₃
    (p := fun x y z => Metric.coneDistance (a, x) (c, z) ≤
      Metric.coneDistance (a, x) (b, y) + Metric.coneDistance (b, y) (c, z)) x y z ?_ ?_
  · unfold Metric.coneDistance
    apply isClosed_le <;> fun_prop
  · intro x y z
    obtain ⟨i, rfl⟩ := C.angles.classOf_surjective x
    obtain ⟨j, rfl⟩ := C.angles.classOf_surjective y
    obtain ⟨k, rfl⟩ := C.angles.classOf_surjective z
    exact coneDistance_triangle_of_approximation C i j k ha hb hc


@[instance_reducible]
def PuncturedConeApproximation.annulusMetricSpace
    (C : PuncturedConeApproximation q r) {a b : ℝ} (ha : 0 < a) :
    let _ := C.angles.metricSpace
    MetricSpace (Metric.ConeAnnulus a b (UniformSpace.Completion (Quotient C.angles.setoid))) := by
  let _ := C.angles.metricSpace
  let _ : CompactSpace (UniformSpace.Completion (Quotient C.angles.setoid)) := C.compact_directions
  exact MetricSpace.ofContinuousDistOfCompact
    (fun x y => Metric.coneDistance ((x.1 : ℝ), x.2) ((y.1 : ℝ), y.2))
    (fun x => Metric.coneDistance_self _)
    (fun x y => Metric.coneDistance_comm _ _)
    (fun x y z => coneDistance_triangle_on_completed_directions C
      (ha.trans_le x.1.property.1) (ha.trans_le y.1.property.1) (ha.trans_le z.1.property.1) _ _ _)
    (fun x y h => by
      have heq := (Metric.coneDistance_eq_zero_iff
        (ha.trans_le x.1.property.1) (ha.trans_le y.1.property.1)).mp h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst heq))
        (congrArg (fun z : ℝ × UniformSpace.Completion (Quotient C.angles.setoid) => z.2) heq))
    (by
      change Continuous (fun p : (Icc a b × UniformSpace.Completion (Quotient C.angles.setoid)) ×
        (Icc a b × UniformSpace.Completion (Quotient C.angles.setoid)) =>
          Metric.coneDistance ((p.1.1 : ℝ), p.1.2) ((p.2.1 : ℝ), p.2.2))
      unfold Metric.coneDistance
      fun_prop)

@[simp] theorem PuncturedConeApproximation.annulusMetricSpace_dist
    (C : PuncturedConeApproximation q r) {a b : ℝ} (ha : 0 < a) :
    let _ := C.angles.metricSpace
    let _ : MetricSpace (Metric.ConeAnnulus a b (UniformSpace.Completion (Quotient C.angles.setoid))) :=
      C.annulusMetricSpace ha
    ∀ x y : Metric.ConeAnnulus a b (UniformSpace.Completion (Quotient C.angles.setoid)),
      dist x y = Metric.coneDistance ((x.1 : ℝ), x.2) ((y.1 : ℝ), y.2) := by
  intros
  rfl

theorem PuncturedConeApproximation.exists_annulus_approximation
    (C : PuncturedConeApproximation q r) {a b eps : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (heps : 0 < eps) :
    let _ := C.angles.metricSpace
    let _ : MetricSpace (Metric.ConeAnnulus a b (UniformSpace.Completion (Quotient C.angles.setoid))) :=
      C.annulusMetricSpace ha
    ∀ᶠ rho in 𝓝[>] (0 : ℝ),
      ∃ F : {x : M // dist (x : UniformSpace.Completion M) q / rho ∈ Icc a b} →
        Metric.ConeAnnulus a b (UniformSpace.Completion (Quotient C.angles.setoid)),
        (∀ x y, |dist (F x) (F y) - dist (x : M) (y : M) / rho| < eps) ∧
        (∀ z, ∃ x, dist z (F x) < eps) ∧
        (∀ x, |((F x).1 : ℝ) - dist (x.val : UniformSpace.Completion M) q / rho| < eps) := by
  classical
  let _ := C.angles.metricSpace
  let _ : MetricSpace (Metric.ConeAnnulus a b (UniformSpace.Completion (Quotient C.angles.setoid))) :=
    C.annulusMetricSpace ha
  dsimp only
  obtain ⟨S, _, hS, hnet, happrox⟩ := C.approximation a b (eps / 4) ha hab
    (by positivity) ∅ (by simp)
  let z (p : S) : Metric.ConeAnnulus a b (UniformSpace.Completion (Quotient C.angles.setoid)) :=
    (⟨p.val.2, hS p.val p.property⟩, C.angles.classOf p.val.1)
  filter_upwards [happrox, self_mem_nhdsWithin] with rho hrho hpos
  change 0 < rho at hpos
  obtain ⟨_, hsource, hcover, hpair⟩ := hrho
  let A := {x : M // dist (x : UniformSpace.Completion M) q / rho ∈ Icc a b}
  have hnear (x : A) : ∃ p : S,
      dist (x.val : UniformSpace.Completion M) (C.ray p.val.1 (rho * p.val.2)) / rho < eps / 4 := by
    obtain ⟨p, hp, hx⟩ := hcover x.val x.property
    exact ⟨⟨p, hp⟩, hx⟩
  choose p hp using hnear
  let F : A → Metric.ConeAnnulus a b (UniformSpace.Completion (Quotient C.angles.setoid)) := fun x => z (p x)
  have hdist (v w : S) :
      |dist (z v) (z w) -
        dist (C.ray v.val.1 (rho * v.val.2)) (C.ray w.val.1 (rho * w.val.2)) / rho| < eps / 4 :=
    hpair v.val v.property w.val w.property
  refine ⟨F, ?_, ?_, ?_⟩
  · intro x y
    have hxy := hp x
    have hyx := hp y
    have hh := abs_lt.mp (hdist (p x) (p y))
    have htri₁ := dist_triangle4 (x.val : UniformSpace.Completion M)
      (C.ray (p x).val.1 (rho * (p x).val.2))
      (C.ray (p y).val.1 (rho * (p y).val.2)) (y.val : UniformSpace.Completion M)
    have htri₂ := dist_triangle4
      (C.ray (p x).val.1 (rho * (p x).val.2)) (x.val : UniformSpace.Completion M)
      (y.val : UniformSpace.Completion M) (C.ray (p y).val.1 (rho * (p y).val.2))
    have htri₁' := div_le_div_of_nonneg_right htri₁ hpos.le
    have htri₂' := div_le_div_of_nonneg_right htri₂ hpos.le
    rw [add_div, add_div, dist_comm (C.ray (p y).val.1 (rho * (p y).val.2)) (y.val : UniformSpace.Completion M),
      UniformSpace.Completion.dist_eq] at htri₁'
    rw [add_div, add_div, dist_comm (C.ray (p x).val.1 (rho * (p x).val.2)) (x.val : UniformSpace.Completion M),
      UniformSpace.Completion.dist_eq] at htri₂'
    change |dist (z (p x)) (z (p y)) - dist (x.val : M) (y.val : M) / rho| < eps
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · intro y
    obtain ⟨v, hv, hy⟩ := hnet y.1 y.1.property y.2
    obtain ⟨x, hx⟩ := (hsource v hv).1
    change (x : UniformSpace.Completion M) = C.ray v.1 (rho * v.2) at hx
    have hxA : x ∈ {x : M | dist (x : UniformSpace.Completion M) q / rho ∈ Icc a b} := by
      change dist (x : UniformSpace.Completion M) q / rho ∈ Icc a b
      rw [dist_comm, hx, (hsource v hv).2]
      exact hS v hv
    let xA : A := ⟨x, hxA⟩
    have hpnear := hp xA
    change dist (x : UniformSpace.Completion M)
      (C.ray (p xA).val.1 (rho * (p xA).val.2)) / rho < eps / 4 at hpnear
    rw [hx] at hpnear
    have hdist' := (abs_lt.mp (hdist ⟨v, hv⟩ (p xA))).2
    have hy' : dist y (z ⟨v, hv⟩) < eps / 4 := hy
    refine ⟨xA, ?_⟩
    have htri := dist_triangle y (z ⟨v, hv⟩) (z (p xA))
    change dist y (z (p xA)) < eps
    linarith only [htri, hdist', hy', hpnear, heps]
  · intro x
    have hrad : dist (C.ray (p x).val.1 (rho * (p x).val.2)) q / rho = (p x).val.2 := by
      rw [dist_comm]
      exact (hsource (p x).val (p x).property).2
    have hh : |dist (C.ray (p x).val.1 (rho * (p x).val.2)) q / rho -
        dist (x.val : UniformSpace.Completion M) q / rho| ≤
        dist (x.val : UniformSpace.Completion M) (C.ray (p x).val.1 (rho * (p x).val.2)) / rho := by
      rw [← sub_div, abs_div, abs_of_pos hpos]
      have ht := abs_dist_sub_le (C.ray (p x).val.1 (rho * (p x).val.2))
        (x.val : UniformSpace.Completion M) q
      rw [dist_comm (C.ray (p x).val.1 (rho * (p x).val.2))
        (x.val : UniformSpace.Completion M)] at ht
      exact div_le_div_of_nonneg_right ht hpos.le
    rw [hrad] at hh
    exact (hh.trans_lt (hp x)).trans (by linarith)

theorem PuncturedConeApproximation.exists_ball_approximation
    (C : PuncturedConeApproximation q r) {delta eps : ℝ}
    (hdelta : 0 < delta) (hsmall : delta < 1 / 2) (heps : 0 < eps) :
    let _ := C.angles.metricSpace
    let _ : MetricSpace (Metric.ConeAnnulus (1 / 2) (3 / 2)
      (UniformSpace.Completion (Quotient C.angles.setoid))) :=
      C.annulusMetricSpace (by norm_num : 0 < (1 / 2 : ℝ))
    ∀ᶠ rho in 𝓝[>] (0 : ℝ), ∃ hpos : 0 < rho,
      ∀ p : M, dist (p : UniformSpace.Completion M) q = rho →
        ∃ F : Metric.closedBall p (delta * rho) →
          Metric.ConeAnnulus (1 / 2) (3 / 2)
            (UniformSpace.Completion (Quotient C.angles.setoid)),
          (∀ x y, |dist (F x) (F y) - dist (x : M) (y : M) / rho| < eps) ∧
          (∀ z ∈ Metric.ball (F ⟨p, Metric.mem_closedBall_self (mul_pos hdelta hpos).le⟩)
            (delta / 2), ∃ x, dist z (F x) < eps) ∧
          (∀ x, |((F x).1 : ℝ) - dist (x.val : UniformSpace.Completion M) q / rho| < eps) := by
  let _ := C.angles.metricSpace
  let _ : MetricSpace (Metric.ConeAnnulus (1 / 2) (3 / 2)
    (UniformSpace.Completion (Quotient C.angles.setoid))) :=
      C.annulusMetricSpace (by norm_num : 0 < (1 / 2 : ℝ))
  dsimp only
  let eta := min eps (delta / 8)
  have heta : 0 < eta := lt_min heps (by positivity)
  have hetaE : eta ≤ eps := min_le_left _ _
  have hetaD : eta ≤ delta / 8 := min_le_right _ _
  filter_upwards [C.exists_annulus_approximation
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) heta,
    self_mem_nhdsWithin] with rho hrho hpos
  change 0 < rho at hpos
  refine ⟨hpos, ?_⟩
  intro p hp
  obtain ⟨A, hA, hcover, hrad⟩ := hrho
  have hin (x : Metric.closedBall p (delta * rho)) :
      dist (x.val : UniformSpace.Completion M) q / rho ∈ Icc (1 / 2) (3 / 2) := by
    have hx : dist (x : M) p ≤ delta * rho := x.property
    have ht := abs_dist_sub_le (x.val : UniformSpace.Completion M)
      (p : UniformSpace.Completion M) q
    rw [hp, UniformSpace.Completion.dist_eq] at ht
    obtain ⟨hl, hu⟩ := abs_le.mp ht
    constructor
    · apply (le_div_iff₀ hpos).mpr
      nlinarith only [hl, hx, mul_pos (sub_pos.mpr hsmall) hpos]
    · apply (div_le_iff₀ hpos).mpr
      nlinarith only [hu, hx, mul_pos (sub_pos.mpr hsmall) hpos]
  let j (x : Metric.closedBall p (delta * rho)) :
      {x : M // dist (x : UniformSpace.Completion M) q / rho ∈ Icc (1 / 2) (3 / 2)} :=
    ⟨x, hin x⟩
  let F := A ∘ j
  let p0 : Metric.closedBall p (delta * rho) :=
    ⟨p, Metric.mem_closedBall_self (mul_pos hdelta hpos).le⟩
  refine ⟨F, fun x y => (hA (j x) (j y)).trans_le hetaE, ?_,
    fun x => (hrad (j x)).trans_le hetaE⟩
  intro z hz
  have hz' : dist z (A (j p0)) < delta / 2 := hz
  obtain ⟨x, hx⟩ := hcover z
  have hpair := (abs_lt.mp (hA x (j p0))).1
  have htri := dist_triangle (A x) z (A (j p0))
  rw [dist_comm (A x) z] at htri
  have hdist : dist (x : M) p / rho < delta := by
    change -eta < dist (A x) (A (j p0)) - dist (x : M) p / rho at hpair
    linarith only [hpair, htri, hx, hz', hetaD, hdelta]
  have hxb : (x : M) ∈ Metric.closedBall p (delta * rho) :=
    ((div_lt_iff₀ hpos).mp hdist).le
  refine ⟨⟨x, hxb⟩, ?_⟩
  have hj : j ⟨x, hxb⟩ = x := Subtype.ext rfl
  change dist z (A (j ⟨x, hxb⟩)) < eps
  rw [hj]
  exact hx.trans_le hetaE

end DifferentialGeometry.Toponogov
