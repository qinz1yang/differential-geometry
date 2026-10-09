import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation

namespace GC.MetricGeometry.PointedBallApprox

universe u v w
variable {X : Type u} {Y : Type v} {L : Type w}
variable [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {R ε η : ℝ}

noncomputable def ofPairedNets (x : L → X) (y : L → Y) (o : L)
    (hxbase : x o = p) (hybase : y o = q)
    (hη : 0 < η) (hεR : ε < R) (herror : 3 * η < ε)
    (hsource : ∀ u : BallCarrier p R, ∃ a : L, dist u.val (x a) ≤ η)
    (htarget : ∀ v : Y, dist v q ≤ R - ε → ∃ a : L, dist v (y a) ≤ η)
    (hmatrix : ∀ a b : L, |dist (y a) (y b) - dist (x a) (x b)| < η) :
    PointedBallApprox p q R ε := by
  classical
  let label (u : BallCarrier p R) : L :=
    if u.val = p then o else (hsource u).choose
  have hlabel (u : BallCarrier p R) : dist u.val (x (label u)) ≤ η := by
    dsimp only [label]
    split_ifs with hu
    · simpa [hu, hxbase] using hη.le
    · exact (hsource u).choose_spec
  refine {
    error_pos := by linarith
    error_lt_radius := hεR
    toFun := fun u => y (label u)
    basepoint := by simp [label, hybase]
    distortion := ?_
    coverage := ?_ }
  · intro u v
    have hu := hlabel u
    have hv := hlabel v
    have hm := abs_lt.mp (hmatrix (label u) (label v))
    have hupper := dist_triangle4 (x (label u)) u.val v.val (x (label v))
    have hlower := dist_triangle4 u.val (x (label u)) (x (label v)) v.val
    rw [dist_comm (x (label u)) u.val] at hupper
    rw [dist_comm (x (label v)) v.val] at hlower
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · intro v hv
    obtain ⟨a, ha⟩ := htarget v hv
    have hrad := (abs_lt.mp (hmatrix a o)).1
    rw [hxbase, hybase] at hrad
    have htri := dist_triangle (y a) v q
    rw [dist_comm (y a) v] at htri
    have hxa : dist (x a) p ≤ R := by linarith
    let u : BallCarrier p R := ⟨x a, hxa⟩
    have hlabelu := hlabel u
    have hm := (abs_lt.mp (hmatrix a (label u))).2
    have htri' := dist_triangle v (y a) (y (label u))
    refine ⟨u, ?_⟩
    dsimp only [u] at hlabelu
    linarith

end GC.MetricGeometry.PointedBallApprox
