import DifferentialGeometry.Geometry.Metric.Approximation.RealBallExamples
import DifferentialGeometry.Geometry.Metric.Approximation.ControlledPointedIsometry

namespace GC.MetricGeometry

open PointedBallApprox

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
variable {p : X} {q : Y} {o : Z} {ε j : ℝ}

theorem commonSourceComparison_forward_error
    (f : PointedBallApprox o p (4 * j + 4) ε)
    (g : PointedBallApprox o q (4 * j + 4) ε)
    (hj : 1 ≤ j) (hε : 10 * ε < j)
    (x : BallCarrier o (4 * j + 4)) (hx : dist (f.toFun x) p ≤ j) :
    dist (g.toFun x) ((commonSourceComparison f g hj hε).toFun ⟨f.toFun x, hx⟩) < 3 * ε := by
  have hsR : 2 * j + 2 + ε ≤ 4 * j + 4 := by linarith [f.error_pos]
  let y : BallCarrier p (2 * j + 2) := ⟨f.toFun x, by linarith⟩
  let z := f.inverseLift hsR y
  have hspec : dist (f.toFun x) (f.toFun z) < ε := f.inverseLift_spec hsR y
  have hdist := (abs_lt.mp (f.distortion x z)).1
  have hg := (abs_lt.mp (g.distortion x z)).2
  have he : (commonSourceComparison f g hj hε).toFun ⟨f.toFun x, hx⟩ = g.toFun z := by
    have hcast {η η' : ℝ} (hh : η = η') (F : PointedBallApprox p q j η)
        (t : BallCarrier p j) :
        (cast (congrArg (fun r => PointedBallApprox p q j r) hh) F).toFun t = F.toFun t := by
      cases hh
      rfl
    change (cast (congrArg (fun r => PointedBallApprox p q j r)
      (by ring : 2 * (4 * ε + ε) = 10 * ε))
      ((f.quasiInverse (s := 2 * j + 2) (by linarith [f.error_pos]) hsR).comp g
        (s := j) (by linarith) (by linarith) (by linarith [f.error_pos]))).toFun _ = _
    rw [hcast (by ring)]
    rfl
  rw [he]
  linarith

open Filter
open scoped Topology

theorem exists_controlled_common_limit_isometry
    {T : ℕ → Type*} [∀ i, MetricSpace (T i)] [ProperSpace X] [ProperSpace Y]
    {o : ∀ i, T i} {J ε : ℕ → ℝ}
    (hJone : ∀ i, 1 ≤ J i) (hJ : Tendsto J atTop atTop)
    (hε : Tendsto ε atTop (𝓝 0)) (hεJ : ∀ i, 10 * ε i < J i)
    (f : ∀ i, PointedBallApprox (o i) p (4 * J i + 4) (ε i))
    (g : ∀ i, PointedBallApprox (o i) q (4 * J i + 4) (ε i)) :
    ∃ (e : X ≃ᵢ Y) (φ : ℕ → ℕ), e p = q ∧ StrictMono φ ∧
      ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
        ∀ x : BallCarrier (o (φ i)) (4 * J (φ i) + 4), dist x.val (o (φ i)) ≤ S →
          dist ((g (φ i)).toFun x) (e ((f (φ i)).toFun x)) < η := by
  have heps : Tendsto (fun i => 10 * ε i) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hε.const_mul 10
  obtain ⟨e, φ, he, hφ, hcontrol⟩ :=
    exists_isometryEquiv_subsequence_of_pointed_approximations hJ heps
      (fun i => commonSourceComparison (f i) (g i) (hJone i) (hεJ i))
  refine ⟨e, φ, he, hφ, ?_⟩
  intro S η hη
  filter_upwards [hcontrol (S + 1) (η / 2) (by positivity),
    (hε.comp hφ.tendsto_atTop).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (hε.comp hφ.tendsto_atTop).eventually (eventually_lt_nhds (by positivity : 0 < η / 6)),
    (hJ.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop (S + 1))]
    with i hi hiε hiη hiJ
  dsimp only [Function.comp_def] at hiε hiη hiJ
  intro x hx
  have hrad := (f (φ i)).radial_upper x
  have hxS : dist ((f (φ i)).toFun x) p ≤ S + 1 := by linarith
  have hxJ := hxS.trans hiJ
  have hnear := commonSourceComparison_forward_error (f (φ i)) (g (φ i))
    (hJone (φ i)) (hεJ (φ i)) x hxJ
  have hc := hi ⟨(f (φ i)).toFun x, hxJ⟩ hxS
  have ht := dist_triangle ((g (φ i)).toFun x)
    ((commonSourceComparison (f (φ i)) (g (φ i)) (hJone (φ i)) (hεJ (φ i))).toFun
      ⟨(f (φ i)).toFun x, hxJ⟩) (e ((f (φ i)).toFun x))
  linarith

end GC.MetricGeometry
