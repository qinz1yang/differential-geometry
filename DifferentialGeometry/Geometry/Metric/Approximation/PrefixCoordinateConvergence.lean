import DifferentialGeometry.Geometry.Metric.Approximation.CalibratedCoordinates
import DifferentialGeometry.Topology.MetricSpace.CalibratedSignedPrefix

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {Y Z : Type*} [MetricSpace Y] [MetricSpace Z]
variable {o : ∀ i, A i} {p : Y} {γ : ℝ → Y} {z : Z} {L R ε E η : ℕ → ℝ}

theorem eventually_distance_coordinate_error_lt_of_converging_prefixes
    (e : Y ≃ᵢ WithLp 2 (ℝ × Z)) (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t, z))
    (hγbase : γ 0 = p)
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (a : ∀ i, A i) (ha : ∀ i, dist (o i) (a i) = L i) (hL : ∀ i, 0 ≤ L i)
    (hE : ∀ i, 0 ≤ E i) (hEzero : Tendsto E atTop (𝓝 0))
    (hηzero : Tendsto η atTop (𝓝 0))
    (σ : ∀ i, Icc (-(L i)) (L i) → A i)
    (hLip : ∀ i, LipschitzWith 1 (σ i))
    (hbase : ∀ i, σ i ⟨0, ⟨by linarith [hL i], hL i⟩⟩ = o i)
    (hcal : ∀ i, ∀ t : Icc (0 : ℝ) (L i),
      t.val - η i ≤ L i - dist (σ i ⟨t.val, ⟨by linarith [t.property.1, hL i], t.property.2⟩⟩) (a i) ∧
      L i - dist (σ i ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hL i]⟩⟩) (a i) ≤
        -t.val + E i + η i)
    (hconv : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ R i ∧ S ≤ L i ∧
      ∀ t : Icc (-(L i)) (L i), |t.val| ≤ S →
        ∀ ht : dist (σ i t) (o i) ≤ R i,
          dist ((f i).toFun ⟨σ i t, ht⟩) (γ t.val) < ζ) :
    ∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ x : BallCarrier (o i) (R i), dist x.val (o i) ≤ S →
        |dist (o i) (a i) - dist x.val (a i) - (e ((f i).toFun x)).fst| < ζ := by
  subst p
  apply eventually_abs_distance_coordinate_error_lt_of_opposite_calibration e halign f hR hε a
    hE hEzero hηzero
  intro T hT ζ hζ
  filter_upwards [hconv T ζ hζ] with i hi
  obtain ⟨hiR, hiL, himap⟩ := hi
  let tPlus : Icc (-(L i)) (L i) := ⟨T, ⟨by linarith [hL i], hiL⟩⟩
  let tMinus : Icc (-(L i)) (L i) := ⟨-T, ⟨by linarith, by linarith [hL i]⟩⟩
  have hrad (t : Icc (-(L i)) (L i)) : dist (σ i t) (o i) ≤ |t.val| := by
    have hh := (hLip i).dist_le_mul t ⟨0, ⟨by linarith [hL i], hL i⟩⟩
    rw [hbase] at hh
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, sub_zero] using hh
  have hpabs : |tPlus.val| ≤ T := by dsimp [tPlus]; rw [abs_of_pos hT]
  have hmabs : |tMinus.val| ≤ T := by dsimp [tMinus]; rw [abs_neg, abs_of_pos hT]
  have hpR := (hrad tPlus).trans (hpabs.trans hiR)
  have hmR := (hrad tMinus).trans (hmabs.trans hiR)
  refine ⟨⟨σ i tPlus, hpR⟩, ⟨σ i tMinus, hmR⟩, ?_, ?_,
    (himap tPlus hpabs hpR).le, (himap tMinus hmabs hmR).le⟩
  · rw [ha]
    exact (hcal i ⟨T, ⟨hT.le, hiL⟩⟩).1
  · rw [ha]
    exact (hcal i ⟨T, ⟨hT.le, hiL⟩⟩).2

end GC.MetricGeometry
