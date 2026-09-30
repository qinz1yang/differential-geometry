import DifferentialGeometry.Geometry.Metric.Approximation.PointedEndpointLines
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixCoordinateConvergence
import DifferentialGeometry.Geometry.Comparison.LineBusemann

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y] [ProperSpace Y] [Finite ι]
variable {o : ∀ i, A i} {p : Y} {L : ℕ → ι → ℝ} {η : ℕ → ℝ}

theorem PointedGHConverges.exists_line_coordinates_of_opposite_endpoints
    (h : PointedGHConverges o p)
    (hs : fourPointComparison 0 (univ : Set Y))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (hcurves : ∀ i, ∀ a b : A i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → A i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (aPlus aMinus : ∀ i, ι → A i)
    (hLpos : ∀ i j, 0 < L i j) (hL : ∀ j, Tendsto (fun i => L i j) atTop atTop)
    (hp : ∀ i j, dist (o i) (aPlus i j) = L i j)
    (hm : ∀ i j, dist (o i) (aMinus i j) = L i j)
    (hE : ∀ j, Tendsto (fun i => 2 * L i j - dist (aPlus i j) (aMinus i j)) atTop (𝓝 0))
    (hηpos : ∀ i, 0 < η i) (hη : Tendsto η atTop (𝓝 0)) :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => o (ψ i)) p ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (o (ψ i)) p (R i) (ε i),
      ∃ q : ∀ i j, Icc (-(L (ψ i) j)) (L (ψ i) j) → A (ψ i),
      (∀ i j, LipschitzWith 1 (q i j)) ∧
      (∀ i j, q i j ⟨0, ⟨by linarith [hLpos (ψ i) j], (hLpos (ψ i) j).le⟩⟩ = o (ψ i)) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (L (ψ i) j),
        t.val - η (ψ i) ≤ L (ψ i) j - dist (q i j ⟨t.val, ⟨by linarith [t.property.1, hLpos (ψ i) j], t.property.2⟩⟩) (aPlus (ψ i) j) ∧
        L (ψ i) j - dist (q i j ⟨t.val, ⟨by linarith [t.property.1, hLpos (ψ i) j], t.property.2⟩⟩) (aPlus (ψ i) j) ≤ t.val ∧
        -t.val ≤ L (ψ i) j - dist (q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos (ψ i) j]⟩⟩) (aPlus (ψ i) j) ∧
        L (ψ i) j - dist (q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos (ψ i) j]⟩⟩) (aPlus (ψ i) j) ≤
          -t.val + (2 * L (ψ i) j - dist (aPlus (ψ i) j) (aMinus (ψ i) j)) + η (ψ i)) ∧
      ∃ γ : ι → ℝ → Y,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧
        (∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ L (ψ i) j ∧
          ∀ t : Icc (-(L (ψ i) j)) (L (ψ i) j), |t.val| ≤ S →
            ∀ ht : dist (q i j t) (o (ψ i)) ≤ R i,
              dist ((f i).toFun ⟨q i j t, ht⟩) (γ j t.val) < ζ) ∧
        (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, ∀ x : BallCarrier (o (ψ i)) (R i), dist x.val (o (ψ i)) ≤ S →
            |dist (o (ψ i)) (aPlus (ψ i) j) - dist x.val (aPlus (ψ i) j) -
              lineCoordinate (γ j) ((f i).toFun x)| < ζ) ∧
        ∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-lineCoordinate (γ j) x)) := by
  obtain ⟨ψ, R, ε, hψ, hψconv, hR, hε, f, σ, hσLip, hσbase, hσcal, γ, hγ, hγ0, hconv⟩ :=
    h.exists_calibrated_lines_of_opposite_endpoints hcurves aPlus aMinus hLpos hL hp hm hE hηpos hη
  refine ⟨ψ, R, ε, hψ, hψconv, hR, hε, f, σ, hσLip, hσbase, hσcal, γ, hγ, hγ0, hconv, ?_, ?_⟩
  · intro S hS ζ hζ
    have hj (j : ι) : ∀ᶠ i in atTop,
        S ≤ R i ∧ ∀ x : BallCarrier (o (ψ i)) (R i), dist x.val (o (ψ i)) ≤ S →
          |dist (o (ψ i)) (aPlus (ψ i) j) - dist x.val (aPlus (ψ i) j) -
            lineCoordinate (γ j) ((f i).toFun x)| < ζ := by
      have hEnonneg (i : ℕ) : 0 ≤ 2 * L (ψ i) j - dist (aPlus (ψ i) j) (aMinus (ψ i) j) := by
        have ht := dist_triangle (aPlus (ψ i) j) (o (ψ i)) (aMinus (ψ i) j)
        rw [dist_comm (aPlus (ψ i) j) (o (ψ i)), hp, hm] at ht
        linarith
      apply eventually_distance_coordinate_error_lt_of_converging_prefixes
        (lineSplitting hs (hγ j) hsegments) (lineSplitting_apply_line hs (hγ j) hsegments)
        (hγ0 j) f hR hε (fun i => aPlus (ψ i) j) (fun i => hp (ψ i) j)
        (fun i => (hLpos (ψ i) j).le)
        (E := fun i => 2 * L (ψ i) j - dist (aPlus (ψ i) j) (aMinus (ψ i) j))
        (η := fun i => η (ψ i))
        hEnonneg ((hE j).comp hψ.tendsto_atTop) (hη.comp hψ.tendsto_atTop)
        (fun i => σ i j) (fun i => hσLip i j) (fun i => hσbase i j)
        (fun i t => ⟨(hσcal i j t).1, (hσcal i j t).2.2.2⟩) ?_ S hS ζ hζ
      intro T δ hδ
      filter_upwards [hconv T δ hδ] with i hi
      exact ⟨hi.1, (hi.2 j).1, (hi.2 j).2⟩
    filter_upwards [hR.eventually (eventually_ge_atTop S), eventually_all.mpr hj] with i hi hjall
    exact ⟨hi, fun j => (hjall j).2⟩
  · intro j x
    exact tendsto_dist_line_sub_lineCoordinate hs (hγ j) hsegments x

end GC.MetricGeometry
