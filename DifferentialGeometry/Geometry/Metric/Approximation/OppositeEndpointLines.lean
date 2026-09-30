import DifferentialGeometry.Topology.MetricSpace.CalibratedSignedPrefix
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixLineLimit

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y] [ProperSpace Y] [Finite ι]
variable {o : ∀ i, A i} {p : Y} {L : ℕ → ι → ℝ} {R ε η : ℕ → ℝ}

theorem exists_calibrated_lines_of_opposite_endpoints
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hcurves : ∀ i, ∀ a b : A i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → A i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (aPlus aMinus : ∀ i, ι → A i)
    (hLpos : ∀ i j, 0 < L i j) (hL : ∀ j, Tendsto (fun i => L i j) atTop atTop)
    (hp : ∀ i j, dist (o i) (aPlus i j) = L i j)
    (hm : ∀ i j, dist (o i) (aMinus i j) = L i j)
    (hE : ∀ j, Tendsto (fun i => 2 * L i j - dist (aPlus i j) (aMinus i j)) atTop (𝓝 0))
    (hηpos : ∀ i, 0 < η i) (hη : Tendsto η atTop (𝓝 0)) :
    ∃ σ : ∀ i j, Icc (-(L i j)) (L i j) → A i,
      (∀ i j, LipschitzWith 1 (σ i j)) ∧
      (∀ i j, σ i j ⟨0, ⟨by linarith [hLpos i j], (hLpos i j).le⟩⟩ = o i) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (L i j),
        t.val - η i ≤ L i j - dist (σ i j ⟨t.val, ⟨by linarith [t.property.1, hLpos i j], t.property.2⟩⟩) (aPlus i j) ∧
        L i j - dist (σ i j ⟨t.val, ⟨by linarith [t.property.1, hLpos i j], t.property.2⟩⟩) (aPlus i j) ≤ t.val ∧
        -t.val ≤ L i j - dist (σ i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos i j]⟩⟩) (aPlus i j) ∧
        L i j - dist (σ i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos i j]⟩⟩) (aPlus i j) ≤
          -t.val + (2 * L i j - dist (aPlus i j) (aMinus i j)) + η i) ∧
      ∃ (γ : ι → ℝ → Y) (φ : ℕ → ℕ),
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧ StrictMono φ ∧
        ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R (φ i) ∧ ∀ j, S ≤ L (φ i) j ∧
          ∀ t : Icc (-(L (φ i) j)) (L (φ i) j), |t.val| ≤ S →
            ∀ ht : dist (σ (φ i) j t) (o (φ i)) ≤ R (φ i),
              dist ((f (φ i)).toFun ⟨σ (φ i) j t, ht⟩) (γ j t.val) < ζ := by
  classical
  choose σ hσLip hσbase hσlow hσrad hσcal using
    fun i j => exists_calibrated_signed_prefix (hcurves i) (o i) (aPlus i j) (aMinus i j)
      (hLpos i j) (hηpos i) (hp i j) (hm i j)
  have hδ (j : ι) : Tendsto
      (fun i => (2 * L i j - dist (aPlus i j) (aMinus i j)) + 2 * η i) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (hE j).add (hη.const_mul 2)
  obtain ⟨γ, φ, hγ, hγ0, hφ, hconv⟩ := exists_isometric_lines_of_signed_prefixes
    f hR hε (fun i j => (hLpos i j).le) hL hδ σ hσLip hσbase hσlow
  exact ⟨σ, hσLip, hσbase, hσcal, γ, φ, hγ, hγ0, hφ, hconv⟩

end GC.MetricGeometry
