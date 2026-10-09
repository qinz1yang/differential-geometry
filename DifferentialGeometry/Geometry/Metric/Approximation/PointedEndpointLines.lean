import DifferentialGeometry.Geometry.Metric.Approximation.OppositeEndpointLines
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y] [ProperSpace Y] [Finite ι]
variable {o : ∀ i, A i} {p : Y} {L : ℕ → ι → ℝ} {η : ℕ → ℝ}

theorem PointedGHConverges.exists_calibrated_lines_of_opposite_endpoints
    (h : PointedGHConverges o p)
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
      ∃ σ : ∀ i j, Icc (-(L (ψ i) j)) (L (ψ i) j) → A (ψ i),
      (∀ i j, LipschitzWith 1 (σ i j)) ∧
      (∀ i j, σ i j ⟨0, ⟨by linarith [hLpos (ψ i) j], (hLpos (ψ i) j).le⟩⟩ = o (ψ i)) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (L (ψ i) j),
        t.val - η (ψ i) ≤ L (ψ i) j - dist (σ i j ⟨t.val, ⟨by linarith [t.property.1, hLpos (ψ i) j], t.property.2⟩⟩) (aPlus (ψ i) j) ∧
        L (ψ i) j - dist (σ i j ⟨t.val, ⟨by linarith [t.property.1, hLpos (ψ i) j], t.property.2⟩⟩) (aPlus (ψ i) j) ≤ t.val ∧
        -t.val ≤ L (ψ i) j - dist (σ i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos (ψ i) j]⟩⟩) (aPlus (ψ i) j) ∧
        L (ψ i) j - dist (σ i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos (ψ i) j]⟩⟩) (aPlus (ψ i) j) ≤
          -t.val + (2 * L (ψ i) j - dist (aPlus (ψ i) j) (aMinus (ψ i) j)) + η (ψ i)) ∧
      ∃ γ : ι → ℝ → Y,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧
        ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ L (ψ i) j ∧
          ∀ t : Icc (-(L (ψ i) j)) (L (ψ i) j), |t.val| ≤ S →
            ∀ ht : dist (σ i j t) (o (ψ i)) ≤ R i,
              dist ((f i).toFun ⟨σ i j t, ht⟩) (γ j t.val) < ζ := by
  classical
  let r : ℕ → ℝ := fun i => (i : ℝ) + 1
  let e : ℕ → ℝ := fun i => (1 / ((i : ℝ) + 1)) / 100
  have hr : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hepos (i : ℕ) : 0 < e i := by dsimp [e]; positivity
  have her (i : ℕ) : e i < r i := by
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp [e, r]
    linarith
  have hezero : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
  obtain ⟨β, hβ, hf⟩ := extraction_forall_of_eventually
    (fun i => h.eventually_approx (hepos i) (her i))
  let f (i : ℕ) : PointedBallApprox (o (β i)) p (r i) (e i) := Classical.choice (hf i)
  obtain ⟨σ, hσLip, hσbase, hσcal, γ, φ, hγ, hγ0, hφ, hcontrol⟩ :=
    GC.MetricGeometry.exists_calibrated_lines_of_opposite_endpoints f hr hezero (fun i => hcurves (β i))
      (fun i => aPlus (β i)) (fun i => aMinus (β i)) (fun i j => hLpos (β i) j)
      (fun j => (hL j).comp hβ.tendsto_atTop) (fun i j => hp (β i) j)
      (fun i j => hm (β i) j) (fun j => (hE j).comp hβ.tendsto_atTop)
      (fun i => hηpos (β i)) (hη.comp hβ.tendsto_atTop)
  let ψ : ℕ → ℕ := fun i => β (φ i)
  have hψ : StrictMono ψ := hβ.comp hφ
  refine ⟨ψ, (fun i => r (φ i)), (fun i => e (φ i)), hψ, h.subsequence hψ,
    hr.comp hφ.tendsto_atTop, hezero.comp hφ.tendsto_atTop, (fun i => f (φ i)),
    (fun i => σ (φ i)), (fun i j => hσLip (φ i) j), (fun i j => hσbase (φ i) j),
    (fun i j => hσcal (φ i) j), γ, hγ, hγ0, ?_⟩
  exact hcontrol

end GC.MetricGeometry
