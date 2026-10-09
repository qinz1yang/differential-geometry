import DifferentialGeometry.Geometry.Metric.Approximation.TwoFullProductLimits

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry.PointedGHConverges

universe u v w z v' w'
variable {T : ℕ → Type u} {E : Type v} {Z : ℕ → Type w} {Y : Type z}
variable {F : Type v'} {U : ℕ → Type w'}
variable [∀ i, MetricSpace (T i)] [MetricSpace E] [∀ i, MetricSpace (Z i)]
variable [MetricSpace F] [∀ i, MetricSpace (U i)]
variable [MetricSpace Y] [ProperSpace E] [ProperSpace F] [ProperSpace Y]
variable {o : ∀ i, T i} {a : E} {c : F} {q : Y} {b : ∀ i, Z i} {d : ∀ i, U i}
variable {δ ν : ℕ → ℝ}

theorem exists_two_full_product_limits
    (hpointed : PointedGHConverges o q)
    (Φ : ∀ i, KleinerLottApprox (o i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0))
    (Ψ : ∀ i, KleinerLottApprox (o i) (WithLp.toLp 2 (c, d i)) (ν i))
    (hν : Tendsto ν atTop (𝓝 0)) :
    ∃ (W : Type) (mW : MetricSpace W), letI := mW
      ∃ (V : Type) (mV : MetricSpace V), letI := mV
        ∃ (w : W) (v : V) (χ : ℕ → ℕ), StrictMono χ ∧
          ProperSpace W ∧ CompleteSpace W ∧ ProperSpace V ∧ CompleteSpace V ∧
          PointedGHConverges (fun i => b (χ i)) w ∧
          PointedGHConverges (fun i => d (χ i)) v ∧
          PointedGHConverges (fun i => o (χ i)) q ∧
          ∃ (eA : Y ≃ᵢ WithLp 2 (E × W)) (eB : Y ≃ᵢ WithLp 2 (F × V)),
            eA q = WithLp.toLp 2 (a, w) ∧ eB q = WithLp.toLp 2 (c, v) ∧
            ∃ R ε P τ Q η : ℕ → ℝ,
              Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
              Tendsto P atTop atTop ∧ Tendsto τ atTop (𝓝 0) ∧
              Tendsto Q atTop atTop ∧ Tendsto η atTop (𝓝 0) ∧
              ∃ (f : ∀ i, PointedBallApprox (o (χ i)) q (R i) (ε i))
                (g : ∀ i, PointedBallApprox (b (χ i)) w (P i) (τ i))
                (h : ∀ i, PointedBallApprox (d (χ i)) v (Q i) (η i)),
                ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
                  S ≤ R i ∧
                  ∀ x : BallCarrier (o (χ i)) (R i), dist x.val (o (χ i)) ≤ S →
                    (dist ((Φ (χ i)).toFun x.val).snd (b (χ i)) ≤ P i ∧
                      ∀ hx : dist ((Φ (χ i)).toFun x.val).snd (b (χ i)) ≤ P i,
                        dist (WithLp.toLp 2 (((Φ (χ i)).toFun x.val).fst,
                          (g i).toFun ⟨((Φ (χ i)).toFun x.val).snd, hx⟩))
                          (eA ((f i).toFun x)) < ζ) ∧
                    (dist ((Ψ (χ i)).toFun x.val).snd (d (χ i)) ≤ Q i ∧
                      ∀ hx : dist ((Ψ (χ i)).toFun x.val).snd (d (χ i)) ≤ Q i,
                        dist (WithLp.toLp 2 (((Ψ (χ i)).toFun x.val).fst,
                          (h i).toFun ⟨((Ψ (χ i)).toFun x.val).snd, hx⟩))
                          (eB ((f i).toFun x)) < ζ) := by
  classical
  let J : ℕ → ℝ := fun i => (i : ℝ) + 1
  let ε : ℕ → ℝ := fun i => (1 / ((i : ℝ) + 1)) / 100
  have hJone (i : ℕ) : 1 ≤ J i := by dsimp [J]; linarith [Nat.cast_nonneg (α := ℝ) i]
  have hJ : Tendsto J atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hεpos (i : ℕ) : 0 < ε i := by dsimp [ε]; positivity
  have hεJ (i : ℕ) : ε i < J i := by
    have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
    dsimp [ε]
    linarith [hJone i]
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
  obtain ⟨β, hβ, hmaps⟩ := extraction_forall_of_eventually
    (fun j => hpointed.eventually_approx (hεpos j) (hεJ j))
  let f (i : ℕ) : PointedBallApprox (o (β i)) q (J i) (ε i) := Classical.choice (hmaps i)
  obtain ⟨W, mW, V, mV, w, v, α, hα, hpW, hcW, hpV, hcV,
      hb, hd, ho, eA, eB, heA, heB, P, τ, Q, η, hP, hτ, hQ, hη, g, h, hcontrol⟩ :=
    exists_two_full_product_limits_of_approximate_products_with_given_maps f hJ hεzero
      (fun i => Φ (β i)) (hδ.comp hβ.tendsto_atTop)
      (fun i => Ψ (β i)) (hν.comp hβ.tendsto_atTop)
  let := mW
  let := mV
  refine ⟨W, mW, V, mV, w, v, (fun i => β (α i)), hβ.comp hα,
    hpW, hcW, hpV, hcV, hb, hd, ho, eA, eB, heA, heB,
    (fun i => J (α i)), (fun i => ε (α i)), P, τ, Q, η,
    hJ.comp hα.tendsto_atTop, hεzero.comp hα.tendsto_atTop,
    hP, hτ, hQ, hη, (fun i => f (α i)), g, h, hcontrol⟩

end GC.MetricGeometry.PointedGHConverges
