import DifferentialGeometry.Geometry.Metric.Approximation.FullProductLimit

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

universe u v w z v' w'
variable {T : ℕ → Type u} {E : Type v} {Z : ℕ → Type w} {Y : Type z}
variable {F : Type v'} {U : ℕ → Type w'}
variable [∀ i, MetricSpace (T i)] [MetricSpace E] [∀ i, MetricSpace (Z i)]
variable [MetricSpace F] [∀ i, MetricSpace (U i)]
variable [MetricSpace Y] [ProperSpace E] [ProperSpace F] [ProperSpace Y]
variable {o : ∀ i, T i} {a : E} {c : F} {q : Y} {b : ∀ i, Z i} {d : ∀ i, U i}
variable {δ ν R ε : ℕ → ℝ}


theorem exists_two_full_product_limits_of_approximate_products_with_given_maps
    (f : ∀ i, PointedBallApprox (o i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
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
            ∃ P τ Q η : ℕ → ℝ,
              Tendsto P atTop atTop ∧ Tendsto τ atTop (𝓝 0) ∧
              Tendsto Q atTop atTop ∧ Tendsto η atTop (𝓝 0) ∧
              ∃ (g : ∀ i, PointedBallApprox (b (χ i)) w (P i) (τ i))
                (h : ∀ i, PointedBallApprox (d (χ i)) v (Q i) (η i)),
                ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
                  S ≤ R (χ i) ∧
                  ∀ x : BallCarrier (o (χ i)) (R (χ i)), dist x.val (o (χ i)) ≤ S →
                    (dist ((Φ (χ i)).toFun x.val).snd (b (χ i)) ≤ P i ∧
                      ∀ hx : dist ((Φ (χ i)).toFun x.val).snd (b (χ i)) ≤ P i,
                        dist (WithLp.toLp 2 (((Φ (χ i)).toFun x.val).fst,
                          (g i).toFun ⟨((Φ (χ i)).toFun x.val).snd, hx⟩))
                          (eA ((f (χ i)).toFun x)) < ζ) ∧
                    (dist ((Ψ (χ i)).toFun x.val).snd (d (χ i)) ≤ Q i ∧
                      ∀ hx : dist ((Ψ (χ i)).toFun x.val).snd (d (χ i)) ≤ Q i,
                        dist (WithLp.toLp 2 (((Ψ (χ i)).toFun x.val).fst,
                          (h i).toFun ⟨((Ψ (χ i)).toFun x.val).snd, hx⟩))
                          (eB ((f (χ i)).toFun x)) < ζ) := by
  obtain ⟨W, mW, w, α, hα, hpW, hcW, hb, _, eA, heA,
    P, τ, hP, hτ, g, hcontrolA⟩ :=
    exists_full_product_limit_of_approximate_products_with_given_maps f hR hε Φ hδ
  let := mW
  let := hpW
  let := hcW
  obtain ⟨V, mV, v, β, hβ, hpV, hcV, hd, ho, eB, heB,
    Q, η, hQ, hη, h, hcontrolB⟩ :=
    exists_full_product_limit_of_approximate_products_with_given_maps
      (fun i => f (α i)) (hR.comp hα.tendsto_atTop) (hε.comp hα.tendsto_atTop)
      (fun i => Ψ (α i)) (hν.comp hα.tendsto_atTop)
  let := mV
  let := hpV
  let := hcV
  refine ⟨W, mW, V, mV, w, v, (fun i => α (β i)), hα.comp hβ,
    hpW, hcW, hpV, hcV, hb.subsequence hβ, hd, ho, eA, eB, heA, heB,
    (fun i => P (β i)), (fun i => τ (β i)), Q, η,
    hP.comp hβ.tendsto_atTop, hτ.comp hβ.tendsto_atTop, hQ, hη,
    (fun i => g (β i)), h, ?_⟩
  intro S ζ hζ
  filter_upwards [hβ.tendsto_atTop.eventually (hcontrolA S ζ hζ),
    hcontrolB S ζ hζ] with i hiA hiB
  exact ⟨hiA.1, fun x hx => ⟨hiA.2 x hx, hiB.2 x hx⟩⟩

end GC.MetricGeometry
