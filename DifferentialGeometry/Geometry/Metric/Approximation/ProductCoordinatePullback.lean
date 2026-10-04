import DifferentialGeometry.Geometry.Metric.Approximation.FullProductLimit
import DifferentialGeometry.Geometry.Metric.Approximation.CoordinatePullback

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

universe u v w z

variable {T : ℕ → Type u} {E : Type v} {Z : ℕ → Type w} {Y : Type z}
variable [∀ i, MetricSpace (T i)] [MetricSpace E] [∀ i, MetricSpace (Z i)]
variable [MetricSpace Y] [ProperSpace E] [ProperSpace Y]
variable {o : ∀ i, T i} {a : E} {q : Y} {b : ∀ i, Z i} {δ R ε : ℕ → ℝ}

theorem exists_product_limit_with_coordinate_pullback
    (f : ∀ i, PointedBallApprox (o i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (Φ : ∀ i, KleinerLottApprox (o i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0))
    (j : ∀ i, Y → T i)
    (hdom : ∀ K : Set Y, Bornology.IsBounded K →
      ∀ᶠ i in atTop, ∀ x ∈ K, dist (j i x) (o i) ≤ R i)
    (hround : ∀ K : Set Y, Bornology.IsBounded K →
      TendstoUniformlyOn (fun i x => (f i).extendToWholeSpace (j i x)) id atTop K) :
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (χ : ℕ → ℕ), StrictMono χ ∧ ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => b (χ i)) w ∧
        PointedGHConverges (fun i => o (χ i)) q ∧
        ∃ e : Y ≃ᵢ WithLp 2 (E × W), e q = WithLp.toLp 2 (a, w) ∧
          (∀ K : Set Y, Bornology.IsBounded K →
            TendstoUniformlyOn (fun i x => ((Φ (χ i)).toFun (j (χ i) x)).fst)
              (fun x => (e x).fst) atTop K) ∧
          ∃ P τ : ℕ → ℝ, Tendsto P atTop atTop ∧ Tendsto τ atTop (𝓝 0) ∧
            ∃ g : ∀ i, PointedBallApprox (b (χ i)) w (P i) (τ i),
              ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
                S ≤ R (χ i) ∧
                ∀ x : BallCarrier (o (χ i)) (R (χ i)), dist x.val (o (χ i)) ≤ S →
                  (dist ((Φ (χ i)).toFun x.val).snd (b (χ i)) ≤ P i ∧
                  ∀ hx : dist ((Φ (χ i)).toFun x.val).snd (b (χ i)) ≤ P i,
                    dist (WithLp.toLp 2 (((Φ (χ i)).toFun x.val).fst,
                      (g i).toFun ⟨((Φ (χ i)).toFun x.val).snd, hx⟩))
                      (e ((f (χ i)).toFun x)) < ζ) := by
  obtain ⟨W, m, w, χ, hχ, hp, hc, hz, ho, e, he, P, τ, hP, hτ, g, hcontrol⟩ :=
    exists_full_product_limit_of_approximate_products_with_given_maps f hR hε Φ hδ
  let := m
  refine ⟨W, m, w, χ, hχ, hp, hc, hz, ho, e, he, ?_, P, τ, hP, hτ, g, hcontrol⟩
  intro K hK
  have hdom' : ∀ᶠ i in atTop, ∀ x ∈ K, dist (j (χ i) x) (o (χ i)) ≤ R (χ i) :=
    hχ.tendsto_atTop.eventually (hdom K hK)
  have hround' : TendstoUniformlyOn
      (fun i x => (f (χ i)).extendToWholeSpace (j (χ i) x)) id atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    exact hχ.tendsto_atTop.eventually
      (Metric.tendstoUniformlyOn_iff.mp (hround K hK) η hη)
  have ht : LipschitzWith 1 (fun x : Y => (e x).fst) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, e.dist_eq] using
      (WithLp.dist_fst_le (e x) (e y))
  apply tendstoUniformlyOn_coordinate_pullback (u := fun i x => ((Φ (χ i)).toFun x).fst)
    (fun i => f (χ i))
    (hε.comp hχ.tendsto_atTop) hK hdom' hround' ht.uniformContinuous
  intro S η hη
  filter_upwards [hcontrol S η hη] with i hi x hx
  obtain ⟨hxg, hdist⟩ := hi.2 x hx
  exact (WithLp.dist_fst_le
    (WithLp.toLp 2 (((Φ (χ i)).toFun x.val).fst,
      (g i).toFun ⟨((Φ (χ i)).toFun x.val).snd, hxg⟩))
    (e ((f (χ i)).toFun x))).trans (hdist hxg).le

end GC.MetricGeometry
