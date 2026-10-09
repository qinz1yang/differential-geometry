import DifferentialGeometry.Geometry.Comparison.FactorGeometry
import DifferentialGeometry.Geometry.Metric.EuclideanFactorCovering
import DifferentialGeometry.Topology.MetricSpace.GeodesicDimension

set_option autoImplicit false

open Set MeasureTheory

namespace IsometryEquiv

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem dimH_real_factor_le {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃ᵢ WithLp 2 (ℝ × Y)) (p : X) (q : Y)
    (hp : e p = WithLp.toLp 2 (0, q))
    (hnets : ∀ S : ℝ, 0 < S → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ F : Finset X,
        (F.card : ℝ) ≤ C * ε ^ (-(n : ℝ)) ∧
        (∀ x ∈ F, dist x p ≤ S) ∧
        ∀ x : X, dist x p ≤ S → ∃ y ∈ F, dist x y ≤ ε) :
    dimH (univ : Set Y) ≤ ENNReal.ofReal ((n - 1 : ℕ) : ℝ) := by
  let v : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toIsometryEquiv
  let e' := e.trans (IsometryEquiv.withLpProdCongr 2 v (IsometryEquiv.refl Y))
  have hp' : e' p = WithLp.toLp 2 (0, q) := by
    change WithLp.toLp 2 (v (e p).fst, (e p).snd) = _
    rw [hp]
    have hv : v 0 = 0 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.map_zero
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, hv]
  exact e'.dimH_euclidean_factor_le hn p q hp' hnets

theorem subsingleton_euclidean_factor_of_polynomial_nets {k : ℕ}
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Y))
    (p : X) (q : Y) (hp : e p = WithLp.toLp 2 (0, q))
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (hnets : ∀ S : ℝ, 0 < S → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ F : Finset X,
        (F.card : ℝ) ≤ C * ε ^ (-(k : ℝ)) ∧
        (∀ x ∈ F, dist x p ≤ S) ∧
        ∀ x : X, dist x p ≤ S → ∃ y ∈ F, dist x y ≤ ε) : Subsingleton Y := by
  apply Metric.subsingleton_of_dimH_lt_one (e.exists_segment_l2_product_factor 0 hsegments)
  have hdim := e.dimH_euclidean_factor_le (le_refl k) p q hp hnets
  simpa only [Nat.sub_self, Nat.cast_zero, ENNReal.ofReal_zero] using
    hdim.trans_lt (by simp : ENNReal.ofReal ((k - k : ℕ) : ℝ) < 1)

theorem exists_pointed_isometryEquiv_euclidean_of_splitting {k : ℕ}
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Y))
    (p : X) (q : Y) (hp : e p = WithLp.toLp 2 (0, q))
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (hnets : ∀ S : ℝ, 0 < S → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ F : Finset X,
        (F.card : ℝ) ≤ C * ε ^ (-(k : ℝ)) ∧
        (∀ x ∈ F, dist x p ≤ S) ∧
        ∀ x : X, dist x p ≤ S → ∃ y ∈ F, dist x y ≤ ε) :
    ∃ f : X ≃ᵢ EuclideanSpace ℝ (Fin k), f p = 0 := by
  let := e.subsingleton_euclidean_factor_of_polynomial_nets p q hp hsegments hnets
  let : Unique Y := ⟨⟨q⟩, fun y => Subsingleton.elim y q⟩
  refine ⟨e.trans (IsometryEquiv.withLpProdUnique 2 (EuclideanSpace ℝ (Fin k)) Y), ?_⟩
  change (e p).fst = 0
  rw [hp]
  rfl

end IsometryEquiv
