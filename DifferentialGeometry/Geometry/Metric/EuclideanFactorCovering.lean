import DifferentialGeometry.Geometry.Metric.L2Product
import DifferentialGeometry.Analysis.InnerProductSpace.SeparatedGrid
import DifferentialGeometry.Topology.MetricSpace.FiniteNets
import DifferentialGeometry.Topology.MetricSpace.PolynomialCovering
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Set Metric MeasureTheory

namespace IsometryEquiv

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem exists_finset_net_euclidean_factor {k n : ℕ} (hkn : k ≤ n)
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Y))
    (p : X) (q : Y) (hp : e p = WithLp.toLp 2 (0, q))
    {R δ C : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hC : 0 < C)
    (hnets : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ S : Finset X,
      (S.card : ℝ) ≤ C * ε ^ (-(n : ℝ)) ∧
      (∀ x ∈ S, dist x p ≤ R + Real.sqrt k + 1) ∧
      ∀ x : X, dist x p ≤ R + Real.sqrt k + 1 → ∃ y ∈ S, dist x y ≤ ε) :
    ∃ F : Finset Y, (F.card : ℝ) ≤ 3 ^ n * C * δ ^ (-((n - k : ℕ) : ℝ)) ∧
      (∀ y ∈ F, dist y q ≤ R) ∧
      ∀ y : Y, dist y q ≤ R → ∃ z ∈ F, dist y z < δ := by
  classical
  let K := (3 : ℝ) ^ n * C * δ ^ (-((n - k : ℕ) : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨G, hGcard, hGnorm, hGsep⟩ := EuclideanSpace.exists_separated_grid k hδ
  obtain ⟨S, hScard, _, hSnet⟩ := hnets (δ / 3) (by positivity) (by linarith)
  let emb : EuclideanSpace ℝ (Fin k) × Y → X := fun a => e.symm (WithLp.toLp 2 a)
  have hemb : Function.Injective emb :=
    e.symm.injective.comp (WithLp.equiv 2 _).symm.injective
  have hbase : emb (0, q) = p := by
    apply e.injective
    simpa only [emb, apply_symm_apply] using hp.symm
  have hpack (F : Finset Y) (hF : (F : Set Y) ⊆ closedBall q R)
      (hsep : (F : Set Y).Pairwise (fun a b => δ ≤ dist a b)) : (F.card : ℝ) ≤ K := by
    let A := (G.product F).image emb
    have hAcard : A.card = G.card * F.card := by
      rw [Finset.card_image_of_injective _ hemb]
      exact Finset.card_product G F
    have hAsep : (A : Set X).Pairwise (fun a b => δ ≤ dist a b) := by
      intro a ha b hb hab
      obtain ⟨⟨v, y⟩, hva, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨⟨w, z⟩, hwb, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hv, hy⟩ := Finset.mem_product.mp hva
      obtain ⟨hw, hz⟩ := Finset.mem_product.mp hwb
      change δ ≤ dist (e.symm (WithLp.toLp 2 (v, y))) (e.symm (WithLp.toLp 2 (w, z)))
      rw [e.symm.dist_eq]
      by_cases hvw : v = w
      · subst w
        have hyz : y ≠ z := fun hh => hab (by rw [hh])
        exact (hsep hy hz hyz).trans (WithLp.dist_snd_le _ _)
      · exact (hGsep hv hw hvw).trans (WithLp.dist_fst_le _ _)
    have hAnet : ∀ a ∈ A, ∃ s ∈ S, dist a s ≤ δ / 3 := by
      intro a ha
      obtain ⟨⟨v, y⟩, hva, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hv, hy⟩ := Finset.mem_product.mp hva
      apply hSnet
      rw [← hbase]
      change dist (e.symm (WithLp.toLp 2 (v, y)))
        (e.symm (WithLp.toLp 2 (0, q))) ≤ _
      rw [e.symm.dist_eq]
      have ht := dist_triangle (WithLp.toLp 2 (v, y)) (WithLp.toLp 2 (0, y))
        (WithLp.toLp 2 (0, q))
      rw [(WithLp.isometry_prodMk_right y).dist_eq v 0,
        (WithLp.isometry_prodMk_left (0 : EuclideanSpace ℝ (Fin k))).dist_eq y q,
        dist_zero_right] at ht
      have hyr : dist y q ≤ R := hF hy
      linarith [hGnorm v hv]
    have hcount := Metric.card_le_card_of_separated_net A S (by linarith : 2 * (δ / 3) < δ)
      hAsep hAnet
    rw [hAcard] at hcount
    have hcountR : (G.card : ℝ) * F.card ≤ S.card := by exact_mod_cast hcount
    have hmult := mul_le_mul_of_nonneg_right hGcard (Nat.cast_nonneg (α := ℝ) F.card)
    have hbound : (δ⁻¹) ^ k * F.card ≤ C * (δ / 3) ^ (-(n : ℝ)) :=
      hmult.trans (hcountR.trans hScard)
    calc
      (F.card : ℝ) ≤ (C * (δ / 3) ^ (-(n : ℝ))) / ((δ⁻¹) ^ k) :=
        (le_div_iff₀ (pow_pos (inv_pos.mpr hδ) k)).mpr (by simpa only [mul_comm] using hbound)
      _ = K := by
        dsimp [K]
        rw [Real.rpow_neg (by positivity : 0 ≤ δ / 3), Real.rpow_natCast,
          Real.rpow_neg hδ.le, Real.rpow_natCast, div_pow, inv_pow]
        have hpow : δ ^ n = δ ^ k * δ ^ (n - k) := by rw [← pow_add, Nat.add_sub_of_le hkn]
        rw [hpow]
        field_simp
  have hpackNat (F : Finset Y) (hF : (F : Set Y) ⊆ closedBall q R)
      (hsep : (F : Set Y).Pairwise (fun a b => δ ≤ dist a b)) : F.card ≤ ⌊K⌋₊ :=
    Nat.le_floor (hpack F hF hsep)
  obtain ⟨F, hcard, hinside, hcover⟩ :=
    Metric.exists_finset_net_card_le_of_packing hδ ⌊K⌋₊ hpackNat
  refine ⟨F, (show (F.card : ℝ) ≤ ⌊K⌋₊ by exact_mod_cast hcard).trans (Nat.floor_le hK),
    fun y hy => hinside hy, hcover⟩

theorem dimH_euclidean_factor_le {k n : ℕ} (hkn : k ≤ n)
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Y))
    (p : X) (q : Y) (hp : e p = WithLp.toLp 2 (0, q))
    (hnets : ∀ S : ℝ, 0 < S → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ F : Finset X,
        (F.card : ℝ) ≤ C * ε ^ (-(n : ℝ)) ∧
        (∀ x ∈ F, dist x p ≤ S) ∧
        ∀ x : X, dist x p ≤ S → ∃ y ∈ F, dist x y ≤ ε) :
    dimH (univ : Set Y) ≤ ENNReal.ofReal ((n - k : ℕ) : ℝ) := by
  have hunion : (⋃ j : ℕ, closedBall q ((j : ℝ) + 1)) = (univ : Set Y) := by
    ext y
    simp only [mem_iUnion, mem_closedBall, mem_univ, iff_true]
    obtain ⟨j, hj⟩ := exists_nat_gt (dist y q)
    exact ⟨j, by linarith⟩
  rw [← hunion]
  apply dimH_iUnion_le_of_polynomial_nets _ (by positivity)
  intro j
  obtain ⟨C, hC, hn⟩ := hnets ((j : ℝ) + 1 + Real.sqrt k + 1) (by positivity)
  refine ⟨3 ^ n * C, by positivity, ?_⟩
  intro δ hδ hδone
  obtain ⟨F, hcard, hinside, hcover⟩ := e.exists_finset_net_euclidean_factor hkn p q hp
    (R := (j : ℝ) + 1) hδ hδone hC hn
  exact ⟨F, hinside, hcard, fun y hy => by
    obtain ⟨z, hz, hd⟩ := hcover y hy
    exact ⟨z, hz, hd.le⟩⟩

end IsometryEquiv
