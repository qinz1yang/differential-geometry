import DifferentialGeometry.Geometry.Metric.EuclideanCone
import DifferentialGeometry.Geometry.Metric.ConeDirectionControl
import DifferentialGeometry.Analysis.InnerProductSpace.SeparatedGrid
import DifferentialGeometry.Topology.MetricSpace.FiniteNets
import DifferentialGeometry.Topology.MetricSpace.PolynomialCovering

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace Metric.EuclideanCone

theorem exists_finset_net_base_of_polynomial_covering
    {Y : Type*} [MetricSpace Y] (hdiam : ∀ y z : Y, dist y z ≤ Real.pi)
    {n : ℕ} (hn : 1 ≤ n) {C δ : ℝ} (hC : 0 < C)
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hnets : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ S : Finset (EuclideanCone Y),
      (S.card : ℝ) ≤ C * ε ^ (-(n : ℝ)) ∧
      ∀ x : EuclideanCone Y, dist x tip ≤ 5 → ∃ y ∈ S, dist x y ≤ ε) :
    ∃ F : Finset Y, (F.card : ℝ) ≤ 3 ^ n * C * δ ^ (-((n - 1 : ℕ) : ℝ)) ∧
      ∀ y : Y, ∃ z ∈ F, dist y z < δ := by
  classical
  let K : ℝ := 3 ^ n * C * δ ^ (-((n - 1 : ℕ) : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨G, hGcard, hGnorm, hGsep⟩ := EuclideanSpace.exists_separated_grid 1 hδ
  have hGcoord (v : G) : |(v : EuclideanSpace ℝ (Fin 1)) 0| ≤ 1 := by
    have h := (PiLp.norm_apply_le (v : EuclideanSpace ℝ (Fin 1)) 0).trans
      (hGnorm v v.property)
    simpa only [Real.norm_eq_abs, Nat.cast_one, Real.sqrt_one] using h
  let r (v : G) : ℝ≥0 := ⟨3 + (v : EuclideanSpace ℝ (Fin 1)) 0, by
    have h := (abs_le.mp (hGcoord v)).1
    linarith⟩
  have hr (v : G) : 2 ≤ (r v : ℝ) ∧ (r v : ℝ) ≤ 4 := by
    have h := abs_le.mp (hGcoord v)
    change 2 ≤ 3 + (v : EuclideanSpace ℝ (Fin 1)) 0 ∧
      3 + (v : EuclideanSpace ℝ (Fin 1)) 0 ≤ 4
    constructor <;> linarith
  let emb : G × Y → EuclideanCone Y := fun a => mk (r a.1) a.2
  have hemb : Function.Injective emb := by
    rintro ⟨v, y⟩ ⟨w, z⟩ heq
    have he : (r v : ℝ) = r w := by
      simpa only [emb, radius_mk] using congrArg radius heq
    have hvw : v = w := by
      apply Subtype.ext
      apply PiLp.ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change 3 + (v : EuclideanSpace ℝ (Fin 1)) 0 =
        3 + (w : EuclideanSpace ℝ (Fin 1)) 0 at he
      linarith
    subst w
    have hp : 0 < (r v : ℝ) := by linarith [(hr v).1]
    have hyz : y = z := by
      change mk (r v) y = mk (r v) z at heq
      rw [mk_pos hp, mk_pos hp] at heq
      exact congrArg Prod.snd (Option.some.inj heq)
    exact Prod.ext rfl hyz
  obtain ⟨S, hScard, hSnet⟩ := hnets (δ / 3) (by positivity) (by linarith)
  have hpack (F : Finset Y)
      (hsep : (F : Set Y).Pairwise (fun a b => δ ≤ dist a b)) : (F.card : ℝ) ≤ K := by
    let A := ((Finset.univ : Finset G).product F).image emb
    have hAcard : A.card = G.card * F.card := by
      rw [Finset.card_image_of_injective _ hemb]
      exact (Finset.card_product (Finset.univ : Finset G) F).trans (by simp)
    have hAsep : (A : Set (EuclideanCone Y)).Pairwise (fun a b => δ ≤ dist a b) := by
      intro a ha b hb hab
      obtain ⟨⟨v, y⟩, hva, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨⟨w, z⟩, hwb, rfl⟩ := Finset.mem_image.mp hb
      have hy : y ∈ F := (Finset.mem_product.mp hva).2
      have hz : z ∈ F := (Finset.mem_product.mp hwb).2
      by_cases hvw : v = w
      · subst w
        have hyz : y ≠ z := fun he => hab (by rw [he])
        have hangle := two_mul_radius_mul_min_dist_le_pi_mul_coneDistance
          (x := ((r v : ℝ), y)) (y := ((r v : ℝ), z))
          (by norm_num : (0 : ℝ) ≤ 2) (hr v).1 (hr v).1
        rw [min_eq_right (hdiam y z), ← dist_mk] at hangle
        have hpi := mul_le_mul_of_nonneg_right Real.pi_le_four
          (dist_nonneg (x := mk (r v) y) (y := mk (r v) z))
        change δ ≤ dist (mk (r v) y) (mk (r v) z)
        nlinarith [hsep hy hz hyz]
      · have hvw' : (v : EuclideanSpace ℝ (Fin 1)) ≠ w :=
          fun he => hvw (Subtype.ext he)
        have hvgap := hGsep v.property w.property hvw'
        change δ ≤ dist (v : EuclideanSpace ℝ (Fin 1)) w at hvgap
        have hdist : dist (v : EuclideanSpace ℝ (Fin 1)) w =
            |(v : EuclideanSpace ℝ (Fin 1)) 0 - (w : EuclideanSpace ℝ (Fin 1)) 0| := by
          rw [EuclideanSpace.dist_eq]
          simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
        have hrad := abs_radius_sub_le_dist (emb (v, y)) (emb (w, z))
        change |radius (mk (r v) y) - radius (mk (r w) z)| ≤
          dist (emb (v, y)) (emb (w, z)) at hrad
        rw [radius_mk, radius_mk] at hrad
        change |(3 + (v : EuclideanSpace ℝ (Fin 1)) 0) -
          (3 + (w : EuclideanSpace ℝ (Fin 1)) 0)| ≤
          dist (emb (v, y)) (emb (w, z)) at hrad
        rw [hdist] at hvgap
        have hrad' : |(v : EuclideanSpace ℝ (Fin 1)) 0 -
            (w : EuclideanSpace ℝ (Fin 1)) 0| ≤ dist (emb (v, y)) (emb (w, z)) := by
          simpa only [add_sub_add_left_eq_sub] using hrad
        exact hvgap.trans hrad'
    have hAnet : ∀ a ∈ A, ∃ s ∈ S, dist a s ≤ δ / 3 := by
      intro a ha
      obtain ⟨⟨v, y⟩, _, rfl⟩ := Finset.mem_image.mp ha
      apply hSnet
      simpa only [emb, dist_tip, radius_mk] using (hr v).2.trans (by norm_num : (4 : ℝ) ≤ 5)
    have hcount := card_le_card_of_separated_net A S (by linarith : 2 * (δ / 3) < δ)
      hAsep hAnet
    rw [hAcard] at hcount
    have hcountR : (G.card : ℝ) * F.card ≤ S.card := by exact_mod_cast hcount
    have hmult := mul_le_mul_of_nonneg_right hGcard (Nat.cast_nonneg (α := ℝ) F.card)
    have hbound : δ⁻¹ * F.card ≤ C * (δ / 3) ^ (-(n : ℝ)) := by
      simpa only [pow_one] using hmult.trans (hcountR.trans hScard)
    calc
      (F.card : ℝ) ≤ (C * (δ / 3) ^ (-(n : ℝ))) / δ⁻¹ :=
        (le_div_iff₀ (inv_pos.mpr hδ)).mpr (by simpa only [mul_comm] using hbound)
      _ = K := by
        dsimp [K]
        rw [Real.rpow_neg (by positivity : 0 ≤ δ / 3), Real.rpow_natCast,
          Real.rpow_neg hδ.le, Real.rpow_natCast, div_pow]
        have hpow : δ ^ n = δ * δ ^ (n - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hn]
        rw [hpow]
        field_simp
  obtain ⟨F, hcard, _, hcover⟩ := exists_finset_net_card_le_of_packing
    (s := (univ : Set Y)) hδ ⌊K⌋₊
    (fun F _ hsep => Nat.le_floor (hpack F hsep))
  exact ⟨F, (show (F.card : ℝ) ≤ ⌊K⌋₊ by exact_mod_cast hcard).trans (Nat.floor_le hK),
    fun y => hcover y (mem_univ _)⟩

theorem dimH_base_le_of_polynomial_covering
    {Y : Type*} [MetricSpace Y] (hdiam : ∀ y z : Y, dist y z ≤ Real.pi)
    {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hC : 0 < C)
    (hnets : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ S : Finset (EuclideanCone Y),
      (S.card : ℝ) ≤ C * ε ^ (-(n : ℝ)) ∧
      ∀ x : EuclideanCone Y, dist x tip ≤ 5 → ∃ y ∈ S, dist x y ≤ ε) :
    dimH (univ : Set Y) ≤ ENNReal.ofReal ((n - 1 : ℕ) : ℝ) := by
  apply dimH_univ_le_of_polynomial_nets (C := 3 ^ n * C) (by positivity) (by positivity)
  intro δ hδ hδone
  obtain ⟨F, hcard, hnet⟩ :=
    exists_finset_net_base_of_polynomial_covering hdiam hn hC hδ hδone hnets
  exact ⟨F, hcard, fun y => by
    obtain ⟨z, hz, hd⟩ := hnet y
    exact ⟨z, hz, hd.le⟩⟩

end Metric.EuclideanCone
