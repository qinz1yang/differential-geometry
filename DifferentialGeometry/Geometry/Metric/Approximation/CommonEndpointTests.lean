import DifferentialGeometry.Analysis.InnerProductSpace.DirectionalSaturation
import DifferentialGeometry.Analysis.InnerProductSpace.AsymmetricTestSaturation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

/-!
# Common long endpoints give the directional tests (FC19)

Blueprint 207B, `lem:fibration-common-endpoints` (FC19, B:1293). The new content of FC19 is the
production of FC15's directional premise from explicit metric data: a product approximation
`φ = (u, z)` of `B(p,H)` with distortion `δ` and coverage of the target radius-`(H-δ)` ball to
error `δ`, and one constant coisometry `A` with `|Ψ − A u − b₀| ≤ E`. For every `x ∈ B(p,L)` and
component `a`, a lift `y` of `(u(x) + s A*eₐ, z(x))` is a COMMON long endpoint for both raw
coordinates; along every initial unit vector `w` of a minimizing segment from `x` to `y` the two
adapted tests then saturate `dFₐ` and `d(AG)ₐ`, so `‖dF − A dG‖ ≤ 2√(k(4ε+ε²))`,
`ε = α + (3δ + 2E)/(s − 2δ)`, at every point. The integration to the `C¹` bound on `B(p,L)` is
FC15 (lane X81).

Conventions: the product metric is the Euclidean `ℓ²` product (`WithLp 2`); "covers to error `δ`"
is read literally as "every target point has a preimage point whose image is within `δ`"; the set
`W x y` stands for the initial unit tangents of minimizing segments from `x` to `y` (nonempty
for `x ≠ y` in a complete connected Riemannian manifold).
-/

open Metric
open scoped InnerProductSpace

namespace GC.MetricGeometry

variable {k m : ℕ}

private theorem dist_toLp_same_snd {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (a b : α) (c : β) :
    dist (WithLp.toLp 2 (a, c) : WithLp 2 (α × β)) (WithLp.toLp 2 (b, c)) = dist a b := by
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  simp only [h2]
  change (dist a b ^ (2 : ℝ) + dist c c ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = dist a b
  rw [dist_self, Real.zero_rpow two_ne_zero, add_zero, ← Real.sqrt_eq_rpow, Real.rpow_two,
    Real.sqrt_sq dist_nonneg]

private theorem ratio_lower_bound {c ℓ s δ E : ℝ} (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hs : 2 * δ < s)
    (hℓ : s - 2 * δ ≤ ℓ) (hℓu : ℓ ≤ s + 2 * δ) (hc : s - δ - 2 * E ≤ c) :
    1 - (3 * δ + 2 * E) / (s - 2 * δ) ≤ c / ℓ := by
  have hs2 : 0 < s - 2 * δ := by linarith
  have hℓpos : 0 < ℓ := hs2.trans_le hℓ
  have h1 : -(3 * δ + 2 * E) / ℓ ≤ (c - ℓ) / ℓ :=
    div_le_div_of_nonneg_right (by linarith) hℓpos.le
  have h2 : (3 * δ + 2 * E) / ℓ ≤ (3 * δ + 2 * E) / (s - 2 * δ) :=
    div_le_div_of_nonneg_left (by positivity) hs2 hℓ
  have h3 : (c - ℓ) / ℓ = c / ℓ - 1 := by field_simp
  rw [neg_div] at h1
  linarith

/-- **FC19, metric step**: a common long endpoint for both raw coordinates. -/
theorem exists_common_long_endpoint {X Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Z]
    (u : X → EuclideanSpace ℝ (Fin m)) (z : X → Z) (Ψ : X → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (b₀ : EuclideanSpace ℝ (Fin k)) {p : X} {z₀ : Z} {L T s H δ E : ℝ} (hT : 0 ≤ T)
    (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hs : T + 2 * δ < s) (hH : L + s + 3 * δ < H)
    (hup : u p = 0) (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p H, ∀ y ∈ ball p H,
      |dist (WithLp.toLp 2 (u x, z x) : WithLp 2 (_ × Z)) (WithLp.toLp 2 (u y, z y)) -
        dist x y| ≤ δ)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin m) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < H - δ →
        ∃ y ∈ ball p H, dist (WithLp.toLp 2 (u y, z y)) q ≤ δ)
    (hΨ : ∀ x ∈ ball p H, ‖Ψ x - A (u x) - b₀‖ ≤ E) {x : X} (hx : x ∈ ball p L) (a : Fin k) :
    ∃ y ∈ ball p H, T < dist x y ∧ s - 2 * δ ≤ dist x y ∧ dist x y ≤ s + 2 * δ ∧
      1 - (3 * δ + 2 * E) / (s - 2 * δ) ≤ (Ψ y a - Ψ x a) / dist x y ∧
      1 - (3 * δ + 2 * E) / (s - 2 * δ) ≤ (A (u y - u x)) a / dist x y := by
  set φ : X → WithLp 2 (EuclideanSpace ℝ (Fin m) × Z) := fun x => WithLp.toLp 2 (u x, z x)
  set e : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single a 1
  set v : EuclideanSpace ℝ (Fin m) := ContinuousLinearMap.adjoint A e
  have hAv : A v = e := by
    have := congrArg (fun S : _ →L[ℝ] _ => S e) hA
    simpa using this
  have hv : ‖v‖ = 1 := by
    have h : ⟪v, v⟫_ℝ = ⟪e, e⟫_ℝ := by
      rw [show ⟪v, v⟫_ℝ = ⟪A v, e⟫_ℝ from ContinuousLinearMap.adjoint_inner_right A v e, hAv]
    have he1 : ‖e‖ = 1 := by simp [e]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he1] at h
    nlinarith [norm_nonneg v]
  have hAn : ‖A‖ ≤ 1 := by
    have hiso : ∀ y, ‖ContinuousLinearMap.adjoint A y‖ = ‖y‖ := fun y => by
      have h : ⟪ContinuousLinearMap.adjoint A y, ContinuousLinearMap.adjoint A y⟫_ℝ = ⟪y, y⟫_ℝ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
        have := congrArg (fun S : _ →L[ℝ] _ => S y) hA
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
        rw [this]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
    have hadj : ‖ContinuousLinearMap.adjoint A‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [hiso, one_mul]
    rwa [LinearIsometryEquiv.norm_map] at hadj
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin k)), |w a| ≤ ‖w‖ := fun w => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w a
  have hpH : p ∈ ball p H := mem_ball_self (by
    have := (dist_nonneg).trans_lt (mem_ball.mp hx); linarith)
  have hxH : x ∈ ball p H := by
    rw [mem_ball] at hx ⊢
    have := (dist_nonneg).trans_lt hx
    linarith
  -- the target point and its lift
  set q : WithLp 2 (EuclideanSpace ℝ (Fin m) × Z) := WithLp.toLp 2 (u x + s • v, z x)
  have hs0 : 0 ≤ s := by linarith
  have hφq : dist (φ x) q = s := by
    rw [dist_toLp_same_snd, dist_eq_norm, show u x - (u x + s • v) = -(s • v) by abel, norm_neg,
      norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg hs0, mul_one]
  have hφp : φ p = WithLp.toLp 2 (0, z₀) := by simp only [φ, hup, hzp]
  have hxp : dist (φ x) (φ p) ≤ dist x p + δ := by
    have := (abs_le.mp (hdist x hxH p hpH)).2; linarith
  have hq : dist q (WithLp.toLp 2 (0, z₀)) < H - δ := by
    rw [← hφp]
    have hxpL : dist x p < L := mem_ball.mp hx
    calc dist q (φ p) ≤ dist q (φ x) + dist (φ x) (φ p) := dist_triangle _ _ _
      _ < H - δ := by rw [dist_comm, hφq]; linarith
  obtain ⟨y, hyH, hyq⟩ := hcover q hq
  have hxy := abs_le.mp (hdist x hxH y hyH)
  have hφxy_lo : s - δ ≤ dist (φ x) (φ y) := by
    have := dist_triangle (φ x) (φ y) q
    rw [hφq, dist_comm (φ y) q] at this
    rw [dist_comm q (φ y)] at this
    linarith
  have hφxy_hi : dist (φ x) (φ y) ≤ s + δ := by
    have := dist_triangle (φ x) q (φ y)
    rw [hφq, dist_comm q (φ y)] at this
    linarith
  have hℓlo : s - 2 * δ ≤ dist x y := by linarith [hxy.2]
  have hℓhi : dist x y ≤ s + 2 * δ := by linarith [hxy.1]
  -- the gains
  have hfst : ‖u y - (u x + s • v)‖ ≤ δ := by
    have := WithLp.dist_fst_le (φ y) q
    rw [← dist_eq_norm]
    exact this.trans hyq
  have hgainA : s - δ ≤ (A (u y - u x)) a := by
    have hsplit : A (u y - u x) = s • e + A (u y - (u x + s • v)) := by
      rw [map_sub, map_sub, map_add, map_smul, hAv]; abel
    rw [hsplit, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have he : e a = 1 := by simp [e]
    rw [he, mul_one]
    have h1 := hcoord (A (u y - (u x + s • v)))
    have h2 : ‖A (u y - (u x + s • v))‖ ≤ δ :=
      (A.le_opNorm _).trans (by nlinarith [norm_nonneg (u y - (u x + s • v))])
    linarith [(abs_le.mp (h1.trans h2)).1]
  have hgainΨ : s - δ - 2 * E ≤ Ψ y a - Ψ x a := by
    have hya := (abs_le.mp ((hcoord _).trans (hΨ y hyH))).1
    have hxa := (abs_le.mp ((hcoord _).trans (hΨ x hxH))).2
    simp only [PiLp.sub_apply] at hya hxa
    have hAa : (A (u y - u x)) a = (A (u y)) a - (A (u x)) a := by
      rw [map_sub, PiLp.sub_apply]
    linarith
  refine ⟨y, hyH, by linarith, hℓlo, hℓhi, ?_, ?_⟩
  · exact ratio_lower_bound hδ hE (by linarith) hℓlo hℓhi hgainΨ
  · exact ratio_lower_bound hδ hE (by linarith) hℓlo hℓhi (by linarith)

private theorem norm_le_of_rows {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Y →L[ℝ] EuclideanSpace ℝ (Fin k)) {c : ℝ} (hc : 0 ≤ c)
    (hrow : ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp L‖ ≤ c) :
    ‖L‖ ≤ Real.sqrt k * c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have hsq : ‖L h‖ ^ 2 ≤ (Real.sqrt k * c * ‖h‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc ∑ i, ‖(L h) i‖ ^ 2 ≤ (Finset.univ : Finset (Fin k)).card • (c * ‖h‖) ^ 2 := by
          refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          have := ((EuclideanSpace.proj i : StrongDual ℝ _).comp L).le_opNorm h
          have h' : ‖(L h) i‖ ≤ ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp L‖ * ‖h‖ := this
          exact h'.trans (mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg h))
      _ = k * c ^ 2 * ‖h‖ ^ 2 := by
          rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **FC19, derivative step**: with the original adapted tests along EVERY minimizing initial
unit vector (`W x y`), the common long endpoints saturate both covectors, so at every point of
`B(p,L)` one has `‖dF − A dG‖ ≤ 2√(k(4ε+ε²))`, `ε = α + (3δ + 2E)/(s − 2δ)`. No continuity of the
chosen directions is used. -/
theorem norm_sub_comp_le_of_common_endpoints {X Z : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Z] {TX : X → Type*} [∀ x, NormedAddCommGroup (TX x)]
    [∀ x, InnerProductSpace ℝ (TX x)] [∀ x, CompleteSpace (TX x)]
    (u : X → EuclideanSpace ℝ (Fin m)) (z : X → Z) (Ψ : X → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (b₀ : EuclideanSpace ℝ (Fin k)) {p : X} {z₀ : Z} {L T s H δ E α : ℝ} (hT : 0 ≤ T)
    (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hα : 0 ≤ α) (hs : T + 2 * δ < s) (hH : L + s + 3 * δ < H)
    (hup : u p = 0) (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p H, ∀ y ∈ ball p H,
      |dist (WithLp.toLp 2 (u x, z x) : WithLp 2 (_ × Z)) (WithLp.toLp 2 (u y, z y)) -
        dist x y| ≤ δ)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin m) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < H - δ →
        ∃ y ∈ ball p H, dist (WithLp.toLp 2 (u y, z y)) q ≤ δ)
    (hΨ : ∀ x ∈ ball p H, ‖Ψ x - A (u x) - b₀‖ ≤ E)
    (W : ∀ x : X, X → Set (TX x)) (hW : ∀ x y, x ≠ y → (W x y).Nonempty)
    (hWunit : ∀ x y, ∀ w ∈ W x y, ‖w‖ = 1)
    (dF : ∀ x, TX x →L[ℝ] EuclideanSpace ℝ (Fin k)) (dG : ∀ x, TX x →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hF : ∀ x ∈ ball p L, ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x)‖ ≤ 1 + α)
    (hG : ∀ x ∈ ball p L, ‖dG x‖ ≤ 1 + α)
    (htestF : ∀ x ∈ ball p L, ∀ y ∈ ball p H, T < dist x y → ∀ w ∈ W x y,
      ‖dF x w - (dist x y)⁻¹ • (Ψ y - Ψ x)‖ ≤ α)
    (htestG : ∀ x ∈ ball p L, ∀ y ∈ ball p H, T < dist x y → ∀ w ∈ W x y,
      ‖dG x w - (dist x y)⁻¹ • (u y - u x)‖ ≤ α) :
    ∀ x ∈ ball p L, ‖dF x - A.comp (dG x)‖ ≤
      2 * Real.sqrt (k * (4 * (α + (3 * δ + 2 * E) / (s - 2 * δ)) +
        (α + (3 * δ + 2 * E) / (s - 2 * δ)) ^ 2)) := by
  intro x hx
  set ε := α + (3 * δ + 2 * E) / (s - 2 * δ) with hεdef
  have hs2 : 0 < s - 2 * δ := by linarith
  have hε0 : 0 ≤ ε := add_nonneg hα (div_nonneg (by positivity) hs2.le)
  have hεα : α ≤ ε := le_add_of_nonneg_right (div_nonneg (by positivity) hs2.le)
  have hAn : ‖A‖ ≤ 1 := by
    have hiso : ∀ y, ‖ContinuousLinearMap.adjoint A y‖ = ‖y‖ := fun y => by
      have h : ⟪ContinuousLinearMap.adjoint A y, ContinuousLinearMap.adjoint A y⟫_ℝ = ⟪y, y⟫_ℝ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
        have := congrArg (fun S : _ →L[ℝ] _ => S y) hA
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
        rw [this]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
    have hadj : ‖ContinuousLinearMap.adjoint A‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [hiso, one_mul]
    rwa [LinearIsometryEquiv.norm_map] at hadj
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin k)) i, |w i| ≤ ‖w‖ := fun w i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w i
  have hrow : ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x - A.comp (dG x))‖ ≤
      2 * Real.sqrt (4 * ε + ε ^ 2) := by
    intro i
    obtain ⟨y, hyH, hTy, hℓlo, -, hratΨ, hratA⟩ :=
      exists_common_long_endpoint u z Ψ A hA b₀ hT hδ hE hs hH hup hzp hdist hcover hΨ hx i
    have hxy : x ≠ y := fun h => by rw [h, dist_self] at hTy; linarith
    obtain ⟨w, hw⟩ := hW x y hxy
    have hwn := hWunit x y w hw
    set ℓ := dist x y
    have hℓ : 0 < ℓ := hs2.trans_le hℓlo
    let f : StrongDual ℝ (TX x) := (EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x)
    let g : StrongDual ℝ (TX x) :=
      (EuclideanSpace.proj i : StrongDual ℝ _).comp (A.comp (dG x))
    have hfw : 1 - ε ≤ f w := by
      have h1 := (abs_le.mp ((hcoord _ i).trans (htestF x hx y hyH hTy w hw))).1
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply] at h1
      have h2 : ℓ⁻¹ * (Ψ y i - Ψ x i) = (Ψ y i - Ψ x i) / ℓ := by rw [inv_mul_eq_div]
      change 1 - ε ≤ (dF x w) i
      linarith
    have hgw : 1 - ε ≤ g w := by
      have hdiff : |(A (dG x w)) i - (A (u y - u x)) i / ℓ| ≤ α := by
        have hrw : (A (dG x w)) i - (A (u y - u x)) i / ℓ =
            (A (dG x w - ℓ⁻¹ • (u y - u x))) i := by
          rw [map_sub A (dG x w) (ℓ⁻¹ • (u y - u x)), map_smul, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul, inv_mul_eq_div]
        rw [hrw]
        refine (hcoord _ i).trans ((A.le_opNorm _).trans ?_)
        calc ‖A‖ * ‖dG x w - ℓ⁻¹ • (u y - u x)‖ ≤ 1 * α :=
              mul_le_mul hAn (htestG x hx y hyH hTy w hw) (norm_nonneg _) zero_le_one
          _ = α := one_mul _
      change 1 - ε ≤ (A (dG x w)) i
      linarith [(abs_le.mp hdiff).1]
    have hfn : ‖f‖ ≤ 1 + ε := (hF x hx i).trans (by linarith)
    have hgn : ‖g‖ ≤ 1 + ε := by
      calc ‖g‖ ≤ ‖(EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin k)))‖ *
            (‖A‖ * ‖dG x‖) :=
            (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
        _ ≤ 1 * (1 * (1 + α)) := by
            gcongr
            · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
                rw [one_mul]; exact PiLp.norm_apply_le v i
            · exact hG x hx
        _ ≤ 1 + ε := by linarith
    have key := ContinuousLinearMap.norm_sub_le_of_common_unit_saturation f g hε0 hfn hgn w hwn
      hfw hgw
    have hfg : (EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x - A.comp (dG x)) = f - g := by
      ext v; simp [f, g]
    rw [hfg]; exact key
  calc ‖dF x - A.comp (dG x)‖ ≤ Real.sqrt k * (2 * Real.sqrt (4 * ε + ε ^ 2)) :=
        norm_le_of_rows _ (by positivity) hrow
    _ = 2 * Real.sqrt (k * (4 * ε + ε ^ 2)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg k)]; ring

end GC.MetricGeometry
