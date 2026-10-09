import DifferentialGeometry.Analysis.InnerProductSpace.AnchorAlignment
import DifferentialGeometry.Analysis.InnerProductSpace.AsymmetricTestSaturation

set_option autoImplicit false

/-!
# The original overlap comparison chain (FC23 kernel)

Blueprint 207B, `found:fibration-original-binding` (FC23, B:1505), using FC20/FC21
(`AnchorAlignment.lean`) and the pointwise FC22 steps of W4-EGP
(`AsymmetricTestSaturation.lean`: `saturation_of_test_gain`, `short_gain_of_long_tests`) and the
FC15 Riesz step (`DirectionalSaturation.lean`).

FC23 is an implementation packet; its geometric source binding (KL 4.21–4.35, 9.12, 11.1, 12.12)
is not produced here. What is proved is the complete analytic chain the packet feeds: the raw
factor data on the SHORT buffer `S` (item 3) give, through FC20 and FC21, ONE coisometry `A` and
translation `b₀`; the asymmetric long/short tests (item 2) on the tested domain `D` then give, at
every point of `D` and with the SAME `A`, the derivative comparison
`‖dF − A dG‖ ≤ 2 √(k (4ε + ε²))` with FC22's exact
`ε = max (α_F + β/ℓ₀) (α_G + (β + δ + 2E)/t)`, `E = e_c + 24kδ_f`. Every packet item is an
explicit hypothesis; no structure is assumed. Tangent spaces may vary with the point.
-/

open scoped InnerProductSpace
open Module

namespace InnerProductSpace

variable {k m : ℕ}

private theorem norm_le_one_of_coisometry
    {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] (A : F →L[ℝ] G)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ G) : ‖A‖ ≤ 1 := by
  have hiso : ∀ y, ‖ContinuousLinearMap.adjoint A y‖ = ‖y‖ := fun y => by
    have h : ⟪ContinuousLinearMap.adjoint A y, ContinuousLinearMap.adjoint A y⟫_ℝ = ⟪y, y⟫_ℝ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
      have := congrArg (fun T : G →L[ℝ] G => T y) hA
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
      rw [this]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have hadj : ‖ContinuousLinearMap.adjoint A‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [hiso, one_mul]
  rwa [LinearIsometryEquiv.norm_map] at hadj

private theorem norm_proj_le {ι : Type*} [Fintype ι] (i : ι) :
    ‖(EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ ι))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact PiLp.norm_apply_le v i

/-- FC22 at one point with its exact asymmetric `ε`: a long raw test on `f` and a short aligned
test on `g` along the SAME unit vector saturate both covectors. -/
theorem norm_sub_le_of_long_short_tests {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [CompleteSpace T] (f g : StrongDual ℝ T) (w : T) (hw : ‖w‖ = 1)
    {αF αG ℓ ℓ₀ t β δ E Ψx Ψy Ψz Ux Uz b : ℝ} (hαF : 0 ≤ αF) (hℓ₀ : 0 < ℓ₀)
    (hℓ : ℓ₀ ≤ ℓ) (ht : 0 < t) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hf : ‖f‖ ≤ 1 + αF) (hg : ‖g‖ ≤ 1 + αG)
    (hlong : ℓ - β ≤ Ψy - Ψx) (hcoarse : Ψy - Ψz ≤ ℓ - t + δ)
    (hx : |Ψx - (Ux + b)| ≤ E) (hz : |Ψz - (Uz + b)| ≤ E)
    (htestF : |f w - (Ψy - Ψx) / ℓ| ≤ αF) (htestG : |g w - (Uz - Ux) / t| ≤ αG) :
    ‖f - g‖ ≤ 2 * Real.sqrt (4 * max (αF + β / ℓ₀) (αG + (β + δ + 2 * E) / t) +
      max (αF + β / ℓ₀) (αG + (β + δ + 2 * E) / t) ^ 2) := by
  set ε := max (αF + β / ℓ₀) (αG + (β + δ + 2 * E) / t)
  have hsF := ContinuousLinearMap.saturation_of_test_gain hℓ₀ hℓ hβ htestF hlong
  have hshort := ContinuousLinearMap.short_gain_of_long_tests hlong hcoarse hx hz
  have hsG := ContinuousLinearMap.saturation_of_test_gain ht le_rfl (by linarith) htestG hshort
  have h1 : αF + β / ℓ₀ ≤ ε := le_max_left _ _
  have h2 : αG + (β + δ + 2 * E) / t ≤ ε := le_max_right _ _
  have hβℓ : 0 ≤ β / ℓ₀ := div_nonneg hβ hℓ₀.le
  have hε0 : 0 ≤ ε := (add_nonneg hαF hβℓ).trans h1
  have hdiv : 0 ≤ (β + δ + 2 * E) / t := div_nonneg (by linarith) ht.le
  exact ContinuousLinearMap.norm_sub_le_of_common_unit_saturation f g hε0 (by linarith)
    (by linarith) w hw (by linarith) (by linarith)

/-- FC22 for a `k`-component comparison at one point: the rowwise saturation of
`norm_sub_le_of_long_short_tests` and square summation give `‖dF − A dG‖ ≤ 2 √(k(4ε+ε²))`. -/
theorem norm_sub_comp_le_of_long_short_tests {T : Type*} [NormedAddCommGroup T]
    [InnerProductSpace ℝ T] [CompleteSpace T] {X : Type*} (u : X → EuclideanSpace ℝ (Fin m))
    (Ψ : X → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (b₀ : EuclideanSpace ℝ (Fin k)) (dF : T →L[ℝ] EuclideanSpace ℝ (Fin k))
    (dG : T →L[ℝ] EuclideanSpace ℝ (Fin m)) {αF αG ℓ₀ t β δ E : ℝ} (hαF : 0 ≤ αF)
    (hℓ₀ : 0 < ℓ₀) (ht : 0 < t) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hF : ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp dF‖ ≤ 1 + αF)
    (hG : ‖dG‖ ≤ 1 + αG) (x : X) (hx : ‖Ψ x - A (u x) - b₀‖ ≤ E)
    (htests : ∀ i : Fin k, ∃ w : T, ‖w‖ = 1 ∧ ∃ y z : X, ∃ ℓ : ℝ, ℓ₀ ≤ ℓ ∧
      ‖Ψ z - A (u z) - b₀‖ ≤ E ∧ ℓ - β ≤ Ψ y i - Ψ x i ∧ Ψ y i - Ψ z i ≤ ℓ - t + δ ∧
      |dF w i - (Ψ y i - Ψ x i) / ℓ| ≤ αF ∧ ‖dG w - t⁻¹ • (u z - u x)‖ ≤ αG) :
    ‖dF - A.comp dG‖ ≤ 2 * Real.sqrt (k * (4 * max (αF + β / ℓ₀) (αG + (β + δ + 2 * E) / t) +
      max (αF + β / ℓ₀) (αG + (β + δ + 2 * E) / t) ^ 2)) := by
  set ε := max (αF + β / ℓ₀) (αG + (β + δ + 2 * E) / t)
  have hAn := norm_le_one_of_coisometry A hA
  have hcoord : ∀ (v : EuclideanSpace ℝ (Fin k)) i, |v i| ≤ ‖v‖ := fun v i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  -- rowwise bound
  have hrow : ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF - A.comp dG)‖ ≤
      2 * Real.sqrt (4 * ε + ε ^ 2) := by
    intro i
    obtain ⟨w, hw, y, z, ℓ, hℓ, hz, hlong, hcoarse, htF, htG⟩ := htests i
    let f : StrongDual ℝ T := (EuclideanSpace.proj i : StrongDual ℝ _).comp dF
    let g : StrongDual ℝ T := (EuclideanSpace.proj i : StrongDual ℝ _).comp (A.comp dG)
    have hg : ‖g‖ ≤ 1 + αG := by
      calc ‖g‖ ≤ ‖(EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin k)))‖ *
            (‖A‖ * ‖dG‖) :=
            (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
        _ ≤ 1 * (1 * (1 + αG)) := by
            gcongr
            · exact norm_proj_le i
        _ = 1 + αG := by ring
    have hxi : |Ψ x i - ((A (u x)) i + b₀ i)| ≤ E := by
      refine le_trans (le_of_eq ?_) ((hcoord _ i).trans hx)
      simp only [PiLp.sub_apply]; ring_nf
    have hzi : |Ψ z i - ((A (u z)) i + b₀ i)| ≤ E := by
      refine le_trans (le_of_eq ?_) ((hcoord _ i).trans hz)
      simp only [PiLp.sub_apply]; ring_nf
    have htestG : |g w - ((A (u z)) i - (A (u x)) i) / t| ≤ αG := by
      have hrw : g w - ((A (u z)) i - (A (u x)) i) / t =
          (A (dG w - t⁻¹ • (u z - u x))) i := by
        simp only [g, ContinuousLinearMap.comp_apply, map_sub, map_smul, PiLp.sub_apply,
          PiLp.smul_apply, smul_eq_mul]
        change (A (dG w)) i - ((A (u z)) i - (A (u x)) i) / t =
          (A (dG w)) i - t⁻¹ * ((A (u z)) i - (A (u x)) i)
        rw [div_eq_inv_mul]
      rw [hrw]
      refine (hcoord _ i).trans ((A.le_opNorm _).trans ?_)
      calc ‖A‖ * ‖dG w - t⁻¹ • (u z - u x)‖ ≤ 1 * αG :=
            mul_le_mul hAn htG (norm_nonneg _) zero_le_one
        _ = αG := one_mul _
    have htestF' : |f w - (Ψ y i - Ψ x i) / ℓ| ≤ αF := by
      simpa [f] using htF
    have key := norm_sub_le_of_long_short_tests f g w hw hαF hℓ₀ hℓ ht hβ hδ hE (hF i) hg
      hlong hcoarse hxi hzi htestF' htestG
    have hfg : (EuclideanSpace.proj i : StrongDual ℝ _).comp (dF - A.comp dG) = f - g := by
      ext v; simp [f, g]
    rw [hfg]; exact key
  -- square summation
  have hε0 : 0 ≤ ε := (add_nonneg hαF (div_nonneg hβ hℓ₀.le)).trans (le_max_left _ _)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have hsq : ‖(dF - A.comp dG) h‖ ^ 2 ≤
      (2 * Real.sqrt (k * (4 * ε + ε ^ 2)) * ‖h‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc ∑ i, ‖((dF - A.comp dG) h) i‖ ^ 2 ≤
          (Finset.univ : Finset (Fin k)).card • (2 * Real.sqrt (4 * ε + ε ^ 2) * ‖h‖) ^ 2 := by
          refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          have := ((EuclideanSpace.proj i : StrongDual ℝ _).comp (dF - A.comp dG)).le_opNorm h
          have h' : ‖((dF - A.comp dG) h) i‖ ≤
              ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF - A.comp dG)‖ * ‖h‖ := this
          exact h'.trans (mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg h))
      _ = 2 ^ 2 * (k * (4 * ε + ε ^ 2)) * ‖h‖ ^ 2 := by
          rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, mul_pow,
            Real.sq_sqrt (by positivity)]
          ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **FC23 kernel** (the overlap comparison chain): raw factor data on the short buffer `S`
(FC21 with the FC20 factor map) and the asymmetric long/short tests at every point of the
tested domain `D` give ONE coisometry `A` and translation `b₀` with the value error
`e_c + 24kδ_f` on `S` and the derivative comparison `2 √(k(4ε+ε²))` on `D`. The tangent space
`T x` may vary with the point. -/
theorem exists_coisometry_overlap_comparison {X : Type*} {T : X → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)] [∀ x, CompleteSpace (T x)]
    (u : X → EuclideanSpace ℝ (Fin m)) (Ψ : X → EuclideanSpace ℝ (Fin k)) (S D : Set X)
    (P : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hP : P.comp (ContinuousLinearMap.adjoint P) = ContinuousLinearMap.id ℝ _)
    (c d : EuclideanSpace ℝ (Fin k)) {a δf ec : ℝ} (ha : 0 < a) (hδf : 0 ≤ δf)
    (hδa : 20 * (k : ℝ) * δf ≤ a) (hec : 0 ≤ ec)
    (f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) (h0 : f 0 = 0)
    (hdist : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → |‖f v - f w‖ - ‖v - w‖| ≤ δf)
    (hraw : ∀ x ∈ S, ‖Ψ x - f (P (u x) - c) - d‖ ≤ ec) (hball : ∀ x ∈ S, ‖P (u x) - c‖ ≤ a)
    (dF : ∀ x, T x →L[ℝ] EuclideanSpace ℝ (Fin k)) (dG : ∀ x, T x →L[ℝ] EuclideanSpace ℝ (Fin m))
    {αF αG ℓ₀ t β δ : ℝ} (hαF : 0 ≤ αF) (hℓ₀ : 0 < ℓ₀) (ht : 0 < t) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hF : ∀ x ∈ D, ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x)‖ ≤ 1 + αF)
    (hG : ∀ x ∈ D, ‖dG x‖ ≤ 1 + αG) (hDS : D ⊆ S)
    (htests : ∀ x ∈ D, ∀ i : Fin k, ∃ w : T x, ‖w‖ = 1 ∧ ∃ y z : X, ∃ ℓ : ℝ, ℓ₀ ≤ ℓ ∧ z ∈ S ∧
      ℓ - β ≤ Ψ y i - Ψ x i ∧ Ψ y i - Ψ z i ≤ ℓ - t + δ ∧
      |dF x w i - (Ψ y i - Ψ x i) / ℓ| ≤ αF ∧ ‖dG x w - t⁻¹ • (u z - u x)‖ ≤ αG) :
    ∃ A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k), ∃ b₀,
      A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
      (∀ x ∈ S, ‖Ψ x - A (u x) - b₀‖ ≤ ec + 24 * k * δf) ∧
      ∀ x ∈ D, ‖dF x - A.comp (dG x)‖ ≤ 2 * Real.sqrt (k * (4 * max (αF + β / ℓ₀)
        (αG + (β + δ + 2 * (ec + 24 * k * δf)) / t) +
          max (αF + β / ℓ₀) (αG + (β + δ + 2 * (ec + 24 * k * δf)) / t) ^ 2)) := by
  obtain ⟨A, b₀, hA, hval⟩ := exists_coisometry_raw_factor_alignment
    (fun x : S => u x) (fun x : S => Ψ x) P hP c d ha hδf
    (by rwa [finrank_euclideanSpace_fin]) f h0 hdist (fun x => hraw x x.2) (fun x => hball x x.2)
  rw [finrank_euclideanSpace_fin] at hval
  have hval' : ∀ x ∈ S, ‖Ψ x - A (u x) - b₀‖ ≤ ec + 24 * k * δf := fun x hx => hval ⟨x, hx⟩
  refine ⟨A, b₀, hA, hval', fun x hx => ?_⟩
  have hE : 0 ≤ ec + 24 * (k : ℝ) * δf := by positivity
  refine norm_sub_comp_le_of_long_short_tests u Ψ A hA b₀ (dF x) (dG x) hαF hℓ₀ ht hβ hδ hE
    (hF x hx) (hG x hx) x (hval' x (hDS hx)) fun i => ?_
  obtain ⟨w, hw, y, z, ℓ, hℓ, hz, h1, h2, h3, h4⟩ := htests x hx i
  exact ⟨w, hw, y, z, ℓ, hℓ, hval' z hz, h1, h2, h3, h4⟩

end InnerProductSpace
