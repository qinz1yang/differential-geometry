import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFrozenProduct
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Lower length bound for cusp paths in a slab (foundation F-f.P, lower half)

For the model cusp `H = dz² + e^{-z} q` (`HyperbolicCusp`) and a `C¹` path
`c : [0, 1] → T² × [0, ∞)` whose heights stay in `[z₀ - a, z₀ + a]`:
`H-length(c) ≥ e^{-a/2} √((z(c 1) - z(c 0))² + e^{-z₀} d_q(t(c 0), t(c 1))²)`
(`HyperbolicCusp.frozen_le_pathELength`). This is the lower half of the frozen-product comparison of
BCP02.b (blueprint 207B, `B:8234–8321`); together with the lifting of short curves of the carrier
into the cusp (needs the repaired finite interior patch) it gives the lower distortion of the actual
splitting map.

Proof: pointwise `|ċ|_H ≥ e^{-a/2} √(ż² + e^{-z₀} |ṫ|_q²)` (`HyperbolicCusp.inner_le_exp_frozen`);
the integral Minkowski inequality in the dual form `√(x² + κ y²) N ≥ x X + κ y Y`
(`ofReal_sqrt_le_lintegral`, no measurability needed); `∫ |ż| ≥ |Δz|` (fundamental theorem of
calculus) and `∫ |ṫ|_q ≥ d_q` (the torus projection is a `C¹` path).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- Integral Minkowski inequality in dual form: lower bounds `X ≤ ∫ |A|` and `Y ≤ ∫ B` give
`√(X² + κ Y²) ≤ ∫ √(A² + κ B²)` (lower Lebesgue integrals, no measurability). -/
theorem ofReal_sqrt_le_lintegral {s : Set ℝ} {A B : ℝ → ℝ} {X Y κ : ℝ} (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hκ : 0 ≤ κ) (hB : ∀ t, 0 ≤ B t)
    (hXA : ENNReal.ofReal X ≤ ∫⁻ t in s, ENNReal.ofReal |A t|)
    (hYB : ENNReal.ofReal Y ≤ ∫⁻ t in s, ENNReal.ofReal (B t)) :
    ENNReal.ofReal (Real.sqrt (X ^ 2 + κ * Y ^ 2)) ≤
      ∫⁻ t in s, ENNReal.ofReal (Real.sqrt (A t ^ 2 + κ * B t ^ 2)) := by
  set N : ℝ := Real.sqrt (X ^ 2 + κ * Y ^ 2) with hN
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (X ^ 2 + κ * Y ^ 2)) with h0 | hpos
  · rw [hN, ← h0, ENNReal.ofReal_zero]
    exact bot_le
  rw [← hN] at hpos
  have hNsq : N ^ 2 = X ^ 2 + κ * Y ^ 2 := Real.sq_sqrt (by positivity)
  have hpt : ∀ t, X / N * |A t| + κ * Y / N * B t ≤ Real.sqrt (A t ^ 2 + κ * B t ^ 2) := by
    intro t
    have hS := Real.sq_sqrt (show 0 ≤ A t ^ 2 + κ * B t ^ 2 by positivity)
    have hS0 := Real.sqrt_nonneg (A t ^ 2 + κ * B t ^ 2)
    have hA2 : |A t| ^ 2 = A t ^ 2 := sq_abs _
    have hcs : X * |A t| + κ * Y * B t ≤ N * Real.sqrt (A t ^ 2 + κ * B t ^ 2) := by
      have hsq : (X * |A t| + κ * Y * B t) ^ 2 ≤
          (N * Real.sqrt (A t ^ 2 + κ * B t ^ 2)) ^ 2 := by
        rw [mul_pow, hNsq, hS]
        nlinarith [mul_nonneg hκ (sq_nonneg (X * B t - Y * |A t|))]
      exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_iff₀ hpos]
    linarith
  have hXN : 0 ≤ X / N := div_nonneg hX hpos.le
  have hYN : 0 ≤ κ * Y / N := div_nonneg (mul_nonneg hκ hY) hpos.le
  calc ENNReal.ofReal N = ENNReal.ofReal (X / N) * ENNReal.ofReal X +
        ENNReal.ofReal (κ * Y / N) * ENNReal.ofReal Y := by
        rw [← ENNReal.ofReal_mul hXN, ← ENNReal.ofReal_mul hYN,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        exact hNsq
    _ ≤ ENNReal.ofReal (X / N) * (∫⁻ t in s, ENNReal.ofReal |A t|) +
        ENNReal.ofReal (κ * Y / N) * ∫⁻ t in s, ENNReal.ofReal (B t) :=
        add_le_add (mul_le_mul' le_rfl hXA) (mul_le_mul' le_rfl hYB)
    _ ≤ (∫⁻ t in s, ENNReal.ofReal (X / N) * ENNReal.ofReal |A t|) +
        ∫⁻ t in s, ENNReal.ofReal (κ * Y / N) * ENNReal.ofReal (B t) :=
        add_le_add (lintegral_const_mul_le _ _) (lintegral_const_mul_le _ _)
    _ ≤ ∫⁻ t in s, (ENNReal.ofReal (X / N) * ENNReal.ofReal |A t| +
        ENNReal.ofReal (κ * Y / N) * ENNReal.ofReal (B t)) := le_lintegral_add _ _
    _ ≤ ∫⁻ t in s, ENNReal.ofReal (Real.sqrt (A t ^ 2 + κ * B t ^ 2)) := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul hXN, ← ENNReal.ofReal_mul hYN,
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg hYN (hB t))]
        exact ENNReal.ofReal_le_ofReal (hpt t)

/-- The height of a path in the half line has the expected derivative. -/
theorem hasDerivAt_val_zero_of_hasMFDerivAt {f : ℝ → EuclideanHalfSpace 1} {t : ℝ}
    {f' : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace (𝓡∂ 1) (f t)}
    (hf : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡∂ 1) f t f') :
    HasDerivAt (fun s => (f s).val 0)
      ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) (f' 1)) t := by
  obtain ⟨-, hd⟩ := hf
  simp only [writtenInExtChartAt, mfld_simps] at hd
  have h1 := ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt
    (x := (f t).val)).comp t (hasFDerivWithinAt_univ.mp hd)
  exact h1.hasDerivAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- F-f.P (lower half): the `H`-length of a `C¹` path in the slab `|z - z₀| ≤ a` is at least
`e^{-a/2} √(Δz² + e^{-z₀} d_q²)`. -/
theorem HyperbolicCusp.frozen_le_pathELength (Hc : HyperbolicCusp) {c : ℝ → CuspHalfSpace}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 c (Icc 0 1)) {z₀ a : ℝ}
    (hslab : ∀ r ∈ Icc (0 : ℝ) 1, |(c r).2.val 0 - z₀| ≤ a) :
    letI : RiemannianBundle (fun x : CuspHalfSpace => TangentSpace halfCollarModel x) :=
      ⟨Hc.metric.toRiemannianMetric⟩
    ENNReal.ofReal (Real.exp (-a / 2) * Real.sqrt (((c 1).2.val 0 - (c 0).2.val 0) ^ 2 +
        Real.exp (-z₀) * (riemannianEDistOf Hc.torusMetric (c 0).1 (c 1).1).toReal ^ 2)) ≤
      pathELength halfCollarModel c 0 1 := by
  let : RiemannianBundle (fun x : CuspHalfSpace => TangentSpace halfCollarModel x) :=
    ⟨Hc.metric.toRiemannianMetric⟩
  set κ : ℝ := Real.exp (-z₀) with hκ
  have hκ0 : 0 ≤ κ := (Real.exp_pos _).le
  let A : ℝ → ℝ := fun t => (mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1).2 0
  let B : ℝ → ℝ := fun t => Real.sqrt (Hc.torusMetric.inner (c t).1
    (mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1).1 (mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1).1)
  have hdiff : ∀ t ∈ Ioo (0 : ℝ) 1, MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel c t :=
    fun t ht => (hc.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  -- the pointwise frozen lower bound
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-a / 2)) *
      ENNReal.ofReal (Real.sqrt (A t ^ 2 + κ * B t ^ 2)) ≤
        ‖mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1‖ₑ := by
    intro t ht
    set v := mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1 with hv
    have hH := (HyperbolicCusp.inner_le_exp_frozen Hc (hslab t (Ioo_subset_Icc_self ht)) v).1
    have hq0 : 0 ≤ Hc.torusMetric.inner (c t).1 v.1 v.1 := metric_inner_self_nonneg _ _ _
    have hB2 : B t ^ 2 = Hc.torusMetric.inner (c t).1 v.1 v.1 := Real.sq_sqrt hq0
    rw [← ofReal_norm, norm_eq_sqrt_real_inner, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hexp : Real.exp (-a / 2) = Real.sqrt (Real.exp (-a)) := by
      rw [← Real.sqrt_sq (Real.exp_pos (-a / 2)).le, ← Real.exp_nat_mul]
      congr 2
      ring
    rw [hexp, ← Real.sqrt_mul (Real.exp_pos _).le]
    apply Real.sqrt_le_sqrt
    change Real.exp (-a) * (v.2 0 ^ 2 + κ * B t ^ 2) ≤ Hc.metric.inner (c t) v v
    rw [hB2]
    exact hH
  -- the height bound `|Δz| ≤ ∫ |ż|`
  have hheight : ENNReal.ofReal |(c 1).2.val 0 - (c 0).2.val 0| ≤
      ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal |A t| := by
    have hζ : ContDiffOn ℝ 1 (fun s => (c s).2.val 0) (Icc 0 1) := by
      have h1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
          ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) ∘
            (𝓡∂ 1) ∘ Prod.snd ∘ c) (Icc 0 1) :=
        (ContinuousLinearMap.contMDiff _).comp_contMDiffOn
          ((𝓡∂ 1).contMDiff.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn hc))
      exact contMDiffOn_iff_contDiffOn.mp h1
    have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hζ zero_le_one
    rw [← restrict_Ioo_eq_restrict_Icc] at h
    rw [Real.enorm_eq_ofReal_abs] at h
    refine h.trans (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_)
    have hsnd := (hasMFDerivAt_snd (c t)).comp t (hdiff t ht).hasMFDerivAt
    have hderiv := (hasDerivAt_val_zero_of_hasMFDerivAt hsnd).deriv
    change ‖deriv (fun s => (c s).2.val 0) t‖ₑ ≤ _
    rw [show (fun s => (c s).2.val 0) = fun s => ((Prod.snd ∘ c) s).val 0 from rfl, hderiv,
      Real.enorm_eq_ofReal_abs]
    rfl
  -- the torus bound `d_q ≤ ∫ |ṫ|_q`
  have htorus : ENNReal.ofReal (riemannianEDistOf Hc.torusMetric (c 0).1 (c 1).1).toReal ≤
      ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (B t) := by
    let : RiemannianBundle (fun x : Torus => TangentSpace torusModel x) :=
      ⟨Hc.torusMetric.toRiemannianMetric⟩
    refine ENNReal.ofReal_toReal_le.trans ?_
    have hfst : ContMDiffOn 𝓘(ℝ, ℝ) torusModel 1 (Prod.fst ∘ c) (Icc 0 1) :=
      contMDiff_fst.comp_contMDiffOn hc
    have h := riemannianEDist_le_pathELength hfst rfl rfl zero_le_one
    change riemannianEDist torusModel (c 0).1 (c 1).1 ≤ _
    refine h.trans ?_
    rw [pathELength_eq_lintegral_mfderiv_Ioo]
    refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    have hfd : mfderiv 𝓘(ℝ, ℝ) torusModel (Prod.fst ∘ c) t 1 =
        (mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1).1 := by
      rw [mfderiv_comp t mdifferentiableAt_fst (hdiff t ht), mfderiv_fst]
      rfl
    rw [← ofReal_norm, norm_eq_sqrt_real_inner, hfd]
    exact le_rfl
  -- assembly
  have hmink := ofReal_sqrt_le_lintegral (abs_nonneg _) ENNReal.toReal_nonneg hκ0
    (fun t => Real.sqrt_nonneg _) hheight htorus
  rw [sq_abs] at hmink
  rw [pathELength_eq_lintegral_mfderiv_Ioo, ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc ENNReal.ofReal (Real.exp (-a / 2)) * ENNReal.ofReal (Real.sqrt
        (((c 1).2.val 0 - (c 0).2.val 0) ^ 2 +
          κ * (riemannianEDistOf Hc.torusMetric (c 0).1 (c 1).1).toReal ^ 2))
      ≤ ENNReal.ofReal (Real.exp (-a / 2)) *
          ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (A t ^ 2 + κ * B t ^ 2)) := by
        gcongr
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-a / 2)) *
          ENNReal.ofReal (Real.sqrt (A t ^ 2 + κ * B t ^ 2)) := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1‖ₑ :=
        setLIntegral_mono' measurableSet_Ioo hpt

end DifferentialGeometry.Geometry.Collapse
