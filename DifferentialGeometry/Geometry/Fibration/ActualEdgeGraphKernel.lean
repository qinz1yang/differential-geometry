import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphModelApplications
import DifferentialGeometry.Geometry.Fibration.ManifoldBlockDerivative
import DifferentialGeometry.Topology.Manifold.LocalExtrema

/-!
# EGP06 (EG): generic kernels of the block-by-block comparison

Blueprint `master207B.tex`, EGP06 (`thm:fibration-actual-edge-graph`, B:5088–5139), proof: "On
`{|η_i| ≤ 8Δ, t ≤ 8Δ}` every block of `R_i⁻¹π₂F` is the corresponding model block evaluated at the
actual coordinate `U_j = s_jη_j`; EGP04 compares `U_j` with `λ_j(η_i)` in `C¹`." The generic pieces:

* `hasMFDerivAt_clm_comp_scaled_KC4`, `mvfderiv_split_KC4`: a block `B` that equals
  `r • L(W(s c))` plus `ψ • E` near `x`, with `ψ(x) = 0` and `dψ_x = 0`, has value and derivative at
  `x` those of `r • L(W(s c))` (chain rule on a manifold source).
* `block_split_KC4` / `own_block_split_KC4`: the algebraic identity
  `((Rζ) e₀c, Rζ) = r L(W_s(s c)) + (ζ − φ(c)) R L(c, 1)` for a scaled cutoff block `W_s`, `rs = R`.
* `fderiv_lift_affine_apply_KC4`: the derivative of `a ↦ L(W(σa + c))`.
* `block_compare_KC4`, `tag_compare_KC4`: one block's `C¹` comparison `≤ 4Bθ`
  (`modelBlock_pointwise_c1_sub_le`).
* `norm_le_card_mul_of_blocks_KC4`: blockwise errors `≤ δ` on a finite set and `0` elsewhere give
  `≤ #S δ` in `ℓ²`; `mvfderiv_clm_comp_apply_KC4`: derivative of a linear map after a map.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section ManifoldGeneric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The chain rule for `y ↦ r • L(W(s c(y)))` with a scalar function `c` on a manifold. -/
theorem hasMFDerivAt_clm_comp_scaled_KC4 (Lf : G →L[ℝ] F) {W : ℝ → G} {c : M → ℝ} {x : M}
    (r s : ℝ) (hc : MDifferentiableAt I 𝓘(ℝ, ℝ) c x) (hW : DifferentiableAt ℝ W (s * c x)) :
    HasMFDerivAt I 𝓘(ℝ, F) (fun y => r • Lf (W (s * c y))) x
      ((r • Lf.comp ((fderiv ℝ W (s * c x)).comp (s • ContinuousLinearMap.id ℝ ℝ))).comp
        (mfderiv I 𝓘(ℝ, ℝ) c x)) := by
  have h1 : HasFDerivAt (fun u : ℝ => s * u) (s • ContinuousLinearMap.id ℝ ℝ) (c x) := by
    have h := (ContinuousLinearMap.id ℝ ℝ).hasFDerivAt (x := c x)
    have h' := h.const_smul s
    refine h'.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp [smul_eq_mul]
  have h2 := hW.hasFDerivAt.comp (c x) h1
  have h3 := (Lf.hasFDerivAt.comp (c x) h2).const_smul r
  have h4 := h3.hasMFDerivAt.comp x hc.hasMFDerivAt
  exact h4

/-- **One block from its model at a point.** If near `x` a map `B` equals
`r • L(W(s c)) + ψ • (R • L(W₀(c)))` with `ψ(x) = 0` and `dψ_x = 0`, then at `x` the value and the
derivative of `B` are those of `r • L(W(s c))`: `B(x) = r L(W(s c(x)))`,
`dB_x(w) = r L(W'(s c(x))(s dc_x(w)))`. -/
theorem mvfderiv_split_KC4 (Lf : G →L[ℝ] F) {B : M → F} {W W₀ : ℝ → G} {c ψ : M → ℝ} {x : M}
    {r s R : ℝ} (hB : ∀ᶠ y in 𝓝 x, B y = r • Lf (W (s * c y)) + ψ y • (R • Lf (W₀ (c y))))
    (hc : MDifferentiableAt I 𝓘(ℝ, ℝ) c x) (hW : DifferentiableAt ℝ W (s * c x))
    (hW₀ : DifferentiableAt ℝ W₀ (c x)) (hψ : MDifferentiableAt I 𝓘(ℝ, ℝ) ψ x) (hψ0 : ψ x = 0)
    (hdψ : mvfderiv I ψ x = 0) (w : TangentSpace I x) :
    B x = r • Lf (W (s * c x)) ∧
      mvfderiv I B x w = r • Lf (fderiv ℝ W (s * c x) (s * mvfderiv I c x w)) := by
  have hBx := Filter.Eventually.self_of_nhds hB
  have hV := hasMFDerivAt_clm_comp_scaled_KC4 Lf r s hc hW
  have hE : MDifferentiableAt I 𝓘(ℝ, F) (fun y => R • Lf (W₀ (c y))) x := by
    have h3 := ((Lf.hasFDerivAt.comp (c x) hW₀.hasFDerivAt).const_smul R).hasMFDerivAt.comp x
      hc.hasMFDerivAt
    exact h3.mdifferentiableAt
  have hPE : MDifferentiableAt I 𝓘(ℝ, F) (fun y => ψ y • (R • Lf (W₀ (c y)))) x :=
    hψ.smul hE
  have hcongr : mfderiv I 𝓘(ℝ, F) B x =
      mfderiv I 𝓘(ℝ, F) (fun y => r • Lf (W (s * c y)) + ψ y • (R • Lf (W₀ (c y)))) x :=
    Filter.EventuallyEq.mfderiv_eq hB
  have hsum : mvfderiv I (fun y => r • Lf (W (s * c y)) + ψ y • (R • Lf (W₀ (c y)))) x =
      mvfderiv I (fun y => r • Lf (W (s * c y))) x +
        mvfderiv I (fun y => ψ y • (R • Lf (W₀ (c y)))) x :=
    mvfderiv_fun_add hV.mdifferentiableAt hPE
  have hprod : mvfderiv I (fun y => ψ y • (R • Lf (W₀ (c y)))) x = 0 := by
    rw [mvfderiv_fun_smul hψ hE, hψ0, hdψ, zero_smul, zero_add]
    ext v
    simp
  refine ⟨by rw [hBx, hψ0, zero_smul, add_zero], ?_⟩
  have step1 : mvfderiv I B x w =
      mvfderiv I (fun y => r • Lf (W (s * c y)) + ψ y • (R • Lf (W₀ (c y)))) x w := by
    rw [mvfderiv_apply_LC, mvfderiv_apply_LC, hcongr]
    rfl
  have step2 : mvfderiv I (fun y => r • Lf (W (s * c y)) + ψ y • (R • Lf (W₀ (c y)))) x w =
      mvfderiv I (fun y => r • Lf (W (s * c y))) x w := by
    rw [hsum, add_apply, hprod, zero_apply, add_zero]
  rw [step1, step2, mvfderiv_apply_LC, hV.mfderiv]
  rfl

/-- The derivative of a continuous linear map after a differentiable map on a manifold. -/
theorem mvfderiv_clm_comp_apply_KC4 {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (Lc : F →L[ℝ] F') {f : M → F} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    (w : TangentSpace I x) :
    mvfderiv I (fun y => Lc (f y)) x w = Lc (mvfderiv I f x w) := by
  have h := Lc.hasFDerivAt.hasMFDerivAt.comp x hf.hasMFDerivAt
  have hfun : (Lc ∘ f) = fun y => Lc (f y) := rfl
  rw [hfun] at h
  rw [mvfderiv_apply_LC, mvfderiv_apply_LC, h.mfderiv]
  rfl

end ManifoldGeneric

section Algebra

/-- Equality in `α ⊕₂ β` from equality of the two components. -/
theorem withLp_prod_ext_KC4 {α β : Type*} {u v : WithLp 2 (α × β)} (h1 : u.fst = v.fst)
    (h2 : u.snd = v.snd) : u = v :=
  WithLp.ofLp_injective 2 (Prod.ext h1 h2)

/-- **The block identity of a scaled cutoff block.** With `r s = R` and `s ≠ 0`:
`((Rζ) e₀c, Rζ) = r L(W_s(s c)) + (ζ − φ(c)) R L(c, 1)`, `W_s = scaledCutoffBlock s φ`, `L` the
lift `(u, m) ↦ (u e₀, m)`. -/
theorem block_split_KC4 (φ : ℝ → ℝ) {R r s : ℝ} (hs : s ≠ 0) (hrs : r * s = R) (ζ c : ℝ) :
    (WithLp.toLp 2 ((R * ζ) • planeAxis c, R * ζ) : WithLp 2 (ℝ² × ℝ)) =
      r • blockLift_KC3 (scaledCutoffBlock s φ (s * c)) +
        (ζ - φ c) • (R • blockLift_KC3 (WithLp.toLp 2 (c, 1))) := by
  have hsc : s⁻¹ • (s * c) = c := by
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have hP : ∀ a : ℝ, planeAxis a = a • planeAxis 1 := fun a => by
    rw [← map_smul, smul_eq_mul, mul_one]
  refine withLp_prod_ext_KC4 ?_ ?_
  · simp only [WithLp.add_fst, WithLp.smul_fst, WithLp.toLp_fst, blockLift_apply_KC3,
      scaledCutoffBlock, hsc]
    rw [hP (φ c • (s * c)), hP c, smul_smul, smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [smul_eq_mul, ← hrs]
    ring
  · simp only [WithLp.add_snd, WithLp.smul_snd, WithLp.toLp_snd, blockLift_apply_KC3,
      scaledCutoffBlock, hsc, smul_eq_mul]
    rw [← hrs]
    ring

/-- The own block identity: `((Rζ) e₀c, Rζ) = R L(c, 1) + (ζ − 1) R L(c, 1)`. -/
theorem own_block_split_KC4 (R ζ c : ℝ) :
    (WithLp.toLp 2 ((R * ζ) • planeAxis c, R * ζ) : WithLp 2 (ℝ² × ℝ)) =
      R • blockLift_KC3 (WithLp.toLp 2 (1 * c, 1)) +
        (ζ - 1) • (R • blockLift_KC3 (WithLp.toLp 2 (c, 1))) := by
  refine withLp_prod_ext_KC4 ?_ ?_
  · simp only [WithLp.add_fst, WithLp.smul_fst, WithLp.toLp_fst, blockLift_apply_KC3, one_mul]
    rw [smul_smul, ← add_smul]
    congr 1
    ring
  · simp only [WithLp.add_snd, WithLp.smul_snd, WithLp.toLp_snd, blockLift_apply_KC3,
      smul_eq_mul]
    ring

end Algebra

section Compare

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of `a ↦ L(W(σa + c))`. -/
theorem fderiv_lift_affine_apply_KC4 (Lf : G →L[ℝ] F) {W : ℝ → G} (hW : Differentiable ℝ W)
    (σ c a v : ℝ) :
    fderiv ℝ (fun a => Lf (W (σ * a + c))) a v = Lf (fderiv ℝ W (σ * a + c) (σ * v)) := by
  have h1 : HasFDerivAt (fun a : ℝ => σ * a + c) (σ • ContinuousLinearMap.id ℝ ℝ) a := by
    have h := ((ContinuousLinearMap.id ℝ ℝ).hasFDerivAt (x := a)).const_smul σ
    refine (h.add_const c).congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp [smul_eq_mul]
  have h2 := (Lf.hasFDerivAt.comp a ((hW (σ * a + c)).hasFDerivAt.comp a h1))
  have hfun : (Lf ∘ (W ∘ fun a : ℝ => σ * a + c)) = fun a => Lf (W (σ * a + c)) := rfl
  rw [hfun] at h2
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul]

/-- **One block's `C¹` comparison.** For a model block `W` with `C²` bounds `B`, actual data
`u, du` and model data `v = σa + c`, `dv = σ da` with `|u − v|, |du − dv| ≤ θ ≤ 1`, `|σ| ≤ 1`,
`|da| ≤ 2`: if `b = r L(W(u))` and `db = r L(W'(u) du)` (`L` norm-preserving, `r ≠ 0`), then
`‖r⁻¹b − L(W(v))‖ ≤ 4Bθ` and `‖r⁻¹db − L(W'(v) dv)‖ ≤ 4Bθ`. -/
theorem block_compare_KC4 (Lf : WithLp 2 (ℝ × ℝ) →L[ℝ] F) (hLf : ∀ m, ‖Lf m‖ = ‖m‖)
    {W : ℝ → WithLp 2 (ℝ × ℝ)} (hW : ContDiff ℝ 2 W) {B θ r u du σ c a da : ℝ} (hB : 0 ≤ B)
    (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B) (hθ1 : θ ≤ 1)
    (hr : r ≠ 0) (hu : |u - (σ * a + c)| ≤ θ) (hdu : |du - σ * da| ≤ θ) (hσ : |σ| ≤ 1)
    (hda : |da| ≤ 2) {b db : F} (hb : b = r • Lf (W u)) (hdb : db = r • Lf (fderiv ℝ W u du)) :
    ‖r⁻¹ • b - Lf (W (σ * a + c))‖ ≤ 4 * B * θ ∧
      ‖r⁻¹ • db - Lf (fderiv ℝ W (σ * a + c) (σ * da))‖ ≤ 4 * B * θ := by
  have hdv : |σ * da| ≤ 2 := by
    rw [abs_mul]
    calc |σ| * |da| ≤ 1 * 2 := mul_le_mul hσ hda (abs_nonneg _) zero_le_one
      _ = 2 := one_mul 2
  obtain ⟨hv, hd⟩ := modelBlock_pointwise_c1_sub_le hW hB h1 h2 hθ1 hu hdu hdv
  rw [hb, hdb, inv_smul_smul₀ hr, inv_smul_smul₀ hr, ← map_sub, ← map_sub, hLf, hLf]
  exact ⟨hv, hd⟩

/-- **One tag's comparison** in the form used by EGP06: actual block `b = r L(W(s u))`,
`db = r L(W'(s u)(s du))`, model component `a ↦ L(W(σa + c))`, EGP04's (EC)
`|s u − (σa + c)|, |s du − σ da| < θ`: both errors at most `4Bθ`. -/
theorem tag_compare_KC4 (Lf : WithLp 2 (ℝ × ℝ) →L[ℝ] F) (hLf : ∀ m, ‖Lf m‖ = ‖m‖)
    {W : ℝ → WithLp 2 (ℝ × ℝ)} (hW : ContDiff ℝ 2 W) {B θ r s u du σ c a da : ℝ} (hB : 0 ≤ B)
    (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B) (hθ1 : θ ≤ 1)
    (hr : r ≠ 0) (hu : |s * u - (σ * a + c)| < θ) (hdu : |s * du - σ * da| < θ) (hσ : |σ| ≤ 1)
    (hda : |da| ≤ 2) {comp : ℝ → F} (hcomp : comp = fun a => Lf (W (σ * a + c))) {b db : F}
    (hb : b = r • Lf (W (s * u))) (hdb : db = r • Lf (fderiv ℝ W (s * u) (s * du))) :
    ‖r⁻¹ • b - comp a‖ ≤ 4 * B * θ ∧ ‖r⁻¹ • db - fderiv ℝ comp a da‖ ≤ 4 * B * θ := by
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  subst hcomp
  rw [fderiv_lift_affine_apply_KC4 Lf hWd]
  exact block_compare_KC4 Lf hLf hW hB h1 h2 hθ1 hr hu.le hdu.le hσ hda hb hdb

/-- Blockwise errors at most `δ` on a finite set `S` of tags and zero elsewhere give an `ℓ²` error
at most `#S · δ`. -/
theorem norm_le_card_mul_of_blocks_KC4 {κ : Type*} [Fintype κ] {V : κ → Type*}
    [∀ t, NormedAddCommGroup (V t)] (v : PiLp 2 V)
    (S : Finset κ) {δ : ℝ} (hδ : 0 ≤ δ) (h1 : ∀ t ∈ S, ‖v t‖ ≤ δ) (h0 : ∀ t, t ∉ S → v t = 0) :
    ‖v‖ ≤ (S.card : ℝ) * δ := by
  classical
  have hsq : ‖v‖ ^ 2 ≤ (S.card : ℝ) * δ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ t, ‖v t‖ ^ 2 ≤ ∑ t, (if t ∈ S then δ ^ 2 else 0) := by
          refine Finset.sum_le_sum fun t _ => ?_
          by_cases ht : t ∈ S
          · simp only [ht, ↓reduceIte]
            exact pow_le_pow_left₀ (norm_nonneg _) (h1 t ht) 2
          · simp only [ht, ↓reduceIte]
            rw [h0 t ht, norm_zero]
            norm_num
      _ = (S.card : ℝ) * δ ^ 2 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hc : (S.card : ℝ) * δ ^ 2 ≤ ((S.card : ℝ) * δ) ^ 2 := by
    have hn : (1 : ℝ) ≤ S.card ∨ S.card = 0 := by
      rcases Nat.eq_zero_or_pos S.card with h | h
      · exact Or.inr h
      · exact Or.inl (by exact_mod_cast h)
    rcases hn with hn | hn
    · have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
      calc (S.card : ℝ) * δ ^ 2 ≤ (S.card : ℝ) * (S.card : ℝ) * δ ^ 2 := by
            have : (S.card : ℝ) ≤ (S.card : ℝ) * (S.card : ℝ) := by nlinarith
            exact mul_le_mul_of_nonneg_right this hδ2
        _ = ((S.card : ℝ) * δ) ^ 2 := by ring
    · rw [hn]
      simp
  have h0' : 0 ≤ (S.card : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - (S.card : ℝ) * δ)]

end Compare

end DifferentialGeometry.Geometry.Collapse
