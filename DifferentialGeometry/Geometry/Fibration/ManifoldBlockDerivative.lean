import DifferentialGeometry.Geometry.Collapse.BlockMapDerivative
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# FC02 on a manifold: the derivative of a finite block map at a point

Blueprint `master207B.tex`, FC02 (`lem:fibration-active-derivative`, B:138), in the form CGP02
(B:3956) needs: the source is a manifold `M` and the derivative of the block map
`F = blockMap R ζ η : M → H` is measured by an arbitrary nonnegative size `ν` of the tangent vector
(for the actual map, `ν = √(g_x(v, v))`, the Riemannian norm). The tree's FC02
(`norm_fderiv_blockMap_le`) is on a normed source; this module proves the manifold version
pointwise, with `mvfderiv` (the manifold derivative with values in the target normed space).

* `hasMFDerivAt_block_LC`: one block `y ↦ ((R ζ) η, R ζ)` has derivative
  `blockDeriv (R x) (ζ x) (η x) dR dζ dη` (computed in the source chart).
* `norm_mvfderiv_block_apply_le`: if `R(x) ≥ 0`, `ζ(x) ∈ [0, 1]`, `‖η(x)‖ ≤ C`,
  `R(x)‖dη(v)‖ ≤ aν`, `R(x)|dζ(v)| ≤ bν` and `|dR(v)| ≤ lν`, the block's derivative at `v` has norm
  at most `(a + (C + 1)(b + l))ν`.
* `mvfderiv_blockMap_apply_apply`: the `i`-th component of `dF(v)` is the derivative of the `i`-th
  block (for `F` differentiable at `x`); `mvfderiv_block_eq_zero_of_notMem_tsupport`: blocks whose
  cutoff vanishes near `x` contribute nothing.
* `norm_mvfderiv_blockMap_apply_le` (**manifold FC02, general form**): if every ACTIVE block
  (`x ∈ supp ζ_i`) has derivative at most `K_i ν` at `v`, then
  `‖dF(v)‖ ≤ (Σ_{active} K_i²)^{1/2} ν`, independently of the number of blocks.
* `norm_mvfderiv_blockMap_apply_le_fc02` (**FC02's shape**): scale tag `(0, ρ)` with `|dρ(v)| ≤ Λν`,
  at most `N` active constant-radius blocks with budget `B`, one `E'` tag with budget `B_E`:
  `‖dF(v)‖ ≤ (Λ² + N B² + B_E²)^{1/2} ν`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology Manifold

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Block

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The value of `blockDeriv` on a vector. -/
theorem blockDeriv_apply_LC (r z : ℝ) (w : W) (dR dζ : E →L[ℝ] ℝ) (dη : E →L[ℝ] W) (v : E) :
    blockDeriv r z w dR dζ dη v =
      WithLp.toLp 2 ((r * z) • dη v + (r * dζ v + z * dR v) • w, r * dζ v + z * dR v) := by
  simp [blockDeriv, smul_eq_mul]

/-- **One block on a manifold**: `y ↦ ((R ζ)(y) η(y), (R ζ)(y))` has derivative
`blockDeriv (R x) (ζ x) (η x) dR dζ dη` at `x`. -/
theorem hasMFDerivAt_block_LC {R ζ : M → ℝ} {η : M → W} {x : M} {dR dζ : E →L[ℝ] ℝ}
    {dη : E →L[ℝ] W} (hR : HasMFDerivAt I 𝓘(ℝ, ℝ) R x dR)
    (hζ : HasMFDerivAt I 𝓘(ℝ, ℝ) ζ x dζ) (hη : HasMFDerivAt I 𝓘(ℝ, W) η x dη) :
    HasMFDerivAt I 𝓘(ℝ, WithLp 2 (W × ℝ))
      (fun y => WithLp.toLp 2 ((R y * ζ y) • η y, R y * ζ y)) x
      (blockDeriv (E := E) (R x) (ζ x) (η x) dR dζ dη) := by
  let e : (W × ℝ) →L[ℝ] WithLp 2 (W × ℝ) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ W ℝ).symm : (W × ℝ) →L[ℝ] WithLp 2 (W × ℝ))
  refine ⟨?_, ?_⟩
  · have hm : ContinuousAt (fun y => R y * ζ y) x := hR.1.mul hζ.1
    exact e.continuous.continuousAt.comp ((hm.smul hη.1).prodMk hm)
  · have h1 := hR.2
    have h2 := hζ.2
    have h3 := hη.2
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp] at h1 h2 h3 ⊢
    have hx : (extChartAt I x).symm (extChartAt I x x) = x := extChartAt_to_inv x
    have hm := h1.mul h2
    have hv := hm.smul h3
    have hp := e.hasFDerivAt.comp_hasFDerivWithinAt (extChartAt I x x) (hv.prodMk hm)
    convert hp using 1
    · funext y
      rfl
    · refine ContinuousLinearMap.ext fun v => ?_
      simp only [Pi.mul_apply, Function.comp_apply, hx]
      rfl

/-- `mvfderiv` on a vector is `mfderiv` on it (the identification of the model tangent space). -/
theorem mvfderiv_apply_LC {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : M → F)
    (x : M) (v : TangentSpace I x) : mvfderiv I f x v = mfderiv I 𝓘(ℝ, F) f x v :=
  rfl

omit [InnerProductSpace ℝ W] in
/-- The norm of a pair in `W ⊕₂ ℝ` is at most the sum of the norms. -/
theorem norm_toLp_prod_le_LC (w : W) (t : ℝ) :
    ‖(WithLp.toLp 2 (w, t) : WithLp 2 (W × ℝ))‖ ≤ ‖w‖ + |t| := by
  rw [WithLp.prod_norm_eq_of_L2, Real.sqrt_le_left (by positivity)]
  have h1 : (WithLp.toLp 2 (w, t) : WithLp 2 (W × ℝ)).fst = w := rfl
  have h2 : (WithLp.toLp 2 (w, t) : WithLp 2 (W × ℝ)).snd = t := rfl
  rw [h1, h2, Real.norm_eq_abs]
  nlinarith [norm_nonneg w, abs_nonneg t, sq_abs t]

/-- **One block's derivative bound.** With `R(x) ≥ 0`, `ζ(x) ∈ [0, 1]`, `‖η(x)‖ ≤ C`,
`R(x)‖dη(v)‖ ≤ aν`, `R(x)|dζ(v)| ≤ bν` and `|dR(v)| ≤ lν`, the derivative of the block at `v` has
norm at most `(a + (C + 1)(b + l))ν`. -/
theorem norm_mvfderiv_block_apply_le {R ζ : M → ℝ} {η : M → W} {x : M}
    (hR : MDifferentiableAt I 𝓘(ℝ, ℝ) R x) (hζ : MDifferentiableAt I 𝓘(ℝ, ℝ) ζ x)
    (hη : MDifferentiableAt I 𝓘(ℝ, W) η x) (v : TangentSpace I x) {ν a b C l : ℝ}
    (hr : 0 ≤ R x) (hz : ζ x ∈ Icc (0 : ℝ) 1) (hC : ‖η x‖ ≤ C)
    (ha : R x * ‖mvfderiv I η x v‖ ≤ a * ν) (hb : R x * |mvfderiv I ζ x v| ≤ b * ν)
    (hl : |mvfderiv I R x v| ≤ l * ν) :
    ‖mvfderiv I (fun y => WithLp.toLp 2 ((R y * ζ y) • η y, R y * ζ y)) x v‖ ≤
      (a + (C + 1) * (b + l)) * ν := by
  have hD := (hasMFDerivAt_block_LC hR.hasMFDerivAt hζ.hasMFDerivAt hη.hasMFDerivAt).mfderiv
  have hval : mvfderiv I (fun y => WithLp.toLp 2 ((R y * ζ y) • η y, R y * ζ y)) x v =
      WithLp.toLp 2 ((R x * ζ x) • mvfderiv I η x v +
        (R x * mvfderiv I ζ x v + ζ x * mvfderiv I R x v) • η x,
        R x * mvfderiv I ζ x v + ζ x * mvfderiv I R x v) := by
    rw [mvfderiv_apply_LC, hD]
    rfl
  rw [hval]
  set p : W := mvfderiv I η x v with hp
  set s : ℝ := mvfderiv I ζ x v with hs
  set t : ℝ := mvfderiv I R x v with ht
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  have hm : |R x * s + ζ x * t| ≤ b * ν + l * ν := by
    have h1 : |R x * s| ≤ b * ν := by rw [abs_mul, abs_of_nonneg hr]; exact hb
    have h2 : |ζ x * t| ≤ l * ν := by
      rw [abs_mul, abs_of_nonneg hz.1]
      calc ζ x * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hz.2 (abs_nonneg t)
        _ ≤ l * ν := by rw [one_mul]; exact hl
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hfirst : ‖(R x * ζ x) • p + (R x * s + ζ x * t) • η x‖ ≤ a * ν + C * (b * ν + l * ν) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr hz.1)]
      calc R x * ζ x * ‖p‖ ≤ R x * 1 * ‖p‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz.2 hr) (norm_nonneg p)
        _ ≤ a * ν := by rw [mul_one]; exact ha
    · rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul hC hm (abs_nonneg _) hC0
  calc ‖(WithLp.toLp 2 ((R x * ζ x) • p + (R x * s + ζ x * t) • η x, R x * s + ζ x * t) :
          WithLp 2 (W × ℝ))‖
      ≤ ‖(R x * ζ x) • p + (R x * s + ζ x * t) • η x‖ + |R x * s + ζ x * t| :=
        norm_toLp_prod_le_LC _ _
    _ ≤ a * ν + C * (b * ν + l * ν) + (b * ν + l * ν) := add_le_add hfirst hm
    _ = (a + (C + 1) * (b + l)) * ν := by ring

end Block

section Assembly

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

/-- The `i`-th component of the derivative of a differentiable block map is the derivative of the
`i`-th block. -/
theorem mvfderiv_blockMap_apply_apply {R ζ : κ → M → ℝ} {η : ∀ i, M → V i} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, BlockSpace V) (blockMap R ζ η) x) (v : TangentSpace I x)
    (i : κ) :
    mvfderiv I (blockMap R ζ η) x v i = mvfderiv I (fun y => blockMap R ζ η y i) x v := by
  let π : BlockSpace V →L[ℝ] WithLp 2 (V i × ℝ) := PiLp.proj 2 (fun i => WithLp 2 (V i × ℝ)) i
  have h := π.hasFDerivAt.hasMFDerivAt.comp x hF.hasMFDerivAt
  have hfun : (π ∘ blockMap R ζ η) = fun y => blockMap R ζ η y i := rfl
  rw [hfun] at h
  rw [mvfderiv_apply_LC, mvfderiv_apply_LC, h.mfderiv]
  rfl

omit [Fintype κ] in
/-- A block whose cutoff vanishes near `x` has zero derivative there. -/
theorem mvfderiv_block_eq_zero_of_notMem_tsupport {R ζ : κ → M → ℝ} {η : ∀ i, M → V i}
    {x : M} {i : κ} (hx : x ∉ tsupport (ζ i)) (v : TangentSpace I x) :
    mvfderiv I (fun y => blockMap R ζ η y i) x v = 0 := by
  have hev : (fun y => blockMap R ζ η y i) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport (ζ i)).isOpen_compl.mem_nhds hx] with y hy
    rw [blockMap_apply, image_eq_zero_of_notMem_tsupport hy, mul_zero, zero_smul]
    rfl
  have h := (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, WithLp 2 (V i × ℝ)))
    (0 : WithLp 2 (V i × ℝ)) x).congr_of_eventuallyEq hev
  rw [mvfderiv_apply_LC, h.mfderiv]
  rfl

open Classical in
/-- **FC02 on a manifold, general form.** If `F = blockMap R ζ η` is differentiable at `x` and every
ACTIVE block (`x ∈ supp ζ_i`) has derivative at most `K_i ν` at `v`, then
`‖dF(v)‖ ≤ (Σ_{active} K_i²)^{1/2} ν`. -/
theorem norm_mvfderiv_blockMap_apply_le {R ζ : κ → M → ℝ} {η : ∀ i, M → V i} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, BlockSpace V) (blockMap R ζ η) x) (v : TangentSpace I x)
    {ν : ℝ} (hν : 0 ≤ ν) {K : κ → ℝ}
    (hK : ∀ i, x ∈ tsupport (ζ i) →
      ‖mvfderiv I (fun y => blockMap R ζ η y i) x v‖ ≤ K i * ν) :
    ‖mvfderiv I (blockMap R ζ η) x v‖ ≤
      Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => x ∈ tsupport (ζ i)), K i ^ 2) * ν := by
  have hcomp : ∀ i, ‖mvfderiv I (blockMap R ζ η) x v i‖ ^ 2 ≤
      if x ∈ tsupport (ζ i) then K i ^ 2 * ν ^ 2 else 0 := by
    intro i
    rw [mvfderiv_blockMap_apply_apply hF v i]
    split_ifs with hi
    · have h := hK i hi
      have h0 : 0 ≤ K i * ν := (norm_nonneg _).trans h
      calc ‖mvfderiv I (fun y => blockMap R ζ η y i) x v‖ ^ 2 ≤ (K i * ν) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = K i ^ 2 * ν ^ 2 := by ring
    · rw [mvfderiv_block_eq_zero_of_notMem_tsupport hi v, norm_zero]
      norm_num
  have hsum : ∑ i, (if x ∈ tsupport (ζ i) then K i ^ 2 * ν ^ 2 else 0) =
      (∑ i ∈ Finset.univ.filter (fun i => x ∈ tsupport (ζ i)), K i ^ 2) * ν ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_mul]
  have hS0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => x ∈ tsupport (ζ i)), K i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [PiLp.norm_eq_of_L2]
  calc Real.sqrt (∑ i, ‖mvfderiv I (blockMap R ζ η) x v i‖ ^ 2)
      ≤ Real.sqrt (∑ i, (if x ∈ tsupport (ζ i) then K i ^ 2 * ν ^ 2 else 0)) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hcomp i)
    _ = Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => x ∈ tsupport (ζ i)), K i ^ 2) * ν := by
        rw [hsum, Real.sqrt_mul hS0, Real.sqrt_sq hν]

open Classical in
/-- **FC02 on a manifold, in FC02's shape**: the scale tag `iρ` contributes `Λν`, at most `N`
active constant-radius blocks contribute `Bν` each, the `E'` tag `iE` contributes `B_E ν`; then
`‖dF(v)‖ ≤ (Λ² + N B² + B_E²)^{1/2} ν`, independently of the number of blocks. -/
theorem norm_mvfderiv_blockMap_apply_le_fc02 {R ζ : κ → M → ℝ} {η : ∀ i, M → V i} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, BlockSpace V) (blockMap R ζ η) x) (v : TangentSpace I x)
    {ν : ℝ} (hν : 0 ≤ ν) (iρ iE : κ) (hρE : iρ ≠ iE) {Λ B BE : ℝ}
    (hscale : ‖mvfderiv I (fun y => blockMap R ζ η y iρ) x v‖ ≤ Λ * ν)
    (hEblock : x ∈ tsupport (ζ iE) →
      ‖mvfderiv I (fun y => blockMap R ζ η y iE) x v‖ ≤ BE * ν)
    (hblock : ∀ i, i ≠ iρ → i ≠ iE → x ∈ tsupport (ζ i) →
      ‖mvfderiv I (fun y => blockMap R ζ η y i) x v‖ ≤ B * ν)
    {N : ℕ} (hcount : {i | i ≠ iρ ∧ i ≠ iE ∧ x ∈ tsupport (ζ i)}.ncard ≤ N) :
    ‖mvfderiv I (blockMap R ζ η) x v‖ ≤ Real.sqrt (Λ ^ 2 + N * B ^ 2 + BE ^ 2) * ν := by
  let K : κ → ℝ := fun i => if i = iρ then Λ else if i = iE then BE else B
  have hK : ∀ i, x ∈ tsupport (ζ i) →
      ‖mvfderiv I (fun y => blockMap R ζ η y i) x v‖ ≤ K i * ν := by
    intro i hi
    by_cases h1 : i = iρ
    · subst h1
      simpa [K] using hscale
    by_cases h2 : i = iE
    · subst h2
      simpa [K, h1] using hEblock hi
    simpa [K, h1, h2] using hblock i h1 h2 hi
  have hmain := norm_mvfderiv_blockMap_apply_le hF v hν hK
  set S := Finset.univ.filter (fun i => x ∈ tsupport (ζ i)) with hS
  have hpt : ∀ i, K i ^ 2 = (if i = iρ then Λ ^ 2 else 0) + (if i = iE then BE ^ 2 else 0) +
      (if i ≠ iρ ∧ i ≠ iE then B ^ 2 else 0) := by
    intro i
    by_cases h1 : i = iρ
    · subst h1
      simp [K, hρE]
    by_cases h2 : i = iE
    · subst h2
      simp [K, h1]
    simp [K, h1, h2]
  have h1 : ∑ i ∈ S, (if i = iρ then Λ ^ 2 else 0) ≤ Λ ^ 2 := by
    rw [Finset.sum_ite_eq' S iρ (fun _ => Λ ^ 2)]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg Λ
  have h2 : ∑ i ∈ S, (if i = iE then BE ^ 2 else 0) ≤ BE ^ 2 := by
    rw [Finset.sum_ite_eq' S iE (fun _ => BE ^ 2)]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg BE
  have hcard : (S.filter (fun i => i ≠ iρ ∧ i ≠ iE)).card ≤ N := by
    have hset : ((S.filter (fun i => i ≠ iρ ∧ i ≠ iE) : Finset κ) : Set κ) =
        {i | i ≠ iρ ∧ i ≠ iE ∧ x ∈ tsupport (ζ i)} := by
      ext i
      simp only [hS, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        mem_ofPred_eq]
      tauto
    rw [← Set.ncard_coe_finset, hset]
    exact hcount
  have h3 : ∑ i ∈ S, (if i ≠ iρ ∧ i ≠ iE then B ^ 2 else 0) ≤ N * B ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg B)
  have hsum : ∑ i ∈ S, K i ^ 2 ≤ Λ ^ 2 + N * B ^ 2 + BE ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith
  exact hmain.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsum) hν)

end Assembly

end DifferentialGeometry.Geometry.Collapse
