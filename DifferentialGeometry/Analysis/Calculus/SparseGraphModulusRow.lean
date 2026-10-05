import DifferentialGeometry.Analysis.Calculus.SparseOrthogonalBlockApplicationsSol
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# FC24 as a row: a dimension-independent graph modulus

Blueprint `master207B.tex`, FC24 (`lem:fibration-graph-modulus`, B:1546–1565): "On a convex
Euclidean domain let a model be a finite orthogonal sum of blocks `b_j ∘ ℓ_j`, where `ℓ_j` is
affine, `‖Dℓ_j‖ ≤ L_j`, and `‖Db_j‖ ≤ A_j`, `‖D²b_j‖ ≤ B_j` globally. Suppose at most `N` blocks
have nonzero derivatives at each point and `A_jL_j ≤ A`, `B_jL_j² ≤ B`. Then its derivative and
Hessian norms are at most `√N A` and `√N B`, respectively. Its derivative is `√N B`-Lipschitz on
every contained line segment."

The Codex X81 kernels (`X81Sol.orthogonalBlocks_active_derivative_modulus`,
`Fibration.finite_packet_sparse_actual_modulus`) need an active set outside of which the FIRST AND
SECOND derivatives vanish (or the blocks are locally zero). The row only counts blocks with nonzero
FIRST derivative. On an OPEN domain this suffices:

* `card_first_or_second_ne_zero_le_RFC`: if at every point of an open `D` at most `N` of the `C²`
  blocks have nonzero derivative, then at every `x ∈ D` at most `N` blocks have nonzero first OR
  second derivative. Proof: the kernels of the nonzero Hessians are proper subspaces, so one
  direction `v` avoids all of them (`Submodule.exists_forall_notMem_of_forall_ne_top`); along
  `x + tv`, `t ≠ 0` small, every such block has nonzero derivative (`HasDerivAt.eventually_ne`),
  and so does every block with `Df_j(x) ≠ 0` (continuity).
* `affine_comp_derivative_bounds_RFC`: `‖D(b ∘ ℓ)‖ ≤ A_bL`, `‖D²(b ∘ ℓ)‖ ≤ B_bL²` for
  `ℓ = M(·) + c`, `‖M‖ ≤ L`.
* `fc24_kernel_RFC` (blocks with global bounds) and the ROW `fc24_row_RFC` (blocks `b_j ∘ ℓ_j`).

The row is stated on an OPEN convex domain. Remark (why "domain" must be read as open): on a
convex set with empty interior the statement fails — on the segment `{x₂ = 0} ⊂ ℝ²` the blocks
`b_j(t) = t²/2` composed with `ℓ_j(x) = x₂` have zero derivative everywhere on the segment (so
`N = 0` blocks count), while the Hessian of the orthogonal sum of `m ≥ 1` such blocks has norm
`√m > 0 = √N B`. Strengthening: `E` any real normed space.
Consumer: `fc24_row_unit_RFC` (all blocks share one profile bound and `‖M_j‖ ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace DifferentialGeometry.Analysis

section Count

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]

open Classical in
/-- **The first-derivative count controls the first-or-second-derivative count on an open set.**
If at every point of the open set `D` at most `N` of the `C²` maps `f_i` have nonzero derivative,
then at every `x ∈ D` at most `N` of them have nonzero first or second derivative. -/
theorem card_first_or_second_ne_zero_le_RFC {f : ∀ i, E → F i} (hf : ∀ i, ContDiff ℝ 2 (f i))
    {D : Set E} (hD : IsOpen D) {N : ℕ}
    (hN : ∀ y ∈ D, (Finset.univ.filter (fun i => fderiv ℝ (f i) y ≠ 0)).card ≤ N)
    {x : E} (hx : x ∈ D) :
    (Finset.univ.filter (fun i => fderiv ℝ (f i) x ≠ 0 ∨
      fderiv ℝ (fderiv ℝ (f i)) x ≠ 0)).card ≤ N := by
  set s := Finset.univ.filter (fun i => fderiv ℝ (f i) x ≠ 0 ∨
    fderiv ℝ (fderiv ℝ (f i)) x ≠ 0)
  -- one direction `v` on which every nonzero Hessian is nonzero
  let J := {i : ι // fderiv ℝ (fderiv ℝ (f i)) x ≠ 0}
  let p : J → Submodule ℝ E := fun i =>
    LinearMap.ker ((fderiv ℝ (fderiv ℝ (f i.1)) x : E →L[ℝ] (E →L[ℝ] F i.1)) :
      E →ₗ[ℝ] (E →L[ℝ] F i.1))
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i htop
    apply i.2
    ext v : 1
    have hv : v ∈ p i := htop ▸ Submodule.mem_top
    simpa [p] using hv
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hcont : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have h := (hline 0).continuousAt.tendsto
    simpa using h
  have hdiff : ∀ i, Differentiable ℝ (fderiv ℝ (f i)) := fun i =>
    ((hf i).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have hev : ∀ i ∈ s, ∀ᶠ t in 𝓝[≠] (0 : ℝ), fderiv ℝ (f i) (x + t • v) ≠ 0 := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with h1 | h2
    · have hc : ContinuousAt (fun t : ℝ => fderiv ℝ (f i) (x + t • v)) 0 := by
        have h := ((hdiff i).continuous.continuousAt (x := x)).comp_of_eq
          (hline 0).continuousAt (by simp)
        exact h
      have h0 : fderiv ℝ (f i) (x + (0 : ℝ) • v) ≠ 0 := by simpa using h1
      exact nhdsWithin_le_nhds (hc.eventually_ne h0)
    · have hd : HasDerivAt (fun t : ℝ => fderiv ℝ (f i) (x + t • v))
          (fderiv ℝ (fderiv ℝ (f i)) x v) 0 := by
        have h := ((hdiff i) x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) (by simp)
        exact h
      have hne : fderiv ℝ (fderiv ℝ (f i)) x v ≠ 0 := by
        have h := hv ⟨i, h2⟩
        simpa [p] using h
      exact hd.eventually_ne hne
  have hmem : ∀ᶠ t in 𝓝[≠] (0 : ℝ), x + t • v ∈ D :=
    nhdsWithin_le_nhds (hcont.eventually (hD.mem_nhds hx))
  have hall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), x + t • v ∈ D ∧
      ∀ i ∈ s, fderiv ℝ (f i) (x + t • v) ≠ 0 :=
    hmem.and ((Filter.eventually_all_finset s).2 hev)
  obtain ⟨t, htD, hts⟩ := hall.exists
  refine (Finset.card_le_card ?_).trans (hN _ htD)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hts i hi⟩

end Count

section Kernel

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]

open Classical in
/-- **FC24 kernel** (blocks with global bounds): on an open convex `D`, `C²` blocks `f_i` with
`‖Df_i‖ ≤ A`, `‖D²f_i‖ ≤ B` and at most `N` blocks with nonzero derivative at each point: the
orthogonal sum has `‖DΦ‖ ≤ √N A`, `‖D²Φ‖ ≤ √N B` on `D`, and `DΦ` is `√N B`-Lipschitz on `D`. -/
theorem fc24_kernel_RFC {f : ∀ i, E → F i} (hf : ∀ i, ContDiff ℝ 2 (f i)) {D : Set E}
    (hDo : IsOpen D) (hDc : Convex ℝ D) {N : ℕ}
    (hN : ∀ y ∈ D, (Finset.univ.filter (fun i => fderiv ℝ (f i) y ≠ 0)).card ≤ N)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ A) (hsecond : ∀ i y, ‖fderiv ℝ (fderiv ℝ (f i)) y‖ ≤ B) :
    (∀ x ∈ D, ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (N : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (N : ℝ) * B) ∧
      ∀ x ∈ D, ∀ y ∈ D,
        ‖fderiv ℝ (orthogonalBlocks f) y - fderiv ℝ (orthogonalBlocks f) x‖ ≤
          Real.sqrt (N : ℝ) * B * ‖y - x‖ := by
  refine X81Sol.orthogonalBlocks_active_derivative_modulus hf D hDc
    (fun x => Finset.univ.filter (fun i => fderiv ℝ (f i) x ≠ 0 ∨
      fderiv ℝ (fderiv ℝ (f i)) x ≠ 0))
    (fun x hx => card_first_or_second_ne_zero_le_RFC hf hDo hN hx) hA hB
    (fun x _ i _ => hfirst i x) (fun x _ i _ => hsecond i x) (fun x _ i hi => ?_)
    (fun x _ i hi => ?_)
  · by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl h⟩)
  · by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr h⟩)

end Kernel

section Affine

variable {E W G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Derivative bounds of a block composed with an affine map** `ℓ = M(·) + c`, `‖M‖ ≤ L`:
`‖D(b ∘ ℓ)‖ ≤ A_b L` and `‖D²(b ∘ ℓ)‖ ≤ B_b L²` from global bounds `‖Db‖ ≤ A_b`, `‖D²b‖ ≤ B_b`. -/
theorem affine_comp_derivative_bounds_RFC (b : W → G) (hb : ContDiff ℝ 2 b) (M : E →L[ℝ] W)
    (c : W) {Ab Bb L : ℝ} (hA : ∀ z, ‖fderiv ℝ b z‖ ≤ Ab)
    (hB : ∀ z, ‖fderiv ℝ (fderiv ℝ b) z‖ ≤ Bb) (hM : ‖M‖ ≤ L) (y : E) :
    ‖fderiv ℝ (fun z => b (M z + c)) y‖ ≤ Ab * L ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => b (M z + c))) y‖ ≤ Bb * L ^ 2 := by
  have hL : 0 ≤ L := (norm_nonneg M).trans hM
  have hAb : 0 ≤ Ab := (norm_nonneg _).trans (hA 0)
  have hBb : 0 ≤ Bb := (norm_nonneg _).trans (hB 0)
  have hℓ : ∀ z, HasFDerivAt (fun z => M z + c) M z := fun z => M.hasFDerivAt.add_const c
  have hbd := hb.differentiable (by norm_num)
  have hbdd : Differentiable ℝ (fderiv ℝ b) :=
    (hb.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  let R : (W →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) := (ContinuousLinearMap.compL ℝ E W G).flip M
  have hD : fderiv ℝ (fun z => b (M z + c)) = fun z => R (fderiv ℝ b (M z + c)) := by
    funext z
    exact ((hbd _).hasFDerivAt.comp z (hℓ z)).fderiv
  have hR : ‖R‖ ≤ L := by
    have h1 : ‖R‖ ≤ ‖(ContinuousLinearMap.compL ℝ E W G).flip‖ * ‖M‖ :=
      ((ContinuousLinearMap.compL ℝ E W G).flip).le_opNorm M
    rw [ContinuousLinearMap.opNorm_flip] at h1
    have h2 := ContinuousLinearMap.norm_compL_le ℝ E W G
    calc ‖R‖ ≤ ‖ContinuousLinearMap.compL ℝ E W G‖ * ‖M‖ := h1
      _ ≤ 1 * L := mul_le_mul h2 hM (norm_nonneg M) zero_le_one
      _ = L := one_mul L
  refine ⟨?_, ?_⟩
  · rw [hD]
    change ‖(fderiv ℝ b (M y + c)).comp M‖ ≤ Ab * L
    exact ((fderiv ℝ b (M y + c)).opNorm_comp_le M).trans
      (mul_le_mul (hA _) hM (norm_nonneg M) hAb)
  · have hDD : HasFDerivAt (fun z => R (fderiv ℝ b (M z + c)))
        (R.comp ((fderiv ℝ (fderiv ℝ b) (M y + c)).comp M)) y :=
      R.hasFDerivAt.comp y ((hbdd _).hasFDerivAt.comp y (hℓ y))
    rw [hD, hDD.fderiv]
    calc ‖R.comp ((fderiv ℝ (fderiv ℝ b) (M y + c)).comp M)‖
        ≤ ‖R‖ * (‖fderiv ℝ (fderiv ℝ b) (M y + c)‖ * ‖M‖) :=
          (R.opNorm_comp_le _).trans
            (mul_le_mul_of_nonneg_left ((fderiv ℝ (fderiv ℝ b) (M y + c)).opNorm_comp_le M)
              (norm_nonneg R))
      _ ≤ L * (Bb * L) :=
          mul_le_mul hR (mul_le_mul (hB _) hM (norm_nonneg M) hBb)
            (mul_nonneg (norm_nonneg _) (norm_nonneg M)) hL
      _ = Bb * L ^ 2 := by ring

end Affine

section Row

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  {W F : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]

open Classical in
/-- **FC24** (`lem:fibration-graph-modulus`, B:1546). On an open convex domain `D`, let the model
be the orthogonal sum of the blocks `b_j ∘ ℓ_j`, `ℓ_j = M_j(·) + c_j` affine with `‖M_j‖ ≤ L_j`,
`b_j` of class `C²` with `‖Db_j‖ ≤ A_j`, `‖D²b_j‖ ≤ B_j` globally, `A_jL_j ≤ A`, `B_jL_j² ≤ B`
(`A, B ≥ 0`), and suppose at most `N` blocks have nonzero derivative at each point of `D`. Then
on `D` the derivative and Hessian norms of the model are at most `√N A` and `√N B`, and its
derivative is `√N B`-Lipschitz on `D` (on every segment, `D` being convex). -/
theorem fc24_row_RFC (b : ∀ i, W i → F i) (M : ∀ i, E →L[ℝ] W i) (c : ∀ i, W i)
    {Ab Bb L : ι → ℝ} {A B : ℝ} {N : ℕ} {D : Set E}
    (hb : ∀ i, ContDiff ℝ 2 (b i)) (hAb : ∀ i z, ‖fderiv ℝ (b i) z‖ ≤ Ab i)
    (hBb : ∀ i z, ‖fderiv ℝ (fderiv ℝ (b i)) z‖ ≤ Bb i) (hM : ∀ i, ‖M i‖ ≤ L i)
    (hAL : ∀ i, Ab i * L i ≤ A) (hBL : ∀ i, Bb i * L i ^ 2 ≤ B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hN : ∀ x ∈ D, (Finset.univ.filter
      (fun i => fderiv ℝ (fun y => b i (M i y + c i)) x ≠ 0)).card ≤ N) :
    (∀ x ∈ D, ‖fderiv ℝ (orthogonalBlocks (fun i y => b i (M i y + c i))) x‖ ≤
        Real.sqrt (N : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks (fun i y => b i (M i y + c i)))) x‖ ≤
        Real.sqrt (N : ℝ) * B) ∧
      ∀ x ∈ D, ∀ y ∈ D,
        ‖fderiv ℝ (orthogonalBlocks (fun i y => b i (M i y + c i))) y -
            fderiv ℝ (orthogonalBlocks (fun i y => b i (M i y + c i))) x‖ ≤
          Real.sqrt (N : ℝ) * B * ‖y - x‖ := by
  have hsm : ∀ i, ContDiff ℝ 2 (fun y => b i (M i y + c i)) := fun i =>
    (hb i).comp ((M i).contDiff.add contDiff_const)
  exact fc24_kernel_RFC hsm hDo hDc hN hA hB
    (fun i y => ((affine_comp_derivative_bounds_RFC (b i) (hb i) (M i) (c i) (hAb i) (hBb i)
      (hM i) y).1).trans (hAL i))
    (fun i y => ((affine_comp_derivative_bounds_RFC (b i) (hb i) (M i) (c i) (hAb i) (hBb i)
      (hM i) y).2).trans (hBL i))

open Classical in
/-- **Consumer**: FC24 when every block has the same profile bounds `A_b, B_b ≥ 0` and its
affine part has `‖M_j‖ ≤ 1` (`L_j = 1`): the model's derivative and Hessian are at most
`√N A_b` and `√N B_b` on `D`. -/
theorem fc24_row_unit_RFC (b : ∀ i, W i → F i) (M : ∀ i, E →L[ℝ] W i) (c : ∀ i, W i)
    {Ab Bb : ℝ} {N : ℕ} {D : Set E} (hb : ∀ i, ContDiff ℝ 2 (b i))
    (hAb : ∀ i z, ‖fderiv ℝ (b i) z‖ ≤ Ab) (hBb : ∀ i z, ‖fderiv ℝ (fderiv ℝ (b i)) z‖ ≤ Bb)
    (hM : ∀ i, ‖M i‖ ≤ 1) (hA : 0 ≤ Ab) (hB : 0 ≤ Bb) (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hN : ∀ x ∈ D, (Finset.univ.filter
      (fun i => fderiv ℝ (fun y => b i (M i y + c i)) x ≠ 0)).card ≤ N) (x : E) (hx : x ∈ D) :
    ‖fderiv ℝ (orthogonalBlocks (fun i y => b i (M i y + c i))) x‖ ≤ Real.sqrt (N : ℝ) * Ab ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks (fun i y => b i (M i y + c i)))) x‖ ≤
        Real.sqrt (N : ℝ) * Bb :=
  (fc24_row_RFC b M c (Ab := fun _ => Ab) (Bb := fun _ => Bb) (L := fun _ => 1) hb hAb hBb hM
    (fun _ => (mul_one Ab).le) (fun _ => by simp) hA hB hDo hDc hN).1 x hx

end Row

end DifferentialGeometry.Analysis
