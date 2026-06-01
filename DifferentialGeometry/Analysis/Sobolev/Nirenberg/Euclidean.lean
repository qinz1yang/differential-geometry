import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients

/-!
# Foundational machinery for second-order divergence-form operators on
Euclidean space

This module sets up the data structures, a priori coercivity bounds, and
auxiliary difference-quotient lemmas for the second-order divergence-form
operator on Euclidean space. The underlying goal is to support the
Nirenberg difference-quotient method for interior second-order regularity
of weak solutions of uniformly elliptic divergence-form equations.

## Setting

Given an open set `Ω : Set (EuclideanSpace ℝ (Fin d))`, smooth coefficient
functions `a : E → Matrix (Fin d) (Fin d) ℝ` (symmetric and uniformly
elliptic on `Ω`) and `c : E → ℝ`, the divergence-form operator is

  `L u(x) = -∂_i (a^{ij}(x) ∂_j u(x)) + c(x) u(x)`,

with associated bilinear form

  `B(u, v) := ∫_Ω (∑ i j, a^{ij} (∂_i u) (∂_j v)) + ∫_Ω c · u · v`.

A weak solution of `L u = f` on `Ω` is `u ∈ H¹(Ω)` such that
`B(u, v) = ⟨f, v⟩_{L²}` for every test function `v ∈ H¹_0(Ω)`.

## Main structures

* `SmoothEllipticBilinearForm d Ω`: smooth uniformly elliptic
  divergence-form data — matrix coefficient `a` (symmetric, smooth,
  coercive on `Ω`) and zeroth-order coefficient `c` (smooth).
* `SmoothEllipticBilinearForm.principalIntegrand`: the integrand
  `∑ i j, a^{ij} ∂_i u ∂_j v` of the principal part.
* `SmoothEllipticBilinearForm.bilin`: the associated bilinear form
  `B(u, v) = ∫_Ω (a^{ij} ∂_i u ∂_j v + c u v)`.
* `SmoothEllipticBilinearForm.IsSmoothWeakSolution`: smooth `u : E → ℝ`
  with `B(u, φ) = ∫ f · φ` for all `φ ∈ C^∞_c(Ω)`.
* `SmoothEllipticBilinearForm.gradientVec`: the gradient packaged as a
  vector in `EuclideanSpace ℝ (Fin d)`.

## Main results

* `SmoothEllipticBilinearForm.exists_cutoff`: a smooth cutoff
  `η ∈ C^∞_c(Ω')` equal to `1` on a given compact `K ⊆ Ω'`. Standard
  Mathlib cutoff re-exposed for use in interior regularity arguments.
* `SmoothEllipticBilinearForm.bounded_a_on_compact`,
  `bounded_c_on_compact`, `bounded_fderiv_a_on_compact`: smooth
  coefficients are uniformly bounded on every compact set, with explicit
  bounds for the coefficient values and their first derivatives.
* `diffQuot_bound_of_smooth_compactSupport`: a `C¹` function with compact
  support has all its difference quotients uniformly bounded by the same
  Lipschitz constant, independently of the step `h`.
* `SmoothEllipticBilinearForm.principalIntegrand_self_eq_inner`: the
  pointwise quadratic form of the principal integrand equals the standard
  inner-product action `⟪∇u, a · ∇u⟫`.
* `SmoothEllipticBilinearForm.principalIntegrand_self_ge`: pointwise
  ellipticity bound: `lam · ‖∇u(x)‖² ≤ ∑ a^{ij} ∂_i u ∂_j u` on `Ω`.
* `SmoothEllipticBilinearForm.bilin_integrand_self_ge`: the corresponding
  pointwise bound on the full bilinear-form integrand.
* `diffQuot_mul`, `diffQuot_coeff_apply`: the discrete product rule for
  difference quotients used to expand `D_h^k(a · ∂u)` into a principal
  piece plus a lower-order error.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
/-- A smooth function with compact support has all its difference quotients
uniformly bounded by a constant independent of `h`. This packages the
Lipschitz estimate for `C¹` functions with compact support and applies it
to bound the difference quotient. -/
theorem diffQuot_bound_of_smooth_compactSupport
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hf_supp : HasCompactSupport f)
    (i : Fin d) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ h : ℝ, ∀ x : E,
        |DifferentialGeometry.Analysis.Sobolev.diffQuot i h f x| ≤ L := by
  obtain ⟨L, hL_nn, hLip⟩ :=
    DifferentialGeometry.Analysis.Sobolev.lipschitz_of_contDiff_compactSupport
      (d := d) hf hf_supp
  refine ⟨L, hL_nn, fun h x => ?_⟩
  by_cases hh : h = 0
  · simp [DifferentialGeometry.Analysis.Sobolev.diffQuot, hh, hL_nn]
  · rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne (d := d) i hh f x]
    have hLip_apply :
        ‖f (x + h • EuclideanSpace.single i 1) - f x‖ ≤
          L * ‖x + h • EuclideanSpace.single i 1 - x‖ := hLip _ _
    have hsimp : x + h • EuclideanSpace.single i 1 - x =
        h • EuclideanSpace.single i 1 := by
      rw [add_sub_cancel_left]
    rw [hsimp] at hLip_apply
    have hsing_norm :
        ‖(EuclideanSpace.single i (1 : ℝ) : E)‖ = 1 := by simp
    have hnorm_smul :
        ‖h • EuclideanSpace.single i (1 : ℝ)‖ = |h| := by
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
    rw [hnorm_smul] at hLip_apply
    rw [abs_div]
    have habs_h : 0 < |h| := abs_pos.mpr hh
    rw [div_le_iff₀ habs_h]
    have h_lhs_norm :
        |f (x + h • EuclideanSpace.single i 1) - f x| =
          ‖f (x + h • EuclideanSpace.single i 1) - f x‖ :=
      (Real.norm_eq_abs _).symm
    rw [h_lhs_norm]
    exact hLip_apply

/-- A smooth uniformly elliptic divergence-form structure on an open set
`Ω : Set E`.

Carries:
- `a : E → Matrix (Fin d) (Fin d) ℝ` — the principal coefficient matrix,
  smooth and symmetric;
- `c : E → ℝ` — the zeroth-order coefficient, smooth;
- `lam, capLam : ℝ` — lower / upper ellipticity constants (`0 < lam ≤ capLam`).

Coercivity: `lam * ‖ξ‖² ≤ ⟪ξ, a x ξ⟫` for all `x ∈ Ω` and `ξ : E`.

The matrix-vector action uses the standard `EuclideanSpace` action
`matMulE` from the elliptic-coefficient layer. -/
structure SmoothEllipticBilinearForm
    (d : ℕ) [NeZero d] (Ω : Set (EuclideanSpace ℝ (Fin d))) where
  a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ
  c : EuclideanSpace ℝ (Fin d) → ℝ
  symm : ∀ x i j, a x i j = a x j i
  smooth_a : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => a x i j)
  smooth_c : ContDiff ℝ (⊤ : ℕ∞) c
  lam : ℝ
  capLam : ℝ
  hlam_pos : 0 < lam
  hlam_le_capLam : lam ≤ capLam
  coercive : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin d),
    lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (a x) ξ⟫_ℝ

namespace SmoothEllipticBilinearForm

/-- Componentwise smoothness of the coefficient matrix. -/
theorem contDiff_a {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => B.a x i j) :=
  B.smooth_a i j

/-- Continuity of each component of the coefficient matrix. -/
theorem continuous_a {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (i j : Fin d) :
    Continuous (fun x : E => B.a x i j) :=
  (B.smooth_a i j).continuous

/-- Continuity of the zeroth-order coefficient. -/
theorem continuous_c {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    Continuous B.c :=
  B.smooth_c.continuous

/-- Lower-ellipticity constant is nonnegative. -/
theorem lam_nonneg {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 ≤ B.lam := B.hlam_pos.le

/-- Upper-ellipticity constant is positive. -/
theorem capLam_pos {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 < B.capLam := lt_of_lt_of_le B.hlam_pos B.hlam_le_capLam

/-- Upper-ellipticity constant is nonnegative. -/
theorem capLam_nonneg {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 ≤ B.capLam := B.capLam_pos.le

/-- A smooth cutoff function: for any compact `K` contained in an open set
`Ω'`, there is `η ∈ C^∞(E)` with `0 ≤ η ≤ 1`, `η = 1` on `K`, and
`tsupport η ⊆ Ω'`. Re-derivation of the standard Mathlib cutoff for use
in this file, public so downstream code can apply it. -/
theorem exists_cutoff
    {K Ω' : Set E} (hK : IsCompact K) (hΩ' : IsOpen Ω') (hKΩ' : K ⊆ Ω') :
    ∃ η : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ K, η x = 1) ∧
      tsupport η ⊆ Ω' := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ' hKΩ'
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ E) (s := Metric.thickening δ K) (t := K)
      isOpen_thickening hK.isClosed (self_subset_thickening hδ_pos K) with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  refine ⟨η, contMDiff_iff_contDiff.mp hη_smooth, ?_, hη_range, ?_, ?_⟩
  · apply HasCompactSupport.intro' (K := Metric.cthickening δ K)
    · exact hK.cthickening (r := δ)
    · simpa using (isClosed_cthickening : IsClosed (Metric.cthickening δ K))
    · intro x hx
      have hxt : x ∉ tsupport η := by
        intro hxt
        have hx_closure : x ∈ closure (Metric.thickening δ K) := by
          rw [tsupport, hη_support] at hxt
          exact hxt
        exact hx ((Metric.closure_thickening_subset_cthickening δ K) hx_closure)
      exact image_eq_zero_of_notMem_tsupport hxt
  · intro x hx
    exact (hη_one_iff x).1 hx
  · rw [tsupport, hη_support]
    exact (Metric.closure_thickening_subset_cthickening δ K).trans hδΩ

/-- A smooth cutoff with a quantitative bound on its derivative.

Strengthening of `exists_cutoff`: in addition to existence of `η ∈ C^∞(E)`
with `0 ≤ η ≤ 1`, `η = 1` on `K`, and `tsupport η ⊆ Ω'`, we extract a finite
constant `N ≥ 0` such that `‖fderiv ℝ η x‖ ≤ N` for every `x : E`. The bound
arises from continuity of the Fréchet derivative on the compact `tsupport η`,
combined with the fact that `fderiv ℝ η = 0` outside `tsupport η`. -/
theorem exists_cutoff_with_fderiv_bound
    {K Ω' : Set E} (hK : IsCompact K) (hΩ' : IsOpen Ω') (hKΩ' : K ⊆ Ω') :
    ∃ η : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ K, η x = 1) ∧
      tsupport η ⊆ Ω' ∧
      ∃ N : ℝ, 0 ≤ N ∧ ∀ x : E, ‖fderiv ℝ η x‖ ≤ N := by
  obtain ⟨η, hη_cd, hη_supp, hη_range, hη_one, hη_tsupp⟩ :=
    exists_cutoff hK hΩ' hKΩ'
  refine ⟨η, hη_cd, hη_supp, hη_range, hη_one, hη_tsupp, ?_⟩
  have h_fderiv_cont : Continuous (fderiv ℝ η) :=
    hη_cd.continuous_fderiv (by simp)
  have h_norm_cont : Continuous (fun x : E => ‖fderiv ℝ η x‖) := h_fderiv_cont.norm
  have h_fderiv_cs : HasCompactSupport (fderiv ℝ η) := hη_supp.fderiv ℝ
  have h_norm_cs : HasCompactSupport (fun x : E => ‖fderiv ℝ η x‖) := by
    apply h_fderiv_cs.comp_left
    simp
  obtain ⟨N₀, hN₀⟩ := h_norm_cont.bddAbove_range_of_hasCompactSupport h_norm_cs
  refine ⟨max N₀ 0, le_max_right _ _, fun x => ?_⟩
  have h_le : ‖fderiv ℝ η x‖ ≤ N₀ := hN₀ ⟨x, rfl⟩
  exact h_le.trans (le_max_left _ _)

/-- The coefficient matrix is bounded on any compact set. -/
theorem bounded_a_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin d, ∀ x ∈ K, |B.a x i j| ≤ M := by
  classical
  have h_each : ∀ ij : Fin d × Fin d, ∃ Mij : ℝ, 0 ≤ Mij ∧
      ∀ x ∈ K, |B.a x ij.1 ij.2| ≤ Mij := by
    intro ij
    rcases hK.bddAbove_image (B.continuous_a ij.1 ij.2 |>.abs.continuousOn) with ⟨Mij, hMij⟩
    refine ⟨max Mij 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hMij (mem_image_of_mem _ hx)
    exact h.trans (le_max_left _ _)
  let pairBound : Fin d × Fin d → ℝ := fun ij => Classical.choose (h_each ij)
  have pairBound_nn : ∀ ij, 0 ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).1
  have pairBound_le : ∀ ij : Fin d × Fin d, ∀ x ∈ K,
      |B.a x ij.1 ij.2| ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).2
  let M : ℝ := ∑ ij : Fin d × Fin d, pairBound ij
  have hM_nn : 0 ≤ M := Finset.sum_nonneg (fun ij _ => pairBound_nn ij)
  refine ⟨M, hM_nn, fun i j x hx => ?_⟩
  have hsingle : pairBound (i, j) ≤ M := by
    refine Finset.single_le_sum (f := pairBound) (s := Finset.univ) ?_ (Finset.mem_univ (i, j))
    intro ij _
    exact pairBound_nn ij
  exact (pairBound_le (i, j) x hx).trans hsingle

/-- The zeroth-order coefficient is bounded on any compact set. -/
theorem bounded_c_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |B.c x| ≤ M := by
  rcases hK.bddAbove_image (B.continuous_c.abs.continuousOn) with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hM (mem_image_of_mem _ hx)
  exact h.trans (le_max_left _ _)

/-- The first partial derivative of each coefficient component is bounded on
any compact set. -/
theorem bounded_fderiv_a_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (k : Fin d) {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin d, ∀ x ∈ K,
      |(fderiv ℝ (fun x : E => B.a x i j) x) (EuclideanSpace.single k 1)| ≤ M := by
  classical
  have h_each : ∀ ij : Fin d × Fin d, ∃ Mij : ℝ, 0 ≤ Mij ∧
      ∀ x ∈ K, |(fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x)
        (EuclideanSpace.single k 1)| ≤ Mij := by
    intro ij
    have hcont : Continuous
        (fun x : E => (fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x)
          (EuclideanSpace.single k 1)) :=
      ((B.contDiff_a ij.1 ij.2).continuous_fderiv (by simp)).clm_apply continuous_const
    rcases hK.bddAbove_image hcont.abs.continuousOn with ⟨Mij, hMij⟩
    refine ⟨max Mij 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hMij (mem_image_of_mem _ hx)
    exact h.trans (le_max_left _ _)
  let pairBound : Fin d × Fin d → ℝ := fun ij => Classical.choose (h_each ij)
  have pairBound_nn : ∀ ij, 0 ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).1
  have pairBound_le : ∀ ij : Fin d × Fin d, ∀ x ∈ K,
      |(fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x) (EuclideanSpace.single k 1)| ≤
        pairBound ij :=
    fun ij => (Classical.choose_spec (h_each ij)).2
  let M : ℝ := ∑ ij : Fin d × Fin d, pairBound ij
  have hM_nn : 0 ≤ M := Finset.sum_nonneg (fun ij _ => pairBound_nn ij)
  refine ⟨M, hM_nn, fun i j x hx => ?_⟩
  have hsingle : pairBound (i, j) ≤ M := by
    refine Finset.single_le_sum (f := pairBound) (s := Finset.univ) ?_ (Finset.mem_univ (i, j))
    intro ij _
    exact pairBound_nn ij
  exact (pairBound_le (i, j) x hx).trans hsingle

/-- The pointwise integrand of the principal part of the bilinear form:
`∑ i, ∑ j, a^{ij}(x) (∂_i u)(x) (∂_j v)(x)`.

In coordinates, this is the dot product `⟪∇v(x), a(x) ∇u(x)⟫_ℝ`. -/
def principalIntegrand {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u v : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    B.a x i j *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
      ((fderiv ℝ v x) (EuclideanSpace.single j 1))

/-- The full bilinear form `B(u, v) = ∫_Ω (a^{ij} ∂_i u ∂_j v + c u v)`. -/
def bilin {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (u v : E → ℝ) : ℝ :=
  ∫ x in Ω, B.principalIntegrand u v x + B.c x * u x * v x

/-- A smooth function `u` is a smooth weak solution of `L u = f` on `Ω` if
`B(u, φ) = ∫_Ω f · φ` for every `φ ∈ C^∞_c(Ω)`. The "smooth" qualifier in
the name refers to `u`, not the equation: `u` is a strong (`C^∞`) solution
of the equation in the sense that the bilinear identity holds against test
functions, which by IBP is equivalent to the classical PDE for smooth `u`. -/
def IsSmoothWeakSolution {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u f : E → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u ∧
  ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    B.bilin u φ = ∫ x in Ω, f x * φ x

/-- Symmetry of the principal-integrand pairing: `∑ a^{ij} ∂_i u ∂_j v =
∑ a^{ij} ∂_i v ∂_j u`, using `a^{ij} = a^{ji}`. -/
theorem principalIntegrand_symm {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u v : E → ℝ) (x : E) :
    B.principalIntegrand u v x = B.principalIntegrand v u x := by
  classical
  unfold principalIntegrand
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [B.symm x j i]
  ring

/-- Continuity of the principal integrand for smooth `u, v`. -/
theorem continuous_principalIntegrand {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous (B.principalIntegrand u v) := by
  classical
  unfold principalIntegrand
  refine continuous_finset_sum _ ?_
  intro i _
  refine continuous_finset_sum _ ?_
  intro j _
  refine ((B.continuous_a i j).mul ?_).mul ?_
  · exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  · exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Continuity of the bilinear-form integrand for smooth `u, v`. -/
theorem continuous_bilin_integrand {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous (fun x => B.principalIntegrand u v x + B.c x * u x * v x) :=
  (B.continuous_principalIntegrand hu hv).add
    ((B.continuous_c.mul hu.continuous).mul hv.continuous)

/-- The gradient of `u` at `x`, packaged as a Euclidean vector
`∇u(x) ∈ EuclideanSpace ℝ (Fin d)`. -/
def gradientVec {Ω : Set E} (_B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) (x : E) : E :=
  WithLp.toLp 2 (fun i : Fin d => (fderiv ℝ u x) (EuclideanSpace.single i 1))

/-- The principal integrand at `x` with `u = v` equals
`⟪∇u(x), a(x) ∇u(x)⟫_ℝ` (using the standard `EuclideanSpace` inner product). -/
theorem principalIntegrand_self_eq_inner {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ) (x : E) :
    B.principalIntegrand u u x =
      ⟪B.gradientVec u x, DeGiorgi.matMulE (B.a x) (B.gradientVec u x)⟫_ℝ := by
  classical
  set ξ : E := B.gradientVec u x with hξ
  set V : Fin d → ℝ := fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1) with hV
  have h_inner :
      ⟪ξ, DeGiorgi.matMulE (B.a x) ξ⟫_ℝ =
        (fun j => (B.a x).mulVec V j) ⬝ᵥ V := by
    have hξofLp : ξ.ofLp = V := by simp [hξ, hV, gradientVec]
    have hmatofLp : (DeGiorgi.matMulE (B.a x) ξ).ofLp = (B.a x).mulVec V := by
      rw [DeGiorgi.matMulE_ofLp, hξofLp]
    change (DeGiorgi.matMulE (B.a x) ξ).ofLp ⬝ᵥ star ξ.ofLp =
      (fun j => (B.a x).mulVec V j) ⬝ᵥ V
    rw [hmatofLp, hξofLp]
    change (B.a x).mulVec V ⬝ᵥ (star V) = (B.a x).mulVec V ⬝ᵥ V
    rfl
  rw [h_inner]
  unfold principalIntegrand
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  change ∑ i, B.a x i j * V i * V j = (B.a x).mulVec V j * V j
  rw [show ((B.a x).mulVec V) j = ∑ i, B.a x j i * V i from rfl]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [B.symm x i j]

/-- The pointwise lower bound for `u = v` from ellipticity: at every `x ∈ Ω`,
`∑ i j, a^{ij} ∂_i u ∂_j u ≥ lam * ‖∇u(x)‖²`. -/
theorem principalIntegrand_self_ge {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ)
    {x : E} (hx : x ∈ Ω) :
    B.lam * ‖B.gradientVec u x‖ ^ 2 ≤
      B.principalIntegrand u u x := by
  rw [principalIntegrand_self_eq_inner]
  exact B.coercive x hx (B.gradientVec u x)

/-- The Euclidean norm squared of the gradient vector equals
`∑ i, (∂_i u(x))²`. -/
theorem gradientVec_norm_sq_eq_sum {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ) (x : E) :
    ‖B.gradientVec u x‖ ^ 2 =
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2 := by
  unfold gradientVec
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  change ‖(fderiv ℝ u x) (EuclideanSpace.single i 1)‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs]

/-- Integrand-level coercivity bound: at every `x ∈ Ω`, the bilinear-form
integrand `principal_integrand u u + c · u²` is bounded below by
`lam · ‖∇u‖² + c · u²`. -/
theorem bilin_integrand_self_ge {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ)
    {x : E} (hx : x ∈ Ω) :
    B.lam * ‖B.gradientVec u x‖ ^ 2 + B.c x * u x * u x ≤
      B.principalIntegrand u u x + B.c x * u x * u x := by
  have h := B.principalIntegrand_self_ge u hx
  linarith

end SmoothEllipticBilinearForm

omit [NeZero d] in
/-- The difference quotient of a product splits as
`D_h^k(f g) = (translate h f) (D_h^k g) + (D_h^k f) g`. -/
theorem diffQuot_mul
    (i : Fin d) (h : ℝ) (f g : E → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot i h (fun x => f x * g x) =
      fun x =>
        (DifferentialGeometry.Analysis.Sobolev.translate i h f x) *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot i h g x) +
          (DifferentialGeometry.Analysis.Sobolev.diffQuot i h f x) * g x := by
  ext x
  by_cases hh : h = 0
  · subst hh
    simp [DifferentialGeometry.Analysis.Sobolev.diffQuot,
          DifferentialGeometry.Analysis.Sobolev.translate]
  · simp only [DifferentialGeometry.Analysis.Sobolev.diffQuot,
               DifferentialGeometry.Analysis.Sobolev.translate, hh, ↓reduceIte]
    field_simp
    ring

omit [NeZero d] in
/-- Pointwise expansion of the difference quotient of `a · v`:
`D_h^k(a v) = (translate h a) (D_h^k v) + (D_h^k a) · v`. -/
theorem diffQuot_coeff_apply
    (k : Fin d) (h : ℝ) (a v : E → ℝ) (x : E) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h (fun y => a y * v y) x =
      DifferentialGeometry.Analysis.Sobolev.translate k h a x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h v x +
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h a x * v x := by
  have h := diffQuot_mul (d := d) k h a v
  exact congrArg (fun f : E → ℝ => f x) h

end DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
