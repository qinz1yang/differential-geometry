import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# CGP06's retained-coordinate bound from the plane's (PP) data and the rough graph (kernel)

Blueprint `master207B.tex`, CGP06 (`lem:fibration-retained-coordinate-graph`, B:4130–4174, its
sufficient criterion: `T = DΦ_i`, `πT = I`, `‖T‖ ≤ Ω`, `‖D(R_i⁻¹π_jF) − T Dη_i‖ ≤ e`, normal error
`ν`, `ν + e ≤ 1/(48Ω)` ⇒ `|πv| ≥ |v|/(2Ω)` on `L_x`); external draft 59 §4 third step (D59-5);
review 66 §5.1 (the plane, its normal error and rank at the SAME preimage).

The plane `L` of the chain comes with (PP) at every preimage `q` of `x` (FC27's tests, TCP06): the
projected derivative `P = Π_L ∘ D` is ONTO `L`, `‖D v − P v‖ ≤ e N(v)` and `N(v) ≤ 2‖P v‖` for `v`
orthogonal (for the source metric) to `ker P`. This module derives CGP06's bound from these data
and the rough-graph derivative error, by bounded preimages instead of a right inverse of `Dη`:

* `exists_bounded_preimage_BAS`: a surjection `P : V → F` (finite dimensions) with the lower bound
  on the `B`-orthogonal complement of its kernel (`B` positive definite) has, for every `y`, a
  preimage `w` with `N(w) ≤ 2‖y‖`.
* `retained_coordinate_lower_bound_of_pp_BAS`: if every `v ∈ L` has `w` with `‖D w − v‖ ≤ 2e‖v‖`,
  `N(w) ≤ 2‖v‖`, and `‖D w − T(Dη w)‖ ≤ e N(w)`, `π T = I`, `‖T y‖ ≤ Ω‖y‖`, `‖π‖ ≤ 1`, and
  `8e(1 + Ω) ≤ 1`, then `‖v‖ ≤ 2Ω‖π v‖` on `L` (CGP06's `m = 1/(2Ω)`).
-/

set_option autoImplicit false

noncomputable section

open Function

namespace DifferentialGeometry.Analysis

/-- **Bounded preimages from the orthogonal lower bound.** `P : V → F` onto (finite dimensions),
`B` a positive definite bilinear form on `V`, and `N(v) ≤ 2‖P v‖` for every `v` that is
`B`-orthogonal to `ker P`. Then every `y` has a preimage `w` with `N(w) ≤ 2‖y‖`. -/
theorem exists_bounded_preimage_BAS {V F : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hBpos : ∀ v, v ≠ 0 → 0 < B v v) (P : V →ₗ[ℝ] F)
    (hP : Surjective P) (N : V → ℝ) (hlow : ∀ v, (∀ k, P k = 0 → B v k = 0) → N v ≤ 2 * ‖P v‖) :
    ∀ y, ∃ w, P w = y ∧ N w ≤ 2 * ‖y‖ := by
  -- the `B`-orthogonal complement of `ker P`
  let Φ : V →ₗ[ℝ] Module.Dual ℝ (LinearMap.ker P) :=
    { toFun := fun v => (B v).domRestrict (LinearMap.ker P)
      map_add' := fun v w => by ext k; simp
      map_smul' := fun c v => by ext k; simp }
  set W : Submodule ℝ V := LinearMap.ker Φ with hW
  have hWmem : ∀ v ∈ W, ∀ k, P k = 0 → B v k = 0 := by
    intro v hv k hk
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hv) ⟨k, hk⟩
    simpa [Φ] using h
  -- `P` is injective on `W`
  have hinj : Injective (P.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hPv : P v = 0 := hv
    have hB0 : B (v : V) v = 0 := hWmem v v.2 v hPv
    by_contra hne
    have hne' : (v : V) ≠ 0 := fun h => hne (Subtype.ext h)
    exact absurd hB0 (hBpos v hne').ne'
  -- dimension count: `dim W ≥ dim V - dim ker P = dim F`
  have h1 := Φ.finrank_range_add_finrank_ker
  have h2 := P.finrank_range_add_finrank_ker
  have h3 : Module.finrank ℝ (LinearMap.range Φ) ≤ Module.finrank ℝ (LinearMap.ker P) :=
    (Submodule.finrank_le _).trans (Subspace.dual_finrank_eq).le
  have hrange : LinearMap.range P = ⊤ := LinearMap.range_eq_top.mpr hP
  have h4 : Module.finrank ℝ (LinearMap.range P) = Module.finrank ℝ F := by
    rw [hrange, finrank_top]
  have hWdim : Module.finrank ℝ F ≤ Module.finrank ℝ W := by
    change Module.finrank ℝ F ≤ Module.finrank ℝ (LinearMap.ker Φ)
    omega
  have hrr : LinearMap.range (P.domRestrict W) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
    rw [LinearMap.finrank_range_of_inj hinj]
    exact hWdim
  intro y
  obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp hrr y
  refine ⟨w, hw, ?_⟩
  have h := hlow w (hWmem w w.2)
  rwa [show P w = y from hw] at h

/-- **CGP06's bound from (PP) and the rough graph.** If every `v ∈ L` has `w` with
`‖D w − v‖ ≤ 2e‖v‖` and `N(w) ≤ 2‖v‖`, the rough-graph derivative error `‖D w − T(Dη w)‖ ≤ eN(w)`
holds for every `w`, `π T = I`, `‖T y‖ ≤ Ω‖y‖`, `‖π‖ ≤ 1` and `8e(1 + Ω) ≤ 1`, then
`‖v‖ ≤ 2Ω‖π v‖` for `v ∈ L`. -/
theorem retained_coordinate_lower_bound_of_pp_BAS {V H E : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : V → ℝ) (π : H →L[ℝ] E) (hπ : ‖π‖ ≤ 1) (T : E →L[ℝ] H) (hπT : ∀ y, π (T y) = y)
    {Ω e : ℝ} (hT : ∀ y, ‖T y‖ ≤ Ω * ‖y‖) (D : V →ₗ[ℝ] H) (Dη : V →ₗ[ℝ] E)
    (hrough : ∀ w, ‖D w - T (Dη w)‖ ≤ e * N w) (L : Set H)
    (hpre : ∀ v ∈ L, ∃ w, ‖D w - v‖ ≤ 2 * e * ‖v‖ ∧ N w ≤ 2 * ‖v‖)
    (hΩ : 1 ≤ Ω) (he : 0 ≤ e) (hsmall : 8 * e * (1 + Ω) ≤ 1) :
    ∀ v ∈ L, ‖v‖ ≤ 2 * Ω * ‖π v‖ := by
  intro v hv
  obtain ⟨w, hw1, hw2⟩ := hpre v hv
  have hvn := norm_nonneg v
  -- `v` is `4e‖v‖`-close to `T(Dη w)`
  have hclose : ‖v - T (Dη w)‖ ≤ 4 * e * ‖v‖ := by
    have h1 : ‖v - T (Dη w)‖ ≤ ‖D w - v‖ + ‖D w - T (Dη w)‖ := by
      have := norm_sub_le (D w - T (Dη w)) (D w - v)
      rw [show D w - T (Dη w) - (D w - v) = v - T (Dη w) by abel] at this
      linarith
    have h2 : e * N w ≤ e * (2 * ‖v‖) := mul_le_mul_of_nonneg_left hw2 he
    linarith [hrough w]
  -- lower bound on `Dη w`
  have hDη : (1 - 4 * e) * ‖v‖ ≤ Ω * ‖Dη w‖ := by
    have h1 : ‖v‖ ≤ ‖T (Dη w)‖ + ‖v - T (Dη w)‖ := by
      have := norm_add_le (T (Dη w)) (v - T (Dη w))
      rwa [add_sub_cancel] at this
    linarith [hT (Dη w)]
  -- the retained coordinate
  have hπv : ‖Dη w‖ - 4 * e * ‖v‖ ≤ ‖π v‖ := by
    have h1 : π v = Dη w + π (v - T (Dη w)) := by
      rw [map_sub, hπT]
      abel
    have h2 : ‖π (v - T (Dη w))‖ ≤ 4 * e * ‖v‖ :=
      (π.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hπ).trans hclose)
    have h3 : ‖Dη w‖ ≤ ‖π v‖ + ‖π (v - T (Dη w))‖ := by
      have := norm_sub_le (π v) (π (v - T (Dη w)))
      rwa [show π v - π (v - T (Dη w)) = Dη w by rw [h1]; abel] at this
    linarith
  have hΩ0 : 0 < Ω := by linarith
  have key : Ω * (‖Dη w‖ - 4 * e * ‖v‖) ≤ Ω * ‖π v‖ := mul_le_mul_of_nonneg_left hπv hΩ0.le
  nlinarith

end DifferentialGeometry.Analysis
