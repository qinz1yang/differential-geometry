import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank of a stage derivative from the plane's (PP) comparison (GAF02 BASES, G6 kernels)

Blueprint `master207B.tex`, GAF02 (B:5797–5870) step 1 as organised by external draft 59 §4 and
review 66 (D66-7: "original rank + same-plane normal error + `Da_j` + CHOICE margin"). At a point
`p` of a stage plateau, the derivative of the stage chart `a_j ∘ π_st ∘ g_st` is compared with the
plane's (PP) data at the same preimage:

* `D0` — the rescaled ORIGINAL derivative `(ρ_i)⁻¹ D(π_st 𝓔⁰)(p)`; its projection `π_L ∘ D0` onto
  the plane `L` is onto, with normal error `e`, lower bound `1/2` on the `Bf`-orthogonal complement
  of its kernel, upper bound `Cu`;
* `B` — the rescaled stage-input derivative `(ρ_i)⁻¹ D(π_st g_st)(p)`, `δ`-close to `D0`;
* `Q` — the derivative `Da(z)` of the chart map, `Ξ`-close to `π_L`.

`rank_ge_of_pp_comparison_BAS` (circle / slim form): `Q ∘ B` has rank at least `dim L` when
`δ + Ξ(Cu + e + δ) < 1/2`. `ne_zero_of_unit_pp_comparison_BAS` (edge form: one unit vector `w₀`):
`Q (B w₀) ≠ 0` under the same margin.

Both are proved by the same estimate: for `w` in the test space,
`‖Q B w‖ ≥ ‖π_L D0 w‖ − ‖π_L (B w − D0 w)‖ − ‖(Q − π_L) B w‖ ≥ (1/2 − δ − Ξ(Cu + e + δ)) N(w)`.

Strengthening of the frozen (b1): the positivity of `Bf` and the signs of `e`, `δ` are not used
(the `Bf`-annihilator of the kernel has dimension `≥ dim L` for any bilinear form; injectivity of
`Q ∘ B` on it comes from the estimate). The verbatim frozen form is kept as an `example`.
-/

set_option autoImplicit false

noncomputable section

open Function

namespace DifferentialGeometry.Analysis

/-- The comparison estimate behind both rank kernels: if `‖π_L D0 w‖ ≥ a`, `‖D0 w − π_L D0 w‖ ≤ b`,
`‖π_L D0 w‖ ≤ c`, `‖B w − D0 w‖ ≤ d` and `‖Q − π_L‖ ≤ Ξ` (`Ξ ≥ 0`), then
`a − d − Ξ(c + b + d) ≤ ‖Q (B w)‖`. -/
theorem pp_comparison_lower_BASP {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (L : Submodule ℝ H)
    [L.HasOrthogonalProjection] (D0 B : V →ₗ[ℝ] H) (Q : H →L[ℝ] H) {a b c d Ξ : ℝ} (w : V)
    (ha : a ≤ ‖L.starProjection (D0 w)‖) (hb : ‖D0 w - L.starProjection (D0 w)‖ ≤ b)
    (hc : ‖L.starProjection (D0 w)‖ ≤ c) (hd : ‖B w - D0 w‖ ≤ d)
    (hQ : ‖Q - L.starProjection‖ ≤ Ξ) (hΞ : 0 ≤ Ξ) :
    a - d - Ξ * (c + b + d) ≤ ‖Q (B w)‖ := by
  set p := L.starProjection (D0 w) with hp
  -- `‖B w‖ ≤ c + b + d`
  have hBw : ‖B w‖ ≤ c + b + d := by
    have h1 : ‖B w‖ ≤ ‖D0 w‖ + ‖B w - D0 w‖ := by
      have := norm_add_le (D0 w) (B w - D0 w)
      rwa [add_sub_cancel] at this
    have h2 : ‖D0 w‖ ≤ ‖p‖ + ‖D0 w - p‖ := by
      have := norm_add_le p (D0 w - p)
      rwa [add_sub_cancel] at this
    linarith
  have hQB : ‖(Q - L.starProjection) (B w)‖ ≤ Ξ * (c + b + d) :=
    ((Q - L.starProjection).le_of_opNorm_le hQ (B w)).trans
      (mul_le_mul_of_nonneg_left hBw hΞ)
  have hπ : ‖L.starProjection (B w - D0 w)‖ ≤ d :=
    (L.norm_starProjection_apply_le _).trans hd
  -- `Q (B w) = p + π_L (B w − D0 w) + (Q − π_L)(B w)`
  have hsplit : p = Q (B w) - L.starProjection (B w - D0 w) - (Q - L.starProjection) (B w) := by
    rw [hp, map_sub, sub_apply]
    abel
  have hs1 := norm_sub_le (Q (B w) - L.starProjection (B w - D0 w)) ((Q - L.starProjection) (B w))
  have hs2 := norm_sub_le (Q (B w)) (L.starProjection (B w - D0 w))
  rw [← hsplit] at hs1
  linarith

/-- **(b1) Rank from the (PP) comparison** (draft 59 §4 step 1, D66-7: "original rank + same-plane
normal error + Da_j + CHOICE margin"). `D0` = the rescaled original derivative at a preimage
(`(ρ_i)⁻¹ D(π_st𝓔⁰)(p)`), with the plane's (PP) data (onto `L`, normal error `e`, lower bound `1/2`
on the `Bf`-orthogonal complement of the kernel, upper bound `Cu`); `B` = the rescaled stage-input
derivative (`(ρ_i)⁻¹ D(π_st g_st)(p)`), `δ`-close to `D0`; `Q` = `Da(z)`, `Ξ`-close to `π_L`. Under
`δ + Ξ(Cu + e + δ) < 1/2`, `Q ∘ B` has rank at least `dim L`.

Strengthening of the frozen statement: `Bf` need not be positive definite and `e`, `δ` need not be
nonnegative (the verbatim form follows as the `example` below). -/
theorem rank_ge_of_pp_comparison_BAS {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (L : Submodule ℝ H) (Bf : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (N : V → ℝ) (hNpos : ∀ v, v ≠ 0 → 0 < N v) (D0 B : V →ₗ[ℝ] H) (Q : H →L[ℝ] H)
    {e δ Ξ Cu : ℝ}
    (hsurj : Surjective fun v => L.orthogonalProjectionOnto (D0 v))
    (hnormal : ∀ v, ‖D0 v - (L.orthogonalProjectionOnto (D0 v) : H)‖ ≤ e * N v)
    (hlow : ∀ v, (∀ k, L.orthogonalProjectionOnto (D0 k) = 0 → Bf v k = 0) →
      1 / 2 * N v ≤ ‖L.orthogonalProjectionOnto (D0 v)‖)
    (hup : ∀ v, ‖L.orthogonalProjectionOnto (D0 v)‖ ≤ Cu * N v)
    (hB : ∀ v, ‖B v - D0 v‖ ≤ δ * N v) (hQ : ‖Q - L.starProjection‖ ≤ Ξ)
    (hΞ : 0 ≤ Ξ) (hsmall : δ + Ξ * (Cu + e + δ) < 1 / 2) :
    Module.finrank ℝ L ≤ Module.finrank ℝ (LinearMap.range ((Q : H →ₗ[ℝ] H) ∘ₗ B)) := by
  -- the projected original derivative `P = π_L ∘ D0 : V → L`
  set P : V →ₗ[ℝ] L := (L.orthogonalProjectionOnto : H →ₗ[ℝ] L) ∘ₗ D0 with hPdef
  have hPapp : ∀ v, P v = L.orthogonalProjectionOnto (D0 v) := fun v => rfl
  -- the `Bf`-annihilator `W` of `ker P`
  let Φ : V →ₗ[ℝ] Module.Dual ℝ (LinearMap.ker P) :=
    { toFun := fun v => (Bf v).domRestrict (LinearMap.ker P)
      map_add' := fun v w => by ext k; simp
      map_smul' := fun c v => by ext k; simp }
  set W : Submodule ℝ V := LinearMap.ker Φ with hW
  have hWmem : ∀ v ∈ W, ∀ k, L.orthogonalProjectionOnto (D0 k) = 0 → Bf v k = 0 := by
    intro v hv k hk
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hv) ⟨k, hk⟩
    simpa [Φ] using h
  -- the comparison estimate on `W`
  set m : ℝ := 1 / 2 - (δ + Ξ * (Cu + e + δ)) with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hest : ∀ w ∈ W, m * N w ≤ ‖Q (B w)‖ := by
    intro w hw
    have hl : 1 / 2 * N w ≤ ‖L.starProjection (D0 w)‖ := hlow w (hWmem w hw)
    have hn : ‖D0 w - L.starProjection (D0 w)‖ ≤ e * N w := hnormal w
    have hu : ‖L.starProjection (D0 w)‖ ≤ Cu * N w := hup w
    have h := pp_comparison_lower_BASP L D0 B Q w hl hn hu (hB w) hQ hΞ
    have hexp : 1 / 2 * N w - δ * N w - Ξ * (Cu * N w + e * N w + δ * N w) = m * N w := by
      rw [hm]; ring
    linarith
  -- `Q ∘ B` is injective on `W`
  have hinj : Injective (((Q : H →ₗ[ℝ] H) ∘ₗ B).domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv0 : Q (B (v : V)) = 0 := hv
    by_contra hne
    have hne' : (v : V) ≠ 0 := fun h => hne (Subtype.ext h)
    have h1 := hest v v.2
    rw [hv0, norm_zero] at h1
    have h2 := mul_pos hm0 (hNpos v hne')
    linarith
  -- dimension count: `dim L ≤ dim W ≤ rank (Q ∘ B)`
  have h1 := Φ.finrank_range_add_finrank_ker
  have h2 := P.finrank_range_add_finrank_ker
  have h3 : Module.finrank ℝ (LinearMap.range Φ) ≤ Module.finrank ℝ (LinearMap.ker P) :=
    (Submodule.finrank_le _).trans (Subspace.dual_finrank_eq).le
  have hrange : LinearMap.range P = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h4 : Module.finrank ℝ (LinearMap.range P) = Module.finrank ℝ L := by
    rw [hrange, finrank_top]
  have hWdim : Module.finrank ℝ L ≤ Module.finrank ℝ W := by
    change Module.finrank ℝ L ≤ Module.finrank ℝ (LinearMap.ker Φ)
    omega
  calc Module.finrank ℝ L ≤ Module.finrank ℝ W := hWdim
    _ = Module.finrank ℝ (LinearMap.range (((Q : H →ₗ[ℝ] H) ∘ₗ B).domRestrict W)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank ℝ (LinearMap.range ((Q : H →ₗ[ℝ] H) ∘ₗ B)) :=
      Submodule.finrank_mono (LinearMap.range_domRestrict_le_range _ _)

/-- The frozen (b1) statement, verbatim (positive definite `Bf`, `0 ≤ e`, `0 ≤ δ`). -/
example {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (L : Submodule ℝ H) (Bf : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (_hBpos : ∀ v, v ≠ 0 → 0 < Bf v v)
    (N : V → ℝ) (hNpos : ∀ v, v ≠ 0 → 0 < N v) (D0 B : V →ₗ[ℝ] H) (Q : H →L[ℝ] H)
    {e δ Ξ Cu : ℝ}
    (hsurj : Surjective fun v => L.orthogonalProjectionOnto (D0 v))
    (hnormal : ∀ v, ‖D0 v - (L.orthogonalProjectionOnto (D0 v) : H)‖ ≤ e * N v)
    (hlow : ∀ v, (∀ k, L.orthogonalProjectionOnto (D0 k) = 0 → Bf v k = 0) →
      1 / 2 * N v ≤ ‖L.orthogonalProjectionOnto (D0 v)‖)
    (hup : ∀ v, ‖L.orthogonalProjectionOnto (D0 v)‖ ≤ Cu * N v)
    (hB : ∀ v, ‖B v - D0 v‖ ≤ δ * N v) (hQ : ‖Q - L.starProjection‖ ≤ Ξ)
    (_he : 0 ≤ e) (_hδ : 0 ≤ δ) (hΞ : 0 ≤ Ξ) (hsmall : δ + Ξ * (Cu + e + δ) < 1 / 2) :
    Module.finrank ℝ L ≤ Module.finrank ℝ (LinearMap.range ((Q : H →ₗ[ℝ] H) ∘ₗ B)) :=
  rank_ge_of_pp_comparison_BAS L Bf N hNpos D0 B Q hsurj hnormal hlow hup hB hQ hΞ hsmall

/-- **(b2) Rank one from the edge's unit-vector (PP)** (test1's form: a unit vector `w₀` with
`‖π_L D0 w₀‖ ≥ 1/2`, strict normal error `< e`, upper bound `Cu`). -/
theorem ne_zero_of_unit_pp_comparison_BAS {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (L : Submodule ℝ H) (D0 B : V →ₗ[ℝ] H) (Q : H →L[ℝ] H) {e δ Ξ Cu : ℝ} (w₀ : V)
    (hw₀ : 1 / 2 ≤ ‖L.starProjection (D0 w₀)‖) (hnormal : ‖D0 w₀ - L.starProjection (D0 w₀)‖ < e)
    (hup : ‖L.starProjection (D0 w₀)‖ ≤ Cu) (hB : ‖B w₀ - D0 w₀‖ ≤ δ)
    (hQ : ‖Q - L.starProjection‖ ≤ Ξ) (hΞ : 0 ≤ Ξ) (hsmall : δ + Ξ * (Cu + e + δ) < 1 / 2) :
    Q (B w₀) ≠ 0 := by
  intro h0
  have h := pp_comparison_lower_BASP L D0 B Q w₀ hw₀ hnormal.le hup hB hQ hΞ
  rw [h0, norm_zero] at h
  linarith

end DifferentialGeometry.Analysis
