/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.CornerRounding.RoundedMin
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Corner rounding by a regularized minimum

A piece `P = {φ ≥ 0} ∩ {ψ ≥ 0}` of a manifold, cut out by two smooth functions, has corners along
`{φ = ψ = 0}`.  It is replaced by `{F ≥ 0}`, `F = roundedMin ε (φ, ψ)`, and its complementary side
`{φ ≤ 0} ∪ {ψ ≤ 0}` by `{F ≤ 0}`: one common smooth boundary `{F = 0}`.

* `hasMFDerivAt_roundedMin`, `mfderiv_roundedMin_eq`: the differential of `F` at `x` is that of
  the convex combination `(1 - t) φ + t ψ` with the frozen weight `t ∈ [0, 1]`.
* `mfderiv_roundedMin_ne_zero`: `0` is a regular value of `F` once the two faces are regular and
  no convex combination of `dφ, dψ` vanishes on the corner band `{φ, ψ ≥ 0, φ + ψ < δ}`,
  `3 ε ≤ δ`.
* set identities: the modification is confined to the band `{φ + ψ < 3 ε}` on both sides, and
  `F = min φ ψ` wherever `ε ≤ |φ - ψ|`.
* `exists_band_subset_of_isCompact`: independence on an open neighbourhood of a compact corner
  set gives such a band.
* fibre compatibility: `F` of functions pulled back along `π` is the pull back of `F`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold.CornerRounding

section Sets

variable {X : Type*} {φ ψ : X → ℝ} {ε : ℝ}

theorem roundedPiece_subset (hε : 0 < ε) :
    {x | 0 ≤ roundedMin ε (φ x) (ψ x)} ⊆ {x | 0 ≤ φ x ∧ 0 ≤ ψ x} :=
  fun _ hx => nonneg_of_roundedMin_nonneg hε hx

theorem diff_roundedPiece_subset (hε : 0 < ε) :
    {x | 0 ≤ φ x ∧ 0 ≤ ψ x} \ {x | 0 ≤ roundedMin ε (φ x) (ψ x)} ⊆
      {x | 0 ≤ φ x ∧ 0 ≤ ψ x ∧ φ x + ψ x < 3 * ε} := by
  rintro x ⟨⟨ha, hb⟩, hF⟩
  exact ⟨ha, hb, (band_of_roundedMin_neg hε ha hb (not_le.mp hF)).2⟩

theorem complement_subset_roundedComplement (hε : 0 < ε) :
    {x | φ x ≤ 0 ∨ ψ x ≤ 0} ⊆ {x | roundedMin ε (φ x) (ψ x) ≤ 0} :=
  fun _ hx => roundedMin_nonpos_of_nonpos hε hx

theorem roundedComplement_diff_subset (hε : 0 < ε) :
    {x | roundedMin ε (φ x) (ψ x) ≤ 0} \ {x | φ x ≤ 0 ∨ ψ x ≤ 0} ⊆
      {x | 0 < φ x ∧ 0 < ψ x ∧ φ x + ψ x < 3 * ε} := by
  rintro x ⟨hF, hx⟩
  have ha : 0 < φ x := not_le.mp fun h => hx (Or.inl h)
  have hb : 0 < ψ x := not_le.mp fun h => hx (Or.inr h)
  exact ⟨ha, hb, (band_of_roundedMin_nonpos hε ha hb hF).2⟩

/-- Off the diagonal band both faces are untouched: there the rounded function is the minimum. -/
theorem roundedMin_eq_min_off_band (hε : 0 < ε) {x : X} (hx : ε ≤ |φ x - ψ x|) :
    roundedMin ε (φ x) (ψ x) = min (φ x) (ψ x) :=
  roundedMin_eq_min hε hx

/-- Fibre compatibility: the rounded piece of pulled-back functions is the full preimage of the
rounded piece downstairs (so it is a union of whole fibres). -/
theorem roundedPiece_comp {Y : Type*} (φ₀ ψ₀ : Y → ℝ) (π : X → Y) (ε' : ℝ) :
    {x | 0 ≤ roundedMin ε' (φ₀ (π x)) (ψ₀ (π x))} =
      π ⁻¹' {y | 0 ≤ roundedMin ε' (φ₀ y) (ψ₀ y)} :=
  rfl

/-- Fibre compatibility of the common boundary. -/
theorem roundedBoundary_comp {Y : Type*} (φ₀ ψ₀ : Y → ℝ) (π : X → Y) (ε' : ℝ) :
    {x | roundedMin ε' (φ₀ (π x)) (ψ₀ (π x)) = 0} =
      π ⁻¹' {y | roundedMin ε' (φ₀ y) (ψ₀ y) = 0} :=
  rfl

/-- A compact corner set inside an open set `V` has a whole corner band inside `V`. -/
theorem exists_band_subset_of_isCompact [TopologicalSpace X] {K V : Set X}
    (hK : IsCompact K) (hV : IsOpen V) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hcorner : ∀ x ∈ K, φ x = 0 → ψ x = 0 → x ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, 0 ≤ φ x → 0 ≤ ψ x → φ x + ψ x < δ → x ∈ V := by
  let C : Set X := K ∩ (Vᶜ ∩ ({x | 0 ≤ φ x} ∩ {x | 0 ≤ ψ x}))
  have hC : IsCompact C := hK.inter_right (hV.isClosed_compl.inter
    ((isClosed_le continuous_const hφ).inter (isClosed_le continuous_const hψ)))
  rcases C.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x hx ha hb _ => ?_⟩
    by_contra hxV
    have hxC : x ∈ C := ⟨hx, hxV, ha, hb⟩
    rw [he] at hxC
    exact hxC
  · obtain ⟨y, hy, hmin⟩ := hC.exists_isMinOn hne (hφ.add hψ).continuousOn
    have hyK : y ∈ K := hy.1
    have hyV : y ∉ V := hy.2.1
    have hya : 0 ≤ φ y := hy.2.2.1
    have hyb : 0 ≤ ψ y := hy.2.2.2
    have hpos : 0 < φ y + ψ y := by
      by_contra hle
      have hle' := not_lt.mp hle
      exact hyV (hcorner y hyK (by linarith) (by linarith))
    refine ⟨φ y + ψ y, hpos, fun x hx ha hb hs => ?_⟩
    by_contra hxV
    have h := isMinOn_iff.mp hmin x ⟨hx, hxV, ha, hb⟩
    simp only [Pi.add_apply] at h
    linarith

end Sets

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem hasMFDerivAt_roundedMin {φ ψ : M → ℝ} {x : M} {φ' ψ' : TangentSpace I x →L[ℝ] ℝ}
    (hφ : HasMFDerivAt I 𝓘(ℝ, ℝ) φ x φ') (hψ : HasMFDerivAt I 𝓘(ℝ, ℝ) ψ x ψ') (ε : ℝ) :
    HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => roundedMin ε (φ y) (ψ y)) x
      ((1 - roundedMinWeight ε (φ x) (ψ x)) • φ' + roundedMinWeight ε (φ x) (ψ x) • ψ') := by
  have habs : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Real.smoothAbs ε) ((φ - ψ) x)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (deriv (Real.smoothAbs ε) (φ x - ψ x))) :=
    (((Real.smoothAbs.contDiff ε).differentiable (by simp) _).hasDerivAt).hasFDerivAt.hasMFDerivAt
  have hall := ((hφ.add hψ).sub (HasMFDerivAt.comp x habs (hφ.sub hψ))).const_smul (1 / 2 : ℝ)
  have hfun : (fun y => roundedMin ε (φ y) (ψ y)) =
      (1 / 2 : ℝ) • ((φ + ψ) - Real.smoothAbs ε ∘ (φ - ψ)) := by
    funext y
    simp only [roundedMin, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Function.comp_apply,
      smul_eq_mul]
    ring
  rw [hfun]
  refine hall.congr_mfderiv ?_
  ext v
  change (1 / 2 : ℝ) * (φ' v + ψ' v - (φ' v - ψ' v) * deriv (Real.smoothAbs ε) (φ x - ψ x)) =
    (1 - roundedMinWeight ε (φ x) (ψ x)) * φ' v + roundedMinWeight ε (φ x) (ψ x) * ψ' v
  rw [roundedMinWeight]
  ring

theorem mfderiv_roundedMin_eq {φ ψ : M → ℝ} {x : M} (hφ : MDifferentiableAt I 𝓘(ℝ, ℝ) φ x)
    (hψ : MDifferentiableAt I 𝓘(ℝ, ℝ) ψ x) (ε : ℝ) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => roundedMin ε (φ y) (ψ y)) x =
      mfderiv I 𝓘(ℝ, ℝ) (fun y => (1 - roundedMinWeight ε (φ x) (ψ x)) * φ y +
        roundedMinWeight ε (φ x) (ψ x) * ψ y) x := by
  have h1 := hasMFDerivAt_roundedMin hφ.hasMFDerivAt hψ.hasMFDerivAt ε
  have h2 := (hφ.hasMFDerivAt.const_smul (1 - roundedMinWeight ε (φ x) (ψ x))).add
    (hψ.hasMFDerivAt.const_smul (roundedMinWeight ε (φ x) (ψ x)))
  have hfun : (fun y => (1 - roundedMinWeight ε (φ x) (ψ x)) * φ y +
      roundedMinWeight ε (φ x) (ψ x) * ψ y) =
      (1 - roundedMinWeight ε (φ x) (ψ x)) • φ + roundedMinWeight ε (φ x) (ψ x) • ψ := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, h1.mfderiv, h2.mfderiv]

/-- Pointwise regularity of the rounded function at its zeros. -/
theorem mfderiv_roundedMin_ne_zero {φ ψ : M → ℝ} {x : M}
    (hφ : MDifferentiableAt I 𝓘(ℝ, ℝ) φ x) (hψ : MDifferentiableAt I 𝓘(ℝ, ℝ) ψ x)
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : 3 * ε ≤ δ)
    (hφreg : φ x = 0 → 0 ≤ ψ x → mfderiv I 𝓘(ℝ, ℝ) φ x ≠ 0)
    (hψreg : ψ x = 0 → 0 ≤ φ x → mfderiv I 𝓘(ℝ, ℝ) ψ x ≠ 0)
    (hband : 0 ≤ φ x → 0 ≤ ψ x → φ x + ψ x < δ → ∀ t ∈ Icc (0 : ℝ) 1,
      mfderiv I 𝓘(ℝ, ℝ) (fun y => (1 - t) * φ y + t * ψ y) x ≠ 0)
    (hzero : roundedMin ε (φ x) (ψ x) = 0) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => roundedMin ε (φ y) (ψ y)) x ≠ 0 := by
  rw [mfderiv_roundedMin_eq hφ hψ ε]
  rcases lt_or_ge |φ x - ψ x| ε with hab | hab
  · obtain ⟨ha, hb, hs⟩ := band_of_roundedMin_eq_zero hε hab hzero
    exact hband ha hb (by linarith) _ (roundedMinWeight_mem_Icc _ _ _)
  · have hmin := roundedMin_eq_min hε hab
    rw [hzero] at hmin
    rcases le_total (φ x) (ψ x) with hle | hle
    · rw [min_eq_left hle] at hmin
      have hgap : ε ≤ ψ x - φ x := by
        rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at hab
      rw [roundedMinWeight_eq_zero hε hgap]
      have hf : (fun y => (1 - 0) * φ y + 0 * ψ y) = φ := by
        funext y
        ring
      rw [hf]
      exact hφreg hmin.symm (by linarith)
    · rw [min_eq_right hle] at hmin
      have hgap : ε ≤ φ x - ψ x := by
        rwa [abs_of_nonneg (by linarith)] at hab
      rw [roundedMinWeight_eq_one hε hgap]
      have hf : (fun y => (1 - 1) * φ y + 1 * ψ y) = ψ := by
        funext y
        ring
      rw [hf]
      exact hψreg hmin.symm (by linarith)

theorem contMDiff_roundedMin {φ ψ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ) (ε : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => roundedMin ε (φ x) (ψ x)) :=
  (contDiff_roundedMin ε).comp_contMDiff (hφ.prodMk_space hψ)

/-- **Corner rounding by a regularized minimum.**  Regular faces and positive independence of the
two differentials on the corner band make `0` a regular value of `F = roundedMin ε (φ, ψ)` for
every `0 < ε ≤ δ / 3`; the rounded piece `{F ≥ 0}` and the rounded complementary side `{F ≤ 0}`
differ from `{φ ≥ 0, ψ ≥ 0}` and `{φ ≤ 0} ∪ {ψ ≤ 0}` only inside the band `{φ + ψ < 3 ε}`, and
`F = min φ ψ` wherever `ε ≤ |φ - ψ|`. -/
theorem roundedMin_corner_rounding
    {φ ψ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ) {δ : ℝ}
    (hφreg : ∀ x, φ x = 0 → 0 ≤ ψ x → mfderiv I 𝓘(ℝ, ℝ) φ x ≠ 0)
    (hψreg : ∀ x, ψ x = 0 → 0 ≤ φ x → mfderiv I 𝓘(ℝ, ℝ) ψ x ≠ 0)
    (hband : ∀ x, 0 ≤ φ x → 0 ≤ ψ x → φ x + ψ x < δ → ∀ t ∈ Icc (0 : ℝ) 1,
      mfderiv I 𝓘(ℝ, ℝ) (fun y => (1 - t) * φ y + t * ψ y) x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hεδ : 3 * ε ≤ δ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => roundedMin ε (φ x) (ψ x)) ∧
    (∀ x, roundedMin ε (φ x) (ψ x) = 0 →
      mfderiv I 𝓘(ℝ, ℝ) (fun y => roundedMin ε (φ y) (ψ y)) x ≠ 0) ∧
    {x | 0 ≤ roundedMin ε (φ x) (ψ x)} ⊆ {x | 0 ≤ φ x ∧ 0 ≤ ψ x} ∧
    {x | 0 ≤ φ x ∧ 0 ≤ ψ x} \ {x | 0 ≤ roundedMin ε (φ x) (ψ x)} ⊆
      {x | 0 ≤ φ x ∧ 0 ≤ ψ x ∧ φ x + ψ x < 3 * ε} ∧
    {x | φ x ≤ 0 ∨ ψ x ≤ 0} ⊆ {x | roundedMin ε (φ x) (ψ x) ≤ 0} ∧
    {x | roundedMin ε (φ x) (ψ x) ≤ 0} \ {x | φ x ≤ 0 ∨ ψ x ≤ 0} ⊆
      {x | 0 < φ x ∧ 0 < ψ x ∧ φ x + ψ x < 3 * ε} ∧
    (∀ x, ε ≤ |φ x - ψ x| → roundedMin ε (φ x) (ψ x) = min (φ x) (ψ x)) :=
  ⟨contMDiff_roundedMin hφ hψ ε,
    fun x hx => mfderiv_roundedMin_ne_zero ((hφ x).mdifferentiableAt (by simp))
      ((hψ x).mdifferentiableAt (by simp)) hε hεδ (hφreg x) (hψreg x) (hband x) hx,
    roundedPiece_subset hε, diff_roundedPiece_subset hε,
    complement_subset_roundedComplement hε, roundedComplement_diff_subset hε,
    fun _ hx => roundedMin_eq_min_off_band hε hx⟩

/-- Qualitative form on a compact manifold: positive independence on an open neighbourhood of the
corner set gives a threshold `ε₀` below which `0` is a regular value of the rounded function. -/
theorem exists_roundedMin_regular_of_compactSpace [CompactSpace M]
    {φ ψ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ)
    (hφreg : ∀ x, φ x = 0 → 0 ≤ ψ x → mfderiv I 𝓘(ℝ, ℝ) φ x ≠ 0)
    (hψreg : ∀ x, ψ x = 0 → 0 ≤ φ x → mfderiv I 𝓘(ℝ, ℝ) ψ x ≠ 0)
    {V : Set M} (hV : IsOpen V) (hcorner : ∀ x, φ x = 0 → ψ x = 0 → x ∈ V)
    (hind : ∀ x ∈ V, 0 ≤ φ x → 0 ≤ ψ x → ∀ t ∈ Icc (0 : ℝ) 1,
      mfderiv I 𝓘(ℝ, ℝ) (fun y => (1 - t) * φ y + t * ψ y) x ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ x, roundedMin ε (φ x) (ψ x) = 0 →
      mfderiv I 𝓘(ℝ, ℝ) (fun y => roundedMin ε (φ y) (ψ y)) x ≠ 0 := by
  obtain ⟨δ, hδ, hsub⟩ := exists_band_subset_of_isCompact isCompact_univ hV hφ.continuous
    hψ.continuous (fun x _ => hcorner x)
  refine ⟨δ / 3, by positivity, fun ε hε hεδ x hx => ?_⟩
  exact mfderiv_roundedMin_ne_zero ((hφ x).mdifferentiableAt (by simp))
    ((hψ x).mdifferentiableAt (by simp)) hε (by linarith) (hφreg x) (hψreg x)
    (fun ha hb hs => hind x (hsub x (mem_univ x) ha hb hs) ha hb) hx

end Manifold

end DifferentialGeometry.Topology.Manifold.CornerRounding
