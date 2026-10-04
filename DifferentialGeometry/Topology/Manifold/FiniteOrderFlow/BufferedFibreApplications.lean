import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.BufferedFibreStability

/-!
# Consumers of the fibre-stability theorems (LFR03, LC82)

* `lfr03_exists_isotopy_point_fibre`: the case of a point `X = {c}` (no side boundary), with
  transversality stated as surjectivity of `D f_t` along `f_t⁻¹ c`. This is the form used by the
  zero-fibre consumers LFR20 (A:26494) and LC85 (A:30968).
* `exists_smooth_isotopy_sublevel_interval`: an explicit family on `ℝ` whose preimages are manifolds
  with nonempty boundary: `f_t x = 1 + t - x²`, `X = [0, ∞)` (pure sublevel, `G = Fin 0 → ℝ`).
  LC82 gives a compactly supported smooth isotopy of `ℝ` carrying `{x² ≤ 1}` onto `{x² ≤ 2}` and
  `{x² = 1}` onto `{x² = 2}`. All hypotheses of `lc82_exists_smooth_isotopy_fibre` are verified.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.ODE

section PointFibre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [SigmaCompactSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']

/-- **LFR03 for fibres over a point.** Let `2 ≤ r`, let `F` be jointly `C^r` on `[0, 1] × M` with
values in a finite-dimensional space `E'`, and let `c : E'`. If `D f_t` is surjective at every
point of `f_t⁻¹ c`, `t ∈ [0, 1]`, and all these fibres lie in a compact `Q` and in an open `N`,
then a jointly `C^{r-1}` isotopy `Φ`, `Φ 0 = id`, the identity off a compact `K ⊆ N`, carries
`f_0⁻¹ c` onto `f_{σ t}⁻¹ c` (`σ = Real.smoothTransition`), in particular onto `f_1⁻¹ c` at
`t = 1`. -/
theorem lfr03_exists_isotopy_point_fibre {r : ℕ} (hr : 2 ≤ r)
    {F : ℝ × M → E'} (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    (c : E')
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) = c →
      Surjective (mfderiv I 𝓘(ℝ, E') (fun y => F (t, y)) x))
    {Q : Set M} (hQ : IsCompact Q) (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) = c → x ∈ Q)
    {N : Set M} (hN : IsOpen N) (hNsub : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) = c → x ∈ N) :
    ∃ (K : Set M) (Φ : ℝ → M ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮I, I⟯ M),
      IsCompact K ∧ K ⊆ N ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ((r - 1 : ℕ) : WithTop ℕ∞) (fun q : ℝ × M => Φ q.1 q.2) ∧
      Φ 0 = Diffeomorph.refl I M ((r - 1 : ℕ) : WithTop ℕ∞) ∧
      (∀ t x, x ∉ K → Φ t x = x) ∧
      (∀ t, Φ t '' {x | F (0, x) = c} = {x | F (Real.smoothTransition t, x) = c}) ∧
      Φ 1 '' {x | F (0, x) = c} = {x | F (1, x) = c} := by
  have hmem : ∀ y : E', y ∈ {y : E' | y - c = 0 ∧ (0 : ℝ) ≤ 1} ↔ y = c := fun y => by
    simp only [mem_ofPred_eq, sub_eq_zero, zero_le_one, and_true]
  have hset : ∀ s : ℝ, {x : M | F (s, x) ∈ {y : E' | y - c = 0 ∧ (0 : ℝ) ≤ 1}} =
      {x | F (s, x) = c} := fun s => by
    ext x
    exact hmem _
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : r ≠ 0 := by omega
    exact_mod_cast this
  have htrans' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ {y : E' | y - c = 0 ∧ (0 : ℝ) ≤ 1} →
      Surjective (mfderiv I 𝓘(ℝ, E') (fun y => F (t, y) - c) x) := by
    intro t ht x hx
    have hslice : ContMDiff I 𝓘(ℝ, E') r (fun y => F (t, y)) :=
      hF.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ => ⟨ht, mem_univ _⟩)
    have hd := ((hslice.mdifferentiable hr0 x).hasMFDerivAt.sub (hasMFDerivAt_const c x)).mfderiv
    have he : mfderiv I 𝓘(ℝ, E') (fun y => F (t, y) - c) x =
        mfderiv I 𝓘(ℝ, E') (fun y => F (t, y)) x := by
      rw [show (fun y => F (t, y) - c) = (fun y => F (t, y)) - (fun _ => c) from rfl, hd]
      exact sub_zero _
    rw [he]
    exact htrans t ht x ((hmem _).1 hx)
  obtain ⟨K, Φ, hK, hKN, hΦ, h0, hoff, himg, -, h1, -⟩ :=
    lfr03_exists_isotopy_fibre (G := E') (φ := fun y => y - c) (β := fun _ => (1 : ℝ))
      (X := {y : E' | y - c = 0 ∧ (0 : ℝ) ≤ 1}) (Xb := {y : E' | y - c = 0 ∧ (1 : ℝ) = 0})
      hr hF (contDiff_id.sub contDiff_const) contDiff_const rfl rfl htrans'
      (fun _ _ _ hx => absurd hx.2 one_ne_zero) hQ
      (fun t ht x hx => hencl t ht x ((hmem _).1 hx)) hN
      (fun t ht x hx => hNsub t ht x ((hmem _).1 hx))
  refine ⟨K, Φ, hK, hKN, hΦ, h0, hoff, fun t => ?_, ?_⟩
  · rw [← hset, ← hset]
    exact himg t
  · rw [← hset, ← hset]
    exact h1

end PointFibre

section Interval

/-- The time-dependent family `f_t x = 1 + t - x²` on `ℝ`. -/
theorem contMDiff_one_add_fst_sub_snd_sq :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × ℝ => 1 + q.1 - q.2 ^ 2) := by
  have hcd : ContDiff ℝ ∞ (fun q : ℝ × ℝ => 1 + q.1 - q.2 ^ 2) :=
    (contDiff_const.add contDiff_fst).sub (contDiff_snd.pow 2)
  exact hcd.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)

/-- **An explicit moving manifold with boundary (consumer of LC82).** The preimages of `[0, ∞)`
under `f_t x = 1 + t - x²` are the intervals `{x² ≤ 1 + t}` with boundary `{x² = 1 + t}`; LC82
gives a compactly supported jointly smooth isotopy of `ℝ` by smooth diffeomorphisms with
`Φ 0 = id`, carrying `{x² ≤ 1}` onto `{x² ≤ 2}` and `{x² = 1}` onto `{x² = 2}`. -/
theorem exists_smooth_isotopy_sublevel_interval :
    ∃ Φ : ℝ → ℝ ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × ℝ => Φ q.1 q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞ ∧
      (∃ K : Set ℝ, IsCompact K ∧ ∀ t x, x ∉ K → Φ t x = x) ∧
      Φ 1 '' {x : ℝ | x ^ 2 ≤ 1} = {x | x ^ 2 ≤ 2} ∧
      Φ 1 '' {x : ℝ | x ^ 2 = 1} = {x | x ^ 2 = 2} := by
  have htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      (1 + t - x ^ 2) ∈ {y : ℝ | (fun _ : ℝ => (0 : Fin 0 → ℝ)) y = 0 ∧ 0 ≤ id y} →
      Surjective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 0 → ℝ)
        (fun y : ℝ => (fun _ : ℝ => (0 : Fin 0 → ℝ)) (1 + t - y ^ 2)) x) := by
    intro t _ x _ z
    exact ⟨0, Subsingleton.elim (α := Fin 0 → ℝ) _ _⟩
  have htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      (1 + t - x ^ 2) ∈ {y : ℝ | (fun _ : ℝ => (0 : Fin 0 → ℝ)) y = 0 ∧ id y = 0} →
      Surjective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 0 → ℝ) × ℝ)
        (fun y : ℝ => ((fun _ : ℝ => (0 : Fin 0 → ℝ)) (1 + t - y ^ 2), id (1 + t - y ^ 2))) x) := by
    intro t ht x hx
    have hx2 : 1 + t - x ^ 2 = 0 := hx.2
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := ht.1
      nlinarith
    have h2 : HasDerivAt (fun y : ℝ => 1 + t - y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub (1 + t)
    have hfd : HasFDerivAt (fun y : ℝ => ((0 : Fin 0 → ℝ), 1 + t - y ^ 2))
        ((0 : ℝ →L[ℝ] (Fin 0 → ℝ)).prod ((1 : ℝ →L[ℝ] ℝ).smulRight (-(2 * x)))) x :=
      (hasFDerivAt_const (0 : Fin 0 → ℝ) x).prodMk h2.hasFDerivAt
    change Surjective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 0 → ℝ) × ℝ)
      (fun y : ℝ => ((0 : Fin 0 → ℝ), 1 + t - y ^ 2)) x)
    rw [hfd.hasMFDerivAt.mfderiv]
    rintro ⟨z, w⟩
    refine ⟨w / (-(2 * x)), Prod.ext (Subsingleton.elim (α := Fin 0 → ℝ) _ _) ?_⟩
    change (w / (-(2 * x))) • (-(2 * x)) = w
    rw [smul_eq_mul, div_mul_cancel₀]
    simpa using hx0
  obtain ⟨Φ, hΦ, h0, hK, -, -, h1, h1b⟩ :=
    lc82_exists_smooth_isotopy_fibre (I := 𝓘(ℝ, ℝ)) (M := ℝ) (G := Fin 0 → ℝ)
      (F := fun q : ℝ × ℝ => 1 + q.1 - q.2 ^ 2)
      (φ := fun _ : ℝ => (0 : Fin 0 → ℝ)) (β := id)
      contMDiff_one_add_fst_sub_snd_sq.contMDiffOn contDiff_const contDiff_id rfl rfl htrans htransb
      (Q := Icc (-2) 2) isCompact_Icc
      (fun t ht x hx => by
        have h : 0 ≤ 1 + t - x ^ 2 := hx.2
        have ht1 := ht.2
        constructor <;> nlinarith)
  refine ⟨Φ, hΦ, h0, hK, ?_, ?_⟩
  · have e0 : {x : ℝ | (1 + (0 : ℝ) - x ^ 2) ∈
        {y : ℝ | (fun _ : ℝ => (0 : Fin 0 → ℝ)) y = 0 ∧ 0 ≤ id y}} = {x : ℝ | x ^ 2 ≤ 1} := by
      ext x
      simp only [mem_ofPred_eq, id, true_and, add_zero, sub_nonneg]
    have e1 : {x : ℝ | (1 + (1 : ℝ) - x ^ 2) ∈
        {y : ℝ | (fun _ : ℝ => (0 : Fin 0 → ℝ)) y = 0 ∧ 0 ≤ id y}} = {x : ℝ | x ^ 2 ≤ 2} := by
      ext x
      simp only [mem_ofPred_eq, id, true_and, sub_nonneg]
      norm_num
    rw [← e0, ← e1]
    exact h1
  · have e0 : {x : ℝ | (1 + (0 : ℝ) - x ^ 2) ∈
        {y : ℝ | (fun _ : ℝ => (0 : Fin 0 → ℝ)) y = 0 ∧ id y = 0}} = {x : ℝ | x ^ 2 = 1} := by
      ext x
      simp only [mem_ofPred_eq, id, true_and, add_zero, sub_eq_zero]
      exact eq_comm
    have e1 : {x : ℝ | (1 + (1 : ℝ) - x ^ 2) ∈
        {y : ℝ | (fun _ : ℝ => (0 : Fin 0 → ℝ)) y = 0 ∧ id y = 0}} = {x : ℝ | x ^ 2 = 2} := by
      ext x
      simp only [mem_ofPred_eq, id, true_and, sub_eq_zero]
      norm_num
      exact eq_comm
    rw [← e0, ← e1]
    exact h1b

end Interval

end DifferentialGeometry.Analysis.ODE
