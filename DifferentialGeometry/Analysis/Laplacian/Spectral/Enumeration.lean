import DifferentialGeometry.Analysis.Laplacian.Spectral.EigenBasis

/-!
# Ascending enumeration of the nonzero Laplacian spectrum

For a closed Riemannian manifold `(M, g)`, the variational Laplacian
`Δ_g = div_g ∘ grad_g` has a discrete spectrum
`{-λ_n}_{n ≥ 0} ⊆ (-∞, 0]` with `0` as the only accumulation point and each
nonzero eigenspace finite-dimensional. This file extracts the strictly
ascending enumeration `n ↦ λ_n` of the distinct nonzero Laplacian eigenvalues.

## Main definitions

* `nonzeroLaplacianEigenvalueSet g : Set ℝ` — the set of distinct nonzero
  Laplacian eigenvalues, equivalently `{ (1 - μ) / μ | μ ∈ Spec(R), μ ∈ (0, 1) }`
  where `R = resolventL2 g`.
* `laplacianEigenvalueAscending g : ℕ → ℝ` — the ascending enumeration. When
  `nonzeroLaplacianEigenvalueSet g` is nonempty, the value at `n = 0` is the
  smallest nonzero Laplacian eigenvalue; the value at `n + 1` is the smallest
  eigenvalue strictly above the previous one, with junk value `0` once the
  set is exhausted (or if the set is empty).

## Main results

* `nonzeroLaplacianEigenvalueSet_finite_below`: for every threshold `N`, only
  finitely many distinct nonzero Laplacian eigenvalues are `≤ N`.
* `laplacianEigenvalueAscending_strictMono_of_infinite`: if the eigenvalue set
  is infinite, `laplacianEigenvalueAscending g` is strictly increasing.
* `laplacianEigenvalueAscending_mem_of_infinite`: each iterate lies in the
  eigenvalue set.
* `laplacianEigenvalueAscending_tendsto_atTop_of_infinite`: under the same hypothesis,
  `laplacianEigenvalueAscending g n → ∞` as `n → ∞`.
* `laplacianEigenvalueAscending_zero_eq_sInf`: the first iterate equals the
  infimum of the eigenvalue set when it is nonempty (`λ_0 = λ_1` in the
  classical notation; we index from zero).

## Sign convention

Geometer convention `Δ_g = div_g ∘ grad_g`, with spectrum
`⊆ (-∞, 0]`. The resolvent is `(1 - Δ_g)⁻¹` with eigenvalues `μ ∈ (0, 1]`,
and the Laplacian eigenvalues are `λ = (1 - μ) / μ ∈ [0, ∞)`. Nonzero
Laplacian eigenvalues correspond to `μ < 1`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The set of distinct nonzero Laplacian eigenvalues, defined as the image of
the resolvent-eigenvalue subtype `{μ ∈ Spec(R) | μ ≠ 0, μ < 1}` under the map
`μ ↦ (1 - μ) / μ`. The condition `μ < 1` excludes the trivial Laplacian
eigenvalue `0` (corresponding to `μ = 1`). -/
def nonzeroLaplacianEigenvalueSet (g : SmoothRiemannianMetric I M) : Set ℝ :=
  { lam : ℝ | ∃ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      μ.val < 1 ∧ laplacianEigenvalueOf μ.val = lam }

/-- Every element of `nonzeroLaplacianEigenvalueSet g` is strictly positive. -/
theorem nonzeroLaplacianEigenvalueSet_pos
    (g : SmoothRiemannianMetric I M) {lam : ℝ}
    (h : lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) :
    0 < lam := by
  rcases h with ⟨μ, hμ_lt, hlam⟩
  rw [← hlam]
  unfold laplacianEigenvalueOf
  have h_pos : 0 < μ.val := nonzeroResolventEigenvalue_pos μ
  have h_num_pos : 0 < 1 - μ.val := by linarith
  exact div_pos h_num_pos h_pos

/-- Given a positive Laplacian eigenvalue candidate `lam = (1 - μ)/μ` with
`μ ∈ (0, 1)`, the resolvent eigenvalue is recovered as `μ = 1 / (lam + 1)`. -/
private lemma resolvent_val_eq_of_laplacianEigenvalueOf
    {μ : ℝ} (hμ_pos : 0 < μ) (hμ_lt : μ < 1) (lam : ℝ)
    (hlam_eq : (1 - μ) / μ = lam) :
    μ = 1 / (lam + 1) := by
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
  have h1 : 1 - μ = lam * μ := by
    have h2 : ((1 - μ) / μ) * μ = lam * μ := by rw [hlam_eq]
    rwa [div_mul_cancel₀ _ hμ_ne] at h2
  have h_sum : 1 = (lam + 1) * μ := by linarith
  have h_lam1_pos : 0 < lam + 1 := by
    have h_lam_nn : 0 ≤ lam := by
      rw [← hlam_eq]
      have h_num : 0 ≤ 1 - μ := by linarith
      exact div_nonneg h_num hμ_pos.le
    linarith
  have h_lam1_ne : (lam + 1 : ℝ) ≠ 0 := ne_of_gt h_lam1_pos
  field_simp
  linarith

/-- For any threshold `N`, the set of distinct nonzero Laplacian eigenvalues
that are `≤ N` is finite.

The proof translates `λ = (1 - μ)/μ ≤ N` (with `μ ∈ (0, 1)`) into the bound
`μ ≥ 1 / (N + 1)`, then applies the finiteness of the resolvent eigenvalues on
the shell `{|μ| ≥ ε}` with `ε = 1 / (N + 1)`. -/
theorem nonzeroLaplacianEigenvalueSet_finite_below
    (g : SmoothRiemannianMetric I M) (N : ℝ) :
    Set.Finite { lam : ℝ |
      lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ N } := by
  by_cases hN : 0 < N
  · set ε : ℝ := 1 / (N + 1) with hε_def
    have hN1_pos : 0 < N + 1 := by linarith
    have hε_pos : 0 < ε := by rw [hε_def]; positivity
    have h_shell_fin :
        Set.Finite { μ : ℝ |
          Module.End.HasEigenvalue
            ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧ ε ≤ |μ| } :=
      resolvent_eigenvalues_finite_above_on_closed
        (I := I) (M := M) g hε_pos
    set S : Set ℝ := { lam : ℝ |
        lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ N }
    set fmap : ℝ → ℝ := fun lam => 1 / (lam + 1) with hfmap_def
    have h_image_subset : fmap '' S ⊆
        { μ : ℝ |
          Module.End.HasEigenvalue
            ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧ ε ≤ |μ| } := by
      rintro y ⟨lam, ⟨h_lam_S, h_lam_le_N⟩, hflam⟩
      rcases h_lam_S with ⟨μ, hμ_lt, hlam_eq⟩
      have hμ_pos : 0 < μ.val := nonzeroResolventEigenvalue_pos μ
      have hμ_le_one : μ.val ≤ 1 := nonzeroResolventEigenvalue_le_one μ
      have hlam_pos : 0 < lam := by
        rw [← hlam_eq]
        unfold laplacianEigenvalueOf
        have h_num_pos : 0 < 1 - μ.val := by linarith
        exact div_pos h_num_pos hμ_pos
      have h_mu_eq : μ.val = 1 / (lam + 1) := by
        unfold laplacianEigenvalueOf at hlam_eq
        exact resolvent_val_eq_of_laplacianEigenvalueOf hμ_pos hμ_lt lam hlam_eq
      have h_y_eq : y = μ.val := by
        rw [← hflam, hfmap_def, h_mu_eq]
      have hlam_eq_unfold : (1 - μ.val) / μ.val = lam := by
        unfold laplacianEigenvalueOf at hlam_eq; exact hlam_eq
      refine ⟨?_, ?_⟩
      · rw [h_y_eq]; exact μ.hasEigenvalue
      · rw [h_y_eq, abs_of_pos hμ_pos]
        have h_div_le : (1 - μ.val) / μ.val ≤ N := by
          rw [hlam_eq_unfold]; exact h_lam_le_N
        have h_mul : 1 - μ.val ≤ N * μ.val := by
          have h := (div_le_iff₀ hμ_pos).mp h_div_le
          linarith
        have h_total : 1 ≤ (N + 1) * μ.val := by linarith
        rw [hε_def]
        exact (div_le_iff₀ hN1_pos).mpr (by linarith)
    have h_image_finite : (fmap '' S).Finite :=
      h_shell_fin.subset h_image_subset
    have h_inj_on : Set.InjOn fmap S := by
      intro a ha b hb hab
      have ha_pos : 0 < a := nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g ha.1
      have hb_pos : 0 < b := nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g hb.1
      have ha1_pos : 0 < a + 1 := by linarith
      have hb1_pos : 0 < b + 1 := by linarith
      have ha1_ne : (a + 1 : ℝ) ≠ 0 := ne_of_gt ha1_pos
      have hb1_ne : (b + 1 : ℝ) ≠ 0 := ne_of_gt hb1_pos
      have h_eq : (a + 1) = (b + 1) := by
        rw [hfmap_def] at hab
        field_simp at hab
        linarith
      linarith
    exact Set.Finite.of_finite_image h_image_finite h_inj_on
  · push Not at hN
    have h_empty : { lam : ℝ |
        lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ N } = ∅ := by
      ext lam
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h_in_S, h_le_N⟩
      have h_pos := nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g h_in_S
      linarith
    rw [h_empty]
    exact Set.finite_empty

/-- The intersection of `nonzeroLaplacianEigenvalueSet g` with `Iic N` is finite. -/
theorem nonzeroLaplacianEigenvalueSet_inter_Iic_finite
    (g : SmoothRiemannianMetric I M) (N : ℝ) :
    Set.Finite ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Iic N) := by
  refine Set.Finite.subset
    (nonzeroLaplacianEigenvalueSet_finite_below (I := I) (M := M) g N) ?_
  intro lam hlam
  exact ⟨hlam.1, hlam.2⟩

/-- The recursive ascending enumeration of `nonzeroLaplacianEigenvalueSet g`.

* `n = 0`: returns `sInf S` if `S` is nonempty, otherwise junk `0`.
* `n + 1`: returns `sInf (S ∩ Ioi prev)` if nonempty, otherwise junk `0`,
  where `prev = laplacianEigenvalueAscending g n`.

If the set is empty, all values are `0`. If the set is nonempty and finite
with exactly `k` elements, the first `k` values enumerate them in ascending
order; subsequent values are `0`. If the set is infinite, the function is a
strictly increasing bijection from `ℕ` onto the set (proved below under
the infinity hypothesis). -/
noncomputable def laplacianEigenvalueAscending
    (g : SmoothRiemannianMetric I M) : ℕ → ℝ
  | 0 =>
      open Classical in
      if (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty then
        sInf (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g)
      else 0
  | n + 1 =>
      let prev := laplacianEigenvalueAscending g n
      open Classical in
      if ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
              Set.Ioi prev).Nonempty then
        sInf ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
              Set.Ioi prev)
      else 0

lemma laplacianEigenvalueAscending_zero
    (g : SmoothRiemannianMetric I M) :
    laplacianEigenvalueAscending (I := I) (M := M) g 0 =
      (open Classical in
       if (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty then
         sInf (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g)
       else 0) := rfl

lemma laplacianEigenvalueAscending_succ
    (g : SmoothRiemannianMetric I M) (n : ℕ) :
    laplacianEigenvalueAscending (I := I) (M := M) g (n + 1) =
      (open Classical in
       if ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
            Set.Ioi (laplacianEigenvalueAscending (I := I) (M := M) g n)).Nonempty then
         sInf ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
              Set.Ioi (laplacianEigenvalueAscending (I := I) (M := M) g n))
       else 0) := rfl

/-- The first iterate equals the infimum of the set, when the set is nonempty. -/
theorem laplacianEigenvalueAscending_zero_eq_sInf
    (g : SmoothRiemannianMetric I M)
    (h_nonempty : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty) :
    laplacianEigenvalueAscending (I := I) (M := M) g 0 =
      sInf (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) := by
  rw [laplacianEigenvalueAscending_zero, if_pos h_nonempty]

/-- When the set is empty, the first iterate is `0`. -/
theorem laplacianEigenvalueAscending_zero_of_empty
    (g : SmoothRiemannianMetric I M)
    (h_empty : ¬ (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty) :
    laplacianEigenvalueAscending (I := I) (M := M) g 0 = 0 := by
  rw [laplacianEigenvalueAscending_zero, if_neg h_empty]

/-- The csInf of a nonempty set `T ⊆ ℝ` that is bounded below and such that
`T ∩ Iic a` is finite for some `a ∈ T`, lies in `T`. This is the key
"discrete attainment of infimum" lemma we'll reuse. -/
private lemma csInf_mem_of_finite_slice
    {T : Set ℝ} (hT_bddBelow : BddBelow T) (a : ℝ) (ha : a ∈ T)
    (hT_slice_fin : Set.Finite (T ∩ Set.Iic a)) :
    sInf T ∈ T := by
  set Tslice : Set ℝ := T ∩ Set.Iic a
  have hTslice_nonempty : Tslice.Nonempty := ⟨a, ha, le_refl a⟩
  have h_csInf_in_slice : sInf Tslice ∈ Tslice :=
    hTslice_nonempty.csInf_mem hT_slice_fin
  have h_lb : ∀ x ∈ T, sInf Tslice ≤ x := by
    intro x hx
    by_cases hxa : x ≤ a
    · exact csInf_le hT_slice_fin.bddBelow ⟨hx, hxa⟩
    · push Not at hxa
      have h_le_a : sInf Tslice ≤ a :=
        csInf_le hT_slice_fin.bddBelow ⟨ha, le_refl a⟩
      linarith
  have h_eq : sInf T = sInf Tslice := by
    apply le_antisymm
    · exact csInf_le hT_bddBelow h_csInf_in_slice.1
    · exact le_csInf ⟨a, ha⟩ h_lb
  rw [h_eq]
  exact h_csInf_in_slice.1

/-- If the eigenvalue set is infinite, the intersection
`S ∩ Ioi t` is infinite for any `t ∈ ℝ`. -/
private lemma nonzeroLaplacianEigenvalueSet_inter_Ioi_infinite
    (g : SmoothRiemannianMetric I M)
    (h_inf : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Infinite)
    (t : ℝ) :
    ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t).Infinite := by
  intro h_fin
  apply h_inf
  have h_below_fin : Set.Finite { lam |
      lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ t } :=
    nonzeroLaplacianEigenvalueSet_finite_below (I := I) (M := M) g t
  have h_S_eq :
      nonzeroLaplacianEigenvalueSet (I := I) (M := M) g =
        { lam | lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ t } ∪
        ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t) := by
    ext lam
    constructor
    · intro hlam
      by_cases hle : lam ≤ t
      · left; exact ⟨hlam, hle⟩
      · right
        push Not at hle
        exact ⟨hlam, hle⟩
    · rintro (⟨hS, _⟩ | ⟨hS, _⟩)
      · exact hS
      · exact hS
  rw [h_S_eq]
  exact h_below_fin.union h_fin

/-- The csInf of `S ∩ Ioi t`, when nonempty, lies in `S ∩ Ioi t`. -/
private lemma sInf_inter_Ioi_mem
    (g : SmoothRiemannianMetric I M) (t : ℝ)
    (h_nonempty : ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
                   Set.Ioi t).Nonempty) :
    sInf ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t) ∈
      (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t := by
  obtain ⟨a, ha_S, ha_gt⟩ := h_nonempty
  set T : Set ℝ := (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t
  have ha_T : a ∈ T := ⟨ha_S, ha_gt⟩
  have hT_bddBelow : BddBelow T := by
    refine ⟨t, ?_⟩
    intro x hx; exact (Set.mem_Ioi.mp hx.2).le
  have hT_slice_fin : Set.Finite (T ∩ Set.Iic a) := by
    apply (nonzeroLaplacianEigenvalueSet_finite_below
      (I := I) (M := M) g a).subset
    rintro lam ⟨⟨hlam_S, _⟩, hlam_a⟩
    exact ⟨hlam_S, hlam_a⟩
  exact csInf_mem_of_finite_slice hT_bddBelow a ha_T hT_slice_fin

/-- Each iterate (under the infinity hypothesis) lies in the eigenvalue set. -/
theorem laplacianEigenvalueAscending_mem_of_infinite
    (g : SmoothRiemannianMetric I M)
    (h_inf : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Infinite)
    (n : ℕ) :
    laplacianEigenvalueAscending (I := I) (M := M) g n ∈
      nonzeroLaplacianEigenvalueSet (I := I) (M := M) g := by
  induction n with
  | zero =>
      rw [laplacianEigenvalueAscending_zero, if_pos h_inf.nonempty]
      set S : Set ℝ := nonzeroLaplacianEigenvalueSet (I := I) (M := M) g
      obtain ⟨a, ha_S⟩ := h_inf.nonempty
      have h_S_bddBelow : BddBelow S := by
        refine ⟨0, ?_⟩
        intro x hx
        exact (nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g hx).le
      have h_slice_fin : Set.Finite (S ∩ Set.Iic a) :=
        nonzeroLaplacianEigenvalueSet_inter_Iic_finite (I := I) (M := M) g a
      exact csInf_mem_of_finite_slice h_S_bddBelow a ha_S h_slice_fin
  | succ n ih =>
      rw [laplacianEigenvalueAscending_succ]
      set prev := laplacianEigenvalueAscending (I := I) (M := M) g n
      have h_inter_inf : ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
                          Set.Ioi prev).Infinite :=
        nonzeroLaplacianEigenvalueSet_inter_Ioi_infinite
          (I := I) (M := M) g h_inf prev
      have h_inter_nonempty : ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
                                Set.Ioi prev).Nonempty := h_inter_inf.nonempty
      rw [if_pos h_inter_nonempty]
      exact (sInf_inter_Ioi_mem (I := I) (M := M) g prev h_inter_nonempty).1

/-- Under the infinity hypothesis, the ascending enumeration is strictly
increasing. -/
theorem laplacianEigenvalueAscending_strictMono_of_infinite
    (g : SmoothRiemannianMetric I M)
    (h_inf : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Infinite) :
    StrictMono (laplacianEigenvalueAscending (I := I) (M := M) g) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [laplacianEigenvalueAscending_succ]
  set prev := laplacianEigenvalueAscending (I := I) (M := M) g n
  have h_inter_inf : ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
                      Set.Ioi prev).Infinite :=
    nonzeroLaplacianEigenvalueSet_inter_Ioi_infinite
      (I := I) (M := M) g h_inf prev
  have h_inter_nonempty := h_inter_inf.nonempty
  rw [if_pos h_inter_nonempty]
  exact (sInf_inter_Ioi_mem (I := I) (M := M) g prev h_inter_nonempty).2

/-- If the set of distinct nonzero Laplacian eigenvalues is infinite, then the
ascending enumeration `laplacianEigenvalueAscending g n` tends to `+∞` as
`n → ∞`. -/
theorem laplacianEigenvalueAscending_tendsto_atTop_of_infinite
    (g : SmoothRiemannianMetric I M)
    (h_inf : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Infinite) :
    Filter.Tendsto (laplacianEigenvalueAscending (I := I) (M := M) g)
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro N
  have h_strictMono := laplacianEigenvalueAscending_strictMono_of_infinite
    (I := I) (M := M) g h_inf
  have h_mem := laplacianEigenvalueAscending_mem_of_infinite
    (I := I) (M := M) g h_inf
  set S := nonzeroLaplacianEigenvalueSet (I := I) (M := M) g
  set Sbelow := {lam | lam ∈ S ∧ lam ≤ N}
  have hSbelow_fin : Set.Finite Sbelow :=
    nonzeroLaplacianEigenvalueSet_finite_below (I := I) (M := M) g N
  refine ⟨hSbelow_fin.toFinset.card, ?_⟩
  intro n hn
  by_contra h_not
  push Not at h_not
  have h_le_N : ∀ k ≤ n, laplacianEigenvalueAscending (I := I) (M := M) g k ≤ N := by
    intro k hk
    have h_mono : laplacianEigenvalueAscending (I := I) (M := M) g k ≤
        laplacianEigenvalueAscending (I := I) (M := M) g n :=
      h_strictMono.monotone hk
    linarith
  have h_in_Sbelow : ∀ k ≤ n,
      laplacianEigenvalueAscending (I := I) (M := M) g k ∈ Sbelow := by
    intro k hk
    exact ⟨h_mem k, h_le_N k hk⟩
  classical
  have h_card_le_fin : n + 1 ≤ hSbelow_fin.toFinset.card := by
    have h_inj_to_finset : ∀ k : Fin (n + 1),
        laplacianEigenvalueAscending (I := I) (M := M) g k.val ∈ hSbelow_fin.toFinset := by
      intro k
      rw [Set.Finite.mem_toFinset]
      exact h_in_Sbelow k.val (Nat.lt_succ_iff.mp k.isLt)
    let g' : Fin (n + 1) → hSbelow_fin.toFinset := fun k =>
      ⟨laplacianEigenvalueAscending (I := I) (M := M) g k.val, h_inj_to_finset k⟩
    have hg'_inj : Function.Injective g' := by
      intro a b hab
      have heq : laplacianEigenvalueAscending (I := I) (M := M) g a.val =
          laplacianEigenvalueAscending (I := I) (M := M) g b.val :=
        Subtype.mk_eq_mk.mp hab
      exact Fin.ext (h_strictMono.injective heq)
    have h_card := Fintype.card_le_of_injective g' hg'_inj
    simp only [Fintype.card_fin, Fintype.card_coe] at h_card
    exact h_card
  omega

example (g : SmoothRiemannianMetric I M) : ℕ → ℝ :=
  laplacianEigenvalueAscending (I := I) (M := M) g

end Laplacian
end Analysis
end DifferentialGeometry

end
