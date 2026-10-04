import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Separation from the convex hull of a compact set in a positive definite form (S-SEP, linear part)

* `isCompact_convexHull_of_isCompact`: in a finite-dimensional real normed space the convex hull of
  a compact set is compact (Carathéodory: a finite union of images of `stdSimplex × Kᵐ`).
* `exists_neg_pairing_of_zero_notMem_convexHull`: for a symmetric positive definite bilinear form
  `B`, a compact nonempty `K` with `0 ∉ conv K` has a `B`-unit vector `v` with `B v u < 0` for all
  `u ∈ K` (`v = -z/|z|_B` for the `B`-nearest point `z` of `conv K` to `0`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimension, the convex hull of a compact set is compact. -/
theorem isCompact_convexHull_of_isCompact {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  set N := Module.finrank ℝ E + 1 with hN
  let simp_ : (m : ℕ) → Set (Fin m → ℝ) := fun m =>
    Set.univ.pi (fun _ => Ici (0 : ℝ)) ∩ {w | ∑ i, w i = 1}
  have hsimp : ∀ m, IsCompact (simp_ m) := by
    intro m
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      ((isClosed_set_pi fun _ _ => isClosed_Ici).inter
        (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)) ?_
    intro w hw i _
    have h0 : ∀ j, 0 ≤ w j := fun j => hw.1 j (mem_univ j)
    refine ⟨h0 i, ?_⟩
    have h1 : ∑ j, w j = 1 := hw.2
    rw [← h1]
    exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  let img : ℕ → Set E := fun m =>
    (fun p : (Fin m → ℝ) × (Fin m → E) => ∑ i, p.1 i • p.2 i) ''
      (simp_ m ×ˢ Set.univ.pi (fun _ => K))
  have himg : ∀ m, IsCompact (img m) := fun m =>
    ((hsimp m).prod (isCompact_univ_pi fun _ => hK)).image
      (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd))
  have heq : convexHull ℝ K = ⋃ m ∈ Finset.range (N + 1), img m := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨ι, _, z, w, hzK, hind, hw, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      set m := Fintype.card ι with hm
      have hmN : m ≤ N := by
        have h1 := AffineIndependent.card_le_finrank_succ hind
        have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ E :=
          Submodule.finrank_le _
        omega
      let e := Fintype.equivFin ι
      refine mem_iUnion₂.2 ⟨m, Finset.mem_range.2 (by omega), ?_⟩
      refine ⟨(w ∘ e.symm, z ∘ e.symm), ⟨⟨fun j _ => mem_Ici.2 (hw _).le, ?_⟩,
        fun j _ => hzK ⟨_, rfl⟩⟩, ?_⟩
      · rw [← hw1]
        exact Equiv.sum_comp e.symm w
      · rw [← hx]
        exact Equiv.sum_comp e.symm (fun i => w i • z i)
    · intro x hx
      obtain ⟨m, -, p, ⟨⟨hp0, hp1⟩, hpK⟩, rfl⟩ := mem_iUnion₂.1 hx
      exact mem_convexHull_of_exists_fintype p.1 p.2 (fun i => hp0 i (mem_univ i)) hp1
        (fun i => hpK i (mem_univ i)) rfl
  rw [heq]
  exact (Finset.range (N + 1)).isCompact_biUnion fun m _ => himg m

/-- **Separation in a positive definite form.** If `0 ∉ conv K` for a compact nonempty `K`, some
`B`-unit vector has negative `B`-pairing with every point of `K`. -/
theorem exists_neg_pairing_of_zero_notMem_convexHull (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ u w, B u w = B w u) (hpos : ∀ u, u ≠ 0 → 0 < B u u) {K : Set E}
    (hKc : IsCompact K) (hKne : K.Nonempty) (h0 : (0 : E) ∉ convexHull ℝ K) :
    ∃ v : E, B v v = 1 ∧ ∀ u ∈ K, B v u < 0 := by
  set C := convexHull ℝ K with hC
  have hCc : IsCompact C := isCompact_convexHull_of_isCompact hKc
  have hCne : C.Nonempty := hKne.mono (subset_convexHull ℝ K)
  have hcont : Continuous (fun u : E => B u u) :=
    B.continuous₂.comp (continuous_id.prodMk continuous_id)
  obtain ⟨z, hzC, hzmin⟩ := hCc.exists_isMinOn hCne hcont.continuousOn
  have hz0 : z ≠ 0 := fun h => h0 (h ▸ hzC)
  have hBz : 0 < B z z := hpos z hz0
  -- first-order optimality: `B z (u - z) ≥ 0` on `C`
  have hopt : ∀ u ∈ C, 0 ≤ B z (u - z) := by
    intro u hu
    by_contra hneg
    push Not at hneg
    set d := u - z with hd
    have hd0 : d ≠ 0 := by
      intro h
      rw [h, map_zero] at hneg
      exact lt_irrefl _ hneg
    have hdd : 0 < B d d := hpos d hd0
    set t := min 1 (-(B z d) / B d d) with ht
    have ht0 : 0 < t := lt_min one_pos (div_pos (neg_pos.2 hneg) hdd)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htd : t * B d d ≤ -(B z d) := by
      have := min_le_right 1 (-(B z d) / B d d)
      rw [← ht] at this
      calc t * B d d ≤ (-(B z d) / B d d) * B d d := mul_le_mul_of_nonneg_right this hdd.le
        _ = -(B z d) := div_mul_cancel₀ _ hdd.ne'
    have hmem : z + t • d ∈ C := by
      have h := (convex_convexHull ℝ K) hzC hu (sub_nonneg.2 ht1) ht0.le (by ring)
      convert h using 1
      rw [hd]
      module
    have hle := hzmin hmem
    simp only [mem_ofPred_eq] at hle
    have hexp : B (z + t • d) (z + t • d) = B z z + 2 * t * B z d + t ^ 2 * B d d := by
      simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hsymm d z]
      ring
    rw [hexp] at hle
    nlinarith
  set c := Real.sqrt (B z z) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 hBz
  refine ⟨(-c⁻¹) • z, ?_, fun u hu => ?_⟩
  · simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    have hcc : c * c = B z z := Real.mul_self_sqrt hBz.le
    field_simp
    linarith
  · have h1 := hopt u (subset_convexHull ℝ K hu)
    simp only [map_sub] at h1
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h2 : 0 < B z u := by linarith
    have : 0 < c⁻¹ * B z u := mul_pos (inv_pos.2 hc0) h2
    linarith

end DifferentialGeometry.Geometry.FiniteSoul
