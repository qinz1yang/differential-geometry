import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.GlobalExistence
import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Parametric
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric
import Mathlib.Topology.Order.ProjIcc

noncomputable section

open Set
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry.Analysis.ODE.Flow

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_linear_ode_solution_on_Icc [CompleteSpace G]
    {A : ℝ → G →L[ℝ] G} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hA : ContinuousOn A (Icc a b)) (z₀ : G) :
    ∃ Z : ℝ → G, Z t₀ = z₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt Z (A t (Z t)) (Icc a b) t := by
  let B : ℝ → ℝ → G →L[ℝ] G := fun _ t =>
    A (projIcc a b (ht₀.1.trans ht₀.2) t)
  have hB : Continuous (Function.uncurry B) :=
    ((continuousOn_iff_continuous_domRestrict.mp hA).comp continuous_projIcc).comp continuous_snd
  have ht₀' : t₀ ∈ Ioo (a - 1) (b + 1) := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  let Z := linearODESolution B (a - 1) (b + 1) t₀ (fun _ => z₀) 0
  refine ⟨Z, linearODESolution_initial _ _ _ _ _ _, ?_⟩
  intro t ht
  have ht' : t ∈ Ioo (a - 1) (b + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd := linearODESolution_hasDerivAt (Z₀ := fun _ => z₀) ht₀'
    (U := univ) hB.continuousOn (x := 0) (mem_univ _) ht'
  simpa only [B, projIcc_of_mem _ ht] using hd.hasDerivWithinAt (s := Icc a b)

theorem linear_ode_unique_on_Icc
    {A : ℝ → G →L[ℝ] G} {a b t₀ : ℝ} {Z W : ℝ → G}
    (ht₀ : t₀ ∈ Icc a b) (hA : ContinuousOn A (Icc a b))
    (hZ : ∀ t ∈ Icc a b, HasDerivWithinAt Z (A t (Z t)) (Icc a b) t)
    (hW : ∀ t ∈ Icc a b, HasDerivWithinAt W (A t (W t)) (Icc a b) t)
    (hinit : Z t₀ = W t₀) : EqOn Z W (Icc a b) := by
  obtain ⟨q, _, hq⟩ := isCompact_Icc.exists_isMaxOn ⟨t₀, ht₀⟩ hA.norm
  let K : ℝ≥0 := ⟨‖A q‖, norm_nonneg _⟩
  have hLip (t : ℝ) (ht : t ∈ Icc a b) : LipschitzOnWith K (A t) univ :=
    ((A t).lipschitzWith_of_opNorm_le (K := K) (hq ht)).lipschitzOnWith
  have hZcont : ContinuousOn Z (Icc a b) := fun t ht => (hZ t ht).continuousWithinAt
  have hWcont : ContinuousOn W (Icc a b) := fun t ht => (hW t ht).continuousWithinAt
  rw [← Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
  refine EqOn.union ?_ ?_
  · have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    exact ODE_solution_unique_of_mem_Icc_left
      (v := fun t z => A t z) (s := fun _ => univ)
      (fun t ht => hLip t (hsub (Ioc_subset_Icc_self ht)))
      (hZcont.mono hsub)
      (fun t ht => (hZ t (hsub (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans ht₀.2⟩))
      (fun _ _ => mem_univ _) (hWcont.mono hsub)
      (fun t ht => (hW t (hsub (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans ht₀.2⟩))
      (fun _ _ => mem_univ _) hinit
  · have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    exact ODE_solution_unique_of_mem_Icc_right
      (v := fun t z => A t z) (s := fun _ => univ)
      (fun t ht => hLip t (hsub (Ico_subset_Icc_self ht)))
      (hZcont.mono hsub)
      (fun t ht => (hZ t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans ht.1, ht.2⟩))
      (fun _ _ => mem_univ _) (hWcont.mono hsub)
      (fun t ht => (hW t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans ht.1, ht.2⟩))
      (fun _ _ => mem_univ _) hinit

theorem linear_ode_solution_contDiffOn_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [CompleteSpace G] {A : F → ℝ → G →L[ℝ] G} {Z : F → ℝ → G} {z₀ : F → G}
    {U : Set F} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (hz₀ : ContDiffOn ℝ ∞ z₀ U) (hinit : ∀ x ∈ U, Z x t₀ = z₀ x)
    (hZ : ∀ x ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Z x) (A x t (Z x t)) (Icc a b) t) :
    ContDiffOn ℝ ∞ (Function.uncurry Z) (U ×ˢ Icc a b) := by
  rcases lt_or_eq_of_le (ht₀.1.trans ht₀.2) with hab | hab
  · have hshift : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => A x (a + t)))
        (Icc 0 (b - a) ×ˢ U) := by
      apply hA.comp ((contDiff_snd.prodMk (contDiff_const.add contDiff_fst)).contDiffOn)
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      exact ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    obtain ⟨B, V, hV, hB, hBeq⟩ := DifferentialGeometry.Analysis.borel_interval_extend_param
      (fun t x => A x (a + t)) (b - a) (sub_pos.mpr hab) U x
      (hU.interior_eq.symm ▸ hx) hshift
    obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hx))
    have hWV : W ⊆ V := fun y hy => (hWsub hy).1
    have hWU : W ⊆ U := fun y hy => (hWsub hy).2
    let C : F → ℝ → G →L[ℝ] G := fun y s => B (s - a) y
    have hC : ContDiffOn ℝ ∞ (Function.uncurry C) (W ×ˢ Ioo (a - 1) (b + 1)) := by
      apply hB.comp ((contDiff_snd.sub contDiff_const).prodMk contDiff_fst).contDiffOn
      exact fun p hp => ⟨mem_univ _, hWV hp.1⟩
    have hCeq (y : F) (hy : y ∈ W) (s : ℝ) (hs : s ∈ Icc a b) : C y s = A y s := by
      have hs' : s - a ∈ Icc 0 (b - a) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      simpa only [C, add_sub_cancel] using hBeq (s - a) hs' y (hWV hy)
    have ht₀' : t₀ ∈ Ioo (a - 1) (b + 1) :=
      ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
    have hI : Icc a b ⊆ Ioo (a - 1) (b + 1) := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    let Y := linearODESolution C (a - 1) (b + 1) t₀ z₀
    have hY : ContDiffOn ℝ ∞ (Function.uncurry Y) (W ×ˢ Icc a b) :=
      (linearODESolution_contDiffOn_top ht₀' hWopen hC (hz₀.mono hWU)).mono
        (prod_mono_right hI)
    have hYeq (y : F) (hy : y ∈ W) : EqOn (Z y) (Y y) (Icc a b) := by
      refine linear_ode_unique_on_Icc ht₀
        (hA.continuousOn.uncurry_left y (hWU hy)) (hZ y (hWU hy)) ?_ ?_
      · intro s hs
        have hd := linearODESolution_hasDerivAt (Z₀ := z₀) ht₀' hC.continuousOn hy (hI hs)
        rw [hCeq y hy s hs] at hd
        exact hd.hasDerivWithinAt
      · simpa only [Y, linearODESolution_initial] using hinit y (hWU hy)
    have hlocal : ContDiffOn ℝ ∞ (Function.uncurry Z) (W ×ˢ Icc a b) :=
      hY.congr (fun p hp => hYeq p.1 hp.1 hp.2)
    apply (hlocal (x, t) ⟨hxW, ht⟩).mono_of_mem_nhdsWithin
    have hWnhds : Prod.fst ⁻¹' W ∈ nhds (x, t) :=
      continuous_fst.continuousAt.preimage_mem_nhds (hWopen.mem_nhds hxW)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hWnhds] with p hp hpW
    exact ⟨hpW, hp.2⟩
  · have hz : ContDiffOn ℝ ∞ (fun p : F × ℝ => z₀ p.1) (U ×ˢ Icc a b) :=
      hz₀.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
    apply hz.congr
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have htt₀ : t = t₀ := by linarith [ht.1, ht.2, ht₀.1, ht₀.2]
    exact htt₀ ▸ hinit x hx

theorem exists_linear_ode_solution_contDiffOn_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [CompleteSpace G] {A : F → ℝ → G →L[ℝ] G} {z₀ : F → G}
    {U : Set F} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (hz₀ : ContDiffOn ℝ ∞ z₀ U) :
    ∃ Z : F → ℝ → G,
      ContDiffOn ℝ ∞ (Function.uncurry Z) (U ×ˢ Icc a b) ∧
      (∀ x ∈ U, Z x t₀ = z₀ x) ∧
      ∀ x ∈ U, ∀ t ∈ Icc a b,
        HasDerivWithinAt (Z x) (A x t (Z x t)) (Icc a b) t := by
  classical
  have hex (x : F) : ∃ Z : ℝ → G, x ∈ U → Z t₀ = z₀ x ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt Z (A x t (Z t)) (Icc a b) t := by
    by_cases hx : x ∈ U
    · obtain ⟨Z, hinit, hZ⟩ := exists_linear_ode_solution_on_Icc ht₀
        (hA.continuousOn.uncurry_left x hx) (z₀ x)
      exact ⟨Z, fun _ => ⟨hinit, hZ⟩⟩
    · exact ⟨fun _ => z₀ x, fun hx' => (hx hx').elim⟩
  choose Z hZ using hex
  have hinit : ∀ x ∈ U, Z x t₀ = z₀ x := fun x hx => (hZ x hx).1
  have hderiv : ∀ x ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Z x) (A x t (Z x t)) (Icc a b) t := fun x hx => (hZ x hx).2
  exact ⟨Z, linear_ode_solution_contDiffOn_Icc ht₀ hU hA hz₀ hinit hderiv, hinit, hderiv⟩

end DifferentialGeometry.Analysis.ODE.Flow
