import DifferentialGeometry.Analysis.ODE.Flow.ClosedInterval
import DifferentialGeometry.Topology.Order.Interval

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis.ODE.Flow

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem linear_ode_unique_on_interval
    {J : Set ℝ} {A : ℝ → G →L[ℝ] G} {t₀ : ℝ} {Z W : ℝ → G}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (hA : ContinuousOn A J)
    (hZ : ∀ t ∈ J, HasDerivWithinAt Z (A t (Z t)) J t)
    (hW : ∀ t ∈ J, HasDerivWithinAt W (A t (W t)) J t)
    (hinit : Z t₀ = W t₀) : EqOn Z W J := by
  intro t ht
  have hsub := hJ.uIcc_subset ht₀ ht
  exact linear_ode_unique_on_Icc (a := min t₀ t) (b := max t₀ t) left_mem_uIcc
    (hA.mono hsub) (fun r hr => (hZ r (hsub hr)).mono hsub)
    (fun r hr => (hW r (hsub hr)).mono hsub) hinit right_mem_uIcc

theorem exists_linear_ode_solution_on_interval [CompleteSpace G]
    {J : Set ℝ} {A : ℝ → G →L[ℝ] G} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (hA : ContinuousOn A J) (z₀ : G) :
    ∃ Z : ℝ → G, Z t₀ = z₀ ∧ ∀ t ∈ J, HasDerivWithinAt Z (A t (Z t)) J t := by
  classical
  have hex (t : ℝ) : ∃ W : ℝ → G, t ∈ J → W t₀ = z₀ ∧
      ∀ r ∈ uIcc t₀ t, HasDerivWithinAt W (A r (W r)) (uIcc t₀ t) r := by
    by_cases ht : t ∈ J
    · obtain ⟨W, hWinit, hW⟩ := exists_linear_ode_solution_on_Icc
        (a := min t₀ t) (b := max t₀ t) left_mem_uIcc (hA.mono (hJ.uIcc_subset ht₀ ht)) z₀
      exact ⟨W, fun _ => ⟨hWinit, hW⟩⟩
    · exact ⟨fun _ => z₀, fun ht' => (ht ht').elim⟩
  choose W hW using hex
  let Z : ℝ → G := fun t => W t t
  refine ⟨Z, (hW t₀ ht₀).1, ?_⟩
  intro t ht
  obtain ⟨a, b, ht₀C, htC, hCJ, hCnhds⟩ :=
    hJ.exists_Icc_subset_mem_nhdsWithin ht₀ ht
  obtain ⟨Y, hYinit, hY⟩ := exists_linear_ode_solution_on_Icc ht₀C (hA.mono hCJ) z₀
  have heq (r : ℝ) (hr : r ∈ Icc a b) : Z r = Y r := by
    have hrJ := hCJ hr
    have hsub : uIcc t₀ r ⊆ Icc a b := uIcc_subset_Icc ht₀C hr
    exact linear_ode_unique_on_Icc (a := min t₀ r) (b := max t₀ r) left_mem_uIcc
      (hA.mono (hJ.uIcc_subset ht₀ hrJ)) (hW r hrJ).2
      (fun q hq => (hY q (hsub hq)).mono hsub)
      ((hW r hrJ).1.trans hYinit.symm) right_mem_uIcc
  rw [heq t htC]
  exact ((hY t htC).mono_of_mem_nhdsWithin hCnhds).congr_of_eventuallyEq
    (Filter.eventually_of_mem hCnhds fun r hr => heq r hr) (heq t htC)

theorem linear_ode_solution_contDiffOn_interval
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [CompleteSpace G] {A : F → ℝ → G →L[ℝ] G} {Z : F → ℝ → G} {z₀ : F → G}
    {U : Set F} {J : Set ℝ} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ J))
    (hz₀ : ContDiffOn ℝ ∞ z₀ U) (hinit : ∀ x ∈ U, Z x t₀ = z₀ x)
    (hZ : ∀ x ∈ U, ∀ t ∈ J, HasDerivWithinAt (Z x) (A x t (Z x t)) J t) :
    ContDiffOn ℝ ∞ (Function.uncurry Z) (U ×ˢ J) := by
  intro p hp
  obtain ⟨a, b, ht₀C, htC, hCJ, hCnhds⟩ :=
    hJ.exists_Icc_subset_mem_nhdsWithin ht₀ hp.2
  have hlocal := linear_ode_solution_contDiffOn_Icc ht₀C hU
    (hA.mono (prod_mono_right hCJ)) hz₀ hinit
    (fun x hx t ht => (hZ x hx t (hCJ ht)).mono hCJ)
  apply (hlocal p ⟨hp.1, htC⟩).mono_of_mem_nhdsWithin
  have hmaps : MapsTo (Prod.snd : F × ℝ → ℝ) (U ×ˢ J) J := fun _ hq => hq.2
  have htime : Tendsto Prod.snd (𝓝[U ×ˢ J] p) (𝓝[J] p.2) :=
    continuousWithinAt_snd.tendsto_nhdsWithin hmaps
  filter_upwards [self_mem_nhdsWithin, htime hCnhds] with q hq hqC
  exact ⟨hq.1, hqC⟩

theorem exists_linear_ode_solution_contDiffOn_interval
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [CompleteSpace G] {A : F → ℝ → G →L[ℝ] G} {z₀ : F → G}
    {U : Set F} {J : Set ℝ} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ J))
    (hz₀ : ContDiffOn ℝ ∞ z₀ U) :
    ∃ Z : F → ℝ → G,
      ContDiffOn ℝ ∞ (Function.uncurry Z) (U ×ˢ J) ∧
      (∀ x ∈ U, Z x t₀ = z₀ x) ∧
      ∀ x ∈ U, ∀ t ∈ J, HasDerivWithinAt (Z x) (A x t (Z x t)) J t := by
  classical
  have hex (x : F) : ∃ Z : ℝ → G, x ∈ U → Z t₀ = z₀ x ∧
      ∀ t ∈ J, HasDerivWithinAt Z (A x t (Z t)) J t := by
    by_cases hx : x ∈ U
    · obtain ⟨Z, hinit, hZ⟩ := exists_linear_ode_solution_on_interval hJ ht₀
        (hA.continuousOn.uncurry_left x hx) (z₀ x)
      exact ⟨Z, fun _ => ⟨hinit, hZ⟩⟩
    · exact ⟨fun _ => z₀ x, fun hx' => (hx hx').elim⟩
  choose Z hZ using hex
  have hinit : ∀ x ∈ U, Z x t₀ = z₀ x := fun x hx => (hZ x hx).1
  have hderiv : ∀ x ∈ U, ∀ t ∈ J,
      HasDerivWithinAt (Z x) (A x t (Z x t)) J t := fun x hx => (hZ x hx).2
  exact ⟨Z, linear_ode_solution_contDiffOn_interval hJ ht₀ hU hA hz₀ hinit hderiv,
    hinit, hderiv⟩

end DifferentialGeometry.Analysis.ODE.Flow
