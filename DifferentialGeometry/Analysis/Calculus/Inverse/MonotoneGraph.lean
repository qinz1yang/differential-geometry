import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

theorem exists_contDiffOn_implicit_graph_of_deriv_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ∞ω} (hn : n ≠ 0) {U : Set E} (hU : IsOpen U)
    {F : E × ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ n F (U ×ˢ Ioo a b))
    (hc : ∀ x ∈ U, ContinuousOn (fun t => F (x, t)) (Icc a b))
    (hderiv : ∀ x ∈ U, ∀ t ∈ Ioo a b, deriv (fun s => F (x, s)) t < 0)
    (ha : ∀ x ∈ U, 0 < F (x, a)) (hb : ∀ x ∈ U, F (x, b) < 0) :
    ∃ g : E → ℝ, ContDiffOn ℝ n g U ∧
      (∀ x ∈ U, g x ∈ Ioo a b ∧ F (x, g x) = 0) ∧
      ∀ x ∈ U, ∀ t ∈ Icc a b,
        (F (x, t) = 0 ↔ t = g x) ∧
        (0 ≤ F (x, t) ↔ t ≤ g x) ∧ (0 < F (x, t) ↔ t < g x) := by
  classical
  have hanti (x : E) (hx : x ∈ U) : StrictAntiOn (fun t => F (x, t)) (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hc x hx)
    simpa only [interior_Icc] using hderiv x hx
  have hroot (x : E) (hx : x ∈ U) : ∃ t ∈ Ioo a b, F (x, t) = 0 := by
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc' hab.le (hc x hx) ⟨(hb x hx).le, (ha x hx).le⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, hFt⟩
    · intro hh
      rw [← hh] at hFt
      exact (ha x hx).ne' hFt
    · intro hh
      rw [hh] at hFt
      exact (hb x hx).ne hFt
  let g : E → ℝ := fun x => if hx : x ∈ U then Classical.choose (hroot x hx) else 0
  have hspec (x : E) (hx : x ∈ U) : g x ∈ Ioo a b ∧ F (x, g x) = 0 := by
    dsimp only [g]
    rw [dif_pos hx]
    exact Classical.choose_spec (hroot x hx)
  have huniq (x : E) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Icc a b) :
      F (x, t) = 0 ↔ t = g x := by
    constructor
    · intro hh
      exact (hanti x hx).injOn ht (Ioo_subset_Icc_self (hspec x hx).1)
        (hh.trans (hspec x hx).2.symm)
    · rintro rfl
      exact (hspec x hx).2
  refine ⟨g, ?_, hspec, ?_⟩
  · intro x hx
    have hFx : ContDiffAt ℝ n F (x, g x) :=
      hF.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hx, (hspec x hx).1⟩)
    have hdf : HasFDerivAt (fun t => F (x, t))
        ((fderiv ℝ F (x, g x)).comp (ContinuousLinearMap.inr ℝ E ℝ)) (g x) := by
      exact (hFx.differentiableAt hn).hasFDerivAt.comp (g x)
        ((hasFDerivAt_const x (g x)).prodMk (hasFDerivAt_id (g x)))
    have hne : ((fderiv ℝ F (x, g x)).comp (ContinuousLinearMap.inr ℝ E ℝ)) 1 ≠ 0 := by
      rw [← hdf.hasDerivAt.deriv]
      exact (hderiv x hx (g x) (hspec x hx).1).ne
    have hinv : ((fderiv ℝ F (x, g x)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible :=
      ⟨_, (hdf.hasDerivAt.hasFDerivAt_equiv hne).unique hdf⟩
    let ψ := hFx.implicitFunction hn hinv
    have hψ : ContDiffAt ℝ n ψ x := hFx.contDiffAt_implicitFunction hn hinv
    have hψx : ψ x = g x := hFx.implicitFunction_apply_self hn hinv
    have hψmem : ∀ᶠ y in 𝓝 x, ψ y ∈ Ioo a b := by
      apply hψ.continuousAt (isOpen_Ioo.mem_nhds _)
      rw [hψx]
      exact (hspec x hx).1
    have heq : g =ᶠ[𝓝 x] ψ := by
      filter_upwards [hU.mem_nhds hx, hψmem, hFx.eventually_apply_implicitFunction hn hinv]
        with y hy hyt heq
      apply ((huniq y hy (ψ y) (Ioo_subset_Icc_self hyt)).mp _).symm
      exact heq.trans (hspec x hx).2
    exact (hψ.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro x hx t ht
    have hg : g x ∈ Icc a b := Ioo_subset_Icc_self (hspec x hx).1
    refine ⟨huniq x hx t ht, ?_, ?_⟩
    · rw [← (hspec x hx).2]
      exact (hanti x hx).le_iff_ge hg ht
    · rw [← (hspec x hx).2]
      exact (hanti x hx).lt_iff_gt hg ht


theorem exists_isOpen_contDiffOn_implicit_graph_of_injOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ∞ω} (hn : n ≠ 0) {W : Set (E × ℝ)} (hW : IsOpen W)
    {F : E × ℝ → ℝ} (hF : ContDiffOn ℝ n F W)
    (hregular : ∀ p ∈ W, F p = 0 → fderiv ℝ F p (0, 1) ≠ 0)
    (hinj : InjOn (Prod.fst : E × ℝ → E) (W ∩ {p | F p = 0})) :
    ∃ O : Set E, IsOpen O ∧ ∃ g : E → ℝ, ContDiffOn ℝ n g O ∧
      W ∩ {p | F p = 0} = {p : E × ℝ | p.1 ∈ O ∧ p.2 = g p.1} := by
  classical
  have hlocal (p : E × ℝ) (hp : p ∈ W) (hz : F p = 0) :
      ∃ ψ : E → ℝ, ContDiffAt ℝ n ψ p.1 ∧ ψ p.1 = p.2 ∧
        ∀ᶠ x in 𝓝 p.1, (x, ψ x) ∈ W ∧ F (x, ψ x) = 0 := by
    have hFp : ContDiffAt ℝ n F p := hF.contDiffAt (hW.mem_nhds hp)
    have hd : HasFDerivAt (fun t => F (p.1, t))
        ((fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ E ℝ)) p.2 :=
      (hFp.differentiableAt hn).hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))
    have hne : ((fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ E ℝ)) 1 ≠ 0 :=
      hregular p hp hz
    have hinv : ((fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible :=
      ⟨_, (hd.hasDerivAt.hasFDerivAt_equiv hne).unique hd⟩
    let ψ := hFp.implicitFunction hn hinv
    have hψ : ContDiffAt ℝ n ψ p.1 := hFp.contDiffAt_implicitFunction hn hinv
    have hψp : ψ p.1 = p.2 := hFp.implicitFunction_apply_self hn hinv
    refine ⟨ψ, hψ, hψp, ?_⟩
    have hmem : ∀ᶠ x in 𝓝 p.1, (x, ψ x) ∈ W :=
      (continuousAt_id.prodMk hψ.continuousAt)
        (hW.mem_nhds (by simpa only [hψp, id_eq, Prod.mk.eta] using hp))
    filter_upwards [hmem, hFp.eventually_apply_implicitFunction hn hinv] with x hx hxF
    exact ⟨hx, hxF.trans hz⟩
  let O : Set E := {x | ∃ t, (x, t) ∈ W ∧ F (x, t) = 0}
  let g : E → ℝ := fun x => if hx : x ∈ O then Classical.choose hx else 0
  have hspec (x : E) (hx : x ∈ O) : (x, g x) ∈ W ∧ F (x, g x) = 0 := by
    dsimp only [g]
    rw [dif_pos hx]
    exact Classical.choose_spec hx
  have huniq (x : E) (hx : x ∈ O) (t : ℝ) (ht : (x, t) ∈ W ∧ F (x, t) = 0) :
      t = g x := congrArg Prod.snd (hinj ht (hspec x hx) rfl)
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ψ, _, _, hψ⟩ := hlocal (x, g x) (hspec x hx).1 (hspec x hx).2
    exact Filter.mem_of_superset hψ (fun y hy => ⟨ψ y, hy⟩)
  refine ⟨O, hO, g, ?_, ?_⟩
  · intro x hx
    obtain ⟨ψ, hψ, _, hψmem⟩ := hlocal (x, g x) (hspec x hx).1 (hspec x hx).2
    have heq : g =ᶠ[𝓝 x] ψ := by
      filter_upwards [hψmem] with y hy
      exact (huniq y ⟨ψ y, hy⟩ (ψ y) hy).symm
    exact (hψ.congr_of_eventuallyEq heq).contDiffWithinAt
  · ext p
    constructor
    · intro hp
      exact ⟨⟨p.2, hp⟩, huniq p.1 ⟨p.2, hp⟩ p.2 hp⟩
    · rintro ⟨hp, heq⟩
      have h := hspec p.1 hp
      change p ∈ W ∧ F p = 0
      simpa only [← heq, Prod.mk.eta] using h


end DifferentialGeometry.Analysis
