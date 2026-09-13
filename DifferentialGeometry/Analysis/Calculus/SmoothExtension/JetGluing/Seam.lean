import DifferentialGeometry.Analysis.Calculus.SmoothExtension.JetGluing.Smooth
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace Analysis
namespace SmoothExtension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

theorem contDiffOn_Icc_ite_of_jet_match {fL fR : ℝ → F} {a b x₀ : ℝ} (ha : a < x₀) (hb : x₀ < b)
    (hL : ContDiffOn ℝ ∞ fL (Icc a x₀)) (hR : ContDiffOn ℝ ∞ fR (Icc x₀ b))
    (hjet : ∀ n : ℕ, iteratedDerivWithin n fL (Icc a x₀) x₀
      = iteratedDerivWithin n fR (Icc x₀ b) x₀) :
    ContDiffOn ℝ ∞ (fun t => if t ≤ x₀ then fL t else fR t) (Icc a b) := by
  set f : ℝ → F := fun t => if t ≤ x₀ then fL t else fR t with hf_def
  set pL : ℝ → FormalMultilinearSeries ℝ ℝ F := ftaylorSeriesWithin ℝ fL (Icc a x₀) with hpL_def
  set pR : ℝ → FormalMultilinearSeries ℝ ℝ F := ftaylorSeriesWithin ℝ fR (Icc x₀ b) with hpR_def
  set p : ℝ → FormalMultilinearSeries ℝ ℝ F :=
    fun t => if t ≤ x₀ then pL t else pR t with hp_def
  have hTL : HasFTaylorSeriesUpToOn ∞ fL pL (Icc a x₀) :=
    hL.ftaylorSeriesWithin (uniqueDiffOn_Icc ha)
  have hTR : HasFTaylorSeriesUpToOn ∞ fR pR (Icc x₀ b) :=
    hR.ftaylorSeriesWithin (uniqueDiffOn_Icc hb)
  have hjetF : ∀ n : ℕ, pL x₀ n = pR x₀ n := by
    intro n
    have heL := congrFun (iteratedFDerivWithin_eq_equiv_comp (𝕜 := ℝ) (n := n) (f := fL)
      (s := Icc a x₀)) x₀
    have heR := congrFun (iteratedFDerivWithin_eq_equiv_comp (𝕜 := ℝ) (n := n) (f := fR)
      (s := Icc x₀ b)) x₀
    simp only [Function.comp_apply] at heL heR
    have hLR : iteratedFDerivWithin ℝ n fL (Icc a x₀) x₀
        = iteratedFDerivWithin ℝ n fR (Icc x₀ b) x₀ := by
      rw [heL, heR, hjet n]
    simpa only [hpL_def, hpR_def, ftaylorSeriesWithin] using hLR
  have hEqL : ∀ m : ℕ, Set.EqOn (fun y => p y m) (fun y => pL y m) (Icc a x₀) := by
    intro m y hy
    simp only [hp_def, if_pos hy.2]
  have hEqR : ∀ m : ℕ, Set.EqOn (fun y => p y m) (fun y => pR y m) (Icc x₀ b) := by
    intro m y hy
    rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    · subst hy0
      simp only [hp_def, if_pos (le_refl x₀), hjetF]
    · simp only [hp_def, if_neg (not_le.mpr hy0)]
  have hzero : ∀ x ∈ Icc a b, (p x 0).curry0 = f x := by
    intro x hx
    by_cases hx' : x ≤ x₀
    · have hval : (pL x 0).curry0 = fL x := hTL.zero_eq x ⟨hx.1, hx'⟩
      simp only [hp_def, hf_def, if_pos hx', hval]
    · have hx'' : x₀ ≤ x := le_of_lt (not_le.mp hx')
      have hval : (pR x 0).curry0 = fR x := hTR.zero_eq x ⟨hx'', hx.2⟩
      simp only [hp_def, hf_def, if_neg hx', hval]
  have hm_lt : ∀ m : ℕ, (m : WithTop ℕ∞) < ∞ := fun m => by
    exact_mod_cast (Nat.cast_lt.mpr m.lt_succ_self).trans_le le_top
  have hderiv : ∀ m : ℕ, ∀ x ∈ Icc a b,
      HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft (Icc a b) x := by
    intro m x hx
    have hpL_succ : ∀ y : ℝ, y ≤ x₀ → p y m.succ = pL y m.succ := fun y hy => by
      simp only [hp_def, if_pos hy]
    have hpR_succ : ∀ y : ℝ, x₀ ≤ y → p y m.succ = pR y m.succ := by
      intro y hy
      rcases eq_or_lt_of_le hy with hy0 | hy0
      · subst hy0; simp only [hp_def, if_pos (le_refl x₀), hjetF]
      · simp only [hp_def, if_neg (not_le.mpr hy0)]
    rcases lt_trichotomy x x₀ with hlt | heq | hgt
    · have hdL : HasFDerivWithinAt (fun y => pL y m) (pL x m.succ).curryLeft (Icc a x₀) x :=
        hTL.fderivWithin m (hm_lt m) x ⟨hx.1, hlt.le⟩
      have hmem : Icc a x₀ ∈ 𝓝[Icc a b] x :=
        mem_of_superset
          (inter_mem (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hlt)) self_mem_nhdsWithin)
          (fun y hy => ⟨hy.2.1, hy.1.le⟩)
      have hdL' : HasFDerivWithinAt (fun y => pL y m) (pL x m.succ).curryLeft (Icc a b) x :=
        hdL.mono_of_mem_nhdsWithin hmem
      have hee : (fun y => p y m) =ᶠ[𝓝[Icc a b] x] (fun y => pL y m) :=
        eventuallyEq_iff_exists_mem.mpr ⟨Icc a x₀, hmem, fun y hy => hEqL m hy⟩
      have hfd : HasFDerivWithinAt (fun y => p y m) (pL x m.succ).curryLeft (Icc a b) x :=
        hdL'.congr_of_eventuallyEq hee (hEqL m ⟨hx.1, hlt.le⟩)
      rw [hpL_succ x hlt.le]
      exact hfd
    · subst x
      have hdL0 : HasFDerivWithinAt (fun y => pL y m) (pL x₀ m.succ).curryLeft (Icc a x₀) x₀ :=
        hTL.fderivWithin m (hm_lt m) x₀ ⟨ha.le, le_refl x₀⟩
      have hdL0' : HasFDerivWithinAt (fun y => p y m) (pL x₀ m.succ).curryLeft (Icc a x₀) x₀ :=
        hdL0.congr (hEqL m) (hEqL m ⟨ha.le, le_refl x₀⟩)
      have hdR0 : HasFDerivWithinAt (fun y => pR y m) (pR x₀ m.succ).curryLeft (Icc x₀ b) x₀ :=
        hTR.fderivWithin m (hm_lt m) x₀ ⟨le_refl x₀, hb.le⟩
      have hdR0' : HasFDerivWithinAt (fun y => p y m) (pL x₀ m.succ).curryLeft (Icc x₀ b) x₀ := by
        have hval : (pR x₀ m.succ).curryLeft = (pL x₀ m.succ).curryLeft := by rw [hjetF]
        rw [← hval]
        exact hdR0.congr (hEqR m) (hEqR m ⟨le_refl x₀, hb.le⟩)
      have hunion : HasFDerivWithinAt (fun y => p y m) (pL x₀ m.succ).curryLeft
          (Icc a x₀ ∪ Icc x₀ b) x₀ := hdL0'.union hdR0'
      rw [Set.Icc_union_Icc_eq_Icc ha.le hb.le] at hunion
      rw [hpL_succ x₀ (le_refl x₀)]
      exact hunion
    · have hdR : HasFDerivWithinAt (fun y => pR y m) (pR x m.succ).curryLeft (Icc x₀ b) x :=
        hTR.fderivWithin m (hm_lt m) x ⟨hgt.le, hx.2⟩
      have hmem : Icc x₀ b ∈ 𝓝[Icc a b] x :=
        mem_of_superset
          (inter_mem (nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hgt)) self_mem_nhdsWithin)
          (fun y hy => ⟨hy.1.le, hy.2.2⟩)
      have hdR' : HasFDerivWithinAt (fun y => pR y m) (pR x m.succ).curryLeft (Icc a b) x :=
        hdR.mono_of_mem_nhdsWithin hmem
      have hee : (fun y => p y m) =ᶠ[𝓝[Icc a b] x] (fun y => pR y m) :=
        eventuallyEq_iff_exists_mem.mpr ⟨Icc x₀ b, hmem, fun y hy => hEqR m hy⟩
      have hfd : HasFDerivWithinAt (fun y => p y m) (pR x m.succ).curryLeft (Icc a b) x :=
        hdR'.congr_of_eventuallyEq hee (hEqR m ⟨hgt.le, hx.2⟩)
      rw [hpR_succ x hgt.le]
      exact hfd
  have hTaylor : HasFTaylorSeriesUpToOn ∞ f p (Icc a b) :=
    (hasFTaylorSeriesUpToOn_top_iff' (le_refl _)).mpr ⟨hzero, hderiv⟩
  exact hTaylor.contDiffOn

theorem contDiffAt_ite_of_jet_match {fL fR : ℝ → F} {a b x₀ : ℝ} (ha : a < x₀) (hb : x₀ < b)
    (hL : ContDiffOn ℝ ∞ fL (Icc a x₀)) (hR : ContDiffOn ℝ ∞ fR (Icc x₀ b))
    (hjet : ∀ n : ℕ, iteratedDerivWithin n fL (Icc a x₀) x₀
      = iteratedDerivWithin n fR (Icc x₀ b) x₀) :
    ContDiffAt ℝ ∞ (fun t => if t ≤ x₀ then fL t else fR t) x₀ :=
  (contDiffOn_Icc_ite_of_jet_match ha hb hL hR hjet).contDiffAt (Icc_mem_nhds ha hb)

theorem contMDiffAt_ite_of_jet_match {fL fR : ℝ → M} {a b x₀ : ℝ} (ha : a < x₀) (hb : x₀ < b)
    (hval : fL x₀ = fR x₀)
    (hcL : ContinuousWithinAt fL (Iic x₀) x₀) (hcR : ContinuousWithinAt fR (Ici x₀) x₀)
    (hL : ContDiffOn ℝ ∞ (extChartAt I' (fL x₀) ∘ fL) (Icc a x₀))
    (hR : ContDiffOn ℝ ∞ (extChartAt I' (fL x₀) ∘ fR) (Icc x₀ b))
    (hjet : ∀ m : ℕ, iteratedDerivWithin m (extChartAt I' (fL x₀) ∘ fL) (Icc a x₀) x₀
      = iteratedDerivWithin m (extChartAt I' (fL x₀) ∘ fR) (Icc x₀ b) x₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) I' ∞ (fun t => if t ≤ x₀ then fL t else fR t) x₀ := by
  set G : ℝ → M := fun t => if t ≤ x₀ then fL t else fR t with hG_def
  set κ : M → E' := fun y => extChartAt I' (fL x₀) y with hκ_def
  have hGx : G x₀ = fL x₀ := by simp only [hG_def, if_pos le_rfl]
  have hglue : κ ∘ G = fun t : ℝ => if t ≤ x₀ then κ (fL t) else κ (fR t) := by
    funext t
    by_cases h : t ≤ x₀
    · simp only [hG_def, hκ_def, Function.comp_apply, if_pos h]
    · simp only [hG_def, hκ_def, Function.comp_apply, if_neg h]
  have hchart : ContDiffAt ℝ ∞ (fun t : ℝ => if t ≤ x₀ then κ (fL t) else κ (fR t)) x₀ :=
    contDiffAt_ite_of_jet_match ha hb hL hR hjet
  have hcont : ContinuousAt G x₀ := by
    have h1 : ContinuousWithinAt G (Iic x₀) x₀ :=
      hcL.congr (fun t ht => by simp only [hG_def, if_pos (mem_Iic.mp ht)]) hGx
    have h2 : ContinuousWithinAt G (Ici x₀) x₀ := by
      refine hcR.congr (fun t ht => ?_) (by simp only [hG_def, if_pos le_rfl]; exact hval)
      rcases eq_or_lt_of_le (mem_Ici.mp ht) with h | h
      · subst h
        simp only [hG_def, if_pos le_rfl]
        exact hval
      · simp only [hG_def, if_neg (not_le.mpr h)]
    simpa only [Iic_union_Ici, continuousWithinAt_univ] using h1.union h2
  refine (contMDiffAt_iff_target).mpr ⟨hcont, ?_⟩
  rw [hGx]
  change ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E') ∞ (κ ∘ G) x₀
  rw [hglue]
  exact ContDiffAt.contMDiffAt hchart


end SmoothExtension
end Analysis
end DifferentialGeometry

end
