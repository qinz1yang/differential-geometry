import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.C1Regularity
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M]

omit [CompleteSpace E] in
theorem chartDeriv_shift {a b r : ℝ} (phi : ℝ → E)
    (u : timeH1 E (b - a))
    (hrep : EqOn u.toFun (fun s ↦ phi (a + s))
      (Icc (0 : ℝ) (b - a)))
    (hr : r ∈ Icc (0 : ℝ) (b - a)) :
    derivWithin phi (Icc a b) (a + r) =
      derivWithin u.toFun (Icc (0 : ℝ) (b - a)) r := by
  let s : Set ℝ := Icc (0 : ℝ) (b - a)
  have hset : a +ᵥ s = Icc a b := by
    ext x
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub,
      mem_Icc, s]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have heq : Filter.EventuallyEq (nhdsWithin r s) u.toFun
      (fun x ↦ phi (a + x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hrep hx
  calc
    derivWithin phi (Icc a b) (a + r) =
        derivWithin (fun x ↦ phi (a + x)) s r := by
      rw [derivWithin_comp_const_add, hset]
    _ = derivWithin u.toFun s r :=
      (heq.derivWithin_eq_of_mem (by simpa only [s] using hr)).symm

omit [CompleteSpace E] in
theorem chartDeriv_change
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {s : Set ℝ} {x : ℝ} (p q : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma s)
    (hx : x ∈ s)
    (huniq : UniqueDiffWithinAt ℝ s x)
    (hp : MapsTo gamma s (chartAt H p).source)
    (hq : gamma x ∈ (chartAt H q).source) :
    derivWithin ((extChartAt I q) ∘ gamma) s x =
      tangentCoordChange I p q (gamma x)
        (derivWithin ((extChartAt I p) ∘ gamma) s x) := by
  let f : E → E := (extChartAt I q) ∘ (extChartAt I p).symm
  have hphi : ContDiffOn ℝ 1 ((extChartAt I p) ∘ gamma) s := by
    have hchart := ((contMDiffOn_iff_target.mp hgamma).2 p).mono
      (fun y hy ↦ ⟨hy, by
        rw [extChartAt_source]
        exact hp hy⟩)
    exact hchart.contDiffOn
  have hder : HasDerivWithinAt ((extChartAt I p) ∘ gamma)
      (derivWithin ((extChartAt I p) ∘ gamma) s x) s x :=
    (hphi.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hpsrc : gamma x ∈ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact hp hx
  have hqsrc : gamma x ∈ (extChartAt I q).source := by
    rw [extChartAt_source]
    exact hq
  have hmap : MapsTo ((extChartAt I p) ∘ gamma) s (range I) := by
    intro y hy
    exact extChartAt_target_subset_range p
      ((extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hp hy))
  have hfun : EqOn ((extChartAt I q) ∘ gamma)
      (f ∘ ((extChartAt I p) ∘ gamma)) s := by
    intro y hy
    simp only [f, Function.comp_apply]
    exact congrArg (extChartAt I q) ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hp hy)).symm
  have htrans := hasFDerivWithinAt_tangentCoordChange (I := I)
    (show gamma x ∈ (extChartAt I p).source ∩
        (extChartAt I q).source from ⟨hpsrc, hqsrc⟩)
  have hchain : HasDerivWithinAt
      (f ∘ ((extChartAt I p) ∘ gamma))
      (tangentCoordChange I p q (gamma x)
        (derivWithin ((extChartAt I p) ∘ gamma) s x)) s x := by
    exact htrans.comp_hasDerivWithinAt_of_eq x hder hmap rfl
  exact (hchain.congr_of_mem hfun hx).derivWithin huniq

omit [CompleteSpace E] in
theorem chartDeriv_overlap
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 < T) (p q : M) (gamma : ℝ → M) (u v : timeH1 E T)
    (hp : MapsTo gamma (Icc (0 : ℝ) T) (chartAt H p).source)
    (hq : MapsTo gamma (Icc (0 : ℝ) T) (chartAt H q).source)
    (hup : EqOn u.toFun ((extChartAt I p) ∘ gamma) (Icc (0 : ℝ) T))
    (huq : EqOn v.toFun ((extChartAt I q) ∘ gamma) (Icc (0 : ℝ) T))
    (hu : ContDiffOn ℝ 1 u.toFun (Icc (0 : ℝ) T))
    (hv : ContDiffOn ℝ 1 v.toFun (Icc (0 : ℝ) T)) :
    EqOn (fun t ↦ derivWithin v.toFun (Icc (0 : ℝ) T) t)
      (fun t ↦ tangentCoordChange I p q (gamma t)
        (derivWithin u.toFun (Icc (0 : ℝ) T) t))
      (Icc (0 : ℝ) T) := by
  let s : Set ℝ := Icc (0 : ℝ) T
  let f : E → E := (extChartAt I q) ∘ (extChartAt I p).symm
  have humap : MapsTo u.toFun s (range I) := by
    intro r hr
    rw [hup hr]
    exact extChartAt_target_subset_range p
      ((extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hp hr))
  have hfun : EqOn v.toFun (f ∘ u.toFun) s := by
    intro r hr
    have hpsrc : gamma r ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hp hr
    rw [huq hr]
    simp only [f, Function.comp_apply]
    rw [hup hr]
    exact congrArg (extChartAt I q) ((extChartAt I p).left_inv hpsrc).symm
  intro t ht
  have hpsrc : gamma t ∈ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact hp ht
  have hqsrc : gamma t ∈ (extChartAt I q).source := by
    rw [extChartAt_source]
    exact hq ht
  have hdu : HasDerivWithinAt u.toFun (derivWithin u.toFun s t) s t :=
    (hu.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hdv : HasDerivWithinAt v.toFun (derivWithin v.toFun s t) s t :=
    (hv.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have htrans := hasFDerivWithinAt_tangentCoordChange (I := I)
    (show gamma t ∈ (extChartAt I p).source ∩ (extChartAt I q).source from
      ⟨hpsrc, hqsrc⟩)
  have hchain : HasDerivWithinAt (f ∘ u.toFun)
      (tangentCoordChange I p q (gamma t) (derivWithin u.toFun s t)) s t := by
    exact htrans.comp_hasDerivWithinAt_of_eq t hdu humap (hup ht).symm
  have hvchain : HasDerivWithinAt v.toFun
      (tangentCoordChange I p q (gamma t) (derivWithin u.toFun s t)) s t :=
    hchain.congr_of_mem hfun ht
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv s hdv hvchain

omit [CompleteSpace E] in
theorem chartDeriv_head
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T L : ℝ} (hT : 0 < T) (hTL : T ≤ L) (p q : M)
    (gamma : ℝ → M) (u : timeH1 E T) (v : timeH1 E L)
    (hp : MapsTo gamma (Icc (0 : ℝ) T) (chartAt H p).source)
    (hq : MapsTo gamma (Icc (0 : ℝ) T) (chartAt H q).source)
    (hup : EqOn u.toFun ((extChartAt I p) ∘ gamma) (Icc (0 : ℝ) T))
    (huq : EqOn v.toFun ((extChartAt I q) ∘ gamma) (Icc (0 : ℝ) T))
    (hu : ContDiffOn ℝ 1 u.toFun (Icc (0 : ℝ) T))
    (hv : ContDiffOn ℝ 1 v.toFun (Icc (0 : ℝ) L)) :
    EqOn (fun t ↦ derivWithin v.toFun (Icc (0 : ℝ) L) t)
      (fun t ↦ tangentCoordChange I p q (gamma t)
        (derivWithin u.toFun (Icc (0 : ℝ) T) t))
      (Icc (0 : ℝ) T) := by
  let s : Set ℝ := Icc (0 : ℝ) T
  let s' : Set ℝ := Icc (0 : ℝ) L
  let f : E → E := (extChartAt I q) ∘ (extChartAt I p).symm
  have hsub : s ⊆ s' := by
    exact Icc_subset_Icc_right hTL
  have humap : MapsTo u.toFun s (range I) := by
    intro r hr
    rw [hup hr]
    exact extChartAt_target_subset_range p
      ((extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hp hr))
  have hfun : EqOn v.toFun (f ∘ u.toFun) s := by
    intro r hr
    have hpsrc : gamma r ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hp hr
    rw [huq hr]
    simp only [f, Function.comp_apply]
    rw [hup hr]
    exact congrArg (extChartAt I q) ((extChartAt I p).left_inv hpsrc).symm
  intro t ht
  have hpsrc : gamma t ∈ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact hp ht
  have hqsrc : gamma t ∈ (extChartAt I q).source := by
    rw [extChartAt_source]
    exact hq ht
  have hdu : HasDerivWithinAt u.toFun (derivWithin u.toFun s t) s t :=
    (hu.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hdv' : HasDerivWithinAt v.toFun (derivWithin v.toFun s' t) s' t :=
    (hv.differentiableOn (by norm_num) t (hsub ht)).hasDerivWithinAt
  have hdv : HasDerivWithinAt v.toFun (derivWithin v.toFun s' t) s t :=
    hdv'.mono hsub
  have htrans := hasFDerivWithinAt_tangentCoordChange (I := I)
    (show gamma t ∈ (extChartAt I p).source ∩ (extChartAt I q).source from
      ⟨hpsrc, hqsrc⟩)
  have hchain : HasDerivWithinAt (f ∘ u.toFun)
      (tangentCoordChange I p q (gamma t) (derivWithin u.toFun s t)) s t := by
    exact htrans.comp_hasDerivWithinAt_of_eq t hdu humap (hup ht).symm
  have hvchain : HasDerivWithinAt v.toFun
      (tangentCoordChange I p q (gamma t) (derivWithin u.toFun s t)) s t :=
    hchain.congr_of_mem hfun ht
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv s hdv hvchain

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
