import DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Compactness.Lindelof
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Mathlib.Topology.Piecewise
import Mathlib.Geometry.Manifold.HasGroupoid

set_option autoImplicit false

open Filter Function MeasureTheory Set
open scoped Manifold Topology Interval

namespace AbsolutelyContinuousOnInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem ae_mdifferentiableAt_of_extChartAt
    {a b : ℝ} {gamma : ℝ → M} (p : M)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) a b)
    (hsrc : MapsTo gamma (uIcc a b) (chartAt H p).source) :
    ∀ᵐ r ∂volume.restrict (uIcc a b), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r := by
  have hmaps : MapsTo ((extChartAt I p) ∘ gamma) (uIcc a b)
      (extChartAt I p).target := by
    intro r hr
    exact (extChartAt I p).map_source (by
      simpa only [extChartAt_source] using hsrc hr)
  have hcont : ContinuousOn gamma (uIcc a b) := by
    have h := (continuousOn_extChartAt_symm p).comp hAC.continuousOn hmaps
    refine h.congr ?_
    intro r hr
    exact ((extChartAt I p).left_inv (by
      simpa only [extChartAt_source] using hsrc hr)).symm
  have hmem : ∀ᵐ r ∂volume.restrict (uIcc a b), r ∈ Ioo (min a b) (max a b) := by
    rw [uIcc, ← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hdiff : ∀ᵐ r ∂volume.restrict (uIcc a b),
      r ∈ uIcc a b → DifferentiableAt ℝ ((extChartAt I p) ∘ gamma) r :=
    ae_mono Measure.restrict_le_self
      hAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  filter_upwards [hdiff, hmem] with r hr hri
  have hcc : r ∈ uIcc a b := ⟨hri.1.le, hri.2.le⟩
  apply (mdifferentiableAt_iff_target_of_mem_source (hsrc hcc)).mpr
  refine ⟨(hcont r hcc).continuousAt (Icc_mem_nhds hri.1 hri.2), ?_⟩
  exact mdifferentiableAt_iff_differentiableAt.mpr (hr hcc)

end AbsolutelyContinuousOnInterval

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def absolutelyContinuousOnInterval (gamma : ℝ → M) (a b : ℝ) : Prop :=
  ContinuousOn gamma (uIcc a b) ∧
    ∀ (p : M) (c d : ℝ), uIcc c d ⊆ uIcc a b →
      MapsTo gamma (uIcc c d) (chartAt H p).source →
      AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) c d

variable {I} {gamma : ℝ → M} {a b c d : ℝ}

theorem absolutelyContinuousOnInterval_continuousOn
    (h : absolutelyContinuousOnInterval I gamma a b) :
    ContinuousOn gamma (uIcc a b) := h.1

theorem absolutelyContinuousOnInterval_mono
    (h : absolutelyContinuousOnInterval I gamma a b) (hsub : uIcc c d ⊆ uIcc a b) :
    absolutelyContinuousOnInterval I gamma c d :=
  ⟨h.1.mono hsub, fun p e f hef hmaps => h.2 p e f (hef.trans hsub) hmaps⟩

theorem absolutelyContinuousOnInterval_symm
    (h : absolutelyContinuousOnInterval I gamma a b) :
    absolutelyContinuousOnInterval I gamma b a := by
  simpa only [absolutelyContinuousOnInterval, uIcc_comm] using h

variable [IsManifold I 1 M]

theorem absolutelyContinuousOnInterval_of_contMDiffOn
    (h : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (uIcc a b)) :
    absolutelyContinuousOnInterval I gamma a b := by
  refine ⟨h.continuousOn, fun p c d hsub hmaps => ?_⟩
  exact ((contMDiffOn_extChartAt (I := I) (x := p) (n := 1)).comp
    (h.mono hsub) hmaps).contDiffOn.absolutelyContinuousOnInterval

variable [FiniteDimensional ℝ E]

theorem absolutelyContinuousOnInterval_ae_mdifferentiableAt
    (h : absolutelyContinuousOnInterval I gamma a b) :
    ∀ᵐ t ∂volume.restrict (uIcc a b), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t := by
  have hlocal : ∀ t ∈ Ioo (min a b) (max a b), ∃ c d : ℝ,
      Icc c d ∈ 𝓝 t ∧
      ∀ᵐ r ∂volume.restrict (Icc c d), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r := by
    intro t ht
    have htcc : t ∈ uIcc a b := ⟨ht.1.le, ht.2.le⟩
    have hcont := (h.1 t htcc).continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hsrc : gamma ⁻¹' (chartAt H (gamma t)).source ∈ 𝓝 t :=
      hcont.preimage_mem_nhds ((chartAt H (gamma t)).open_source.mem_nhds (mem_chart_source H (gamma t)))
    obtain ⟨c, d, htcd, hnhds, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds
      (inter_mem (Icc_mem_nhds ht.1 ht.2) hsrc)
    have hcd : c ≤ d := htcd.1.trans htcd.2
    have hmaps : MapsTo gamma (uIcc c d) (chartAt H (gamma t)).source := by
      rw [uIcc_of_le hcd]
      exact fun r hr => (hsub hr).2
    have hac := h.2 (gamma t) c d (by
      rw [uIcc_of_le hcd]
      exact fun r hr => (hsub hr).1) hmaps
    refine ⟨c, d, hnhds, ?_⟩
    simpa only [uIcc_of_le hcd] using hac.ae_mdifferentiableAt_of_extChartAt (gamma t) hmaps
  choose c d hnhds hae using hlocal
  obtain ⟨s, hs, hcover⟩ := (isLindelof_iff_lindelofSpace.mpr
    (inferInstance : LindelofSpace (Ioo (min a b) (max a b)))).elim_nhds_subcover'
      (fun t ht => Icc (c t ht) (d t ht)) hnhds
  have hunion : ∀ᵐ r ∂volume.restrict
      (⋃ t ∈ s, Icc (c t t.2) (d t t.2)), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r :=
    (ae_restrict_biUnion_iff _ hs _).mpr (fun t _ => hae t t.2)
  have hinner := ae_mono (Measure.restrict_mono_set volume hcover) hunion
  rw [uIcc, ← restrict_Ioo_eq_restrict_Icc]
  exact hinner

end Manifold

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem absolutelyContinuousOnInterval_piecewise_Iic
    {alpha beta : ℝ → M} {a c b : ℝ}
    (hα : absolutelyContinuousOnInterval I alpha a c)
    (hβ : absolutelyContinuousOnInterval I beta c b)
    (hac : a ≤ c) (hcb : c ≤ b) (hnode : alpha c = beta c) :
    absolutelyContinuousOnInterval I (piecewise (Iic c) alpha beta) a b := by
  classical
  let gamma := piecewise (Iic c) alpha beta
  have hleft : ∀ t ≤ c, gamma t = alpha t := fun t ht => piecewise_eq_of_mem _ _ _ ht
  have hright : ∀ t, c ≤ t → gamma t = beta t := by
    intro t ht
    by_cases htc : t = c
    · subst t
      exact (hleft c le_rfl).trans hnode
    · exact piecewise_eq_of_notMem _ _ _ (not_le.mpr (lt_of_le_of_ne ht (Ne.symm htc)))
  constructor
  · rw [uIcc_of_le (hac.trans hcb)]
    apply ContinuousOn.piecewise
    · intro t ht
      have htc : t = c := by simpa only [frontier_Iic, mem_singleton_iff] using ht.2
      simpa only [htc] using hnode
    · apply hα.1.mono
      rw [isClosed_Iic.closure_eq, uIcc_of_le hac]
      exact fun t ht => ⟨ht.1.1, ht.2⟩
    · apply hβ.1.mono
      rw [compl_Iic, closure_Ioi, uIcc_of_le hcb]
      exact fun t ht => ⟨ht.2, ht.1.2⟩
  have hordered : ∀ (p : M) (x y : ℝ), x ≤ y → Icc x y ⊆ Icc a b →
      MapsTo gamma (Icc x y) (chartAt H p).source →
      AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) x y := by
    intro p x y hxy hsub hsrc
    have hax : a ≤ x := (hsub (left_mem_Icc.mpr hxy)).1
    have hyb : y ≤ b := (hsub (right_mem_Icc.mpr hxy)).2
    by_cases hyc : y ≤ c
    · have hsrα : MapsTo alpha (uIcc x y) (chartAt H p).source := by
        rw [uIcc_of_le hxy]
        intro t ht
        rw [← hleft t (ht.2.trans hyc)]
        exact hsrc ht
      have hsα : uIcc x y ⊆ uIcc a c := by
        rw [uIcc_of_le hxy, uIcc_of_le hac]
        exact Icc_subset_Icc hax hyc
      apply (hα.2 p x y hsα hsrα).congr
      intro t ht
      dsimp only [Function.comp_apply]
      rw [hleft t ((show t ≤ y from (show t ∈ Icc x y by simpa only [uIcc_of_le hxy] using ht).2).trans hyc)]
    by_cases hcx : c ≤ x
    · have hsrβ : MapsTo beta (uIcc x y) (chartAt H p).source := by
        rw [uIcc_of_le hxy]
        intro t ht
        rw [← hright t (hcx.trans ht.1)]
        exact hsrc ht
      have hsβ : uIcc x y ⊆ uIcc c b := by
        rw [uIcc_of_le hxy, uIcc_of_le hcb]
        exact Icc_subset_Icc hcx hyb
      apply (hβ.2 p x y hsβ hsrβ).congr
      intro t ht
      dsimp only [Function.comp_apply]
      rw [hright t (hcx.trans (show x ≤ t from (show t ∈ Icc x y by simpa only [uIcc_of_le hxy] using ht).1))]
    have hxc : x ≤ c := (lt_of_not_ge hcx).le
    have hcy : c ≤ y := (lt_of_not_ge hyc).le
    have hsrα : MapsTo alpha (uIcc x c) (chartAt H p).source := by
      rw [uIcc_of_le hxc]
      intro t ht
      rw [← hleft t ht.2]
      exact hsrc ⟨ht.1, ht.2.trans hcy⟩
    have hsrβ : MapsTo beta (uIcc c y) (chartAt H p).source := by
      rw [uIcc_of_le hcy]
      intro t ht
      rw [← hright t ht.1]
      exact hsrc ⟨hxc.trans ht.1, ht.2⟩
    have hsα : uIcc x c ⊆ uIcc a c := by
      rw [uIcc_of_le hxc, uIcc_of_le hac]
      exact Icc_subset_Icc_left hax
    have hsβ : uIcc c y ⊆ uIcc c b := by
      rw [uIcc_of_le hcy, uIcc_of_le hcb]
      exact Icc_subset_Icc_right hyb
    have hjoin := (hα.2 p x c hsα hsrα).piecewise_Iic hxc hcy
      (hβ.2 p c y hsβ hsrβ) (congrArg (extChartAt I p) hnode)
    apply hjoin.congr
    intro t _
    by_cases htc : t ≤ c
    · simp only [piecewise_eq_of_mem (Iic c) _ _ htc, Function.comp_apply, hleft t htc]
    · simp only [piecewise_eq_of_notMem (Iic c) _ _ htc, Function.comp_apply,
        hright t (le_of_not_ge htc)]
  intro p x y hsub hsrc
  rcases le_total x y with hxy | hyx
  · apply hordered p x y hxy
    · simpa only [uIcc_of_le hxy, uIcc_of_le (hac.trans hcb)] using hsub
    · simpa only [uIcc_of_le hxy] using hsrc
  · apply AbsolutelyContinuousOnInterval.symm
    apply hordered p y x hyx
    · simpa only [uIcc_of_ge hyx, uIcc_of_le (hac.trans hcb)] using hsub
    · simpa only [uIcc_of_ge hyx] using hsrc

end Manifold

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem absolutelyContinuousOnInterval_congr
    {gamma eta : ℝ → M} {a b : ℝ}
    (h : absolutelyContinuousOnInterval I gamma a b) (heq : EqOn gamma eta (uIcc a b)) :
    absolutelyContinuousOnInterval I eta a b := by
  refine ⟨h.1.congr (fun t ht => (heq ht).symm), ?_⟩
  intro p c d hsub hsrc
  have hsrc' : MapsTo gamma (uIcc c d) (chartAt H p).source := by
    intro t ht
    rw [heq (hsub ht)]
    exact hsrc ht
  apply (h.2 p c d hsub hsrc').congr
  intro t ht
  exact congrArg (extChartAt I p) (heq (hsub ht))

theorem absolutelyContinuousOnInterval_subtype_of_val
    (U : TopologicalSpace.Opens M) {eta : ℝ → U} {a b : ℝ}
    (h : absolutelyContinuousOnInterval I (Subtype.val ∘ eta) a b) :
    absolutelyContinuousOnInterval I eta a b := by
  have hcont : ContinuousOn eta (uIcc a b) := by
    exact Topology.IsInducing.subtypeVal.continuousOn_iff.mpr h.1
  refine ⟨hcont, ?_⟩
  intro p c d hsub hsrc
  have hsrc' : MapsTo (Subtype.val ∘ eta) (uIcc c d) (chartAt H p.val).source := by
    intro t ht
    have hp := hsrc ht
    simpa only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
      mem_preimage, Function.comp_apply] using hp
  have hac := h.2 p.val c d hsub hsrc'
  exact hac

theorem exists_absolutelyContinuousOnInterval_openSubtype
    (U : TopologicalSpace.Opens M) {gamma : ℝ → M} {a b : ℝ}
    (h : absolutelyContinuousOnInterval I gamma a b)
    (hU : MapsTo gamma (uIcc a b) U) :
    ∃ eta : ℝ → U, absolutelyContinuousOnInterval I eta a b ∧
      EqOn (Subtype.val ∘ eta) gamma (uIcc a b) := by
  classical
  let eta : ℝ → U := fun t => if ht : t ∈ uIcc a b then ⟨gamma t, hU ht⟩
    else ⟨gamma a, hU left_mem_uIcc⟩
  have heq : EqOn (Subtype.val ∘ eta) gamma (uIcc a b) := by
    intro t ht
    simp only [eta, dif_pos ht, Function.comp_apply]
  refine ⟨eta, ?_, heq⟩
  apply absolutelyContinuousOnInterval_subtype_of_val U
  exact absolutelyContinuousOnInterval_congr h heq.symm

end Manifold

namespace Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem absolutelyContinuousOnInterval_of_extChartAt
    {γ : ℝ → M} {a b : ℝ} (p : M)
    (hsrc : MapsTo γ (uIcc a b) (chartAt H p).source)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ γ) a b) :
    absolutelyContinuousOnInterval I γ a b := by
  have hsrc' : MapsTo γ (uIcc a b) (extChartAt I p).source := by
    simpa only [extChartAt_source] using hsrc
  have hcont : ContinuousOn γ (uIcc a b) := by
    have hmaps : MapsTo ((extChartAt I p) ∘ γ) (uIcc a b) (extChartAt I p).target :=
      fun r hr => (extChartAt I p).map_source (hsrc' hr)
    have hc := (continuousOn_extChartAt_symm p).comp hAC.continuousOn hmaps
    apply hc.congr
    intro r hr
    exact ((extChartAt I p).left_inv (hsrc' hr)).symm
  refine ⟨hcont, ?_⟩
  intro q c d hsub hqsrc
  let F : E → E := extChartAt I q ∘ (extChartAt I p).symm
  let K : Set E := ((extChartAt I p) ∘ γ) '' uIcc c d
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn (hAC.continuousOn.mono hsub)
  have hKcoord : K ⊆ ((extChartAt I p).symm ≫ extChartAt I q).source := by
    rintro x ⟨r, hr, rfl⟩
    refine ⟨(extChartAt I p).map_source (hsrc' (hsub hr)), ?_⟩
    change (extChartAt I p).symm ((extChartAt I p) (γ r)) ∈ (extChartAt I q).source
    rw [(extChartAt I p).left_inv (hsrc' (hsub hr))]
    simpa only [extChartAt_source] using hqsrc hr
  have hlocal : LocallyLipschitzOn K F := by
    intro x hx
    have hcoord := contDiffWithinAt_ext_coord_change (I := I) (n := (1 : WithTop ℕ∞)) q p (hKcoord hx)
    have hcd : ContDiffAt ℝ 1 F x := by
      apply hcoord.contDiffAt
      simp only [ModelWithCorners.range_eq_univ, univ_mem]
    obtain ⟨C, V, hV, hCV⟩ := hcd.exists_lipschitzOnWith
    exact ⟨C, V, mem_nhdsWithin_of_mem_nhds hV, hCV⟩
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact hK
  have hh := hC.comp_absolutelyContinuousOnInterval (hAC.mono hsub)
    (fun r hr => mem_image_of_mem _ hr)
  apply hh.congr
  intro r hr
  change (extChartAt I q) ((extChartAt I p).symm ((extChartAt I p) (γ r))) =
    (extChartAt I q) (γ r)
  rw [(extChartAt I p).left_inv (hsrc' (hsub hr))]


omit [I.Boundaryless] [IsManifold I 1 M] in
theorem absolutelyContinuousOnInterval_of_finite_partition
    {γ : ℝ → M} {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hpiece : ∀ i : Fin m, absolutelyContinuousOnInterval I γ (t i.castSucc) (t i.succ)) :
    absolutelyContinuousOnInterval I γ (t 0) (t (Fin.last m)) := by
  have hprefix (k : Fin (m + 1)) : absolutelyContinuousOnInterval I γ (t 0) (t k) := by
    induction k using Fin.induction with
    | zero =>
      have hconst : absolutelyContinuousOnInterval I (fun _ : ℝ => γ (t 0)) (t 0) (t 0) := by
        refine ⟨continuousOn_const, ?_⟩
        intro p c d _ _
        exact (contDiff_const.contDiffOn.absolutelyContinuousOnInterval :
          AbsolutelyContinuousOnInterval (fun _ : ℝ => extChartAt I p (γ (t 0))) c d)
      apply absolutelyContinuousOnInterval_congr hconst
      intro r hr
      have heq : r = t 0 := by simpa only [uIcc_self, mem_singleton_iff] using hr
      subst r
      rfl
    | succ k ih =>
      have hh := absolutelyContinuousOnInterval_piecewise_Iic ih (hpiece k)
        (ht (Fin.zero_le _)) (ht k.castSucc_le_succ) rfl
      simpa only [Set.piecewise_same] using hh
  exact hprefix (Fin.last m)

end Manifold

open scoped ContDiff

namespace Manifold

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

theorem absolutelyContinuousOnInterval_comp_contMDiff
    {gamma : ℝ → M} {a b : ℝ} (hgamma : absolutelyContinuousOnInterval I gamma a b)
    {f : M → N} (hf : ContMDiff I J 1 f) :
    absolutelyContinuousOnInterval J (f ∘ gamma) a b := by
  have hpart (q : N) (c d : ℝ) (hcd : c ≤ d)
      (hsub : uIcc c d ⊆ uIcc a b)
      (hmaps : MapsTo (f ∘ gamma) (uIcc c d) (chartAt H' q).source) :
      AbsolutelyContinuousOnInterval ((extChartAt J q) ∘ f ∘ gamma) c d := by
    obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hcharts⟩ :=
      DifferentialGeometry.Geometry.exists_chart_subdivision (H := H) hcd
        (hgamma.1.mono (Icc_subset_uIcc.trans hsub))
    have hsegment (n : ℕ) : AbsolutelyContinuousOnInterval
        ((extChartAt J q) ∘ f ∘ gamma) (t n).val (t (n + 1)).val := by
      have hle : (t n).val ≤ (t (n + 1)).val := htmono (Nat.le_succ n)
      have hseg : uIcc (t n).val (t (n + 1)).val ⊆ uIcc c d := by
        rw [uIcc_of_le hle, uIcc_of_le hcd]
        exact Icc_subset_Icc (t n).property.1 (t (n + 1)).property.2
      obtain ⟨p, hp⟩ := hcharts n
      have hsrc : MapsTo gamma (uIcc (t n).val (t (n + 1)).val) (chartAt H p).source := by
        simpa only [uIcc_of_le hle] using hp
      have hAC := hgamma.2 p (t n).val (t (n + 1)).val (hseg.trans hsub) hsrc
      let K := ((extChartAt I p) ∘ gamma) '' uIcc (t n).val (t (n + 1)).val
      have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn hAC.continuousOn
      have hKr : K ⊆ range I := by
        rintro x ⟨r, hr, rfl⟩
        exact extChartAt_target_subset_range p ((extChartAt I p).map_source
          (by simpa only [extChartAt_source] using hsrc hr))
      have hloc : LocallyLipschitzOn K ((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) := by
        rintro x ⟨r, hr, rfl⟩
        have hC := ((contMDiffAt_iff_of_mem_source (hsrc hr) (hmaps (hseg hr))).mp
          (hf.contMDiffAt (x := gamma r))).2
        obtain ⟨L, V, hV, hLip⟩ := hC.exists_lipschitzOnWith I.convex_range
        exact ⟨L, V, nhdsWithin_mono _ hKr hV, hLip⟩
      obtain ⟨L, hLip⟩ := hloc.exists_lipschitzOnWith_of_compact hK
      have h := hLip.comp_absolutelyContinuousOnInterval hAC
        (fun r hr => mem_image_of_mem ((extChartAt I p) ∘ gamma) hr)
      apply h.congr
      intro r hr
      dsimp only [Function.comp_apply]
      rw [(extChartAt I p).left_inv (by simpa only [extChartAt_source] using hsrc hr)]
    have hjoin (n : ℕ) : AbsolutelyContinuousOnInterval
        ((extChartAt J q) ∘ f ∘ gamma) c (t n).val := by
      induction n with
      | zero =>
        rw [ht0]
        have h := hsegment 0
        rw [ht0] at h
        exact h.mono (by simp)
      | succ n ih =>
        simpa only [Set.piecewise_same] using
          AbsolutelyContinuousOnInterval.piecewise_Iic (t n).property.1
            (htmono (Nat.le_succ n)) ih (hsegment n) rfl
    simpa only [hm m le_rfl] using hjoin m
  refine ⟨hf.continuous.comp_continuousOn hgamma.1, ?_⟩
  intro q c d hsub hmaps
  rcases le_total c d with hcd | hdc
  · exact hpart q c d hcd hsub hmaps
  · exact (hpart q d c hdc (by simpa only [uIcc_comm] using hsub)
      (by simpa only [uIcc_comm] using hmaps)).symm

end Manifold
