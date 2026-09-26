import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
set_option autoImplicit false

open Filter Function MeasureTheory Set
open scoped Manifold Topology Interval

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
