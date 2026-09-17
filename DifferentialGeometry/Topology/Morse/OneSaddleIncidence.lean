import DifferentialGeometry.Topology.Morse.OneSaddleSuperlevels
import DifferentialGeometry.Topology.Morse.SaddleComponents

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

local notation "S₂" => sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_saddleBandLevelCurve_subset_superlevel_components_of_one_saddle
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hone : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | f x < a})
    {g : S₂ → P} (B : (ℝ × ℝ) ≃ₘ[ℝ] P)
    {β : (ℝ × ℝ) → S₂} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    (hg : ∀ z ∈ U, ContMDiffAt (𝓡 2) 𝓘(ℝ, P) ∞ g (β z))
    {c s : ℝ} (hs : 0 < s)
    (hfst : ∀ z ∈ U, g (β z) = B z)
    (hheight : ∀ z ∈ U, f (β z) = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    (hβcrit : IsCriticalPointAt (𝓡 2) f (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) (β (0, 0))).symm y))
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ m p q : S₂,
      f m < f (β (0, 0)) ∧ f (β (0, 0)) < f p ∧ f p < f q ∧
      IsMinOn f univ m ∧ IsMaxOn f univ q ∧ IsLocalMax f p ∧
      IsNondegenerateCriticalPointAt (𝓡 2) f p ∧
      {x | IsCriticalPointAt (𝓡 2) f x} = {m, β (0, 0), p, q} ∧
      (∀ a ∈ Ioo (f (β (0, 0))) (f p), ∀ x, f x ∈ Ico a (f p) →
        ¬ IsCriticalPointAt (𝓡 2) f x) ∧
      ∃ δ k : ℝ, 0 < δ ∧ c + s + δ ≤ f p ∧ 0 < k ∧ k < 1 ∧
        ∃ σ ∈ ({-1, 1} : Set ℝ), ∀ t ∈ Ioo (0 : ℝ) δ,
          saddleBandLevelCurve s t σ '' Icc (-k) k ⊆ U ∧
          saddleBandLevelCurve s t (-σ) '' Icc (-k) k ⊆ U ∧
          β '' (saddleBandLevelCurve s t σ '' Icc (-k) k) ⊆
            connectedComponentIn {x | c + s + t ≤ f x} p ∩ {x | f x = c + s + t} ∧
          β '' (saddleBandLevelCurve s t (-σ) '' Icc (-k) k) ⊆
            connectedComponentIn {x | c + s + t ≤ f x} q ∩ {x | f x = c + s + t} ∧
          Disjoint (connectedComponentIn {x | c + s + t ≤ f x} p)
            (connectedComponentIn {x | c + s + t ≤ f x} q) := by
  obtain ⟨m, xₛ, p, q, hms, hsp, hpq, hm, hqmax, hpmax, hC, hsindex, hregular,
    hcomponents, hinter⟩ := exists_superlevel_components_of_one_saddle hf hnd hinj hone hconn
  have hsc : IsCriticalPointAt (𝓡 2) f xₛ := hC.symm.subset (by simp)
  have hpc : IsCriticalPointAt (𝓡 2) f p := hC.symm.subset (by simp)
  have hsβ : xₛ = β (0, 0) := by
    obtain ⟨r, hr⟩ := ncard_eq_one.mp hone
    have hsset : xₛ ∈ {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
        (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1} :=
      ⟨hsc, hsindex⟩
    have hβset : β (0, 0) ∈ {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
        (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1} :=
      ⟨hβcrit, hβindex⟩
    rw [hr] at hsset hβset
    exact (mem_singleton_iff.mp hsset).trans (mem_singleton_iff.mp hβset).symm
  subst xₛ
  have hβheight : f (β (0, 0)) = c + s := by
    simpa using hheight (0, 0) hzero
  have hclosures : β (0, 0) ∈ closure (connectedComponentIn {x | c + s < f x} p) ∩
      closure (connectedComponentIn {x | c + s < f x} q) := by
    rw [← hβheight, hinter]
    exact mem_singleton _
  have hne : connectedComponentIn {x | c + s < f x} p ≠
      connectedComponentIn {x | c + s < f x} q := by
    rw [← hβheight]
    intro heq
    have hdisj := (hcomponents (f (β (0, 0))) ⟨le_rfl, hsp⟩).2.1
    exact disjoint_left.mp hdisj (mem_connectedComponentIn hsp)
      (heq ▸ mem_connectedComponentIn hsp)
  obtain ⟨δ, k, hδ, hδbound, hk, hkone, σ, hσ, hcurves⟩ :=
    exists_saddleBandLevelCurve_subset_closure_connectedComponentIn_of_graph
      (I := 𝓡 2) (by simp) (fun x => (g x, f x)) B hU hzero hβ hg hs
      (by rw [← hβheight]; exact hsp)
      (fun z hz => Prod.ext (hfst z hz) (hheight z hz))
      hclosures.1 hclosures.2 hne
      (fun a ha => (hcomponents a ⟨by rw [hβheight]; exact ha.1.le, ha.2⟩).1)
  refine ⟨m, p, q, hms, hsp, hpq, hm, hqmax, hpmax, hnd p hpc, hC, hregular,
    δ, k, hδ, hδbound, hk, hkone, σ, hσ, ?_⟩
  intro t ht
  have hcurvest := hcurves t ht
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hlevel (ε : ℝ) (hε : ε ^ 2 = 1)
      (hUε : saddleBandLevelCurve s t ε '' Icc (-k) k ⊆ U) :
      β '' (saddleBandLevelCurve s t ε '' Icc (-k) k) ⊆ {x | f x = c + s + t} := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rw [mem_ofPred_eq, hheight _ (hUε ⟨u, hu, rfl⟩)]
    exact saddleBandLevelCurve_height hs.le ht.1 hε
      ⟨by linarith [hu.1], hu.2.trans_lt hkone⟩ c
  have hclosed : IsClosed {x | c + s + t ≤ f x} := isClosed_le continuous_const hf.continuous
  refine ⟨hcurvest.1, hcurvest.2.1, ?_, ?_, ?_⟩
  · exact subset_inter
      (hcurvest.2.2.1.trans (closure_connectedComponentIn_subset hclosed
        (fun x hx => (show c + s + t < f x from hx).le) p))
      (hlevel σ hσsq hcurvest.1)
  · exact subset_inter
      (hcurvest.2.2.2.trans (closure_connectedComponentIn_subset hclosed
        (fun x hx => (show c + s + t < f x from hx).le) q))
      (hlevel (-σ) (by simpa only [neg_sq] using hσsq) hcurvest.2.1)
  · have ha : c + s + t ∈ Ioo (f (β (0, 0))) (f p) := by
      rw [hβheight]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmax := isMaxOn_connectedComponentIn_superlevel_of_no_critical_values hf (hnd p hpc)
      hpmax ha.2 (isClosed_Icc.preimage hf.continuous).isCompact
      (hregular (c + s + t) ha)
    apply disjoint_left.mpr
    intro x hxp hxq
    have heq := (connectedComponentIn_eq hxp).trans (connectedComponentIn_eq hxq).symm
    have hqin : q ∈ connectedComponentIn {x | c + s + t ≤ f x} p := by
      rw [heq]
      exact mem_connectedComponentIn (ha.2.trans hpq).le
    exact hpq.not_ge (hmax hqin)

end DifferentialGeometry.Topology.Morse
