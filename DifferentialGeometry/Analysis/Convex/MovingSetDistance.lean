import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Convex

open Filter Set Metric
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuousWithinAt_infDist_of_seqClosedGraph_of_approx
    [FiniteDimensional ℝ F]
    {a b : ℝ} (C : ℝ → Set F)
    (hCne : ∀ τ : ℝ, τ ∈ Set.Icc a b → (C τ).Nonempty)
    (hgraph : ∀ τ₀ : ℝ, τ₀ ∈ Set.Icc a b → ∀ q : F, ∀ (τn : ℕ → ℝ) (qn : ℕ → F),
      Tendsto τn atTop (𝓝 τ₀) → Tendsto qn atTop (𝓝 q) →
        (∀ᶠ n in atTop, τn n ∈ Set.Icc a b ∧ qn n ∈ C (τn n)) → q ∈ C τ₀)
    (happrox : ∀ τ₀ : ℝ, τ₀ ∈ Set.Icc a b → ∀ q : F, q ∈ C τ₀ → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, τ ∈ Set.Icc a b → |τ - τ₀| < δ →
        ∃ q' : F, q' ∈ C τ ∧ dist q' q < ε)
    (x₀ : ℝ × F) (hx₀ : x₀ ∈ Set.Icc a b ×ˢ (Set.univ : Set F)) :
    ContinuousWithinAt (fun q : ℝ × F => Metric.infDist q.2 (C q.1))
      (Set.Icc a b ×ˢ (Set.univ : Set F)) x₀ := by
  classical
  let τ₀ : ℝ := x₀.1
  let p₀ : F := x₀.2
  let d₀ : ℝ := Metric.infDist p₀ (C τ₀)
  have hτ₀ : τ₀ ∈ Set.Icc a b := by
    simpa [τ₀] using hx₀.1
  change Tendsto (fun q : ℝ × F => Metric.infDist q.2 (C q.1))
    (𝓝[Set.Icc a b ×ˢ (Set.univ : Set F)] x₀) (𝓝 (Metric.infDist x₀.2 (C x₀.1)))
  refine (Filter.tendsto_iff_seq_tendsto
    (k := 𝓝[Set.Icc a b ×ˢ (Set.univ : Set F)] x₀)
    (l := 𝓝 (Metric.infDist x₀.2 (C x₀.1)))).2 ?_
  intro u hu
  let τn : ℕ → ℝ := fun n => (u n).1
  let pn : ℕ → F := fun n => (u n).2
  have huamb : Tendsto u atTop (𝓝 x₀) :=
    hu.mono_right (nhdsWithin_le_nhds (a := x₀) (s := Set.Icc a b ×ˢ (Set.univ : Set F)))
  have hτn : Tendsto τn atTop (𝓝 τ₀) := by
    have hfst := (continuousAt_fst (p := x₀)).tendsto.comp huamb
    simpa [τn, τ₀] using! hfst
  have hpn : Tendsto pn atTop (𝓝 p₀) := by
    have hsnd := (continuousAt_snd (p := x₀)).tendsto.comp huamb
    simpa [pn, p₀] using! hsnd
  have hmem : ∀ᶠ n in atTop, τn n ∈ Set.Icc a b := by
    have h := hu (U := Set.Icc a b ×ˢ (Set.univ : Set F)) self_mem_nhdsWithin
    filter_upwards [h] with n hn
    exact hn.1
  have hd₀ : d₀ = Metric.infDist x₀.2 (C x₀.1) := by
    simp [d₀, τ₀, p₀]
  change Tendsto (fun n : ℕ => Metric.infDist (pn n) (C (τn n))) atTop (𝓝 d₀)
  rw [hd₀]
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hε2 : 0 < ε / 2 := by positivity
  have hε6 : 0 < ε / 6 := by positivity
  have hlt₀ : Metric.infDist p₀ (C τ₀) < d₀ + ε / 3 := by
    rw [show d₀ = Metric.infDist p₀ (C τ₀) from rfl]
    exact lt_add_of_pos_right _ hε3
  rcases (Metric.infDist_lt_iff (s := C τ₀) (x := p₀) (r := d₀ + ε / 3)
      (hCne τ₀ hτ₀)).mp hlt₀ with ⟨q₀, hq₀C, hq₀dist⟩
  rcases happrox τ₀ hτ₀ q₀ hq₀C (ε / 3) hε3 with ⟨δ₁, hδ₁pos, hδ₁⟩
  have hτnear₁ : ∀ᶠ n in atTop, |τn n - τ₀| < δ₁ := by
    have h := (Metric.tendsto_atTop.mp hτn) δ₁ hδ₁pos
    have hev : ∀ᶠ n in atTop, dist (τn n) τ₀ < δ₁ := eventually_atTop.mpr h
    filter_upwards [hev] with n hn
    simpa [Real.dist_eq] using hn
  have hpnear₁ : ∀ᶠ n in atTop, dist (pn n) p₀ < ε / 3 := by
    have := (Metric.tendsto_atTop.mp hpn) (ε / 3) hε3
    exact eventually_atTop.mpr this
  have happ₁ : ∀ᶠ n in atTop, ∃ q' : F, q' ∈ C (τn n) ∧ dist q' q₀ < ε / 3 := by
    filter_upwards [hmem, hτnear₁] with n hni hτi
    exact hδ₁ (τn n) hni (by simpa [abs_sub_comm] using hτi)
  let qn₁ : ℕ → F := fun n => if hn : ∃ q' : F, q' ∈ C (τn n) ∧ dist q' q₀ < ε / 3 then
    Classical.choose hn else 0
  have hqn₁ : ∀ᶠ n in atTop, qn₁ n ∈ C (τn n) ∧ dist (qn₁ n) q₀ < ε / 3 := by
    filter_upwards [happ₁] with n hn
    dsimp [qn₁]
    rw [dif_pos hn]
    exact Classical.choose_spec hn
  have husc : ∀ᶠ n in atTop, Metric.infDist (pn n) (C (τn n)) < d₀ + ε := by
    filter_upwards [hpnear₁, hqn₁] with n hpn₁ hqni
    have h₁ : Metric.infDist (pn n) (C (τn n)) ≤ dist (pn n) (qn₁ n) :=
      Metric.infDist_le_dist_of_mem (x := pn n) hqni.1
    have h₂ : dist (pn n) (qn₁ n) ≤ dist (pn n) p₀ + dist p₀ q₀ + dist q₀ (qn₁ n) :=
      dist_triangle4 (pn n) p₀ q₀ (qn₁ n)
    have h₃ : dist (pn n) p₀ + dist p₀ q₀ + dist q₀ (qn₁ n) < ε / 3 + (d₀ + ε / 3) + ε / 3 := by
      have h3 : dist q₀ (qn₁ n) < ε / 3 := by simpa [dist_comm] using hqni.2
      nlinarith
    linarith
  have hlsc : ∀ᶠ n in atTop, d₀ < Metric.infDist (pn n) (C (τn n)) + ε := by
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop, Metric.infDist (pn n) (C (τn n)) + ε ≤ d₀ := by
      exact (Filter.not_eventually.mp hnot).mono (fun n hn => le_of_not_gt hn)
    obtain ⟨ns, hns, hnsProp⟩ := exists_seq_forall_of_frequently hfreq
    have hτsub : Tendsto (fun m : ℕ => τn (ns m)) atTop (𝓝 τ₀) := hτn.comp hns
    have hpsub : Tendsto (fun m : ℕ => pn (ns m)) atTop (𝓝 p₀) := hpn.comp hns
    have hmemSub : ∀ᶠ m in atTop, τn (ns m) ∈ Set.Icc a b := hns.eventually hmem
    have hdsub : ∀ m : ℕ, Metric.infDist (pn (ns m)) (C (τn (ns m))) ≤ d₀ - ε := by
      intro m
      linarith [hnsProp m]
    have hq₀' : ∀ m : ℕ, Metric.infDist (pn (ns m)) (C (τn (ns m))) <
        Metric.infDist (pn (ns m)) (C (τn (ns m))) + ε / 2 := by
      intro m
      exact lt_add_of_pos_right _ hε2
    let qn : ℕ → F := fun m => if hm : τn (ns m) ∈ Set.Icc a b then
      Classical.choose ((Metric.infDist_lt_iff (s := C (τn (ns m))) (x := pn (ns m))
        (r := Metric.infDist (pn (ns m)) (C (τn (ns m))) + ε / 2)
        (hCne (τn (ns m)) hm)).mp (hq₀' m)) else 0
    have hqnC : ∀ᶠ m in atTop, qn m ∈ C (τn (ns m)) := by
      filter_upwards [hmemSub] with m hm
      dsimp [qn]
      rw [dif_pos hm]
      exact (Classical.choose_spec ((Metric.infDist_lt_iff
        (s := C (τn (ns m))) (x := pn (ns m))
        (r := Metric.infDist (pn (ns m)) (C (τn (ns m))) + ε / 2)
        (hCne (τn (ns m)) hm)).mp (hq₀' m))).1
    have hqndist : ∀ᶠ m in atTop, dist (pn (ns m)) (qn m) < d₀ - ε / 2 := by
      filter_upwards [hmemSub] with m hm
      have hqn_eq : qn m = Classical.choose ((Metric.infDist_lt_iff
          (s := C (τn (ns m))) (x := pn (ns m))
          (r := Metric.infDist (pn (ns m)) (C (τn (ns m))) + ε / 2)
          (hCne (τn (ns m)) hm)).mp (hq₀' m)) := by
        dsimp [qn]
        rw [dif_pos hm]
      have hspec := Classical.choose_spec ((Metric.infDist_lt_iff
        (s := C (τn (ns m))) (x := pn (ns m))
        (r := Metric.infDist (pn (ns m)) (C (τn (ns m))) + ε / 2)
        (hCne (τn (ns m)) hm)).mp (hq₀' m))
      have h₁ : dist (pn (ns m)) (qn m) <
          Metric.infDist (pn (ns m)) (C (τn (ns m))) + ε / 2 := by
        rw [hqn_eq]
        exact hspec.2
      have h₂ : Metric.infDist (pn (ns m)) (C (τn (ns m))) ≤ d₀ - ε := hdsub m
      linarith
    have hbounded : ∃ᶠ m in atTop, qn m ∈ closedBall (0 : F) (d₀ + ‖p₀‖ + 1) := by
      have hnormp : ∀ᶠ m in atTop, ‖pn (ns m)‖ ≤ ‖p₀‖ + 1 := by
        have hlim : Tendsto (fun m : ℕ => ‖pn (ns m)‖) atTop (𝓝 ‖p₀‖) := hpsub.norm
        have := (Metric.tendsto_atTop.mp hlim) 1 (by norm_num)
        have hev : ∀ᶠ m in atTop, dist ‖pn (ns m)‖ ‖p₀‖ < 1 := eventually_atTop.mpr this
        filter_upwards [hev] with m hm
        have hnorm : ‖pn (ns m)‖ ≤ ‖p₀‖ + dist ‖pn (ns m)‖ ‖p₀‖ := by
          have h := norm_le_norm_add_norm_sub (‖p₀‖ : ℝ) (‖pn (ns m)‖ : ℝ)
          simpa [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using h
        nlinarith
      have hev : ∀ᶠ m in atTop, qn m ∈ closedBall (0 : F) (d₀ + ‖p₀‖ + 1) := by
        filter_upwards [hqndist, hnormp] with m hd hnp
        rw [mem_closedBall]
        simp only [dist_eq_norm, sub_zero]
        have h₁ : ‖qn m‖ ≤ dist (pn (ns m)) (qn m) + ‖pn (ns m)‖ := by
          have hle : ‖qn m‖ ≤ ‖pn (ns m)‖ + ‖pn (ns m) - qn m‖ :=
            norm_le_norm_add_norm_sub (pn (ns m)) (qn m)
          rw [show ‖pn (ns m) - qn m‖ = dist (pn (ns m)) (qn m) by rw [dist_eq_norm]] at hle
          linarith
        linarith
      exact hev.frequently
    have hsc : IsSeqCompact (closedBall (0 : F) (d₀ + ‖p₀‖ + 1)) := by
      have hc : IsCompact (closedBall (0 : F) (d₀ + ‖p₀‖ + 1)) :=
        isCompact_closedBall (α := F) 0 (d₀ + ‖p₀‖ + 1)
      exact hc.isSeqCompact
    have hsubseq := hsc.subseq_of_frequently_in (x := qn) hbounded
    rcases hsubseq with ⟨qbar, hqbar, φ, hφ, hφq⟩
    have hτsub' : Tendsto (fun m : ℕ => τn (ns (φ m))) atTop (𝓝 τ₀) :=
      hτsub.comp hφ.tendsto_atTop
    have hmemSub' : ∀ᶠ m in atTop, τn (ns (φ m)) ∈ Set.Icc a b :=
      hφ.tendsto_atTop.eventually hmemSub
    have hqnC' : ∀ᶠ m in atTop, qn (φ m) ∈ C (τn (ns (φ m))) :=
      hφ.tendsto_atTop.eventually hqnC
    have hmemAll : ∀ᶠ m in atTop, τn (ns (φ m)) ∈ Set.Icc a b ∧
        qn (φ m) ∈ C (τn (ns (φ m))) := by
      exact hmemSub'.and hqnC'
    have hqbarC : qbar ∈ C τ₀ := hgraph τ₀ hτ₀ qbar (fun m => τn (ns (φ m))) (fun m => qn (φ m))
      hτsub' hφq hmemAll
    have hdistTendsto : Tendsto (fun m : ℕ => dist (pn (ns (φ m))) (qn (φ m))) atTop
        (𝓝 (dist p₀ qbar)) := by
      have hpsub' : Tendsto (fun m : ℕ => pn (ns (φ m))) atTop (𝓝 p₀) :=
        hpsub.comp hφ.tendsto_atTop
      have hpair' : Tendsto (fun m : ℕ => (pn (ns (φ m)), qn (φ m))) atTop (𝓝 (p₀, qbar)) :=
        by
          have h := Tendsto.prodMk hpsub' hφq
          simpa [nhds_prod_eq] using h
      simpa using! continuous_dist.continuousAt.tendsto.comp hpair'
    have hdistLe : ∀ᶠ m in atTop, dist (pn (ns (φ m))) (qn (φ m)) ≤ d₀ - ε / 2 := by
      filter_upwards [hφ.tendsto_atTop.eventually hqndist] with m hm
      exact le_of_lt hm
    have hlimLe : dist p₀ qbar ≤ d₀ - ε / 2 :=
      le_of_tendsto hdistTendsto hdistLe
    have hcontr : d₀ ≤ dist p₀ qbar :=
      Metric.infDist_le_dist_of_mem (x := p₀) hqbarC
    linarith
  have hmain : ∀ᶠ n in atTop, |Metric.infDist (pn n) (C (τn n)) - d₀| < ε := by
    filter_upwards [husc, hlsc] with n h₁ h₂
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hN : ∃ N : ℕ, ∀ n ≥ N, dist (Metric.infDist (pn n) (C (τn n))) d₀ < ε := by
    exact eventually_atTop.mp (by
      filter_upwards [hmain] with n hn
      simpa [Real.dist_eq] using hn)
  exact hN

theorem continuousOn_infDist_of_seqClosedGraph_of_approx
    [FiniteDimensional ℝ F]
    {a b : ℝ} (C : ℝ → Set F)
    (hCne : ∀ τ : ℝ, τ ∈ Set.Icc a b → (C τ).Nonempty)
    (hgraph : ∀ τ₀ : ℝ, τ₀ ∈ Set.Icc a b → ∀ q : F, ∀ (τn : ℕ → ℝ) (qn : ℕ → F),
      Tendsto τn atTop (𝓝 τ₀) → Tendsto qn atTop (𝓝 q) →
        (∀ᶠ n in atTop, τn n ∈ Set.Icc a b ∧ qn n ∈ C (τn n)) → q ∈ C τ₀)
    (happrox : ∀ τ₀ : ℝ, τ₀ ∈ Set.Icc a b → ∀ q : F, q ∈ C τ₀ → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, τ ∈ Set.Icc a b → |τ - τ₀| < δ →
        ∃ q' : F, q' ∈ C τ ∧ dist q' q < ε) :
    ContinuousOn (fun q : ℝ × F => Metric.infDist q.2 (C q.1))
      (Set.Icc a b ×ˢ (Set.univ : Set F)) := by
  intro x₀ hx₀
  exact continuousWithinAt_infDist_of_seqClosedGraph_of_approx (C := C)
    hCne hgraph happrox x₀ hx₀

end DifferentialGeometry.Analysis.Convex

end
