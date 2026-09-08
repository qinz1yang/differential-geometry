import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue

open Set Filter
open scoped Topology

namespace IsIntegralCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v : ℝ → ℝ × E → ℝ × E} {γ : ℝ → ℝ × E}

theorem fst_eq_zero_iff_of_tangent (hγ : IsIntegralCurve γ v)
    (hv : ContDiff ℝ 1 (fun p : ℝ × (ℝ × E) => v p.1 p.2))
    (htangent : ∀ t : ℝ, ∀ y : E, (v t (0, y)).1 = 0) (s t : ℝ) :
    (γ s).1 = 0 ↔ (γ t).1 = 0 := by
  let Z : Set ℝ := {u | (γ u).1 = 0}
  have hclosed : IsClosed Z := isClosed_eq (continuous_fst.comp hγ.continuous) continuous_const
  have hopen : IsOpen Z := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro u hu
    change (γ u).1 = 0 at hu
    obtain ⟨K, U, hU, hLip⟩ :=
      (hv.contDiffAt (x := (u, γ u))).exists_lipschitzOnWith
    let W : ℝ → ℝ → ℝ := fun a b => (v a (b, (γ a).2)).1
    let D : ℝ → Set ℝ := fun a => {b | (a, (b, (γ a).2)) ∈ U}
    have hW : ∀ a : ℝ, LipschitzOnWith K (W a) (D a) := by
      intro a
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro b hb c hc
      calc
        dist (W a b) (W a c) ≤ dist (v a (b, (γ a).2)) (v a (c, (γ a).2)) :=
          le_max_left _ _
        _ ≤ K * dist (a, (b, (γ a).2)) (a, (c, (γ a).2)) :=
          hLip.dist_le_mul _ hb _ hc
        _ = K * dist b c := by simp [Prod.dist_eq]
    have hγU : ∀ᶠ a in 𝓝 u, (γ a).1 ∈ D a := by
      have h := (continuous_id.prodMk hγ.continuous).continuousAt.preimage_mem_nhds hU
      exact h
    have hzeroU : ∀ᶠ a in 𝓝 u, (0 : ℝ) ∈ D a := by
      have hpoint : (u, ((0 : ℝ), (γ u).2)) = (u, γ u) := by
        rw [← hu]
      have h := (continuous_id.prodMk (continuous_const.prodMk
        (continuous_snd.comp hγ.continuous))).continuousAt.preimage_mem_nhds (hpoint.symm ▸ hU)
      exact h
    have hγ' : ∀ᶠ a in 𝓝 u, HasDerivAt (fun a => (γ a).1) (W a ((γ a).1)) a :=
      Eventually.of_forall fun a => (hγ a).fst
    have hzero : ∀ᶠ a in 𝓝 u, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (W a 0) a :=
      Eventually.of_forall fun a => by
        change HasDerivAt (fun _ : ℝ => (0 : ℝ)) ((v a (0, (γ a).2)).1) a
        rw [htangent]
        exact hasDerivAt_const a 0
    have heq : (fun a => (γ a).1) =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) :=
      ODE_solution_unique_of_eventually (Eventually.of_forall hW)
        (hγ'.and hγU) (hzero.and hzeroU) hu
    exact heq
  have hclopen : IsClopen Z := ⟨hclosed, hopen⟩
  constructor
  · intro hs
    have hZ : Z = univ := hclopen.eq_univ ⟨s, hs⟩
    change t ∈ Z
    rw [hZ]
    exact mem_univ t
  · intro ht
    have hZ : Z = univ := hclopen.eq_univ ⟨t, ht⟩
    change s ∈ Z
    rw [hZ]
    exact mem_univ s

theorem fst_pos_iff_of_tangent (hγ : IsIntegralCurve γ v)
    (hv : ContDiff ℝ 1 (fun p : ℝ × (ℝ × E) => v p.1 p.2))
    (htangent : ∀ t : ℝ, ∀ y : E, (v t (0, y)).1 = 0) (s t : ℝ) :
    0 < (γ s).1 ↔ 0 < (γ t).1 := by
  have hpos : ∀ a b : ℝ, 0 < (γ a).1 → 0 < (γ b).1 := by
    intro a b ha
    by_contra hb
    have hb' : (γ b).1 ≤ 0 := le_of_not_gt hb
    obtain ⟨u, hu⟩ := intermediate_value_univ b a
      (continuous_fst.comp hγ.continuous) ⟨hb', ha.le⟩
    have ha₀ := (hγ.fst_eq_zero_iff_of_tangent hv htangent u a).mp hu
    exact ha.ne' ha₀
  exact ⟨hpos s t, hpos t s⟩

theorem fst_nonneg_iff_of_tangent (hγ : IsIntegralCurve γ v)
    (hv : ContDiff ℝ 1 (fun p : ℝ × (ℝ × E) => v p.1 p.2))
    (htangent : ∀ t : ℝ, ∀ y : E, (v t (0, y)).1 = 0) (s t : ℝ) :
    0 ≤ (γ s).1 ↔ 0 ≤ (γ t).1 := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt]
  exact or_congr
    (by simpa only [eq_comm] using hγ.fst_eq_zero_iff_of_tangent hv htangent s t)
    (hγ.fst_pos_iff_of_tangent hv htangent s t)

theorem fst_neg_iff_of_tangent (hγ : IsIntegralCurve γ v)
    (hv : ContDiff ℝ 1 (fun p : ℝ × (ℝ × E) => v p.1 p.2))
    (htangent : ∀ t : ℝ, ∀ y : E, (v t (0, y)).1 = 0) (s t : ℝ) :
    (γ s).1 < 0 ↔ (γ t).1 < 0 := by
  simpa only [not_le] using not_congr (hγ.fst_nonneg_iff_of_tangent hv htangent s t)

theorem fst_nonpos_iff_of_tangent (hγ : IsIntegralCurve γ v)
    (hv : ContDiff ℝ 1 (fun p : ℝ × (ℝ × E) => v p.1 p.2))
    (htangent : ∀ t : ℝ, ∀ y : E, (v t (0, y)).1 = 0) (s t : ℝ) :
    (γ s).1 ≤ 0 ↔ (γ t).1 ≤ 0 := by
  simpa only [not_lt] using not_congr (hγ.fst_pos_iff_of_tangent hv htangent s t)

end IsIntegralCurve
