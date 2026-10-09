import Mathlib.Analysis.Normed.Group.AddCircle
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.ContinuousMap.Basic

noncomputable section

open Set

namespace AddCircle

theorem norm_coe_eq_of_nonneg_of_add_norm_lt {p x : ℝ} (hx : 0 ≤ x)
    (hxp : x + ‖(x : AddCircle p)‖ < p) : ‖(x : AddCircle p)‖ = x := by
  have hp : 0 < p := lt_of_le_of_lt (add_nonneg hx (norm_nonneg _)) hxp
  by_cases hhalf : x ≤ p / 2
  · have he := (norm_coe_eq_abs_iff p hp.ne').mpr (by
      rw [abs_of_nonneg hx, abs_of_pos hp]
      exact hhalf)
    simpa only [abs_of_nonneg hx] using he
  · have hxp' : x < p := lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg _)) hxp
    have hsmall : |x - p| ≤ |p| / 2 := by
      rw [abs_of_pos hp, abs_of_nonpos (sub_nonpos.mpr hxp'.le)]
      linarith
    have he := (norm_coe_eq_abs_iff p hp.ne').mpr hsmall
    have hcoe : ((x - p : ℝ) : AddCircle p) = (x : AddCircle p) := by simp
    rw [hcoe, abs_of_nonpos (sub_nonpos.mpr hxp'.le)] at he
    linarith

theorem dist_coe_eq_sub_of_le_of_sub_add_dist_lt {p a b : ℝ} (hab : a ≤ b)
    (hgap : b - a + dist (b : AddCircle p) (a : AddCircle p) < p) :
    dist (b : AddCircle p) (a : AddCircle p) = b - a := by
  rw [dist_eq_norm, ← coe_sub] at hgap ⊢
  exact norm_coe_eq_of_nonneg_of_add_norm_lt (sub_nonneg.mpr hab) hgap

theorem dist_coe_le_dist_coe_of_monotone {p : ℝ} {f : ℝ → ℝ} (hf : Monotone f)
    {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hgap : f b - f a + dist (f b : AddCircle p) (f a : AddCircle p) < p) :
    dist (f s : AddCircle p) (f t : AddCircle p) ≤
      dist (f b : AddCircle p) (f a : AddCircle p) := by
  have hab : a ≤ b := hs.1.trans hs.2
  have he := dist_coe_eq_sub_of_le_of_sub_add_dist_lt (hf hab) hgap
  rw [he, dist_eq_norm, ← coe_sub]
  calc
    ‖((f s - f t : ℝ) : AddCircle p)‖ ≤ ‖f s - f t‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ ≤ f b - f a := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hf hs.1, hf hs.2, hf ht.1, hf ht.2]

end AddCircle

end

noncomputable section

open Set

namespace DifferentialGeometry.Topology

theorem exists_pos_dist_comp_lt_of_map_thirds
    {M : Type*} [PseudoMetricSpace M] (γ : C(AddCircle (1 : ℝ), M))
    (hγ : _root_.Topology.IsEmbedding γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ f : CircleDeg1Lift,
      f (1 / 3) = f 0 + 1 / 3 → f (2 / 3) = f 0 + 2 / 3 →
      ∀ a b : ℝ, b - a ≤ 1 / 3 →
      dist (γ (f b : AddCircle (1 : ℝ))) (γ (f a : AddCircle (1 : ℝ))) < η →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        dist (γ (f s : AddCircle (1 : ℝ))) (γ (f t : AddCircle (1 : ℝ))) < ε := by
  have huγ : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  obtain ⟨δ, hδ, hδmap⟩ := Metric.uniformContinuous_iff.mp huγ ε hε
  let δ' := min δ (1 / 3 : ℝ)
  have hδ' : 0 < δ' := lt_min hδ (by norm_num)
  let : CompactSpace (range γ) := isCompact_iff_compactSpace.mp (isCompact_range γ.continuous)
  have hinv : UniformContinuous hγ.toHomeomorph.symm :=
    CompactSpace.uniformContinuous_of_continuous hγ.toHomeomorph.symm.continuous
  obtain ⟨η, hη, hηmap⟩ := Metric.uniformContinuous_iff.mp hinv δ' hδ'
  refine ⟨η, hη, ?_⟩
  intro f hf₁ hf₂ a b hab hclose s hs t ht
  have hcircle : dist (f b : AddCircle (1 : ℝ)) (f a : AddCircle (1 : ℝ)) < δ' := by
    have h := hηmap
      (a := ⟨γ (f b : AddCircle (1 : ℝ)), mem_range_self _⟩)
      (b := ⟨γ (f a : AddCircle (1 : ℝ)), mem_range_self _⟩) hclose
    change dist (hγ.toHomeomorph.symm (hγ.toHomeomorph (f b : AddCircle (1 : ℝ))))
      (hγ.toHomeomorph.symm (hγ.toHomeomorph (f a : AddCircle (1 : ℝ)))) < δ' at h
    simpa only [hγ.toHomeomorph.symm_apply_apply] using h
  have hgap : f b - f a + dist (f b : AddCircle (1 : ℝ)) (f a : AddCircle (1 : ℝ)) < 1 := by
    have hg := f.sub_le_two_thirds_of_map_thirds hf₁ hf₂ hab
    have hc := hcircle.trans_le (min_le_right δ (1 / 3 : ℝ))
    linarith
  apply hδmap
  exact (AddCircle.dist_coe_le_dist_coe_of_monotone f.monotone hs ht hgap).trans_lt
    (hcircle.trans_le (min_le_left δ (1 / 3 : ℝ)))

end DifferentialGeometry.Topology

end

noncomputable section

open Set

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology

theorem exists_pos_dist_comp_lt_of_three_fixed_points
    {M : Type*} [PseudoMetricSpace M] (γ : C(loopCircle, M))
    (hγ : _root_.Topology.IsEmbedding γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ σ : C(loopCircle, loopCircle), IsWeaklyMonotoneOnce σ →
      σ 0 = 0 → σ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) →
      σ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle) →
      ∀ a b : ℝ, b - a ≤ 1 / 3 →
      dist (γ (σ (b : loopCircle))) (γ (σ (a : loopCircle))) < η →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        dist (γ (σ (s : loopCircle))) (γ (σ (t : loopCircle))) < ε := by
  obtain ⟨η, hη, hbound⟩ := exists_pos_dist_comp_lt_of_map_thirds γ hγ hε
  refine ⟨η, hη, ?_⟩
  intro σ hσ h0 h1 h2 a b hab hclose s hs t ht
  obtain ⟨ψ, _, hl, hm, hp, hψ0, hψ1, hψ2⟩ :=
    hσ.exists_monotone_lift_of_three_fixed_points
      (a := 1 / 3) (b := 2 / 3) (by norm_num) (by norm_num) (by norm_num) h0 h1 h2
  let f : CircleDeg1Lift := ⟨⟨ψ, hm⟩, hp⟩
  have hf₁ : f (1 / 3) = f 0 + 1 / 3 := by change ψ _ = ψ _ + _; rw [hψ0, hψ1]; ring
  have hf₂ : f (2 / 3) = f 0 + 2 / 3 := by change ψ _ = ψ _ + _; rw [hψ0, hψ2]; ring
  have hclose' : dist (γ (f b : loopCircle)) (γ (f a : loopCircle)) < η := by
    change dist (γ (ψ b : loopCircle)) (γ (ψ a : loopCircle)) < η
    simpa only [hl] using hclose
  have h := hbound f hf₁ hf₂ a b hab hclose' s hs t ht
  change dist (γ (ψ s : loopCircle)) (γ (ψ t : loopCircle)) < ε at h
  simpa only [hl] using h

end DifferentialGeometry.Geometry

end
