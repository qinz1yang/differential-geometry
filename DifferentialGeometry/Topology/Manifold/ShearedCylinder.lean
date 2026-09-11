import DifferentialGeometry.Topology.Manifold.BoundaryOrder
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Topology.Order.ProjIcc

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem endpoint_order_of_regular_patch_on_variable_height_cylinder
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace N] [ChartedSpace H N] [BoundarylessManifold I N]
    [CompactSpace N] (h : N → ℝ) (c : ℝ)
    (hvary : ∃ p q, h p ≠ h q) (hpos : ∃ p, 0 < h p)
    (u : N × unitInterval → ℝ) (i j : Bool) (a b : ℝ)
    (hreg : ∀ w, mvfderiv (I.prod (𝓡∂ 1)) u w ≠ 0)
    (hzero : ∀ p, u (p, 0) = a) (hone : ∀ p, u (p, 1) = b)
    (hlocal₀ : ∀ᶠ w in 𝓝ˢ ((univ : Set N) ×ˢ {0}),
      u w = if i then ((w.2 : ℝ) - 1) * h w.1 + c else (w.2 : ℝ) * h w.1)
    (hlocal₁ : ∀ᶠ w in 𝓝ˢ ((univ : Set N) ×ˢ {1}),
      u w = if j then ((w.2 : ℝ) - 1) * h w.1 + c else (w.2 : ℝ) * h w.1) :
    i = false ∧ j = true ∧ a = 0 ∧ b = c ∧ 0 < c := by
  have ha (p : N) : a = if i then -h p + c else 0 := by
    have hp := subset_of_mem_nhdsSet hlocal₀ (show (p, 0) ∈ (univ : Set N) ×ˢ {0} from
      ⟨mem_univ _, mem_singleton _⟩)
    simpa using (hzero p).symm.trans hp
  have hb (p : N) : b = if j then c else h p := by
    have hp := subset_of_mem_nhdsSet hlocal₁ (show (p, 1) ∈ (univ : Set N) ×ˢ {1} from
      ⟨mem_univ _, mem_singleton _⟩)
    simpa using (hone p).symm.trans hp
  have hi : i = false := by
    cases i with
    | false => rfl
    | true =>
      obtain ⟨p, q, hpq⟩ := hvary
      have hp := ha p
      have hq := ha q
      simp only [↓reduceIte] at hp hq
      exact False.elim (hpq (by linarith only [hp, hq]))
  have hj : j = true := by
    cases j with
    | true => rfl
    | false =>
      obtain ⟨p, q, hpq⟩ := hvary
      have hp := hb p
      have hq := hb q
      simp only [Bool.false_eq_true, ↓reduceIte] at hp hq
      exact False.elim (hpq (hp.symm.trans hq))
  obtain ⟨p, hp⟩ := hpos
  have ha0 : a = 0 := by simpa [hi] using ha p
  have hbc : b = c := by simpa [hj] using hb p
  have hbdy (w : N × unitInterval) (hw : (I.prod (𝓡∂ 1)).IsBoundaryPoint w) :
      u w = 0 ∨ u w = c := by
    change w ∈ (I.prod (𝓡∂ 1)).boundary (N × unitInterval) at hw
    rw [ModelWithCorners.boundary_of_boundaryless_left, boundary_Icc] at hw
    rcases hw.2 with hw | hw
    · left
      have heq : w = (w.1, 0) := Prod.ext rfl hw
      exact (congrArg u heq).trans ((hzero w.1).trans ha0)
    · right
      have heq : w = (w.1, 1) := Prod.ext rfl hw
      exact (congrArg u heq).trans ((hone w.1).trans hbc)
  let γ : ℝ → N × unitInterval := fun t ↦ (p, projIcc 0 1 zero_le_one t)
  have hγ : Continuous γ := continuous_const.prodMk continuous_projIcc
  have hγ₀ : γ 0 ∈ (univ : Set N) ×ˢ {0} := by simp [γ]
  have hlocal : u =ᶠ[𝓝 (γ 0)] (fun w ↦ (w.2 : ℝ) * h w.1) := by
    change {w | u w = (w.2 : ℝ) * h w.1} ∈ 𝓝 (γ 0)
    simpa [hi] using mem_nhdsSet_iff_forall.mp hlocal₀ _ hγ₀
  have hcoordinate : ∀ᶠ t in 𝓝[≥] (0 : ℝ), ((γ t).2 : ℝ) * h (γ t).1 = 0 + h p * t := by
    filter_upwards [Icc_mem_nhdsGE (show (0 : ℝ) < 1 from zero_lt_one)] with t ht
    change (projIcc 0 1 zero_le_one t : ℝ) * h p = 0 + h p * t
    rw [projIcc_of_mem zero_le_one ht]
    ring
  exact ⟨hi, hj, ha0, hbc, boundary_value_lt_of_inward_coordinate hreg hbdy γ
    hγ.continuousWithinAt hlocal hp hcoordinate⟩

end DifferentialGeometry.Topology.Manifold
