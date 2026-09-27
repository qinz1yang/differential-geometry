/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarCoordinates

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_compact_source_sheets_of_markedCrossingChart
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hτ : hD.IsBranchDeckInvolution c J τ) (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} {e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)}
    (he : hD.IsMarkedCrossingChartAt c J τ ρ a e) :
    ∃ (A₀ A₁ : Set (EuclideanSpace ℝ (Fin 2))) (U : Set M),
      IsCompact A₀ ∧ IsCompact A₁ ∧ A₀ ⊆ C ∧ A₁ ⊆ C ∧ Disjoint A₀ A₁ ∧
      a ∈ interior A₀ ∧ τ a ∈ interior A₁ ∧ InjOn D A₀ ∧ InjOn D A₁ ∧
      IsOpen U ∧ D a ∈ U ∧ U ⊆ e.source ∧
      (∀ x ∈ D.domain, D x ∈ U → x ∈ interior A₀ ∪ interior A₁) ∧
      (∀ y ∈ U, y ∈ D '' A₀ ↔ (e y).2.2 = 0) ∧
      (∀ y ∈ U, y ∈ D '' A₁ ↔ (e y).2.1 = 0) ∧
      (∀ y ∈ U, y ∈ hD.singularSet.branchCarrier c ↔ (e y).2 = 0) ∧
      (∀ x ∈ A₀, 0 < (e (D x)).2.1 ↔ ∃ s ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, s)) ∧
      ∀ x ∈ A₁, 0 < (e (D x)).2.2 ↔ ∃ s ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, s) := by
  obtain ⟨ha, hae, -, P₀, P₁, -, -, hPP, hP₀D, hP₁D, hP₀n, hP₁n,
    hP₀inj, hP₁inj, -, -, hP₀read, hP₁read, hΓread, hpos₀, hpos₁⟩ := he
  have hτa : τ a ∈ J := hτ.2.2.2.1 ha
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hP₀n (hρ.2.2.2.2.1 a ha))
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hP₁n (hρ.2.2.2.2.1 (τ a) hτa))
  let A₀ := closedBall a (r₀ / 2)
  let A₁ := closedBall (τ a) (r₁ / 2)
  have hA₀sub : A₀ ⊆ P₀ ∩ C :=
    (closedBall_subset_ball (half_lt_self hr₀)).trans hball₀
  have hA₁sub : A₁ ⊆ P₁ ∩ C :=
    (closedBall_subset_ball (half_lt_self hr₁)).trans hball₁
  have haA : a ∈ interior A₀ :=
    mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (half_pos hr₀))
  have hτaA : τ a ∈ interior A₁ :=
    mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (half_pos hr₁))
  have hDaΓ : D a ∈ hD.singularSet.branchCarrier c :=
    (show a ∈ hD.branchPreimage c from hτ.1.symm ▸ ha).2
  have hfiber : ∀ x ∈ D.domain, D x = D a → x ∈ interior A₀ ∪ interior A₁ := by
    intro x hx hxa
    have hxpre : x ∈ hD.branchPreimage c := ⟨hx, by
      change D x ∈ hD.singularSet.branchCarrier c
      rwa [hxa]⟩
    have hxJ : x ∈ J := hτ.1 ▸ hxpre
    rcases (hτ.2.2.2.2.2.2.2.2 a ha x hxJ).mp hxa.symm with rfl | rfl
    · exact Or.inl haA
    · exact Or.inr hτaA
  obtain ⟨N, hN, hNpre⟩ := exists_mem_nhds_forall_mem_of_isCompact
    D.isPLBall_domain.isPolyhedron.isCompact D.continuousOn
    (isOpen_interior.union isOpen_interior) hfiber
  have hneighborhood : {y | y ∈ e.source ∧ y ∈ N ∧
      (y ∈ D '' P₀ ↔ (e y).2.2 = 0) ∧ (y ∈ D '' P₁ ↔ (e y).2.1 = 0) ∧
      (y ∈ hD.singularSet.branchCarrier c ↔ (e y).2 = 0)} ∈ 𝓝 (D a) := by
    filter_upwards [e.open_source.mem_nhds hae, hN, hP₀read, hP₁read, hΓread]
      with y hy hNy h₀ h₁ hΓ
    exact ⟨hy, hNy, h₀, h₁, hΓ⟩
  obtain ⟨U, hUsub, hUopen, haU⟩ := mem_nhds_iff.mp hneighborhood
  have hpre : ∀ x ∈ D.domain, D x ∈ U → x ∈ interior A₀ ∪ interior A₁ :=
    fun x hx hxU => hNpre x hx (hUsub hxU).2.1
  have hread₀ : ∀ y ∈ U, y ∈ D '' A₀ ↔ y ∈ D '' P₀ := by
    intro y hy
    constructor
    · exact fun h => image_mono (hA₀sub.trans inter_subset_left) h
    · rintro ⟨x, hxP, hxy⟩
      rcases hpre x (hP₀D hxP) (hxy.symm ▸ hy) with hxA | hxA
      · exact ⟨x, interior_subset hxA, hxy⟩
      · exact (disjoint_left.mp hPP hxP (hA₁sub (interior_subset hxA)).1).elim
  have hread₁ : ∀ y ∈ U, y ∈ D '' A₁ ↔ y ∈ D '' P₁ := by
    intro y hy
    constructor
    · exact fun h => image_mono (hA₁sub.trans inter_subset_left) h
    · rintro ⟨x, hxP, hxy⟩
      rcases hpre x (hP₁D hxP) (hxy.symm ▸ hy) with hxA | hxA
      · exact (disjoint_left.mp hPP (hA₀sub (interior_subset hxA)).1 hxP).elim
      · exact ⟨x, interior_subset hxA, hxy⟩
  exact ⟨A₀, A₁, U, isCompact_closedBall _ _, isCompact_closedBall _ _,
    hA₀sub.trans inter_subset_right, hA₁sub.trans inter_subset_right,
    hPP.mono (hA₀sub.trans inter_subset_left) (hA₁sub.trans inter_subset_left), haA, hτaA,
    hP₀inj.mono (hA₀sub.trans inter_subset_left), hP₁inj.mono (hA₁sub.trans inter_subset_left),
    hUopen, haU, fun _ hy => (hUsub hy).1, hpre,
    fun y hy => (hread₀ y hy).trans (hUsub hy).2.2.1,
    fun y hy => (hread₁ y hy).trans (hUsub hy).2.2.2.1,
    fun _ hy => (hUsub hy).2.2.2.2,
    fun x hx => hpos₀ x (hA₀sub hx).1, fun x hx => hpos₁ x (hA₁sub hx).1⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
