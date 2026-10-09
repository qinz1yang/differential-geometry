/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Maps.FiniteFiberNeighborhoods
import DifferentialGeometry.Topology.PuncturedConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

open Set Filter Topology

namespace DifferentialGeometry.Topology

/-- A continuous factor through a locally injective map with compact Hausdorff
source extends across the center of a punctured complex disk when its composition
has a continuous limit there. The extension stays in one embedded source sheet
and agrees with the given factor on the smaller punctured disk. -/
theorem exists_local_extension_of_punctured_compact_locallyInjective_factor
    {Y Z : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TopologicalSpace Z] [T2Space Z]
    {g : Y → Z} (hg : Continuous g) (hloc : IsLocallyInjective g)
    {a : ℂ → Z} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (ha : ContinuousAt a z)
    (τ : C(↥(Metric.ball z r \ {z}), Y))
    (hvalue : ∀ w : ↥(Metric.ball z r \ {z}), g (τ w) = a w) :
    ∃ (ρ : ℝ) (_ : 0 < ρ) (hρr : ρ ≤ r) (T : C(Metric.ball z ρ, Y)),
      (∀ w : Metric.ball z ρ, g (T w) = a w) ∧
      ∀ (w : Metric.ball z ρ) (hw : (w : ℂ) ≠ z),
        T w = τ ⟨(w : ℂ), Metric.ball_subset_ball hρr w.property, hw⟩ := by
  classical
  obtain ⟨_, U, V, hU, hdisj, hVopen, hazV, hcover⟩ :=
    exists_disjoint_embedded_fiber_neighborhoods hg hloc (a z)
  have hpre : a ⁻¹' V ∈ 𝓝 z := ha (hVopen.mem_nhds hazV)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let ρ : ℝ := min ε r
  have hρ : 0 < ρ := lt_min hε hr
  have hρr : ρ ≤ r := min_le_right _ _
  have hρε : ρ ≤ ε := min_le_left _ _
  have haV (w : Metric.ball z ρ) : a w ∈ V :=
    hεsub (Metric.ball_subset_ball hρε w.property)
  let P : Set ℂ := Metric.ball z ρ \ {z}
  have hPopen : IsOpen P := Metric.isOpen_ball.sdiff isClosed_singleton
  have hPconnected : IsConnected P :=
    (Metric.isPathConnected_ball_sdiff_singleton
      (by simp [Complex.rank_real_complex]) z hρ).isConnected
  let : ConnectedSpace P := isConnected_iff_connectedSpace.mp hPconnected
  let t : P → Y := fun w =>
    τ ⟨(w : ℂ), Metric.ball_subset_ball hρr w.property.1, w.property.2⟩
  have ht : Continuous t :=
    τ.continuous.comp (continuous_subtype_val.subtype_mk fun w : P =>
      ⟨Metric.ball_subset_ball hρr w.property.1, w.property.2⟩)
  have htvalue (w : P) : g (t w) = a w :=
    hvalue ⟨(w : ℂ), Metric.ball_subset_ball hρr w.property.1, w.property.2⟩
  have hcoverP (w : P) : ∃ i : g ⁻¹' {a z}, t w ∈ U i := by
    apply Set.mem_iUnion.mp
    apply hcover
    change g (t w) ∈ V
    rw [htvalue]
    exact haV ⟨(w : ℂ), w.property.1⟩
  obtain ⟨w₀, hw₀⟩ := hPconnected.nonempty
  obtain ⟨i, hi⟩ := hcoverP ⟨w₀, hw₀⟩
  have hcompl : (t ⁻¹' U i)ᶜ =
      ⋃ j : {j : g ⁻¹' {a z} // j ≠ i}, t ⁻¹' U j.val := by
    ext w
    constructor
    · intro hw
      obtain ⟨j, hj⟩ := hcoverP w
      have hji : j ≠ i := by
        intro hji
        apply hw
        change t w ∈ U i
        exact hji ▸ hj
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hw
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hw
      intro hwi
      exact Set.disjoint_left.mp (hdisj j.property) hj hwi
  have hclosed : IsClosed (t ⁻¹' U i) := by
    apply isOpen_compl_iff.mp
    rw [hcompl]
    exact isOpen_iUnion fun j => (hU j.val).1.preimage ht
  have hclopen : IsClopen (t ⁻¹' U i) :=
    ⟨hclosed, (hU i).1.preimage ht⟩
  have hall : t ⁻¹' U i = Set.univ := hclopen.eq_univ ⟨⟨w₀, hw₀⟩, hi⟩
  have hsheet (w : P) : t w ∈ U i := by
    have hw : w ∈ t ⁻¹' U i := hall.symm ▸ Set.mem_univ w
    exact hw
  have haP : ContinuousOn a P := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun w : P => a (w : ℂ))
    have heq : (fun w : P => a (w : ℂ)) = g ∘ t :=
      funext fun w => (htvalue w).symm
    rw [heq]
    exact hg.comp ht
  have haBall : ContinuousOn a (Metric.ball z ρ) := by
    intro w hw
    by_cases hwz : w = z
    · subst w
      exact ha.continuousWithinAt
    · exact ((haP w ⟨hw, hwz⟩).continuousAt
        (hPopen.mem_nhds ⟨hw, hwz⟩)).continuousWithinAt
  have haImage (w : Metric.ball z ρ) :
      a w ∈ Set.range ((U i).domRestrict g) := by
    by_cases hwz : (w : ℂ) = z
    · refine ⟨⟨i.val, (hU i).2.1⟩, ?_⟩
      change g i.val = a w
      rw [hwz]
      exact i.property
    · let wP : P := ⟨(w : ℂ), w.property, hwz⟩
      exact ⟨⟨t wP, hsheet wP⟩, htvalue wP⟩
  let A : C(Metric.ball z ρ, Set.range ((U i).domRestrict g)) :=
    ⟨fun w => ⟨a w, haImage w⟩, haBall.domRestrict.subtype_mk haImage⟩
  let e : U i ≃ₜ Set.range ((U i).domRestrict g) := (hU i).2.2.toHomeomorph
  let T : C(Metric.ball z ρ, Y) :=
    ⟨fun w => (e.symm (A w) : Y),
      continuous_subtype_val.comp (e.symm.continuous.comp A.continuous)⟩
  have hTvalue (w : Metric.ball z ρ) : g (T w) = a w := by
    have heq := congrArg (Subtype.val : Set.range ((U i).domRestrict g) → Z)
      (e.apply_symm_apply (A w))
    exact heq
  refine ⟨ρ, hρ, hρr, T, hTvalue, ?_⟩
  intro w hw
  let wP : P := ⟨(w : ℂ), w.property, hw⟩
  have heq : e.symm (A w) = ⟨t wP, hsheet wP⟩ := by
    apply (hU i).2.2.injective
    change g (T w) = g (t wP)
    exact (hTvalue w).trans (htvalue wP).symm
  exact congrArg (Subtype.val : U i → Y) heq

end DifferentialGeometry.Topology
