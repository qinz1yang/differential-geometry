/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_local_disks_of_surface_chart
    {E : Type*} [TopologicalSpace E] {A : Set E} {x : E} (hx : x ∈ A)
    (hA : ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ A) ≃ₜ V)) :
    ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x := by
  obtain ⟨W, -, hxW, V, hV, ⟨ψ⟩⟩ := hA
  intro N hN
  obtain ⟨c, r, g, hr, hgc, hgi, hgm, hgx⟩ :=
    exists_ball_chart_of_homeomorph_isOpen hV ψ ⟨hxW, hx⟩
      (mem_nhdsWithin_of_mem_nhds hN)
  exact ⟨c, r, g, hr, hgc, hgi, fun y hy => ⟨(hgm hy).1.2, (hgm hy).2⟩, hgx⟩

theorem HasPLCrossingAt.exists_lineChart_of_local_disks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} {x : E} (hcross : HasPLCrossingAt A B x)
    (hA : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x)
    (hB : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (B ∩ N) ∧ g c = x) :
    ∃ (U : Set E) (φ : E → ℝ × ℝ × ℝ) (ρ : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < ρ ∧
      IsPLHomeomorphOn φ U (Metric.ball 0 ρ) ∧ φ x = 0 ∧
      ∀ y ∈ U, (y ∈ A ↔ (φ y).2.2 = 0) ∧ (y ∈ B ↔ (φ y).2.1 = 0) := by
  obtain ⟨U, φ, ρ, α, β, hU, hxU, hρ, hφ, hφx, hα, hβ, hloc⟩ :=
    hcross.exists_coordinateChart
  have hαzero : α = 0 := hα.resolve_right fun hne =>
    false_of_ballChart_of_halfPlane hU hxU hφ hφx hne
      (fun y hy hyA => (hloc y hy).1.mp hyA)
      hA
  let τ : (ℝ × ℝ × ℝ) ≃ₗᵢ[ℝ] (ℝ × ℝ × ℝ) :=
    { LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ) (LinearEquiv.prodComm ℝ ℝ ℝ) with
      norm_map' := by
        rintro ⟨a, b, c⟩
        change max ‖a‖ (max ‖c‖ ‖b‖) = max ‖a‖ (max ‖b‖ ‖c‖)
        rw [max_comm ‖c‖ ‖b‖] }
  have hτ : IsPLHomeomorphOn τ (Metric.ball 0 ρ) (Metric.ball 0 ρ) := by
    have hτpl := isPLHomeomorphOn_linearEquiv τ.toLinearEquiv
      (V := Metric.ball 0 ρ) Metric.isOpen_ball
    change IsPLHomeomorphOn τ (Metric.ball 0 ρ) (τ '' Metric.ball 0 ρ) at hτpl
    have hτball := τ.image_ball 0 ρ
    rw [map_zero] at hτball
    rwa [hτball] at hτpl
  let ψ : E → ℝ × ℝ × ℝ := τ ∘ φ
  have hψ : IsPLHomeomorphOn ψ U (Metric.ball 0 ρ) := hφ.trans hτ
  have hψx : ψ x = 0 := by simp [ψ, hφx]
  let β' := β.comp τ.symm.toLinearMap
  have hβzero : β = 0 := hβ.resolve_right fun hne => by
    have hβ' : β' (1, 0, 0) ≠ 0 := by simpa [β', τ] using hne
    apply false_of_ballChart_of_halfPlane hU hxU hψ hψx hβ' _
      hB
    intro y hy hyB
    have hyφ := (hloc y hy).2.mp hyB
    refine ⟨hyφ.1, ?_⟩
    simpa [β', ψ] using hyφ.2
  refine ⟨U, φ, ρ, hU, hxU, hρ, hφ, hφx, fun y hy => ⟨?_, ?_⟩⟩
  · simpa [hαzero] using (hloc y hy).1
  · simpa [hβzero] using (hloc y hy).2

theorem HasPLCrossingAt.exists_lineChart_of_surface_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} {x : E} (hcross : HasPLCrossingAt A B x) (hx : x ∈ A ∩ B)
    (hA : ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ A) ≃ₜ V))
    (hB : ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ B) ≃ₜ V)) :
    ∃ (U : Set E) (φ : E → ℝ × ℝ × ℝ) (ρ : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < ρ ∧
      IsPLHomeomorphOn φ U (Metric.ball 0 ρ) ∧ φ x = 0 ∧
      ∀ y ∈ U, (y ∈ A ↔ (φ y).2.2 = 0) ∧ (y ∈ B ↔ (φ y).2.1 = 0) := by
  exact hcross.exists_lineChart_of_local_disks
    (exists_local_disks_of_surface_chart hx.1 hA)
    (exists_local_disks_of_surface_chart hx.2 hB)

theorem HasPLCrossingAt.exists_lineChart_of_eventuallyEq_surface_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B A' B' : Set E} {x : E} (hcross : HasPLCrossingAt A B x) (hx : x ∈ A ∩ B)
    (hA : ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ A) ≃ₜ V))
    (hB : ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ B) ≃ₜ V))
    (hAA' : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ A')
    (hBB' : ∀ᶠ y in 𝓝 x, y ∈ B ↔ y ∈ B') :
    ∃ (U : Set E) (φ : E → ℝ × ℝ × ℝ) (ρ : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < ρ ∧
      IsPLHomeomorphOn φ U (Metric.ball 0 ρ) ∧ φ x = 0 ∧
      ∀ y ∈ U, (y ∈ A' ↔ (φ y).2.2 = 0) ∧ (y ∈ B' ↔ (φ y).2.1 = 0) := by
  have hdisks {S T : Set E} (hxS : x ∈ S)
      (hS : ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen V ∧ Nonempty (↥(W ∩ S) ≃ₜ V))
      (hST : ∀ᶠ y in 𝓝 x, y ∈ S ↔ y ∈ T) :
      ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
        (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
          InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (T ∩ N) ∧ g c = x := by
    intro N hN
    obtain ⟨c, r, g, hr, hgc, hgi, hgm, hgx⟩ :=
      exists_local_disks_of_surface_chart hxS hS
        (N ∩ {y | y ∈ S ↔ y ∈ T}) (Filter.inter_mem hN hST)
    exact ⟨c, r, g, hr, hgc, hgi,
      fun y hy => ⟨(hgm hy).2.2.mp (hgm hy).1, (hgm hy).2.1⟩, hgx⟩
  exact (hcross.congr hAA' hBB').exists_lineChart_of_local_disks
    (hdisks hx.1 hA hAA') (hdisks hx.2 hB hBB')

end DifferentialGeometry.Topology.PiecewiseLinear
