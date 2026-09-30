import DifferentialGeometry.Topology.Engulfing.Newman.Step.NewmanLocalStep

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology
open scoped ContinuousMap

variable {Z M F : Type*} [TopologicalSpace Z] [CompactSpace Z]
  [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_restoration_buffers_of_chart_balls (f : C(Z, M))
    (e : OpenPartialHomeomorph M F) (c : F) {rB rU rA R : ℝ}
    (hBU : rB < rU) (hUA : rU < rA) (hAR : rA < R)
    (hR : closedBall c R ⊆ e.target) :
    ∃ A B U : Set Z,
      IsCompact A ∧ IsClosed B ∧ IsOpen U ∧ B ⊆ U ∧ U ⊆ interior A ∧
      (∀ x ∈ A, f x ∈ e.source) ∧
      (∀ x ∈ A, e (f x) ∈ closedBall c rA) ∧
      B = f ⁻¹' (e.symm '' closedBall c rB) ∧
      U = f ⁻¹' (e.source ∩ e ⁻¹' ball c rU) ∧
      ∀ S : Set M, S ⊆ e.symm '' closedBall c rB →
        f ⁻¹' S ⊆ B ∧ ∀ D : Set Z, Disjoint (f '' (D \ U)) S := by
  let A : Set Z := f ⁻¹' (e.symm '' closedBall c rA)
  let B : Set Z := f ⁻¹' (e.symm '' closedBall c rB)
  let U : Set Z := f ⁻¹' (e.source ∩ e ⁻¹' ball c rU)
  have hAe : closedBall c rA ⊆ e.target :=
    (closedBall_subset_closedBall hAR.le).trans hR
  have hBe : closedBall c rB ⊆ e.target :=
    (closedBall_subset_closedBall (hBU.trans hUA).le).trans hAe
  have hAc : IsClosed A := ((isCompact_closedBall c rA).image_of_continuousOn
    (e.continuousOn_symm.mono hAe)).isClosed.preimage f.continuous
  have hBc : IsClosed B := ((isCompact_closedBall c rB).image_of_continuousOn
    (e.continuousOn_symm.mono hBe)).isClosed.preimage f.continuous
  have hUo : IsOpen U := (e.isOpen_inter_preimage isOpen_ball).preimage f.continuous
  have hBU' : B ⊆ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    change f x ∈ e.source ∩ e ⁻¹' ball c rU
    rw [← hxy]
    exact ⟨e.map_target (hBe hy), by
      change e (e.symm y) ∈ ball c rU
      rw [e.right_inv (hBe hy)]
      exact closedBall_subset_ball hBU hy⟩
  have hUA' : U ⊆ A := by
    intro x hx
    exact ⟨e (f x), ball_subset_closedBall ((ball_subset_ball hUA.le) hx.2), e.left_inv hx.1⟩
  refine ⟨A, B, U, hAc.isCompact, hBc, hUo, hBU',
    hUo.subset_interior_iff.mpr hUA', ?_, ?_, rfl, rfl, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact hxy ▸ e.map_target (hAe hy)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [← hxy, e.right_inv (hAe hy)]
    exact hy
  · intro S hS
    refine ⟨preimage_mono hS, ?_⟩
    intro D
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    exact hx.2 (hBU' (hS hy))

end DifferentialGeometry.Topology.Engulfing
