import DifferentialGeometry.Topology.Engulfing.Local.Buffers.RestorationBuffers

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology
open scoped ContinuousMap

variable {Z M F : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [MetricSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_stable_restoration_buffers (f : C(Z, M))
    (e : OpenPartialHomeomorph M F) (c : F) {r₀ rB rU rCut rA R : ℝ}
    (h₀B : r₀ < rB) (hBU : rB < rU) (hUC : rU < rCut)
    (hCA : rCut < rA) (hAR : rA < R) (hR : closedBall c R ⊆ e.target) :
    ∃ A B U : Set Z, ∃ r : ℝ, ∃ δ : ℝ,
      IsCompact A ∧ IsClosed B ∧ IsOpen U ∧ B ⊆ U ∧ U ⊆ interior A ∧
      r < R ∧ 0 < δ ∧
      B = f ⁻¹' (e.symm '' closedBall c rB) ∧
      U = f ⁻¹' (e.source ∩ e ⁻¹' ball c rU) ∧
      ∀ g : C(Z, M), (∀ x, dist (g x) (f x) < δ) →
        (∀ x ∈ A, g x ∈ e.source) ∧
        (∀ x ∈ A, e (g x) ∈ closedBall c r) ∧
        (∀ x ∈ U, g x ∈ e.source ∧ e (g x) ∈ closedBall c rCut) ∧
        g ⁻¹' (e.symm '' closedBall c r₀) ⊆ B := by
  let r := (rA + R) / 2
  have hAr : rA < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  obtain ⟨A, B, U, hA, hB, hU, hBU', hUA, hsource, hrange, hBeq, hUeq, -⟩ :=
    exists_restoration_buffers_of_chart_balls f e c hBU (hUC.trans hCA) hAR hR
  let VA := e.source ∩ e ⁻¹' ball c r
  have hVA : IsOpen VA := e.isOpen_inter_preimage isOpen_ball
  have hfVA : f '' A ⊆ VA := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hsource x hx, closedBall_subset_ball hAr (hrange x hx)⟩
  obtain ⟨δA, hδA, hcontrolA⟩ := exists_perturbation_control f hA hVA isClosed_empty
    hfVA (disjoint_empty _)
  have hUT : closedBall c rU ⊆ e.target :=
    (closedBall_subset_closedBall ((hUC.trans hCA).trans hAR).le).trans hR
  let AU := f ⁻¹' (e.symm '' closedBall c rU)
  have hAUcompact : IsCompact AU := (((isCompact_closedBall c rU).image_of_continuousOn
    (e.continuousOn_symm.mono hUT)).isClosed.preimage f.continuous).isCompact
  let VU := e.source ∩ e ⁻¹' ball c rCut
  have hVU : IsOpen VU := e.isOpen_inter_preimage isOpen_ball
  have hfVU : f '' AU ⊆ VU := by
    rintro _ ⟨x, ⟨y, hy, hxy⟩, rfl⟩
    rw [← hxy]
    exact ⟨e.map_target (hUT hy), by
      change e (e.symm y) ∈ ball c rCut
      rw [e.right_inv (hUT hy)]
      exact closedBall_subset_ball hUC hy⟩
  obtain ⟨δU, hδU, hcontrolU⟩ := exists_perturbation_control f hAUcompact hVU isClosed_empty
    hfVU (disjoint_empty _)
  have hU_AU : U ⊆ AU := by
    intro x hx
    rw [hUeq] at hx
    exact ⟨e (f x), ball_subset_closedBall hx.2, e.left_inv hx.1⟩
  let S := e.symm '' closedBall c r₀
  have h₀T : closedBall c r₀ ⊆ e.target :=
    (closedBall_subset_closedBall ((h₀B.trans hBU).trans ((hUC.trans hCA).trans hAR)).le).trans hR
  have hS : IsClosed S := ((isCompact_closedBall c r₀).image_of_continuousOn
    (e.continuousOn_symm.mono h₀T)).isClosed
  have hpre : f ⁻¹' S ⊆ interior B := by
    let V := f ⁻¹' (e.source ∩ e ⁻¹' ball c rB)
    have hV : IsOpen V := (e.isOpen_inter_preimage isOpen_ball).preimage f.continuous
    have hVB : V ⊆ B := by
      intro x hx
      rw [hBeq]
      exact ⟨e (f x), ball_subset_closedBall hx.2, e.left_inv hx.1⟩
    have hpreV : f ⁻¹' S ⊆ V := by
      rintro x ⟨y, hy, hxy⟩
      change f x ∈ e.source ∩ e ⁻¹' ball c rB
      rw [← hxy]
      exact ⟨e.map_target (h₀T hy), by
        change e (e.symm y) ∈ ball c rB
        rw [e.right_inv (h₀T hy)]
        exact closedBall_subset_ball h₀B hy⟩
    exact hpreV.trans (hV.subset_interior_iff.mpr hVB)
  have havoid : Disjoint (f '' (interior B)ᶜ) S := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    exact hx (hpre hy)
  obtain ⟨δB, hδB, hcontrolB⟩ := exists_perturbation_control f
    (isOpen_interior.isClosed_compl.isCompact) isOpen_univ hS (subset_univ _) havoid
  let δ := min δA (min δU δB)
  refine ⟨A, B, U, r, δ, hA, hB, hU, hBU', hUA, hrR,
    lt_min hδA (lt_min hδU hδB), hBeq, hUeq, ?_⟩
  intro g hg
  have hgA : g '' A ⊆ VA := (hcontrolA g
    (fun x _ => (hg x).trans_le (min_le_left _ _))).1
  have hgU : g '' AU ⊆ VU := (hcontrolU g
    (fun x _ => (hg x).trans_le ((min_le_right _ _).trans (min_le_left _ _)))).1
  have hgB : Disjoint (g '' (interior B)ᶜ) S := (hcontrolB g
    (fun x _ => (hg x).trans_le ((min_le_right _ _).trans (min_le_right _ _)))).2
  refine ⟨fun x hx => (hgA (mem_image_of_mem g hx)).1,
    fun x hx => ball_subset_closedBall (hgA (mem_image_of_mem g hx)).2,
    fun x hx => ⟨(hgU (mem_image_of_mem g (hU_AU hx))).1,
      ball_subset_closedBall (hgU (mem_image_of_mem g (hU_AU hx))).2⟩, ?_⟩
  intro x hx
  by_contra hn
  exact disjoint_left.mp hgB (mem_image_of_mem g (fun hi => hn (interior_subset hi))) hx

end DifferentialGeometry.Topology.Engulfing
