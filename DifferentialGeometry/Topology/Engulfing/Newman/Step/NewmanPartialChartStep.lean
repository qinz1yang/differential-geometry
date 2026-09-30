import DifferentialGeometry.Topology.Engulfing.Newman.Step.NewmanLocalStep
import DifferentialGeometry.Topology.Engulfing.Simplex.PartialChartEngulfing

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

section SimplexStep

variable {Z M E F : Type*} [MetricSpace Z] [MetricSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq F] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq F] in
theorem exists_simplex_step_of_lower_quotient_partial_chart
    (Q LQ DQ : SimplicialComplex ℝ E) (fQ : C(Q.space, M))
    (q : C(Z, Q.space)) (f : C(Z, M)) (hdesc : ∀ x, fQ (q x) = f x)
    {L D A B U S : Set Z} {X V : Set M} (hD : IsCompact D)
    (hX : IsClosed X) (hV : IsOpen V)
    (hLQ : ∀ x ∈ L ∪ (D ∩ U), (q x).1 ∈ LQ.space)
    (hDQ : ∀ x ∈ D, (q x).1 ∈ DQ.space)
    (e : OpenPartialHomeomorph M F)
    (hA : IsCompact A) (hB : IsClosed B) (hU : IsOpen U)
    (hBU : B ⊆ U) (hUA : U ⊆ interior A)
    (c : F) {r R ε : ℝ} (hrR : r < R) (hR : closedBall c R ⊆ e.target)
    (hfsource : ∀ x ∈ A, f x ∈ e.source)
    (hfrange : ∀ x ∈ A, e (f x) ∈ closedBall c r)
    (s : SimplexSplit ι) (v : ι → F) (hv : AffineIndependent ℝ v)
    (a : OpenPartialHomeomorph M F)
    (hSB : S ⊆ B) (hfS : f '' S ⊆ a.symm '' convexHull ℝ (range v))
    (havoid : Disjoint (f '' (D \ U)) (a.symm '' convexHull ℝ (range v)))
    {T W : Set F} (hT : IsCompact T) (hW : IsOpen W)
    (hWbounded : Bornology.IsBounded W)
    (hWa : closure W ⊆ a.target)
    (hσa : convexHull ℝ (range v) ⊆ a.target)
    (hmoving : convexHull ℝ (range v) \ s.lowerRoof v ⊆ W)
    (hattach : a.symm ⁻¹' (X ∪ f '' D) ∩ convexHull ℝ (range v) ⊆ s.lowerRoof v ∪ T)
    (hroof : a.symm '' s.lowerRoof v ⊆ X ∪ f '' (D ∩ U))
    (hcolumns : a.symm '' s.columnSaturation v hv T ⊆ X ∪ f '' (D ∩ U))
    (hlower : ∀ δ : ℝ, 0 < δ → newmanConclusion Q LQ DQ fQ X V δ)
    (hε : 0 < ε) :
    ∃ (G : C(Z, M)) (H : M ≃ₜ M), EqOn G f L ∧ EqOn G f S ∧
      (∀ x, dist (G x) (f x) < ε) ∧
      X ∪ G '' (D ∪ S) ⊆ H '' V ∧ IsCompact (closure {x | H x ≠ x}) ∧ EqOn G f B := by
  have hσ : IsClosed (a.symm '' convexHull ℝ (range v)) :=
    (((finite_range v).isCompact_convexHull ℝ).image_of_continuousOn
      (a.continuousOn_symm.mono hσa)).isClosed
  obtain ⟨G, H, hGL, hGB, hGnear, hcover, hinter, hGlocal, hH⟩ :=
    exists_restored_pullback_of_newmanConclusion Q LQ DQ fQ q f hdesc hD hLQ hDQ e
      hA hB hU hBU hUA c hrR hR hfsource hfrange hσ havoid hlower hε
  have hlocal : X ∪ f '' (D ∩ U) ⊆ X ∪ G '' D := by
    intro y hy
    rcases hy with hy | ⟨x, hx, rfl⟩
    · exact Or.inl hy
    · exact Or.inr ⟨x, hx.1, hGlocal hx⟩
  have hGattach : a.symm ⁻¹' (X ∪ G '' D) ∩ convexHull ℝ (range v) ⊆
      s.lowerRoof v ∪ T := by
    intro x hx
    apply hattach
    refine ⟨?_, hx.2⟩
    rcases hx.1 with hxX | hxG
    · exact Or.inl hxX
    · exact Or.inr ((Set.ext_iff.mp hinter (a.symm x)).mp
        ⟨hxG, mem_image_of_mem a.symm hx.2⟩).1
  obtain ⟨H', -, -, hfinish, hH'⟩ :=
    s.exists_simplex_engulfing_in_partial_chart_of_exceptional_columns v hv a hT
      (H.isOpenMap _ hV) hW (hX.union (hD.image G.continuous).isClosed) hcover
      hWbounded hWa hσa (hroof.trans (hlocal.trans hcover)) hmoving hGattach
      (hcolumns.trans (hlocal.trans hcover))
  refine ⟨G, H.trans H', hGL, hGB.mono hSB, hGnear, ?_,
    isCompact_closure_moved_trans H H' hH hH', hGB⟩
  intro y hy
  have hy' : y ∈ (X ∪ G '' D) ∪ a.symm '' convexHull ℝ (range v) := by
    rcases hy with hy | ⟨x, hx, rfl⟩
    · exact Or.inl (Or.inl hy)
    · rcases hx with hxD | hxS
      · exact Or.inl (Or.inr (mem_image_of_mem G hxD))
      · rw [hGB (hSB hxS)]
        exact Or.inr (hfS (mem_image_of_mem f hxS))
  obtain ⟨y', ⟨z, hz, rfl⟩, hy'⟩ := hfinish hy'
  exact ⟨z, hz, hy'⟩

end SimplexStep

end DifferentialGeometry.Topology.Engulfing
