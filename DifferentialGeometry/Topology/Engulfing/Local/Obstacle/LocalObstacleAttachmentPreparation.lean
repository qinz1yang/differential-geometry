import DifferentialGeometry.Topology.Engulfing.Local.Obstacle.LocalObstaclePullbackSetup
import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanMembraneIteration

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

variable {E M : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] {n p q : ℕ}

structure LocalObstacleAttachmentPreparation
    (K L : SimplicialComplex ℝ E) (g : C(K.space, M)) {X : Set M}
    (b : AdaptedPiecewiseLinearChart K L g X n p) (C : Set E) (V : Finset E) (U : Set M)
    (p q : ℕ) (ε : ℝ) where
  chartSetup : LocalObstacleChartSetup K L g b (convexHull ℝ (V : Set E)) (p + 1) ε
  model : ObstaclePullbackModel chartSetup.approximation
  covered : SimplicialComplex ℝ E
  covered_faces : covered.faces ⊆ model.source.faces
  covered_space : covered.space = C
  covered_dimension : ∀ s ∈ covered.faces, s.card ≤ p + 1
  active : SimplicialComplex ℝ E
  active_faces : active.faces ⊆ model.source.faces
  active_space : active.space = convexHull ℝ (V : Set E)
  active_dimension : ∀ s ∈ model.source.faces,
    convexHull ℝ (s : Set E) ⊆ active.space → s.card ≤ q + 2
  expansion : FiniteSimplexExpansionIn model.source covered.space (covered.space ∪ active.space)
  covered_image : X ∪ chartSetup.pullbackMap model '' (Subtype.val ⁻¹' covered.space) ⊆ U

theorem exists_local_obstacle_attachment_preparation
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ p + 2) (hpn : p + 1 ≤ n)
    (g : C(K.space, M)) {X U : Set M} (hU : IsOpen U)
    (b : AdaptedPiecewiseLinearChart K L g X n p)
    (C : Set E) (hC : IsCompact C) (hCpoly : isSubcomplexSpace K C)
    (hCp : C ⊆ (skeleton K p).space)
    (V B : Finset E) (hV : V ∈ K.faces) (hVq : V.card ≤ q + 2)
    (ha : SimplexAttachment C V B)
    (hVcore : ∀ x : K.space, x.val ∈ convexHull ℝ (V : Set E) → g x ∈ b.toBufferedChart.core)
    (hcover : X ∪ g '' (Subtype.val ⁻¹' C) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (LocalObstacleAttachmentPreparation K L g b C V U p q ε) := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  have hC' : IsCompact (Subtype.val ⁻¹' C : Set K.space) :=
    (hC.isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨δ, hδ, hcontrol⟩ := exists_perturbation_control g hC' hU isClosed_empty
    (subset_union_right.trans hcover) (disjoint_empty _)
  obtain ⟨S₀⟩ := exists_local_obstacle_chart_setup K L hK hLK hd (Nat.le_succ p) g b
    (convexHull ℝ (V : Set E)) (V.finite_toSet.isCompact_convexHull ℝ)
    (K.convexHull_subset_space hV) hVcore (lt_min hε hδ)
  let S : LocalObstacleChartSetup K L g b (convexHull ℝ (V : Set E)) (p + 1) ε :=
    { S₀ with map_near := fun x => (S₀.map_near x).trans_le (min_le_left ε δ) }
  obtain ⟨m⟩ := S.approximation.exists_pullbackModel hpn
  have hspace : m.source.space = K.space := m.space.trans S.space
  have href : simplicialRefines m.source K := m.refines.trans S.refines
  obtain ⟨H, hHK, hHC, hHd⟩ := (hCpoly.refine href hspace).exists_of_subset_skeleton
    (hCp.trans (href.old_skeleton_subset hspace p))
  obtain ⟨Y, hYK, hYV⟩ := (isSubcomplexSpace.face hV).refine href hspace
  have hYd : ∀ s ∈ m.source.faces,
      convexHull ℝ (s : Set E) ⊆ Y.space → s.card ≤ q + 2 := by
    intro s hs hsub
    have hcard := (m.source.indep hs).card_le_card_of_subset_affineSpan
      (fun x hx => convexHull_subset_affineSpan (V : Set E)
        (hYV.subset (hsub (subset_convexHull ℝ _ hx))))
    exact hcard.trans hVq
  have hexp : FiniteSimplexExpansionIn K C (C ∪ convexHull ℝ (V : Set E)) :=
    FiniteSimplexExpansionIn.snoc (.refl C) hV ha
  have hexp' := m.expansions C (C ∪ convexHull ℝ (V : Set E))
    (fun x hx => S.space.symm ▸
      (union_subset hCpoly.subset (K.convexHull_subset_space hV) hx))
    (S.expansions C _ hexp)
  let κ : m.source.space ≃ₜ K.space := Homeomorph.setCongr hspace
  let F := S.pullbackMap m
  let Fback : C(K.space, M) := F.comp ⟨κ.symm, κ.symm.continuous⟩
  have hn (x : K.space) : dist (Fback x) (g x) < δ := by
    have h := (S₀.map_near
      ⟨(κ.symm x).val, m.space ▸ (κ.symm x).property⟩).trans_le (min_le_right ε δ)
    exact h
  have hcover' : X ∪ F '' (Subtype.val ⁻¹' H.space) ⊆ U := by
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact hcover (Or.inl hy)
    · have hc := (hcontrol Fback (fun x _ => hn x)).1
        ⟨κ x, hHC.subset hx, rfl⟩
      change F (κ.symm (κ x)) ∈ U at hc
      rwa [κ.symm_apply_apply] at hc
  refine ⟨⟨S, m, H, hHK, hHC, hHd, Y, hYK, hYV, hYd, ?_, hcover'⟩⟩
  simpa only [hHC, hYV] using hexp'

end

end DifferentialGeometry.Topology.Engulfing
