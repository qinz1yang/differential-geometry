import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanMembraneAvoidance

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable (M : Type*) [MetricSpace M] (n p q : ℕ)

def localSkeletalAttachmentAt : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E],
    ∀ (K L : SimplicialComplex ℝ E), K.faces.Finite → L.faces ⊆ K.faces →
      (∀ s ∈ K.faces, s.card ≤ p + 2) →
    ∀ (g : C(K.space, M)) (X U : Set M), IsClosed X → IsOpen U →
      p + 3 ≤ n → NewmanConnectivity M U p →
      InjOn g (Subtype.val ⁻¹' L.space) → hasAdaptedPiecewiseLinearCharts K L g X n p →
    ∀ (b : AdaptedPiecewiseLinearChart K L g X n p) (C : Set E) (V B : Finset E),
      IsCompact C → isSubcomplexSpace K C → C ⊆ (skeleton K p).space →
      V ∈ K.faces → V.card ≤ q + 2 → SimplexAttachment C V B →
      (∀ x : K.space, x.val ∈ convexHull ℝ (V : Set E) → g x ∈ b.toBufferedChart.core) →
      (∀ x : K.space, x.val ∈ convexHull ℝ (V : Set E) → x.val ∈ L.space → g x ∉ X) →
      X ∪ g '' (Subtype.val ⁻¹' C) ⊆ U →
    ∀ ε : ℝ, 0 < ε → ∃ (g' : C(K.space, M)) (G : M ≃ₜ M),
      (∀ x : K.space, x.val ∈ L.space → g' x = g x) ∧
      (∀ x, dist (g' x) (g x) < ε) ∧
      X ∪ g' '' (Subtype.val ⁻¹' (C ∪
        (convexHull ℝ (V : Set E) ∩ (skeleton K q).space))) ⊆ G '' U ∧
      IsCompact (closure {x | G x ≠ x})

variable {M n p q}

theorem singleSimplexNewmanAt_of_localAttachment
    (hlocal : localSkeletalAttachmentAt M n p q) : singleSimplexNewmanAt M n p q := by
  apply singleSimplexNewmanAt_of_assigned_chart_steps
  intro E _ _ _ _ _ P s D havoid R C V B hC hCpoly hBase _ hCp hV hVq ha hRegion g H hg hcover ε hε
  by_cases hVC : convexHull ℝ (V : Set (ConeSpace E)) ⊆ C
  · refine ⟨g, Homeomorph.refl M, fun _ _ => rfl,
      fun _ => by simpa only [dist_self] using hε, ?_, by simp⟩
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact ⟨y, hcover (Or.inl hy), rfl⟩
    · exact ⟨g x, hcover (Or.inr ⟨x, hx.elim id (fun h => hVC h.1), rfl⟩), rfl⟩
  · have hVbase : ¬ convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.covered :=
      fun h => hVC (h.trans hBase)
    have hinj : InjOn g (Subtype.val ⁻¹' R.fixed.space) := by
      intro x hx y hy he
      apply R.fixed_injective hx hy
      rwa [← hg.1 x hx, ← hg.1 y hy]
    let b := (R.charts ⟨V, hV⟩).withMap g hg.1
    exact hlocal (ConeSpace E) R.source R.fixed R.finite R.fixed_faces R.dimension
      g P.obstacle (H '' P.openSet) P.obstacle_closed (H.isOpenMap _ P.open_openSet)
      P.codimension (P.connectivity.image H) hinj (R.hasAdaptedPiecewiseLinearCharts_map.withMap g hg.1)
      b C V B hC hCpoly hCp hV hVq ha
      (fun x hx => hg.2 ⟨V, hV⟩ x hx)
      (R.active_face_fixed_avoids_obstacle havoid g hg.1 hV
        (subset_union_right.trans hRegion) hVbase)
      hcover ε hε

end DifferentialGeometry.Topology.Engulfing
