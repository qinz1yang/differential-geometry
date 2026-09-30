import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanInduction
import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanLocalData
import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.ExceptionalEngulfing

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped _root_.Topology ContinuousMap

section Restoration

variable {Z M F : Type*} [MetricSpace Z] [MetricSpace M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_local_restoration_tolerance (f : C(Z, M))
    (e : OpenPartialHomeomorph M F) {A B U : Set Z}
    (hA : IsCompact A) (hB : IsClosed B) (hU : IsOpen U)
    (hBU : B ⊆ U) (hUA : U ⊆ interior A)
    (c : F) {r R ε : ℝ} (hrR : r < R) (hR : closedBall c R ⊆ e.target)
    (hfsource : ∀ x ∈ A, f x ∈ e.source)
    (hfrange : ∀ x ∈ A, e (f x) ∈ closedBall c r) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : C(Z, M), (∀ x, dist (g x) (f x) < δ) →
      ∃ G : C(Z, M),
        (∀ x ∈ B, G x = f x) ∧ (∀ x ∉ U, G x = g x) ∧
        (∀ x, g x = f x → G x = g x) ∧ (∀ x, dist (G x) (f x) < ε) := by
  let r' := (r + R) / 2
  have hrr' : r < r' := by dsimp [r']; linarith
  have hr'R : r' < R := by dsimp [r']; linarith
  let V : Set M := e.source ∩ e ⁻¹' ball c r'
  have hV : IsOpen V := e.isOpen_inter_preimage isOpen_ball
  have hfV : f '' A ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hfsource x hx, closedBall_subset_ball hrr' (hfrange x hx)⟩
  obtain ⟨δ₁, hδ₁, hcontrol⟩ := exists_perturbation_control f hA hV isClosed_empty hfV
    (disjoint_empty _)
  obtain ⟨η, hη, -, hblend⟩ := exists_chart_blend_tolerance (X := Z) e c hr'R hR
    (show 0 < ε / 2 by positivity)
  let C : Set M := e.symm '' closedBall c R
  have hC : IsCompact C := (isCompact_closedBall c R).image_of_continuousOn
    (e.continuousOn_symm.mono hR)
  have hCsource : C ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hR hy)
  have huc : UniformContinuousOn e C := hC.uniformContinuousOn_of_continuous
    (e.continuousOn.mono hCsource)
  obtain ⟨δ₂, hδ₂, hcoord⟩ := Metric.uniformContinuousOn_iff.mp huc η hη
  let δ := min δ₁ (min δ₂ (ε / 2))
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ (by positivity))
  refine ⟨δ, hδ, fun g hnear => ?_⟩
  have hgV : g '' A ⊆ V := (hcontrol g (fun x _ =>
    (hnear x).trans_le (min_le_left _ _))).1
  have hmemC (y : M) (hy : y ∈ V) : y ∈ C := by
    exact ⟨e y, ball_subset_closedBall ((ball_subset_ball hr'R.le) hy.2), e.left_inv hy.1⟩
  let fA : C(A, F) := ⟨fun x => e (f x), e.continuousOn.comp_continuous
    (f.continuous.comp continuous_subtype_val) (fun x => hfsource x x.2)⟩
  have hgsource (x : A) : g x ∈ e.source := (hgV (mem_image_of_mem g x.2)).1
  have hgrange (x : A) : e (g x) ∈ closedBall c r' :=
    ball_subset_closedBall (hgV (mem_image_of_mem g x.2)).2
  have hcoordnear (x : A) : ‖fA x - e (g x)‖ < η := by
    rw [← dist_eq_norm]
    apply hcoord _ (hmemC _ (hfV (mem_image_of_mem f x.2))) _
      (hmemC _ (hgV (mem_image_of_mem g x.2)))
    rw [dist_comm]
    exact (hnear x).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨G, hGcore, hGout, hGfix, hGnear, -⟩ :=
    hblend hA.isClosed hB hU hBU hUA g fA hgsource hgrange hcoordnear
  refine ⟨G, ?_, hGout, ?_, ?_⟩
  · intro x hx
    have hxA : x ∈ A := interior_subset (hUA (hBU hx))
    exact (hGcore ⟨x, hxA⟩ hx).trans (e.left_inv (hfsource x hxA))
  · intro x heq
    by_cases hxA : x ∈ A
    · apply hGfix ⟨x, hxA⟩
      exact congrArg e heq.symm
    · exact hGout x (fun hxU => hxA (interior_subset (hUA hxU)))
  · intro x
    calc
      dist (G x) (f x) ≤ dist (G x) (g x) + dist (g x) (f x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hGnear x)
        ((hnear x).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
      _ = ε := add_halves ε

omit [MetricSpace Z] [MetricSpace M] in
theorem restoration_fixes_protected {f g G : Z → M} {D U : Set Z}
    (hout : ∀ x ∉ U, G x = g x) (hagree : ∀ x, g x = f x → G x = g x)
    (hprotected : ∀ x ∈ D, x ∈ U → g x = f x) : EqOn G g D := by
  intro x hx
  by_cases hxU : x ∈ U
  · exact hagree x (hprotected x hx hxU)
  · exact hout x hxU

end Restoration

theorem image_inter_eq_of_eqOn_and_avoid {Z M : Type*} {f g : Z → M}
    {D U : Set Z} {S : Set M} (hfix : EqOn g f (D ∩ U))
    (hfavoid : Disjoint (f '' (D \ U)) S)
    (hgavoid : Disjoint (g '' (D \ U)) S) : (g '' D) ∩ S = (f '' D) ∩ S := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    have hxU : x ∈ U := by
      by_contra h
      exact Set.disjoint_left.mp hgavoid (mem_image_of_mem g ⟨hx, h⟩) hy
    exact ⟨⟨x, hx, hfix ⟨hx, hxU⟩ |>.symm⟩, hy⟩
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    have hxU : x ∈ U := by
      by_contra h
      exact Set.disjoint_left.mp hfavoid (mem_image_of_mem f ⟨hx, h⟩) hy
    exact ⟨⟨x, hx, hfix ⟨hx, hxU⟩⟩, hy⟩

section LowerPullback

variable {Z M E F : Type*} [MetricSpace Z] [MetricSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_restored_pullback_of_newmanConclusion
    (Q LQ DQ : SimplicialComplex ℝ E) (fQ : C(Q.space, M))
    (q : C(Z, Q.space)) (f : C(Z, M)) (hdesc : ∀ x, fQ (q x) = f x)
    {L D A B U : Set Z} {X V : Set M} (hD : IsCompact D)
    (hLQ : ∀ x ∈ L ∪ (D ∩ U), (q x).1 ∈ LQ.space)
    (hDQ : ∀ x ∈ D, (q x).1 ∈ DQ.space)
    (e : OpenPartialHomeomorph M F)
    (hA : IsCompact A) (hB : IsClosed B) (hU : IsOpen U)
    (hBU : B ⊆ U) (hUA : U ⊆ interior A)
    (c : F) {r R ε : ℝ} (hrR : r < R) (hR : closedBall c R ⊆ e.target)
    (hfsource : ∀ x ∈ A, f x ∈ e.source)
    (hfrange : ∀ x ∈ A, e (f x) ∈ closedBall c r)
    {S : Set M} (hS : IsClosed S) (havoid : Disjoint (f '' (D \ U)) S)
    (hlower : ∀ δ : ℝ, 0 < δ → newmanConclusion Q LQ DQ fQ X V δ)
    (hε : 0 < ε) :
    ∃ (G : C(Z, M)) (H : M ≃ₜ M),
      EqOn G f L ∧ EqOn G f B ∧ (∀ x, dist (G x) (f x) < ε) ∧
      X ∪ G '' D ⊆ H '' V ∧ (G '' D) ∩ S = (f '' D) ∩ S ∧
      EqOn G f (D ∩ U) ∧ IsCompact (closure {x | H x ≠ x}) := by
  obtain ⟨δ₁, hδ₁, hrestore⟩ := exists_local_restoration_tolerance f e hA hB hU
    hBU hUA c hrR hR hfsource hfrange hε
  obtain ⟨δ₂, hδ₂, hcontrol⟩ := exists_perturbation_control f
    (hD.diff hU) isOpen_univ hS (subset_univ _) havoid
  obtain ⟨gQ, H, hgQfix, hgQnear, hcover, hH⟩ := hlower (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
  let g : C(Z, M) := gQ.comp q
  have hgnear (x : Z) : dist (g x) (f x) < min δ₁ δ₂ := by
    change dist (gQ (q x)) (f x) < min δ₁ δ₂
    rw [← hdesc x]
    exact hgQnear (q x)
  have hgfix : EqOn g f (L ∪ (D ∩ U)) := by
    intro x hx
    exact (hgQfix (q x) (hLQ x hx)).trans (hdesc x)
  obtain ⟨G, hGB, hGout, hGagree, hGnear⟩ := hrestore g
    (fun x => (hgnear x).trans_le (min_le_left _ _))
  have hGD : EqOn G g D := restoration_fixes_protected hGout hGagree
    (fun x hx hxU => hgfix (Or.inr ⟨hx, hxU⟩))
  have hGlocal : EqOn G f (D ∩ U) := fun x hx =>
    (hGD hx.1).trans (hgfix (Or.inr hx))
  have hgavoid : Disjoint (g '' (D \ U)) S := (hcontrol g
    (fun x _ => (hgnear x).trans_le (min_le_right _ _))).2
  have hGavoid : Disjoint (G '' (D \ U)) S := by
    rwa [show G '' (D \ U) = g '' (D \ U) from
      Set.EqOn.image_eq (hGD.mono sdiff_subset)]
  refine ⟨G, H, ?_, hGB, hGnear, ?_,
    image_inter_eq_of_eqOn_and_avoid hGlocal havoid hGavoid, hGlocal, hH⟩
  · intro x hx
    exact (hGagree x (hgfix (Or.inl hx))).trans (hgfix (Or.inl hx))
  · intro y hy
    apply hcover
    rcases hy with hy | ⟨x, hx, rfl⟩
    · exact Or.inl hy
    · exact Or.inr ⟨q x, hDQ x hx, (hGD hx).symm⟩

end LowerPullback

section SimplexStep

variable {Z M E F : Type*} [MetricSpace Z] [MetricSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq F] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq F] in
theorem exists_simplex_step_of_lower_quotient
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
    {j : F → M} (hj : IsOpenEmbedding j)
    (hSB : S ⊆ B) (hfS : f '' S ⊆ j '' convexHull ℝ (range v))
    (havoid : Disjoint (f '' (D \ U)) (j '' convexHull ℝ (range v)))
    {T W : Set F} (hT : IsCompact T) (hW : IsOpen W)
    (hWbounded : Bornology.IsBounded W)
    (hmoving : convexHull ℝ (range v) \ s.lowerRoof v ⊆ W)
    (hattach : j ⁻¹' (X ∪ f '' D) ∩ convexHull ℝ (range v) ⊆ s.lowerRoof v ∪ T)
    (hroof : j '' s.lowerRoof v ⊆ X ∪ f '' (D ∩ U))
    (hcolumns : j '' s.columnSaturation v hv T ⊆ X ∪ f '' (D ∩ U))
    (hlower : ∀ δ : ℝ, 0 < δ → newmanConclusion Q LQ DQ fQ X V δ)
    (hε : 0 < ε) :
    ∃ (G : C(Z, M)) (H : M ≃ₜ M), EqOn G f L ∧ EqOn G f S ∧
      (∀ x, dist (G x) (f x) < ε) ∧
      X ∪ G '' (D ∪ S) ⊆ H '' V ∧ IsCompact (closure {x | H x ≠ x}) ∧ EqOn G f B := by
  classical
  have hσ : IsClosed (j '' convexHull ℝ (range v)) :=
    (((finite_range v).isCompact_convexHull ℝ).image hj.continuous).isClosed
  obtain ⟨G, H, hGL, hGB, hGnear, hcover, hinter, hGlocal, hH⟩ :=
    exists_restored_pullback_of_newmanConclusion Q LQ DQ fQ q f hdesc hD hLQ hDQ e
      hA hB hU hBU hUA c hrR hR hfsource hfrange hσ havoid hlower hε
  have hlocal : X ∪ f '' (D ∩ U) ⊆ X ∪ G '' D := by
    intro y hy
    rcases hy with hy | ⟨x, hx, rfl⟩
    · exact Or.inl hy
    · exact Or.inr ⟨x, hx.1, hGlocal hx⟩
  have hGattach : j ⁻¹' (X ∪ G '' D) ∩ convexHull ℝ (range v) ⊆
      s.lowerRoof v ∪ T := by
    intro x hx
    apply hattach
    refine ⟨?_, hx.2⟩
    rcases hx.1 with hxX | hxG
    · exact Or.inl hxX
    · exact Or.inr ((Set.ext_iff.mp hinter (j x)).mp
        ⟨hxG, mem_image_of_mem j hx.2⟩).1
  obtain ⟨H', -, -, hfinish, hH'⟩ :=
    s.exists_simplex_engulfing_in_chart_of_exceptional_columns v hv hj hT
      (H.isOpenMap _ hV) hW (hX.union (hD.image G.continuous).isClosed) hcover
      hWbounded (hroof.trans (hlocal.trans hcover)) hmoving hGattach
      (hcolumns.trans (hlocal.trans hcover))
  refine ⟨G, H.trans H', hGL, hGB.mono hSB, hGnear, ?_,
    isCompact_closure_moved_trans H H' hH hH', hGB⟩
  intro y hy
  have hy' : y ∈ (X ∪ G '' D) ∪ j '' convexHull ℝ (range v) := by
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
