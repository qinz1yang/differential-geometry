import DifferentialGeometry.Topology.Engulfing.Newman.Inner.NewmanInnerModel

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] {n p q : ℕ}
    {K L H : SimplicialComplex ℝ E} {F : C(K.space, M)} {X : Set M}
    {raw : E → EuclideanSpace ℝ (Fin n)} {Y : Set E}

theorem NewmanInnerModel.exists_cell_step (d : NewmanInnerModel K L H F X raw Y p)
    (hlower : relativeNewmanAt M n p q) (hqp : q ≤ p)
    (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ p + 2)
    (hX : IsClosed X) (hp : p + 3 ≤ n)
    (hdata : hasAdaptedPiecewiseLinearCharts K L F X n p)
    (hfixed : InjOn F (Subtype.val ⁻¹' L.space))
    (Q : SimplicialComplex ℝ E) (hQK : Q.faces ⊆ K.faces)
    (hQd : ∀ s ∈ Q.faces, s.card ≤ p + 1)
    (hHQ : H.space ⊆ Q.space) (hQHY : Q.space ⊆ H.space ∪ Y)
    (σ B : Finset E) (hσK : σ ∈ K.faces) (hσd : σ.card ≤ q + 2)
    (hattach : SimplexAttachment Q.space σ B) (hσY : convexHull ℝ (σ : Set E) ⊆ Y)
    (g : C(K.space, M)) (hg : d.good g)
    {V : Set M} (hV : IsOpen V) (hconn : NewmanConnectivity M V p)
    (hcover : X ∪ g '' (Subtype.val ⁻¹' Q.space) ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g' : C(K.space, M)) (G : M ≃ₜ M), d.good g' ∧
      EqOn g' g (Subtype.val ⁻¹' L.space) ∧
      (∀ x, dist (g' x) (g x) < ε) ∧
      X ∪ g' '' (Subtype.val ⁻¹' (Q.space ∪ convexHull ℝ (σ : Set E))) ⊆ G '' V ∧
      IsCompact (closure {x | G x ≠ x}) := by
  classical
  obtain ⟨δ, hδ, hmargin⟩ := d.exists_near_margin hK hg.2
  obtain ⟨Aσ, hAσ⟩ := d.affine σ hσK
  let m := hattach.affineModel raw Aσ hAσ (d.injective σ hσK)
  let : Nonempty σ := m.nonempty_index
  let v : σ → EuclideanSpace ℝ (Fin n) := fun i => raw i.val
  have hshape : convexHull ℝ (range v) = raw '' convexHull ℝ (σ : Set E) := m.simplex_eq
  have hσrawY : convexHull ℝ (range v) ⊆ raw '' Y := hshape.subset.trans (image_mono hσY)
  have hσtarget : convexHull ℝ (range v) ⊆ d.chart.chart.target :=
    hσrawY.trans (fun _ h => (d.block_image h).1.1)
  have hgL : EqOn g F (Subtype.val ⁻¹' L.space) := hg.1.mono (preimage_mono subset_union_left)
  have hgC : EqOn g F (Subtype.val ⁻¹' d.localComplex.space) :=
    hg.1.mono (preimage_mono subset_union_right)
  have hcoords (x : K.space) (hx : x.val ∈ d.localComplex.space) :
      g x ∈ d.chart.chart.source ∧ d.chart.chart (g x) = raw x.val := by
    rw [hgC hx]
    exact d.coordinates x hx
  have hQlocal : (Subtype.val ⁻¹' Q.space : Set K.space) ∩ d.blendSource ⊆
      Subtype.val ⁻¹' d.localComplex.space := by
    rintro x ⟨hxQ, hxU⟩
    rcases hQHY hxQ with hxH | hxY
    · exact d.covered_blend ⟨hxH, hxU⟩
    · exact d.block_local hxY
  obtain ⟨hsource, hrange, hUcoords, hbufferY⟩ := d.control g hg.2
  have hHcoords (x : K.space) (hx : x.val ∈ Q.space)
      (hxσ : g x ∈ d.chart.chart.symm '' convexHull ℝ (range v)) :
      d.chart.chart (g x) = raw x.val := by
    have hxB := hbufferY (image_mono hσrawY hxσ)
    exact (hcoords x (hQlocal ⟨hx, d.fixed_blend hxB⟩)).2
  have hroofRaw : raw '' (Q.space ∩ convexHull ℝ (σ : Set E)) ⊆ m.split.lowerRoof v := by
    rw [hattach.intersection]
    exact m.lowerRoof_eq.symm.subset
  obtain ⟨T, hT, hTd, hTσ, hTcolumns, hbound⟩ :=
    d.gp.exists_exceptional_columns hK hp hqp Q hQK hQd d.jointObstacle
      d.jointObstacle_faces d.jointObstacle_dimension g d.chart.chart X
      ⟨σ, hσK⟩ hσd m.split v m.independent hshape hσtarget hHcoords hroofRaw
      (fun x hx => d.jointObstacle_contains ⟨hx.1, hσrawY hx.2⟩)
      (d.shared_avoids ⟨σ, hσK⟩ hσY)
  have hfixedg : InjOn g (Subtype.val ⁻¹' L.space) := by
    intro x hx y hy hxy
    apply hfixed hx hy
    rwa [← hgL hx, ← hgL hy]
  have hLaff : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → g x ∈ d.chart.core →
        d.chart.chart (g x) = A x.val := by
    intro s hs
    obtain ⟨A, hA⟩ := d.fixed_affine s hs
    refine ⟨A, fun x hx hxcore => ?_⟩
    have heq := hgL (L.convexHull_subset_space hs hx)
    rw [heq] at hxcore ⊢
    exact hA x hx hxcore
  have hLcovers (x : K.space) (hxL : x.val ∈ L.space)
      (hxsource : g x ∈ d.chart.chart.source) (hxcut : d.chart.chart (g x) ∈ d.cut.space) :
      x.val ∈ d.localComplex.space := by
    rw [hgL hxL] at hxsource hxcut
    exact d.fixed_covers x hxL hxsource hxcut
  have hroof : d.chart.chart.symm '' m.split.lowerRoof v ⊆
      g '' (Subtype.val ⁻¹' Q.space) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [m.lowerRoof_eq] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxσ := simplexRoof_subset σ B hx
    have hxK := K.convexHull_subset_space hσK hxσ
    have hc := hcoords ⟨x, hxK⟩ (d.block_local (hσY hxσ))
    exact ⟨⟨x, hxK⟩, hattach.roof_subset hx,
      (d.chart.chart.left_inv hc.1).symm.trans (congrArg d.chart.chart.symm hc.2)⟩
  have hFS : g '' (Subtype.val ⁻¹' convexHull ℝ (σ : Set E)) ⊆
      d.chart.chart.symm '' convexHull ℝ (range v) := by
    rintro _ ⟨x, hx, rfl⟩
    have hc := hcoords x (d.block_local (hσY hx))
    refine ⟨raw x.val, hshape.symm ▸ mem_image_of_mem raw hx, ?_⟩
    exact (congrArg d.chart.chart.symm hc.2).symm.trans (d.chart.chart.left_inv hc.1)
  obtain ⟨g', G, hfixL, hfixB, hnear, hcover', hcompact, hfixD⟩ :=
    exists_simplex_step_of_protected_model hlower K L d.localComplex Q hK hLK
      d.local_subcomplex hQK raw (fun s hs => d.affine s (d.local_subcomplex hs))
      (fun s hs => d.injective s (d.local_subcomplex hs)) g hfixedg hd hQd hX hV
      (subset_union_left.trans hcover) (subset_union_right.trans hcover) hp hconn
      (hdata.withMap g (fun x hx => hgL hx)) d.chart hcoords hLaff
      d.cut T d.obstacle d.cut_finite hT d.obstacle_finite
      (hTσ.trans (hσrawY.trans (fun _ h => (d.block_image h).1.2))) d.cut_core
      hLcovers hTd (hqp.trans (Nat.le_succ p)) d.obstacle_dimension d.obstacle_contains
      d.outer_compact d.fixed_closed d.blend_open d.fixed_blend d.blend_outer hQlocal
      hUcoords d.center d.radii_lt d.outer_target hsource hrange m.split v m.independent
      hσtarget hTσ (hσrawY.trans (image_mono d.block_local)) hTcolumns hFS
      (fun _ h => hbufferY (image_mono hσrawY h)) d.support_open d.support_bounded
      d.support_target (sdiff_subset.trans (hσrawY.trans (fun _ h => (d.block_image h).2)))
      hbound hroof (lt_min hε hδ)
  have hfixC : EqOn g' g (Subtype.val ⁻¹' d.localComplex.space) := by
    have hDpre := localProtectedSet_preimage (Subtype.val : K.space → E) raw
      (C := d.localComplex.space) (H := Q.space) (B := d.cut.space) (T := T.space)
      (fun x hx => ⟨⟨x, subcomplex_space_subset K d.localComplex d.local_subcomplex hx⟩, rfl⟩)
    have hD' : EqOn g' g (localProtectedSet (raw ∘ Subtype.val)
        (Subtype.val ⁻¹' d.localComplex.space) (Subtype.val ⁻¹' Q.space) d.cut.space T.space) := by
      rw [hDpre]
      exact hfixD
    apply eqOn_local_model_of_saturated_fixed hfixL hfixB hD'
    · intro x hx
      rcases d.local_covered hx with (hxL | hxH) | hxY
      · exact Or.inl (Or.inl hxL)
      · exact Or.inl (Or.inr (hHQ hxH))
      · exact Or.inr (d.block_fixed hxY)
    · rintro _ ⟨x, ⟨⟨hxC, hxL⟩, hxQ⟩, rfl⟩
      exact d.local_raw_cut ⟨x.val, ⟨⟨hxC, hxL⟩, hQHY hxQ⟩, rfl⟩
  have hgood : d.good g' := by
    refine ⟨?_, hmargin g' (fun x => (hnear x).trans_le (min_le_right _ _))⟩
    intro x hx
    rcases hx with hxL | hxC
    · exact (hfixL hxL).trans (hgL hxL)
    · exact (hfixC hxC).trans (hgC hxC)
  exact ⟨g', G, hgood, hfixL, fun x => (hnear x).trans_le (min_le_left _ _),
    hcover', hcompact⟩

end DifferentialGeometry.Topology.Engulfing
