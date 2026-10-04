import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapShell
import DifferentialGeometry.Topology.Manifold.ClosedCellInterior
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

/-!
The true ball-plus-shell extension in the same bounded zero-sphere capping.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric TopologicalSpace GC.GraphManifold.MixedBoundaryCertificate
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open scoped Manifold ContDiff Topology

universe u

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

namespace GC.GraphManifold

local instance boundedPlugSideBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

local instance boundedPlugSideBallSmooth :
    IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

local instance boundedPlugSideBallLiftedCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ULift.{u} sphereCapBallOpen) :=
  uliftChartedSpace (EuclideanHalfSpace 3) sphereCapBallOpen

private abbrev boundedPlugOpenBall : Opens (EuclideanSpace ℝ (Fin 3)) :=
  ⟨Metric.ball 0 1, isOpen_ball⟩

private abbrev boundedPlugCellInterior : Opens (ClosedCell 3) :=
  intrinsicInterior (𝓡∂ 3) ∞ (by simp)

private def boundedPlugCellInteriorCongr :
    boundedPlugCellInterior ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ sphereCapBallOpen := by
  have he : (boundedPlugCellInterior : Set (ClosedCell 3)) = sphereCapBallOpen :=
    closedCell_interior_eq_ball 2
  refine
    { toEquiv := (Homeomorph.setCongr he).toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff sphereCapBallOpen _).mp
    exact contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff boundedPlugCellInterior _).mp
    exact contMDiff_subtype_val

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

private def boundedPlugCapInteriorChart (i : Fin B.sphereCount) :
    PartialDiffeomorph (𝓡 3) B.sphereCapCarrier.model
      (EuclideanSpace ℝ (Fin 3)) B.sphereCapCarrier.Carrier ∞ := by
  let := B.sphereCapQuotientChartedSpace
  let U := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3)
    boundedPlugOpenBall ⟨⟨0, by simp⟩⟩
  let V : boundedPlugOpenBall ≃ₘ⟮𝓡 3, 𝓡∂ 3⟯ boundedPlugCellInterior :=
    (closedCellInteriorDiffeomorph 2).symm
  let D := V.trans boundedPlugCellInteriorCongr
  let L : PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) sphereCapBallOpen
      (ULift.{u} sphereCapBallOpen) ∞ :=
    (uliftDiffeomorph (I := 𝓡∂ 3) (M := sphereCapBallOpen)).toPartialDiffeomorph
  let P := B.sphereCapPatchDiffeomorph B.exists_sphereCapQuotientAtlas.choose_spec.2 (.inr (.inl i))
  exact U.symm.trans (D.toPartialDiffeomorph.trans (L.trans P))

private theorem boundedPlugCapBallPatch_source (i : Fin B.sphereCount) :
    letI := B.sphereCapQuotientChartedSpace
    (B.sphereCapPatchDiffeomorph B.exists_sphereCapQuotientAtlas.choose_spec.2
      (.inr (.inl i))).source = univ := by
  simp only [sphereCapPatchDiffeomorph, sphereCapPatch, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ]

private theorem boundedPlugCapInteriorChart_mem (i : Fin B.sphereCount)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ < 1) :
    x ∈ (boundedPlugCapInteriorChart B i).source := by
  change x ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3)
    boundedPlugOpenBall ⟨⟨0, by simp⟩⟩).target ∧ _ ∈ _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  refine ⟨mem_ball_zero_iff.mpr hx, ?_⟩
  change _ ∈ univ ∧ (_ ∈ univ ∧ _ ∈ _)
  refine ⟨mem_univ _, mem_univ _, ?_⟩
  exact (boundedPlugCapBallPatch_source B i).symm.subset (mem_univ _)

private theorem boundedPlugCapInteriorChart_apply (i : Fin B.sphereCount)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ < 1) :
    boundedPlugCapInteriorChart B i x = B.sphereCapBall i ⟨x, hx.le⟩ := by
  let U := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3)
    boundedPlugOpenBall ⟨⟨0, by simp⟩⟩
  change B.sphereCapBall i (((closedCellInteriorDiffeomorph 2).symm (U.symm x)).val) = _
  apply congrArg (B.sphereCapBall i)
  apply Subtype.ext
  change (U.symm x).val = x
  apply U.right_inv
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  exact mem_ball_zero_iff.mpr hx

def boundedPlugSidePolar :
    PartialDiffeomorph (𝓡 3) sphereSignedCollarModel
      (EuclideanSpace ℝ (Fin 3)) (ClosureSphere.{u} × ℝ) ∞ :=
  (spherePolarChart (n := 2) SplitTube.poleS2).symm.trans
    ((uliftDiffeomorph (I := 𝓡 2) (M := SphereTwo)).prodCongr
      (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).toPartialDiffeomorph

theorem boundedPlugSidePolar_apply (x : EuclideanSpace ℝ (Fin 3)) :
    boundedPlugSidePolar x = (ULift.up (sphereDirection SplitTube.poleS2 x), ‖x‖) := rfl

theorem boundedPlugSidePolar_source :
    boundedPlugSidePolar.source = ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) := by
  change {0}ᶜ ∩ _ ⁻¹' univ = _
  simp only [preimage_univ, inter_univ]

def boundedPlugSideCapMap (i : Fin B.sphereCount) (x : EuclideanSpace ℝ (Fin 3)) :
    B.sphereCapCarrier.Carrier :=
  if hx : ‖x‖ ≤ 1 then B.boundedPlugWholeCap i ⟨x, hx⟩
  else B.boundedPlugWholeCap i ⟨0, by simp⟩

theorem boundedPlugSideCapMap_apply (i : Fin B.sphereCount)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 1) :
    boundedPlugSideCapMap B i x = B.boundedPlugWholeCap i ⟨x, hx⟩ := dite_eq_left hx

theorem boundedPlugSideCapMap_local (i : Fin B.sphereCount)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ < 1) :
    IsLocalDiffeomorphAt (𝓡 3) B.sphereCapCarrier.model ∞
      (boundedPlugSideCapMap B i) x := by
  have hn : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ < 1 →
      ‖boundedPlugCapRadialDiffeomorph y‖ < 1 := by
    intro y hy
    rw [boundedPlugCapRadialDiffeomorph_norm]
    simpa only [boundedPlugCapRadius_one] using boundedPlugCapRadius_strictMono hy
  have hr := boundedPlugCapRadialDiffeomorph.toPartialDiffeomorph.isLocalDiffeomorphAt
    (𝓡 3) (𝓡 3) ∞ (mem_univ x)
  have hc := (boundedPlugCapInteriorChart B i).isLocalDiffeomorphAt
    (𝓡 3) B.sphereCapCarrier.model ∞ (boundedPlugCapInteriorChart_mem B i _ (hn x hx))
  have hg := hr.comp B.sphereCapCarrier.model B.sphereCapCarrier.Carrier hc
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := hg)
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
  change boundedPlugSideCapMap B i y =
    boundedPlugCapInteriorChart B i (boundedPlugCapRadialDiffeomorph y)
  rw [boundedPlugSideCapMap_apply B i y hy.le,
    boundedPlugCapInteriorChart_apply B i _ (hn y hy), B.boundedPlugWholeCap_eq]
  apply congrArg (B.sphereCapBall i)
  apply Subtype.ext
  exact boundedPlugCapBallDiffeomorph_apply ⟨y, hy.le⟩

variable {W : CompactCarrier.{u}}
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior) {n : ℕ} (A : BoundaryTori W n)
  (hA : W.model.boundary W.Carrier = A.image)
  (hav : ∀ i, Disjoint (A.collar i).target d.target)
  (E : ElementaryPresentation W) {j : Fin E.toTorus.pairing.count} {b : Bool}
  (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))

def boundedPlugSideBallMap (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3)) :
    (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.Carrier :=
  if hx : ‖x‖ ≤ 1 then
    (boundedPlugCutBoundary d hs hI A hA hav).boundedPlugWholeCap i ⟨x, hx⟩
  else boundedPlugCapShell d hs hI A hA hav E h hlin i (boundedPlugSidePolar x)

theorem boundedPlugSideBallMap_cap (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3))
    (hx : ‖x‖ ≤ 1) :
    boundedPlugSideBallMap d hs hI A hA hav E h hlin i x =
      (boundedPlugCutBoundary d hs hI A hA hav).boundedPlugWholeCap i ⟨x, hx⟩ :=
  dite_eq_left hx

theorem boundedPlugSideBallMap_shell (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3))
    (hx : 1 < ‖x‖) :
    boundedPlugSideBallMap d hs hI A hA hav E h hlin i x =
      boundedPlugCapShell d hs hI A hA hav E h hlin i
        (ULift.up (sphereDirection SplitTube.poleS2 x), ‖x‖) :=
  dite_eq_right (not_le.mpr hx)

include heq in
theorem exists_boundedPlugSideBallMap_normal_germ :
    ∃ ε > (0 : ℝ), ε < 1 / 4 ∧
      ∀ (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3)), |‖x‖ - 1| < ε →
        boundedPlugSideBallMap d hs hI A hA hav E h hlin i x =
          (boundedPlugCutBoundary d hs hI A hA hav).boundedPlugCapNormal i
            (boundedPlugSidePolar x) := by
  let B := boundedPlugCutBoundary d hs hI A hA hav
  obtain ⟨ε, hε, hε1, hg⟩ := B.exists_boundedPlugWholeCap_normal_germ
  refine ⟨ε, hε, hε1, ?_⟩
  intro i x hx
  have hpos : 0 < ‖x‖ := by
    have hh := (abs_lt.mp hx).1
    linarith
  have hx0 : x ≠ 0 := norm_pos_iff.mp hpos
  by_cases hc : ‖x‖ ≤ 1
  · rw [boundedPlugSideBallMap_cap d hs hI A hA hav E h hlin i x hc]
    rw [boundedPlugSidePolar_apply]
    have hr : boundedPlugCapRadialPoint (ULift.up (sphereDirection SplitTube.poleS2 x))
        ‖x‖ (norm_nonneg x) hc = (⟨x, hc⟩ : ClosedCell 3) := by
      apply Subtype.ext
      exact norm_smul_sphereDirection SplitTube.poleS2 hx0
    exact hr ▸ hg i (ULift.up (sphereDirection SplitTube.poleS2 x))
      ‖x‖ (norm_nonneg x) hc hx
  · have h1 : 1 < ‖x‖ := lt_of_not_ge hc
    rw [boundedPlugSideBallMap_shell d hs hI A hA hav E h hlin i x h1,
      boundedPlugSidePolar_apply]
    apply boundedPlugCapShell_eq_normal d hs hI A hA hav E h hlin heq i _ h1
    have hh := (abs_lt.mp hx).2
    linarith

include heq in
theorem boundedPlugSideBallMap_local (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3))
    (hx : ‖x‖ < 5 / 2) :
    IsLocalDiffeomorphAt (𝓡 3)
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.model ∞
      (boundedPlugSideBallMap d hs hI A hA hav E h hlin i) x := by
  let B := boundedPlugCutBoundary d hs hI A hA hav
  by_cases hc : ‖x‖ < 1
  · have hg := boundedPlugSideCapMap_local B i x hc
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := hg)
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hc] with y hy
    rw [boundedPlugSideBallMap_cap d hs hI A hA hav E h hlin i y hy.le,
      boundedPlugSideCapMap_apply B i y hy.le]
  · have hge : 1 ≤ ‖x‖ := le_of_not_gt hc
    have hp : x ∈ boundedPlugSidePolar.source := by
      rw [boundedPlugSidePolar_source]
      exact norm_pos_iff.mp (by linarith)
    have hl := boundedPlugSidePolar.isLocalDiffeomorphAt (𝓡 3) sphereSignedCollarModel ∞ hp
    by_cases he : ‖x‖ = 1
    · have hn : boundedPlugSidePolar x ∈ (B.boundedPlugCapNormal i).source := by
        apply (B.boundedPlugCapNormal_source i).symm.subset
        change _ ∈ univ ∧ boundedPlugCapProfile ‖x‖ ∈ Ioo (-1 : ℝ) 1
        refine ⟨mem_univ _, ?_⟩
        rw [he, boundedPlugCapProfile_inner (by norm_num)]
        norm_num
      have hg := hl.comp B.sphereCapCarrier.model B.sphereCapCarrier.Carrier
        ((B.boundedPlugCapNormal i).isLocalDiffeomorphAt
          sphereSignedCollarModel B.sphereCapCarrier.model ∞ hn)
      apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := hg)
      obtain ⟨ε, hε, hε1, hnormal⟩ :=
        exists_boundedPlugSideBallMap_normal_germ d hs hI A hA hav E h hlin heq
      have hnx : |‖x‖ - 1| < ε := by simpa [he] using hε
      filter_upwards [(isOpen_lt ((continuous_norm.sub continuous_const).abs)
        continuous_const).mem_nhds hnx] with y hy
      exact hnormal i y hy
    · have hgt : 1 < ‖x‖ := lt_of_le_of_ne hge (Ne.symm he)
      have hg := hl.comp B.sphereCapCarrier.model B.sphereCapCarrier.Carrier
        (boundedPlugCapShell_local d hs hI A hA hav E h hlin heq i
          (boundedPlugSidePolar x) hgt hx)
      apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := hg)
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hgt] with y hy
      exact boundedPlugSideBallMap_shell d hs hI A hA hav E h hlin i y hy

include heq in
theorem boundedPlugSideBallMap_injOn (i : Fin 2) :
    InjOn (boundedPlugSideBallMap d hs hI A hA hav E h hlin i)
      (Metric.ball 0 (5 / 2)) := by
  let B := boundedPlugCutBoundary d hs hI A hA hav
  have hn : ∀ (x y : EuclideanSpace ℝ (Fin 3)), 1 < ‖x‖ → ‖x‖ < 5 / 2 →
      ‖y‖ ≤ 1 → boundedPlugSideBallMap d hs hI A hA hav E h hlin i x ≠
        boundedPlugSideBallMap d hs hI A hA hav E h hlin i y := by
    intro x y hx hx1 hy he
    have hd := boundedPlugCapShell_disjoint_ball d hs hI A hA hav E h hlin heq i i
    apply Set.disjoint_left.mp hd
    · refine ⟨boundedPlugSidePolar x, ⟨mem_univ _, hx, hx1⟩, ?_⟩
      exact (boundedPlugSideBallMap_shell d hs hI A hA hav E h hlin i x hx).symm
    · rw [he, boundedPlugSideBallMap_cap d hs hI A hA hav E h hlin i y hy]
      exact (B.boundedPlugWholeCap_range i).subset ⟨⟨y, hy⟩, rfl⟩
  intro x hx y hy he
  have hx1 : ‖x‖ < 5 / 2 := mem_ball_zero_iff.mp hx
  have hy1 : ‖y‖ < 5 / 2 := mem_ball_zero_iff.mp hy
  by_cases hxc : ‖x‖ ≤ 1
  · by_cases hyc : ‖y‖ ≤ 1
    · rw [boundedPlugSideBallMap_cap d hs hI A hA hav E h hlin i x hxc,
        boundedPlugSideBallMap_cap d hs hI A hA hav E h hlin i y hyc] at he
      have hf := (B.boundedPlugWholeCap_eq i ⟨x, hxc⟩).symm.trans
        (he.trans (B.boundedPlugWholeCap_eq i ⟨y, hyc⟩))
      have hh := boundedPlugCapBallDiffeomorph.injective (B.sphereCapBall_injective i hf)
      exact congrArg Subtype.val hh
    · exact (hn y x (lt_of_not_ge hyc) hy1 hxc he.symm).elim
  · have hx0 : 1 < ‖x‖ := lt_of_not_ge hxc
    by_cases hyc : ‖y‖ ≤ 1
    · exact (hn x y hx0 hx1 hyc he).elim
    · have hy0 : 1 < ‖y‖ := lt_of_not_ge hyc
      rw [boundedPlugSideBallMap_shell d hs hI A hA hav E h hlin i x hx0,
        boundedPlugSideBallMap_shell d hs hI A hA hav E h hlin i y hy0] at he
      have hp := boundedPlugCapShell_injOn d hs hI A hA hav E h hlin heq i
        (show boundedPlugSidePolar x ∈ univ ×ˢ Ioo (1 : ℝ) (5 / 2) from
          ⟨mem_univ _, hx0, hx1⟩)
        (show boundedPlugSidePolar y ∈ univ ×ˢ Ioo (1 : ℝ) (5 / 2) from
          ⟨mem_univ _, hy0, hy1⟩) he
      apply boundedPlugSidePolar.injOn
      · rw [boundedPlugSidePolar_source]
        exact norm_pos_iff.mp (by linarith)
      · rw [boundedPlugSidePolar_source]
        exact norm_pos_iff.mp (by linarith)
      · exact hp

theorem boundedPlugSideBallMap_cap_image (i : Fin 2) :
    boundedPlugSideBallMap d hs hI A hA hav E h hlin i '' Metric.closedBall 0 1 =
      range ((boundedPlugCutBoundary d hs hI A hA hav).sphereCapBall i) := by
  let B := boundedPlugCutBoundary d hs hI A hA hav
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [boundedPlugSideBallMap_cap d hs hI A hA hav E h hlin i x
      (mem_closedBall_zero_iff.mp hx)]
    exact (B.boundedPlugWholeCap_range i).subset
      ⟨⟨x, mem_closedBall_zero_iff.mp hx⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx⟩ := B.boundedPlugWholeCap_range i |>.symm.subset hy
    refine ⟨x.val, mem_closedBall_zero_iff.mpr x.property, ?_⟩
    rw [boundedPlugSideBallMap_cap d hs hI A hA hav E h hlin i x.val x.property]
    exact hx

theorem boundedPlugSideBallMap_outer (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3))
    (hx : 3 / 2 ≤ ‖x‖) :
    boundedPlugSideBallMap d hs hI A hA hav E h hlin i x =
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
        (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
          (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
          (E.boundedSplitTubeMap h hlin
            (sphereDirection SplitTube.poleS2 x, boundedPlugCapShellSign i * ‖x‖))) := by
  rw [boundedPlugSideBallMap_shell d hs hI A hA hav E h hlin i x (by linarith)]
  unfold boundedPlugCapShell boundedPlugCapShellLift boundedPlugCapShellPoint
  rw [boundedPlugCapProfile_outer hx]

end GC.GraphManifold
