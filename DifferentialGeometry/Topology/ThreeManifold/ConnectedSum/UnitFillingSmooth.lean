import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.UnitLaw
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Set Function

namespace DifferentialGeometry.Topology

theorem isLocalDiffeomorphAt_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
    {f g : M → N} {x : M} (h : f =ᶠ[𝓝 x] g)
    (hg : IsLocalDiffeomorphAt I J n g x) : IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨φ, hx, hφ⟩ := hg
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp h
  have hsm : ∀ y ∈ φ.toPartialEquiv.source ∩ W, f y = φ.toPartialEquiv.toFun y :=
    fun y hy => (hWsub hy.2).trans (hφ hy.1)
  refine ⟨{ toFun := f
            invFun := φ.toPartialEquiv.invFun
            source := φ.toPartialEquiv.source ∩ W
            target := φ.toPartialEquiv.toFun '' (φ.toPartialEquiv.source ∩ W)
            map_source' := fun y hy => ⟨y, hy, (hsm y hy).symm⟩
            map_target' := fun y hy => by
              obtain ⟨z, hz, rfl⟩ := hy
              rw [φ.toPartialEquiv.left_inv' hz.1]
              exact hz
            left_inv' := fun y hy => by
              rw [hsm y hy]
              exact φ.toPartialEquiv.left_inv' hy.1
            right_inv' := fun y hy => by
              obtain ⟨z, hz, rfl⟩ := hy
              rw [φ.toPartialEquiv.left_inv' hz.1]
              exact hsm z hz
            open_source := φ.open_source.inter hWopen
            open_target := φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
              (φ.open_source.inter hWopen) inter_subset_left
            contMDiffOn_toFun := (φ.contMDiffOn_toFun.mono inter_subset_left).congr
              (fun y hy => hsm y hy)
            contMDiffOn_invFun := φ.contMDiffOn_invFun.mono
              (by rintro z ⟨w, hw, rfl⟩; exact φ.map_source hw.1) },
    ⟨hx, hxW⟩, fun y hy => rfl⟩

theorem isLocalDiffeomorphAt_subtype_val
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (x : U) :
    IsLocalDiffeomorphAt I I ∞ (Subtype.val : U → M) x := by
  classical
  let F : M → U := fun y => if h : y ∈ U then (⟨y, h⟩ : U) else x
  let φ : PartialEquiv U M :=
    { toFun := Subtype.val
      invFun := F
      source := Set.univ
      target := (U : Set M)
      map_source' := fun y _ => y.2
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun y _ => by
        simp only [F]
        split_ifs with h
        · rfl
        · exact absurd y.2 h
      right_inv' := fun y hy => by
        simp only [F]
        split_ifs with h
        · rfl
        · exact absurd hy h }
  let Ψ : PartialDiffeomorph I I U M ∞ :=
    { toPartialEquiv := φ
      open_source := isOpen_univ
      open_target := U.2
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff (U := U)
          (f := F) (s := (U : Set M)) y]
        exact (contMDiffWithinAt_id (I := I) (s := (U : Set M)) (x := y)).congr
          (f₁ := fun z : M => (F z : M))
          (fun z hz => by
            simp only [F]
            split_ifs with h
            · rfl
            · exact absurd hz h)
          (by
            simp only [F]
            split_ifs with h
            · rfl
            · exact absurd hy h) }
  exact ⟨Ψ, Set.mem_univ x, fun y _ => rfl⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology
namespace ConnectedSumUnit

universe u

variable {M : ConnectedClosedOrientedManifold.{u} 3}
variable {c : OrientedBallChart M.toClosedOrientedManifold}
variable {d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold}
variable {a : BoundaryAttachment}

theorem isLocalDiffeomorphAt_chart_rad (hc : OrientedBallChart M.toClosedOrientedManifold)
    (hd : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (ha : BoundaryAttachment) (p : ConnectedSumQuotient.K) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun q : ConnectedSumQuotient.K => hc.toBallChart.chart (ConnectedSumQuotient.rad q)) p := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient hc.toBallChart hd.toBallChart ha.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace hc.toBallChart hd.toBallChart ha.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient hc.toBallChart hd.toBallChart ha.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold hc.toBallChart hd.toBallChart ha.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap ha.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv ha.1)
  have hseam : ConnectedSumQuotient.seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph ∈
      atlas (EuclideanSpace ℝ (Fin 3))
        (ConnectedSumQuotient hc.toBallChart hd.toBallChart ha.1.toHomeomorph) :=
    OrientationAssembly.mem_atlas_seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph
  let φ : PartialDiffeomorph (𝓡 3) (𝓡 3)
      (ConnectedSumQuotient hc.toBallChart hd.toBallChart ha.1.toHomeomorph)
      (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toPartialEquiv :=
        (ConnectedSumQuotient.seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph).toPartialEquiv
      open_source :=
        (ConnectedSumQuotient.seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph).open_source
      open_target :=
        (ConnectedSumQuotient.seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph).open_target
      contMDiffOn_toFun :=
        ConnectedSumQuotient.contMDiffOn_seamChartX hc.toBallChart hd.toBallChart ha.1 hseam
      contMDiffOn_invFun :=
        ConnectedSumQuotient.contMDiffOn_seamChartX_symm hc.toBallChart hd.toBallChart ha.1 hseam }
  have hsrc : φ.source =
      (ConnectedSumQuotient.seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph).source :=
    rfl
  have hmem : ConnectedSumQuotient.collarMap hc.toBallChart hd.toBallChart ha.1 p ∈ φ.source := by
    rw [hsrc, ConnectedSumQuotient.seamChartX_source]
    exact ConnectedSumQuotient.collarMap_mem_range hc.toBallChart hd.toBallChart ha.1 p
  have hsc : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun q => ConnectedSumQuotient.seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph q)
      (ConnectedSumQuotient.collarMap hc.toBallChart hd.toBallChart ha.1 p) :=
    PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ φ hmem
  have hgcol : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (ConnectedSumQuotient.collarMap hc.toBallChart hd.toBallChart ha.1) p :=
    (smoothConnectedSum M standardThreeSphereLift hc hd ha).collar_localDiffeomorph p
  have hcomp : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun x : ConnectedSumQuotient.K =>
        ConnectedSumQuotient.seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph
          (ConnectedSumQuotient.collarMap hc.toBallChart hd.toBallChart ha.1 x)) p :=
    hgcol.comp (K := 𝓡 3) (P := EuclideanSpace ℝ (Fin 3)) hsc
  have hrad_eq : (fun x : ConnectedSumQuotient.K =>
        ConnectedSumQuotient.seamChartX hc.toBallChart hd.toBallChart ha.1.toHomeomorph
          (ConnectedSumQuotient.collarMap hc.toBallChart hd.toBallChart ha.1 x))
      = fun x : ConnectedSumQuotient.K => ConnectedSumQuotient.rad x := by
    funext x
    rw [ConnectedSumQuotient.collarMap_eq_seamChartX hc.toBallChart hd.toBallChart ha.1 x]
    exact OpenPartialHomeomorph.right_inv _ (by
      rw [ConnectedSumQuotient.seamChartX_target]
      exact ConnectedSumQuotient.rad_mem_SeamShell x)
  have hrad : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun q : ConnectedSumQuotient.K => ConnectedSumQuotient.rad q) p :=
    hrad_eq ▸ hcomp
  have hchart : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun x : EuclideanSpace ℝ (Fin 3) => hc.toBallChart.chart x)
      (ConnectedSumQuotient.rad p) :=
    PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hc.toBallChart.chart (by
      refine hc.toBallChart.closedBall_subset_source ?_
      rw [Metric.mem_closedBall, dist_zero_right, ConnectedSumQuotient.norm_rad]
      linarith [p.2.2.2])
  exact hrad.comp (K := 𝓡 3) (P := M.Carrier) hchart

theorem isLocalDiffeomorph_quotientMap (F : UnitFilling c d a) (hcollar : BallComplementCollar F)
    (hS : BallComplementSmooth F) :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (quotientMap F) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
  intro y
  rcases ConnectedSumQuotient.interior_collar_cover c.toBallChart d.toBallChart a.1 y with
    ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨p, rfl⟩
  · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1) u :=
      (smoothConnectedSum M standardThreeSphereLift c d a).interiorLeft_localDiffeomorph u
    have heq : (fun x : c.toBallChart.interior =>
          quotientMap F (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x))
        = fun x : c.toBallChart.interior => (x : M.Carrier) :=
      funext fun x => rfl
    have hFcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : c.toBallChart.interior =>
          quotientMap F (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x)) u :=
      heq ▸ isLocalDiffeomorphAt_subtype_val c.toBallChart.interior u
    have hpt : hg.localInverse
        (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 u) = u :=
      hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : c.toBallChart.interior =>
          quotientMap F (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x))
        (hg.localInverse (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 u)) := by
      rw [hpt]
      exact hFcomp
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => quotientMap F (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1
          (hg.localInverse y)))
        (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 u) :=
      hg.localInverse_isLocalDiffeomorphAt.comp (K := 𝓡 3) (P := M.Carrier) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    exact congrArg (quotientMap F) hy.symm
  · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1) v :=
      (smoothConnectedSum M standardThreeSphereLift c d a).interiorRight_localDiffeomorph v
    have heq : (fun x : d.toBallChart.interior =>
          quotientMap F (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x))
        = fun x : d.toBallChart.interior =>
          (F.fill (d.toBallChart.interiorToPunctured x) : M.Carrier) :=
      funext fun x => rfl
    have hFcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : d.toBallChart.interior =>
          quotientMap F (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x)) v :=
      heq ▸ hS v
    have hpt : hg.localInverse
        (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 v) = v :=
      hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : d.toBallChart.interior =>
          quotientMap F (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x))
        (hg.localInverse (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 v)) := by
      rw [hpt]
      exact hFcomp
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => quotientMap F (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1
          (hg.localInverse y)))
        (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 v) :=
      hg.localInverse_isLocalDiffeomorphAt.comp (K := 𝓡 3) (P := M.Carrier) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    exact congrArg (quotientMap F) hy.symm
  · have hg : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1) p :=
      (smoothConnectedSum M standardThreeSphereLift c d a).collar_localDiffeomorph p
    have heq : (fun x : ConnectedSumQuotient.K =>
          quotientMap F (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 x))
        = fun x : ConnectedSumQuotient.K => c.toBallChart.chart (ConnectedSumQuotient.rad x) :=
      funext fun x => quotientMap_collarMap F hcollar x
    have hFcomp : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x : ConnectedSumQuotient.K =>
          quotientMap F (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 x)) p :=
      heq ▸ isLocalDiffeomorphAt_chart_rad c d a p
    have hpt : hg.localInverse
        (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p) = p :=
      hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x : ConnectedSumQuotient.K =>
          quotientMap F (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 x))
        (hg.localInverse (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p)) := by
      rw [hpt]
      exact hFcomp
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => quotientMap F (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1
          (hg.localInverse y)))
        (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p) :=
      hg.localInverse_isLocalDiffeomorphAt.comp (K := 𝓡 3) (P := M.Carrier) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    exact congrArg (quotientMap F) hy.symm

theorem nonempty_chart_interior (hc : OrientedBallChart M.toClosedOrientedManifold) :
    Nonempty hc.toBallChart.interior := by
  classical
  refine ⟨⟨hc.toBallChart.chart ((2 : ℝ) • (ConnectedSumQuotient.spherePoint (n := 3) (by norm_num) :
      EuclideanSpace ℝ (Fin 3))), ?_⟩⟩
  rw [BallChart.mem_interior]
  rintro ⟨w, hw, hweq⟩
  have h2z : (2 : ℝ) • (ConnectedSumQuotient.spherePoint (n := 3) (by norm_num) :
      EuclideanSpace ℝ (Fin 3)) ∈ hc.toBallChart.chart.source := by
    refine hc.toBallChart.closedBall_subset_source ?_
    rw [Metric.mem_closedBall, dist_zero_right,
      BallChart.norm_radial (ConnectedSumQuotient.spherePoint (n := 3) (by norm_num)) (by norm_num)]
  have hws : w ∈ hc.toBallChart.chart.source := hc.toBallChart.closedBall_one_subset_source hw
  have hzw : w = (2 : ℝ) • (ConnectedSumQuotient.spherePoint (n := 3) (by norm_num) :
      EuclideanSpace ℝ (Fin 3)) :=
    hc.toBallChart.chart.toPartialEquiv.injOn hws h2z hweq
  have hnorm : ‖w‖ = (2 : ℝ) := by
    rw [hzw, BallChart.norm_radial (ConnectedSumQuotient.spherePoint (n := 3) (by norm_num))
      (by norm_num)]
  have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  linarith

theorem nonempty_diffeomorph_of_unitFilling (F : UnitFilling c d a) (hcollar : BallComplementCollar F)
    (hS : BallComplementSmooth F) :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      M.Carrier) :=
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
  ⟨IsLocalDiffeomorph.diffeomorphOfBijective (isLocalDiffeomorph_quotientMap F hcollar hS)
    (quotientMap_bijective F)⟩

end ConnectedSumUnit
end DifferentialGeometry.Topology
