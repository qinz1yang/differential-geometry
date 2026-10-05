import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialFibreSphere
import DifferentialGeometry.Topology.Manifold.HalfSpaceCenteredChart
import DifferentialGeometry.Topology.Manifold.SmoothLiftedCharts
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget
import DifferentialGeometry.Topology.Embedding.Diffeomorph

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance targetCellCharts_X135 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  Handle.closedCellChartedSpaceSucc 1

local instance targetCellSmooth_X135 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  Handle.closedCellIsManifold 1

theorem edgeFibre_chart_shift (c : Circle) (x : ClosedCell 2) :
    let h := (edgeFibreSphereInterior_embedding c).isImmersion.isImmersionAt x
    ∃ (w : EuclideanSpace ℝ (Fin 2))
      (L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3)),
      w 0 = 0 ∧ (L (h.equiv ((h.domChart.extend (𝓡∂ 2)) x + w, 0))) 0 = 1 := by
  let h := (edgeFibreSphereInterior_embedding c).isImmersion.isImmersionAt x
  let u : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.basisFun (Fin 2) ℝ 1
  have hu : u ≠ 0 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ne_zero 1
  let v : EuclideanSpace ℝ (Fin 3) := h.equiv (u, 0)
  have hv : v ≠ 0 := by
    intro hz
    have hh : (u, (0 : h.complement)) = 0 :=
      h.equiv.injective (by simpa only [v, map_zero] using hz)
    exact hu (congrArg Prod.fst hh)
  have hex : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra! hall
    apply hv
    ext i
    exact hall i
  obtain ⟨i, hi⟩ := hex
  let L := (Handle.closedCellPermute (Equiv.swap i 0)).toContinuousLinearEquiv
  have ha : (L v) 0 ≠ 0 := by
    change (Handle.closedCellPermute (Equiv.swap i 0) v) 0 ≠ 0
    rw [Handle.closedCellPermute_apply]
    simpa using hi
  let q := (h.domChart.extend (𝓡∂ 2)) x
  let d : ℝ := (1 - (L (h.equiv (q, 0))) 0) / (L v) 0
  refine ⟨d • u, L, ?_, ?_⟩
  · change d * u 0 = 0
    simp [u]
  · change (L (h.equiv (q + d • u, 0))) 0 = 1
    have hp : (q + d • u, (0 : h.complement)) = (q, 0) + d • (u, 0) := by
      apply Prod.ext
      · rfl
      · change (0 : h.complement) = 0 + d • 0
        exact ((zero_add _).trans (smul_zero d)).symm
    rw [hp, map_add, map_smul, map_add, map_smul]
    change (L (h.equiv (q, 0))) 0 + d * (L v) 0 = 1
    dsimp [d]
    field_simp [ha]
    ring

local instance carrierCharts_TargetX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_TargetX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

theorem edgeFibreAt_immersionAt (c : Circle) (x : ClosedCell 2) :
    IsImmersionAt (𝓡∂ 2) (𝓡∂ 3) ∞ (edgeFibreAt c) x := by
  classical
  let h := (edgeFibreSphereInterior_embedding c).isImmersion.isImmersionAt x
  obtain ⟨w, L, hw, hshift⟩ := edgeFibre_chart_shift c x
  let D : EuclideanHalfSpace 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ EuclideanHalfSpace 2 :=
    EuclideanHalfSpace.tangentialShiftDiffeomorph 1 w hw
  let a := h.domChart.trans D.toHomeomorph.toOpenPartialHomeomorph
  let b : PartialDiffeomorph (𝓡 3) (𝓡 3)
      radialSphereInterior (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toPartialEquiv := h.codChart.toPartialEquiv
      open_source := h.codChart.open_source
      open_target := h.codChart.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas }
  let t := DifferentialGeometry.Topology.Manifold.affinePartialDiffeomorph_GSF
    L (h.equiv (w, 0)) ∞
  let bt := b.trans t
  let lifted := bt.toOpenPartialHomeomorph.lift_openEmbedding
    sphereInteriorToCarrier_openEmbedding
  let lb : PartialDiffeomorph (𝓡∂ 3) (𝓡 3)
      carrier.Carrier (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toPartialEquiv := lifted.toPartialEquiv
      open_source := lifted.open_source
      open_target := lifted.open_target
      contMDiffOn_toFun :=
        DifferentialGeometry.Topology.Manifold.contMDiffOn_lift_openEmbedding
          (𝓡 3) (𝓡∂ 3) (𝓡 3) sphereInteriorToCarrier
          sphereInteriorToCarrier_openEmbedding sphereInteriorToCarrier_localDiffeomorph
          bt.toOpenPartialHomeomorph bt.contMDiffOn_toFun
      contMDiffOn_invFun :=
        DifferentialGeometry.Topology.Manifold.contMDiffOn_lift_openEmbedding_symm
          (𝓡 3) (𝓡∂ 3) (𝓡 3) sphereInteriorToCarrier
          sphereInteriorToCarrier_openEmbedding sphereInteriorToCarrier_smooth
          bt.toOpenPartialHomeomorph bt.contMDiffOn_invFun }
  let beta := lb.trans
    (DifferentialGeometry.Topology.Manifold.modelInverseInterior_GSF (𝓡∂ 3) ∞)
  have hnormal : h.codChart (edgeFibreSphereInterior c x) =
      h.equiv ((h.domChart.extend (𝓡∂ 2)) x, 0) := by
    have he := h.writtenInCharts ((h.domChart.extend (𝓡∂ 2)).map_source
      (by simpa only [OpenPartialHomeomorph.extend_source] using h.mem_domChart_source))
    dsimp only [Function.comp_apply] at he
    rw [h.domChart.extend_left_inv h.mem_domChart_source] at he
    exact he
  have hlift : lb (edgeFibreAt c x) =
      L (h.codChart (edgeFibreSphereInterior c x) + h.equiv (w, 0)) := by
    exact bt.toOpenPartialHomeomorph.lift_openEmbedding_apply
      sphereInteriorToCarrier_openEmbedding
  have hpos : lb (edgeFibreAt c x) ∈ interior (range (𝓡∂ 3)) := by
    rw [hlift, hnormal, ← map_add, Prod.mk_add_mk, add_zero]
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    change 0 < (L (h.equiv ((h.domChart.extend (𝓡∂ 2)) x + w, 0))) 0
    rw [hshift]
    norm_num
  have hbeta : edgeFibreAt c x ∈ beta.source := by
    refine ⟨?_, hpos⟩
    exact ⟨edgeFibreSphereInterior c x, ⟨h.mem_codChart_source, mem_univ _⟩, rfl⟩
  let s := edgeFibreAt c ⁻¹' beta.source
  have hf : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ (edgeFibreAt c) :=
    sphereInteriorToCarrier_smooth.comp (edgeFibreSphereInterior_embedding c).contMDiff
  have hs : IsOpen s := beta.open_source.preimage hf.continuous
  let alpha := a.restr s
  have ha : a ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ (ClosedCell 2) := by
    apply a.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (D ∘ h.domChart) a.source
      simpa [a] using D.contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas)
    · exact (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        D.symm.contMDiff.contMDiffOn (fun _ hz => hz.2)
  apply IsImmersionAtOfComplement.isImmersionAt (F := h.complement)
  apply IsImmersionAtOfComplement.mk_of_continuousAt hf.continuous.continuousAt
    (h.equiv.trans L) alpha beta.toOpenPartialHomeomorph
  · exact ⟨⟨h.mem_domChart_source, mem_univ _⟩, hs.interior_eq.symm ▸ hbeta⟩
  · exact hbeta
  · exact restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 2)) ha hs
  · exact beta.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      beta.contMDiffOn_toFun beta.contMDiffOn_invFun
  · intro z hz
    let y := (alpha.extend (𝓡∂ 2)).symm z
    have hy : y ∈ alpha.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using
        (alpha.extend (𝓡∂ 2)).map_target hz
    have hyd : y ∈ h.domChart.source := hy.1.1
    have hret : (h.domChart.extend (𝓡∂ 2)) y + w = z := by
      exact (alpha.extend (𝓡∂ 2)).right_inv hz
    have hn := h.writtenInCharts ((h.domChart.extend (𝓡∂ 2)).map_source
      (by simpa only [OpenPartialHomeomorph.extend_source] using hyd))
    have hny : h.codChart (edgeFibreSphereInterior c y) =
        h.equiv ((h.domChart.extend (𝓡∂ 2)) y, 0) := by
      dsimp only [Function.comp_apply] at hn
      rw [h.domChart.extend_left_inv hyd] at hn
      exact hn
    have hpy : edgeFibreAt c y ∈ beta.source := by
      have hys : y ∈ s := by simpa only [hs.interior_eq] using hy.2
      exact hys
    change (𝓡∂ 3) ((𝓡∂ 3).symm (lb (edgeFibreAt c y))) = L (h.equiv (z, 0))
    have hp : lb (edgeFibreAt c y) ∈ interior (range (𝓡∂ 3)) := hpy.2
    apply Eq.trans ((𝓡∂ 3).right_inv (interior_subset hp))
    change lifted (sphereInteriorToCarrier (edgeFibreSphereInterior c y)) =
      L (h.equiv (z, 0))
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    change L (h.codChart (edgeFibreSphereInterior c y) + h.equiv (w, 0)) =
      L (h.equiv (z, 0))
    rw [hny, ← map_add, Prod.mk_add_mk, add_zero, hret]

theorem edgeFibreAt_embedding (c : Circle) :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ (edgeFibreAt c) :=
  ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_isImmersionAt
      (edgeFibreAt_immersionAt c),
    sphereInteriorToCarrier_embedding.comp
      (edgeFibreSphereInterior_embedding c).isEmbedding⟩

end GC.GraphManifold.Assembly.FC39P0.X135Radial
