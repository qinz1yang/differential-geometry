import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCollaredStarCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreComponentRetraction
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition

set_option autoImplicit false

noncomputable section

open Set Topology Manifold Function Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

def middleLevel : Icc (-2 : ℝ) 2 := ⟨0, by norm_num⟩

def middleSphereSlice : Sphere 2 → TubeDomain := fun y => (y, middleLevel)

@[simp] theorem middleSphereSlice_apply (y : Sphere 2) :
    middleSphereSlice y = (y, middleLevel) := rfl

theorem injective_middleSphereSlice : Injective middleSphereSlice := by
  intro y₁ y₂ h
  simpa [middleSphereSlice] using congrArg Prod.fst h

theorem isEmbedding_middleSphereSlice : IsEmbedding middleSphereSlice :=
  isEmbedding_prodMkLeft middleLevel

theorem contMDiff_middleSphereSlice :
    ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡∂ 1)) ∞ middleSphereSlice :=
  contMDiff_id.prodMk contMDiff_const

theorem range_middleSphereSlice :
    range middleSphereSlice = {z : TubeDomain | z.2.1 = 0} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hz
    exact ⟨z.1, Prod.ext rfl (Subtype.ext (by simpa [middleLevel] using hz.symm))⟩

theorem chartAt_middleLevel_apply :
    (chartAt (EuclideanHalfSpace 1) middleLevel) middleLevel =
      ⟨WithLp.toLp 2 (fun _ => (2 : ℝ)), by norm_num⟩ := by
  rw [Icc_chartedSpaceChartAt_of_le_top (z := middleLevel) (by norm_num [middleLevel])]
  simp [IccLeftChart_apply, middleLevel]

theorem chartAt_middleLevel_extend_apply :
    ((chartAt (EuclideanHalfSpace 1) middleLevel).extend (𝓡∂ 1)) middleLevel =
      WithLp.toLp 2 (fun _ => (2 : ℝ)) := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, chartAt_middleLevel_apply]
  rfl

theorem chartAt_middleLevel_extend_ne_zero :
    ((chartAt (EuclideanHalfSpace 1) middleLevel).extend (𝓡∂ 1)) middleLevel ≠ 0 := by
  rw [chartAt_middleLevel_extend_apply]
  intro h
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem middleSphere_eq_image_middleSphereSlice (a : T.Index) :
    T.middleSphere a = T.tube a '' range middleSphereSlice := by
  rw [range_middleSphereSlice]
  rfl

theorem range_tube_middleSphereSlice (a : T.Index) :
    range (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) = T.middleSphere a := by
  rw [show (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) =
      (T.tube a) ∘ middleSphereSlice from rfl,
    Set.range_comp, range_middleSphereSlice]
  rfl

theorem isEmbedding_tube_middleSphereSlice (a : T.Index) :
    IsEmbedding (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) :=
  (T.embedding a).comp isEmbedding_middleSphereSlice

def middleSphereSliceSmoothEmbedding : Prop :=
  IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod (𝓡∂ 1)) ∞ middleSphereSlice

section Smooth

variable [ChartedSpace ThreeSpace M]

theorem contMDiff_tube_middleSphereSlice (a : T.Index)
    (hsm : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ContMDiff (𝓡 2) ThreeModel ∞ (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) :=
  hsm.contMDiff.comp contMDiff_middleSphereSlice

theorem isSmoothEmbedding_tube_middleSphereSlice
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (hslice : middleSphereSliceSmoothEmbedding) (a : T.Index) :
    IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) :=
  IsSmoothEmbedding.comp (I := 𝓡 2) (J := (𝓡 2).prod (𝓡∂ 1)) (J' := ThreeModel)
    (f := middleSphereSlice) (g := fun z => T.tube a z) (hsm a) hslice (by decide)

end Smooth

end TubeSystem

theorem continuousLinearMap_eq_zero_of_eqOn_of_mem_nhds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : E →L[ℝ] F} {U : Set E} {z : E} {c : F} (hU : U ∈ 𝓝 z) (h : ∀ w ∈ U, D w = c) :
    c = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hz : D z = c := h z (hball (by rw [Metric.mem_ball, dist_self]; exact hδ))
  have hw : ∀ w : E, D w = 0 := by
    intro w
    have hpos : 0 < δ / (2 * (‖w‖ + 1)) := by positivity
    have hsmall : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg w]
    have hmem : z + (δ / (2 * (‖w‖ + 1))) • w ∈ U :=
      hball (by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hpos]
        exact hsmall)
    have h1 : D z + (δ / (2 * (‖w‖ + 1))) • D w = D z := by
      rw [← map_smul, ← map_add, h (z + _ • w) hmem, hz]
    have h2 : (δ / (2 * (‖w‖ + 1))) • D w = 0 :=
      add_left_cancel (show D z + (δ / (2 * (‖w‖ + 1))) • D w = D z + 0 by rw [add_zero]; exact h1)
    exact (smul_eq_zero.mp h2).resolve_left (ne_of_gt hpos)
  rw [← hz, hw z]


theorem not_exists_eqOn_canonicalProductChart (y : Sphere 2)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (equiv : (EuclideanSpace ℝ (Fin 2) × F) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) :
    ¬ EqOn ((((chartAt (EuclideanSpace ℝ (Fin 2)) y).prod
            (chartAt (EuclideanHalfSpace 1) middleLevel)).extend ((𝓡 2).prod (𝓡∂ 1))) ∘
          middleSphereSlice ∘
          (((chartAt (EuclideanSpace ℝ (Fin 2)) y).extend (𝓡 2)).symm))
        (fun z => equiv (z, 0))
        (((chartAt (EuclideanSpace ℝ (Fin 2)) y).extend (𝓡 2)).target) := by
  intro h
  let χ := chartAt (EuclideanSpace ℝ (Fin 2)) y
  let e := chartAt (EuclideanHalfSpace 1) middleLevel
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1))).comp
      ((equiv : (EuclideanSpace ℝ (Fin 2) × F) →L[ℝ]
        (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) F))
  have hconst : ∀ z ∈ (χ.extend (𝓡 2)).target, D z = (e.extend (𝓡∂ 1)) middleLevel := by
    intro z hz
    have hw : ((χ.extend (𝓡 2)).symm z) ∈ χ.source := by
      have hm := (χ.extend (𝓡 2)).map_target hz
      rwa [χ.extend_source] at hm
    have hmem_pair : (((χ.extend (𝓡 2)).symm z), middleLevel) ∈ (χ.prod e).source :=
      ⟨hw, mem_chart_source _ _⟩
    have hval : ((χ.prod e).extend ((𝓡 2).prod (𝓡∂ 1)))
        ((χ.extend (𝓡 2)).symm z, middleLevel) = (z, (e.extend (𝓡∂ 1)) middleLevel) := by
      rw [OpenPartialHomeomorph.extend_prod χ e, PartialEquiv.prod_coe]
      exact Prod.ext ((χ.extend (𝓡 2)).right_inv hz) rfl
    have hz'' : ((χ.prod e).extend ((𝓡 2).prod (𝓡∂ 1)))
        ((χ.extend (𝓡 2)).symm z, middleLevel) = equiv (z, 0) := by
      simpa only [Function.comp_apply, middleSphereSlice_apply] using h hz
    rw [hval] at hz''
    have hsnd := congrArg Prod.snd hz''
    simpa [D] using hsnd.symm
  have hmem : (χ.extend (𝓡 2)).target ∈ 𝓝 ((χ.extend (𝓡 2)) y) :=
    χ.isOpen_extend_target.mem_nhds (by
      rw [χ.extend_target_eq_image_source]
      exact mem_image_of_mem _ (mem_chart_source _ y))
  refine chartAt_middleLevel_extend_ne_zero ?_
  simpa only [e] using continuousLinearMap_eq_zero_of_eqOn_of_mem_nhds hmem hconst

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

def middleSphereCuttingSeparation : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      SimplyConnectedSpace ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))

theorem childCoreSimplyConnectedOfParent_of_middleSphereCuttingSeparation
    (hsep : E.middleSphereCuttingSeparation) : E.childCoreSimplyConnectedOfParent :=
  fun c hpar => E.simplyConnectedSpace_childCore_of_puncturedCoreComponent c (hsep c hpar)

theorem componentwisePuncturedCoreOfParent_of_middleSphereCuttingSeparation
    (hsep : E.middleSphereCuttingSeparation) : E.ComponentwisePuncturedCoreOfParent :=
  fun c hpar => hsep c hpar

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
