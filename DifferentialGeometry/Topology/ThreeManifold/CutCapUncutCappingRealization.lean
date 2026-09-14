import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import DifferentialGeometry.Topology.ThreeManifold.CutCapUncutComponentRealization

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

local instance instUncutCappingCoreChartedSpace :
    ChartedSpace (EuclideanHalfSpace 3) E.tubes.core :=
  E.capping.coreCharts

local instance instUncutCappingCoreIsManifold :
    IsManifold (𝓡∂ 3) ∞ E.tubes.core :=
  E.capping.coreSmooth

abbrev uncutCoreInclusion (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    (M.component C).Carrier → E.tubes.core :=
  fun y => ⟨y.1, E.componentSet_subset_core_of_cutIndices_eq_empty C hC y.2⟩

private theorem eventually_isInvertible_fderiv {G : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)} {V : Set (EuclideanSpace ℝ (Fin 3))}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hV : IsOpen V) (hx : x ∈ V) (hG : ContDiffOn ℝ ∞ G V)
    (hinv : (fderiv ℝ G x).IsInvertible) :
    ∀ᶠ y in 𝓝 x, (fderiv ℝ G y).IsInvertible := by
  obtain ⟨e, he⟩ := hinv
  have hinv_nhds : {L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) |
      L.IsInvertible} ∈ 𝓝 (fderiv ℝ G x) := by
    rw [← he]
    exact e.nhds
  exact ((hG.contDiffAt (hV.mem_nhds hx)).continuousAt_fderiv (by simp)).preimage_mem_nhds
    hinv_nhds

private noncomputable def smoothEuclideanChart {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N] (y : N) :
    PartialDiffeomorph (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N
      (EuclideanSpace ℝ (Fin 3)) ∞ where
  toPartialEquiv := extChartAt (𝓡 3) y
  open_source := isOpen_extChartAt_source y
  open_target := isOpen_extChartAt_target y
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := 𝓡 3) (x := y)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm y

theorem isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N]
    {f : E.tubes.core → N} (hf : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ f)
    {z : E.tubes.core} (hz : (𝓡∂ 3).IsInteriorPoint z)
    (hbi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) f z)) :
    IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ f z := by
  let c : PartialDiffeomorph (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) E.tubes.core
      (EuclideanSpace ℝ (Fin 3)) ∞ :=
    DifferentialGeometry.Manifold.interiorChart (𝓡∂ 3) ∞ z
  let d := smoothEuclideanChart (f z)
  let V : Set (EuclideanSpace ℝ (Fin 3)) :=
    c.target ∩ (c.symm : EuclideanSpace ℝ (Fin 3) → E.tubes.core)
      ⁻¹' (univ ∩ f ⁻¹' d.source)
  let K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun w => d (f (c.symm w))
  have hV : IsOpen V :=
    c.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_target
      ((hf.contMDiffOn.continuousOn).isOpen_inter_preimage isOpen_univ d.open_source)
  have hzc : z ∈ c.source := by
    rw [DifferentialGeometry.Manifold.mem_interiorChart_source_iff]
    exact hz
  have hczV : c z ∈ V := by
    refine ⟨c.toPartialEquiv.map_source hzc, ?_⟩
    change c.toPartialEquiv.symm (c.toPartialEquiv z) ∈ univ ∩ f ⁻¹' d.source
    rw [c.toPartialEquiv.left_inv hzc]
    exact ⟨trivial, mem_extChartAt_source (f z)⟩
  have hinner : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞
      (fun w => f (c.symm w)) V :=
    hf.comp_contMDiffOn (c.contMDiffOn_invFun.mono inter_subset_left)
  have hK : ContDiffOn ℝ ∞ K V :=
    (d.contMDiffOn_toFun.comp hinner (fun w hw => hw.2.2)).contDiffOn
  have hinvK : (fderiv ℝ K (c z)).IsInvertible := by
    have hKdef : K = writtenInExtChartAt (𝓡∂ 3) (𝓡 3) z f := rfl
    have hcz : c z = extChartAt (𝓡∂ 3) z z := rfl
    rw [hKdef, hcz]
    have hmd : MDifferentiableAt (𝓡∂ 3) (𝓡 3) f z :=
      hf.contMDiffAt.mdifferentiableAt (by simp)
    have hderiv : fderiv ℝ (writtenInExtChartAt (𝓡∂ 3) (𝓡 3) z f)
        (extChartAt (𝓡∂ 3) z z) = mfderiv (𝓡∂ 3) (𝓡 3) f z := by
      rw [hmd.mfderiv]
      exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hz)).symm
    rw [hderiv]
    exact ⟨(LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) f z).toLinearMap
      hbi).toContinuousLinearEquiv, rfl⟩
  have hevent := eventually_isInvertible_fderiv hV hczV hK hinvK
  have hgood : {w : EuclideanSpace ℝ (Fin 3) | (fderiv ℝ K w).IsInvertible} ∩ V ∈
      𝓝 (c z) :=
    inter_mem hevent (hV.mem_nhds hczV)
  obtain ⟨W, hWsub, hW, hczW⟩ := mem_nhds_iff.mp hgood
  refine DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_coordinates c d hW hzc hczW
    (fun w hw => (hWsub hw).2.2.2) ?_ ?_
  · exact hK.mono (fun _ hw => (hWsub hw).2)
  · intro w hw
    exact (hWsub hw).1

theorem continuous_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    Continuous (uncutCoreInclusion E C hC) :=
  continuous_subtype_val.subtype_mk _

theorem contMDiffAt_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞
      (uncutCoreInclusion E C hC) y := by
  have hcont : ContinuousAt (uncutCoreInclusion E C hC) y :=
    (continuous_uncutCoreInclusion E C hC).continuousAt
  rw [ContMDiffAt.iff_comp_isImmersionAt (φ := (Subtype.val : E.tubes.core → M.Carrier))
    (E.capping.core_induced.isImmersion.isImmersionAt (uncutCoreInclusion E C hC y))]
  exact ⟨hcont, (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
    (U := ClosedOrientedManifold.componentOpen M C)).contMDiffAt⟩

theorem isLocalDiffeomorphAt_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞
      (uncutCoreInclusion E C hC) y := by
  have hint : (𝓡∂ 3).IsInteriorPoint (uncutCoreInclusion E C hC y) :=
    E.isInteriorPoint_of_mem_coreComponentSet C hC y.2
  have hg : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞
      (Subtype.val : E.tubes.core → M.Carrier) (uncutCoreInclusion E C hC y) :=
    E.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv
      E.capping.core_induced.contMDiff hint
      (E.capping.core_positive (uncutCoreInclusion E C hC y) hint).1
  have hgi : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞
      (fun z : (M.component C).Carrier =>
        ((uncutCoreInclusion E C hC z : E.tubes.core) : M.Carrier)) y :=
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (U := ClosedOrientedManifold.componentOpen M C)) y
  have hpre : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞
      (hg.localInverse ∘ fun z : (M.component C).Carrier =>
        ((uncutCoreInclusion E C hC z : E.tubes.core) : M.Carrier)) y :=
    IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (J := 𝓡 3)
      (K := 𝓡∂ 3) (n := ∞) (hf := hgi) (hg := hg.localInverse_isLocalDiffeomorphAt)
  have hcont : Tendsto (uncutCoreInclusion E C hC) (𝓝 y)
      (𝓝 (uncutCoreInclusion E C hC y)) :=
    (continuous_uncutCoreInclusion E C hC).continuousAt
  have heq : (hg.localInverse ∘ fun z : (M.component C).Carrier =>
      ((uncutCoreInclusion E C hC z : E.tubes.core) : M.Carrier)) =ᶠ[𝓝 y]
      (uncutCoreInclusion E C hC) :=
    hcont.eventually hg.localInverse_eventuallyEq_left
  exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq heq.symm hpre

theorem isLocalDiffeomorphAt_coreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ (⇑E.capping.coreInclusion)
      (uncutCoreInclusion E C hC y) :=
  E.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv
    E.capping.core_embedding.contMDiff
    (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)
    (E.capping.core_positive (uncutCoreInclusion E C hC y)
      (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)).2.1

theorem mdifferentiableAt_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
      (uncutCoreInclusion E C hC) y :=
  (isLocalDiffeomorphAt_uncutCoreInclusion E C hC y).mdifferentiableAt (by simp)

theorem mdifferentiableAt_subtypeVal_core (x : E.tubes.core) :
    MDifferentiableAt (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier) x :=
  (E.capping.core_induced.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)

theorem mfderiv_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
        (uncutCoreInclusion E C hC) y) =
      (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : E.tubes.core → M.Carrier) (uncutCoreInclusion E C hC y)).toLinearMap
        (E.capping.core_positive (uncutCoreInclusion E C hC y)
          (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)).1).symm.toContinuousLinearEquiv :
        TangentSpace (𝓡 3) ((uncutCoreInclusion E C hC y : E.tubes.core) : M.Carrier) →L[ℝ]
          TangentSpace (𝓡∂ 3) (uncutCoreInclusion E C hC y))) := by
  obtain ⟨hi, -, -⟩ := E.capping.core_positive (uncutCoreInclusion E C hC y)
    (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)
  apply ContinuousLinearMap.ext
  intro v
  have hchain := mfderiv_comp
    (g := (Subtype.val : E.tubes.core → M.Carrier)) (f := uncutCoreInclusion E C hC)
    (x := y) (mdifferentiableAt_subtypeVal_core E (uncutCoreInclusion E C hC y))
    (mdifferentiableAt_uncutCoreInclusion E C hC y)
  have hval := congrArg (fun L => L v) hchain
  have hfun : ((Subtype.val : E.tubes.core → M.Carrier) ∘ uncutCoreInclusion E C hC) =
      (Subtype.val : (M.component C).Carrier → M.Carrier) := rfl
  rw [hfun] at hval
  have hsub_apply : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3)
      (Subtype.val : (M.component C).Carrier → M.Carrier) y) v = v :=
    DifferentialGeometry.mfderiv_subtype_val_apply
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (U := ClosedOrientedManifold.componentOpen M C) y v
  have hv : (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier)
      (uncutCoreInclusion E C hC y))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
        (uncutCoreInclusion E C hC) y v) = v := by
    have h2 : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3)
        (Subtype.val : (M.component C).Carrier → M.Carrier) y) v =
        ((mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier)
          (uncutCoreInclusion E C hC y)).comp
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
            (uncutCoreInclusion E C hC) y)) v := hval
    exact h2.symm.trans hsub_apply
  exact (LinearEquiv.eq_symm_apply _).mpr hv

def uncutMap (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    (M.component C).Carrier →
      (E.capped.component (ConnectedComponents.mk (E.capping.coreInclusion x))).Carrier :=
  fun y => ⟨E.capping.coreInclusion (uncutCoreInclusion E C hC y), by
    change E.capping.coreInclusion (uncutCoreInclusion E C hC y) ∈
      E.capped.componentSet (ConnectedComponents.mk (E.capping.coreInclusion x))
    rw [← E.image_coreComponentSet_eq_componentSet C hC hx]
    exact ⟨uncutCoreInclusion E C hC y, y.2, rfl⟩⟩

theorem uncutMap_apply (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) (y : (M.component C).Carrier) :
    (uncutMap E C hC x hx y).1 = E.capping.coreInclusion (uncutCoreInclusion E C hC y) := rfl

theorem isLocalDiffeomorphAt_uncutMap (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C)
    (y : (M.component C).Carrier) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (uncutMap E C hC x hx) y := by
  have hcomp : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞
      (fun z : (M.component C).Carrier =>
        E.capping.coreInclusion (uncutCoreInclusion E C hC z)) y :=
    IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (J := 𝓡∂ 3)
      (K := 𝓡 3) (n := ∞) (hf := isLocalDiffeomorphAt_uncutCoreInclusion E C hC y)
      (hg := isLocalDiffeomorphAt_coreInclusion E C hC y)
  have hres := DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (V := ClosedOrientedManifold.componentOpen E.capped
      (ConnectedComponents.mk (E.capping.coreInclusion x)))
    (f := fun z : (M.component C).Carrier =>
      E.capping.coreInclusion (uncutCoreInclusion E C hC z)) (fun z => ?_) hcomp
  · convert hres using 1 <;> try rfl
  · change E.capping.coreInclusion (uncutCoreInclusion E C hC z) ∈
      E.capped.componentSet (ConnectedComponents.mk (E.capping.coreInclusion x))
    rw [← E.image_coreComponentSet_eq_componentSet C hC hx]
    exact ⟨uncutCoreInclusion E C hC z, z.2, rfl⟩

theorem contMDiff_uncutMap (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (uncutMap E C hC x hx) :=
  fun y => (isLocalDiffeomorphAt_uncutMap E C hC x hx y).contMDiffAt

theorem uncutMap_injective (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    Function.Injective (uncutMap E C hC x hx) := by
  intro y y' h
  have hcoe : E.capping.coreInclusion (uncutCoreInclusion E C hC y) =
      E.capping.coreInclusion (uncutCoreInclusion E C hC y') := congrArg Subtype.val h
  have hcore : uncutCoreInclusion E C hC y = uncutCoreInclusion E C hC y' :=
    E.capping.core_embedding.isEmbedding.injective hcoe
  exact Subtype.ext (congrArg (fun z : E.tubes.core => (z : M.Carrier)) hcore)

theorem uncutMap_surjective (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    Function.Surjective (uncutMap E C hC x hx) := by
  intro z
  have hz : z.1 ∈ E.capping.coreInclusion '' E.coreComponentSet C := by
    have hz' : z.1 ∈ E.capped.componentSet
        (ConnectedComponents.mk (E.capping.coreInclusion x)) := z.2
    rwa [← E.image_coreComponentSet_eq_componentSet C hC hx] at hz'
  obtain ⟨w, hw, hweq⟩ := hz
  exact ⟨⟨(w : M.Carrier), hw⟩, Subtype.ext hweq⟩

theorem uncutMap_bijective (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    Function.Bijective (uncutMap E C hC x hx) :=
  ⟨uncutMap_injective E C hC x hx, uncutMap_surjective E C hC x hx⟩

noncomputable def uncutMapDiffeomorph (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (M.component C).Carrier
      (E.capped.component (ConnectedComponents.mk (E.capping.coreInclusion x))).Carrier ∞ :=
  IsLocalDiffeomorph.diffeomorphOfBijective
    (fun y => isLocalDiffeomorphAt_uncutMap E C hC x hx y) (uncutMap_bijective E C hC x hx)

theorem mfderiv_uncutMap (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) (y : (M.component C).Carrier) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        (uncutMap E C hC x hx) y) =
      ((mfderiv (𝓡∂ 3) (𝓡 3) (⇑E.capping.coreInclusion)
          (uncutCoreInclusion E C hC y)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
          (uncutCoreInclusion E C hC) y)) := by
  have hdiff : MDifferentiableAt (𝓡∂ 3) (𝓡 3) (⇑E.capping.coreInclusion)
      (uncutCoreInclusion E C hC y) :=
    (E.capping.core_embedding.contMDiff.contMDiffAt
      (x := uncutCoreInclusion E C hC y)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (x := y) (g := (⇑E.capping.coreInclusion))
    (f := uncutCoreInclusion E C hC) hdiff (mdifferentiableAt_uncutCoreInclusion E C hC y)
  have hfun : ((⇑E.capping.coreInclusion) ∘ uncutCoreInclusion E C hC) =
      (fun z : (M.component C).Carrier => (uncutMap E C hC x hx z).1) := rfl
  rw [hfun] at hchain
  have hsub := DifferentialGeometry.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
    (U := ClosedOrientedManifold.componentOpen E.capped
      (ConnectedComponents.mk (E.capping.coreInclusion x)))
    (f := uncutMap E C hC x hx) y
  exact hsub.symm.trans hchain
theorem uncutMapDiffeomorph_preservesOrientation (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    (uncutMapDiffeomorph E C hC x hx).preservesOrientation
      (M.component C).orientation
      (E.capped.component (ConnectedComponents.mk (E.capping.coreInclusion x))).orientation := by
  intro y
  obtain ⟨hi, hj, hpos⟩ := E.capping.core_positive (uncutCoreInclusion E C hC y)
    (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)
  let A : TangentSpace (𝓡∂ 3) (uncutCoreInclusion E C hC y) ≃ₗ[ℝ]
      TangentSpace (𝓡 3) ((uncutCoreInclusion E C hC y : E.tubes.core) : M.Carrier) :=
    LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : E.tubes.core → M.Carrier) (uncutCoreInclusion E C hC y)).toLinearMap hi
  let B : TangentSpace (𝓡∂ 3) (uncutCoreInclusion E C hC y) ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (E.capping.coreInclusion (uncutCoreInclusion E C hC y)) :=
    LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (⇑E.capping.coreInclusion)
      (uncutCoreInclusion E C hC y)).toLinearMap hj
  have hL : (((uncutMapDiffeomorph E C hC x hx).mfderivToContinuousLinearEquiv (by simp)
        y).toLinearEquiv :
      TangentSpace (𝓡 3) y.1 ≃ₗ[ℝ]
        TangentSpace (𝓡 3) (E.capping.coreInclusion (uncutCoreInclusion E C hC y))) =
      (A.symm.trans B :
        TangentSpace (𝓡 3) y.1 ≃ₗ[ℝ]
          TangentSpace (𝓡 3) (E.capping.coreInclusion (uncutCoreInclusion E C hC y))) := by
    apply LinearEquiv.ext
    intro v
    change (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (uncutMap E C hC x hx) y) v = (A.symm.trans B) v
    rw [mfderiv_uncutMap E C hC x hx y]
    rw [mfderiv_uncutCoreInclusion E C hC y]
    rfl
  rw [hL]
  rw [show (uncutMapDiffeomorph E C hC x hx) y = uncutMap E C hC x hx y from rfl]
  have hleft : ((M.component C).orientation).orientation y = M.orientation.orientation y.1 :=
    ClosedOrientedManifold.componentTangentOrientation_apply M C y
  have hright : ((E.capped.component
        (ConnectedComponents.mk (E.capping.coreInclusion x))).orientation).orientation
        (uncutMap E C hC x hx y) =
      E.capped.orientation.orientation
        (E.capping.coreInclusion (uncutCoreInclusion E C hC y)) := by
    change ClosedOrientedManifold.componentTangentOrientation E.capped
      (ConnectedComponents.mk (E.capping.coreInclusion x)) (uncutMap E C hC x hx y) = _
    have hct := ClosedOrientedManifold.componentTangentOrientation_apply E.capped
      (ConnectedComponents.mk (E.capping.coreInclusion x)) (uncutMap E C hC x hx y)
    exact hct.trans (by rw [uncutMap_apply])
  rw [hleft, hright]
  exact hpos

theorem uncutCappingRealization : E.UncutCappingRealization := by
  intro C hC x hx
  exact ⟨⟨uncutMapDiffeomorph E C hC x hx,
    uncutMapDiffeomorph_preservesOrientation E C hC x hx⟩⟩

theorem noTubeRealization_of_cappedPresentationRealization
    (h : E.CappedPresentationRealization) : E.NoTubeRealization :=
  E.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization
    E.uncutCappingRealization h

theorem noTubeRealization_of_retained_of_discarded_cappedPresentation
    (h₁ : E.CappedRetainedPresentationRealization)
    (h₂ : E.CappedDiscardedPresentationRealization) : E.NoTubeRealization :=
  E.noTubeRealization_of_uncutCappingRealization_of_retained_of_discarded
    E.uncutCappingRealization h₁ h₂

theorem isPoincareStandard_of_capped (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C)
    (hstd : isPoincareStandard ((E.capped.component
      (ConnectedComponents.mk (E.capping.coreInclusion x))).toClosedOrientedManifold).Carrier) :
    isPoincareStandard (M.component C).Carrier :=
  E.isPoincareStandard_of_capped_of_uncutCappingRealization E.uncutCappingRealization
    C hC x hx hstd

theorem noTubeRealization : E.NoTubeRealization :=
  E.noTubeRealization_of_uncutCappingRealization E.uncutCappingRealization

theorem graphSumRealization_iff_cutComponentRealization :
    E.graphSumRealization ↔ E.cutComponentRealization :=
  E.graphSumRealization_iff_noTubeRealization_and_cutComponentRealization.trans
    ⟨fun h => h.2, fun h => ⟨E.noTubeRealization, h⟩⟩

theorem componentConnectedSumDecomposition_iff_cutComponentRealization :
    E.componentConnectedSumDecomposition ↔ E.cutComponentRealization :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.trans
    ⟨fun h => h.2, fun h => ⟨E.noTubeRealization, h⟩⟩

end SphericalCutCapTransition

end DifferentialGeometry.Topology
