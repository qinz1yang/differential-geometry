import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CoreSurvivorLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedMaps
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Tensor.LinearAlgebra.Orientation
import DifferentialGeometry.Topology.ThreeManifold.LocalOrientationNaturality
import DifferentialGeometry.Topology.Homology.SingletonFiber

section

attribute [local instance]
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreCharts
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreSmooth

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

theorem rfs_whole_parent_map_isLocalDiffeomorphAt_childCore
    (x : G.transition.ChildCore c) (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    IsLocalDiffeomorphAt ThreeModel ThreeModel ∞ K.canonicalWholeParentMap
      (G.transition.childCoreIntoParent c x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
  let : IsManifold (𝓡∂ 3) ∞ (H.event i).old := (H.event i).oldSmooth
  obtain ⟨U, hxU, σ, hσ, hσval, hσout⟩ := K.exists_smooth_survivor_lift x hx
  let f : U → (G.Child c).Carrier := fun y => K.canonicalWholeParentMap y.1
  let a : (H.event i).old → (H.stage i.castSucc).Carrier := fun z => z.1.1
  have ha : ContMDiff (𝓡∂ 3) ThreeModel ∞ a := (H.event i).old_induced.contMDiff
  have hout : (fun y : U => (f y).1) = (H.event i).oldOutput ∘ σ :=
    (funext hσout).symm
  have hf : ContMDiff ThreeModel ThreeModel ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff ((H.stage i.succ).componentOpen c) f).mp
    change ContMDiff ThreeModel ThreeModel ∞ (fun y : U => (f y).1)
    rw [hout]
    exact (H.event i).contMDiff_oldOutput.comp hσ
  have hσinj : ∀ y, Function.Injective (mfderiv ThreeModel (𝓡∂ 3) σ y) := by
    intro y v w hvw
    have hfun : a ∘ σ = (fun z : U => z.1.1) := funext hσval
    have hchain := mfderiv_comp y (ha.mdifferentiable (by simp) _) (hσ.mdifferentiable (by simp) y)
    rw [hfun] at hchain
    have hval : mfderiv ThreeModel ThreeModel (fun z : U => z.1.1) y =
        ContinuousLinearMap.id ℝ ThreeSpace := by
      have hh := mfderiv_comp y
        ((contMDiff_subtype_val (I := ThreeModel) (n := ∞)
          (U := (H.stage i.castSucc).componentOpen (G.transition.childParent c))).mdifferentiable (by simp) _)
        ((contMDiff_subtype_val (I := ThreeModel) (n := ∞) (U := U)).mdifferentiable (by simp) y)
      ext v
      have hv := DFunLike.congr_fun hh v
      exact hv.trans ((mfderiv_subtype_val_apply (I := ThreeModel)
        (M := (H.stage i.castSucc).Carrier)
        ((H.stage i.castSucc).componentOpen (G.transition.childParent c)) y.1
        (mfderiv ThreeModel ThreeModel (Subtype.val : U → (G.Parent c).Carrier) y v)).trans
        (mfderiv_subtype_val_apply (I := ThreeModel) (M := (G.Parent c).Carrier) U y v))
    rw [hval] at hchain
    have heq := congrArg (mfderiv (𝓡∂ 3) ThreeModel a (σ y)) hvw
    change ((mfderiv (𝓡∂ 3) ThreeModel a (σ y)).comp
      (mfderiv ThreeModel (𝓡∂ 3) σ y)) v =
      ((mfderiv (𝓡∂ 3) ThreeModel a (σ y)).comp
        (mfderiv ThreeModel (𝓡∂ 3) σ y)) w at heq
    rw [← hchain] at heq
    exact heq
  have hinj : ∀ y, Function.Injective (mfderiv ThreeModel ThreeModel f y) := by
    intro y v w hvw
    have hchain := mfderiv_comp y
      ((H.event i).contMDiff_oldOutput.mdifferentiable (by simp) (σ y))
      (hσ.mdifferentiable (by simp) y)
    have hproj := mfderiv_comp y
      ((contMDiff_subtype_val (I := ThreeModel) (n := ∞)
        (U := (H.stage i.succ).componentOpen c)).mdifferentiable (by simp) (f y))
      (hf.mdifferentiable (by simp) y)
    rw [← hout] at hchain
    have hcomp := hproj.symm.trans hchain
    apply hσinj y
    apply ((H.event i).oldOutput_mfderiv_bijective (σ y)).injective
    have hV := DFunLike.congr_fun hcomp v
    have hW := DFunLike.congr_fun hcomp w
    have hv1 := mfderiv_subtype_val_apply (I := ThreeModel) (M := (H.stage i.succ).Carrier)
      ((H.stage i.succ).componentOpen c) (f y) (mfderiv ThreeModel ThreeModel f y v)
    have hw1 := mfderiv_subtype_val_apply (I := ThreeModel) (M := (H.stage i.succ).Carrier)
      ((H.stage i.succ).componentOpen c) (f y) (mfderiv ThreeModel ThreeModel f y w)
    exact hV.symm.trans (hv1.trans (hvw.trans (hw1.symm.trans hW)))
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      f hf hinj rfl
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (f := (Subtype.val : U → (G.Parent c).Carrier))
    (g := K.canonicalWholeParentMap) (x := ⟨G.transition.childCoreIntoParent c x, hxU⟩)
    (hlocal ⟨_, hxU⟩)
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := ThreeModel) (U := U) ⟨_, hxU⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

end

end

section

attribute [local instance]
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreCharts
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreSmooth

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

theorem rfs_whole_parent_map_preservesTangentOrientationAt_childCore
    (x : G.transition.ChildCore c) (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel K.canonicalWholeParentMap
      (G.transition.childCoreIntoParent c x)),
      PreservesTangentOrientationAt (G.Parent c).orientation (G.Child c).orientation
        K.canonicalWholeParentMap (G.transition.childCoreIntoParent c x) hf := by
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
  let : IsManifold (𝓡∂ 3) ∞ (H.event i).old := (H.event i).oldSmooth
  obtain ⟨U, hxU, σ, hσ, hσval, hσout⟩ := K.exists_smooth_survivor_lift x hx
  let z : U := ⟨G.transition.childCoreIntoParent c x, hxU⟩
  let α : U → G.transition.trace.tubes.core := fun y => (σ y).1
  have hα : ContMDiff ThreeModel (𝓡∂ 3) ∞ α :=
    (H.event i).contMDiff_oldInclusion.comp hσ
  have hαz : α z = x.1 := Subtype.ext (hσval z)
  let a : G.transition.trace.tubes.core → (H.stage i.castSucc).Carrier := Subtype.val
  let j := G.transition.trace.capping.coreInclusion
  let F := K.canonicalWholeParentMap
  have hF : MDifferentiableAt ThreeModel ThreeModel F z.1 :=
    (K.rfs_whole_parent_map_isLocalDiffeomorphAt_childCore x hx).mdifferentiableAt (by simp)
  have hsrc : a ∘ α = (fun y : U => y.1.1) := funext hσval
  have hleft := mfderiv_comp z
    (G.transition.core_induced.contMDiff.mdifferentiable (by simp) (α z))
    (hα.mdifferentiable (by simp) z)
  have hsrcdiff := mfderiv_comp z
    ((contMDiff_subtype_val (I := ThreeModel) (n := ∞)
      (U := (H.stage i.castSucc).componentOpen (G.transition.childParent c))).mdifferentiable (by simp) z.1)
    ((contMDiff_subtype_val (I := ThreeModel) (n := ∞) (U := U)).mdifferentiable (by simp) z)
  have hsource (v : ThreeSpace) :
      mfderiv (𝓡∂ 3) ThreeModel a x.1 (mfderiv ThreeModel (𝓡∂ 3) α z v) = v := by
    have hv := DFunLike.congr_fun hleft v
    rw [hαz] at hv
    have hsid := DFunLike.congr_fun hsrcdiff v
    have hv1 := mfderiv_subtype_val_apply (I := ThreeModel) (M := (H.stage i.castSucc).Carrier)
      ((H.stage i.castSucc).componentOpen (G.transition.childParent c)) z.1
      (mfderiv ThreeModel ThreeModel (Subtype.val : U → (G.Parent c).Carrier) z v)
    have hv2 := mfderiv_subtype_val_apply (I := ThreeModel) (M := (G.Parent c).Carrier) U z v
    have hfun : (fun y : U => (↑(α y) : (H.stage i.castSucc).Carrier)) = (fun y : U => y.1.1) := hsrc
    have hsame := congrArg (fun q : U → (H.stage i.castSucc).Carrier =>
      mfderiv ThreeModel ThreeModel q z v) hfun
    exact hv.symm.trans (hsame.trans (hsid.trans (hv1.trans hv2)))
  have heq : (fun y : U => G.transition.presentation (j (α y))) =
      (fun y : U => (Sum.inl (F y.1).1 : (H.stage i.succ).Carrier ⊕ (H.event i).discarded.Carrier)) := by
    funext y
    rw [G.transition.presentation_eq, (H.event i).oldOutput_eq, hσout]
  have hj := mfderiv_comp z
    (G.transition.core_inclusion_smooth.contMDiff.mdifferentiable (by simp) (α z))
    (hα.mdifferentiable (by simp) z)
  have hp := mfderiv_comp z
    (G.transition.presentation.contMDiff.mdifferentiable (by simp) (j (α z)))
    ((G.transition.core_inclusion_smooth.contMDiff.comp hα).mdifferentiable (by simp) z)
  have hFu : MDifferentiableAt ThreeModel ThreeModel (fun y : U => F y.1) z :=
    hF.comp z ((contMDiff_subtype_val (I := ThreeModel) (n := ∞) (U := U)).mdifferentiable (by simp) z)
  have hFV := mfderiv_comp z
    ((contMDiff_subtype_val (I := ThreeModel) (n := ∞)
      (U := (H.stage i.succ).componentOpen c)).mdifferentiable (by simp) (F z.1)) hFu
  have hUF := mfderiv_comp z hF
    ((contMDiff_subtype_val (I := ThreeModel) (n := ∞) (U := U)).mdifferentiable (by simp) z)
  have hsum := mfderiv_comp z
    (hasMFDerivAt_inl (I := ThreeModel) (M := (H.stage i.succ).Carrier)
      (M' := (H.event i).discarded.Carrier) (p := Sum.inl (F z.1).1)).mdifferentiableAt
    (((contMDiff_subtype_val (I := ThreeModel) (n := ∞)
      (U := (H.stage i.succ).componentOpen c)).mdifferentiable (by simp) (F z.1)).comp z hFu)
  have hout (v : ThreeSpace) :
      mfderiv ThreeModel ThreeModel F z.1 v =
        mfderiv ThreeModel ThreeModel G.transition.presentation (j x.1)
          (mfderiv (𝓡∂ 3) ThreeModel j x.1 (mfderiv ThreeModel (𝓡∂ 3) α z v)) := by
    have hpv := DFunLike.congr_fun hp v
    have hjv := DFunLike.congr_fun hj v
    have hsame := congrArg (fun q : U → (H.stage i.succ).Carrier ⊕ (H.event i).discarded.Carrier =>
      mfderiv ThreeModel ThreeModel q z v) heq
    have hsv := DFunLike.congr_fun hsum v
    have hfv := DFunLike.congr_fun hFV v
    have huv := DFunLike.congr_fun hUF v
    rw [mfderiv_sumInl (p := Sum.inl (F z.1).1)] at hsv
    change mfderiv ThreeModel ThreeModel
      (G.transition.presentation ∘ G.transition.trace.capping.coreInclusion ∘ α) z v =
      mfderiv ThreeModel ThreeModel G.transition.presentation (j (α z))
        (mfderiv ThreeModel ThreeModel (j ∘ α) z v) at hpv
    change mfderiv ThreeModel ThreeModel (j ∘ α) z v =
      mfderiv (𝓡∂ 3) ThreeModel j (α z) (mfderiv ThreeModel (𝓡∂ 3) α z v) at hjv
    change mfderiv ThreeModel ThreeModel
      (Sum.inl ∘ Subtype.val ∘ fun y : U => F y.1) z v =
      mfderiv ThreeModel ThreeModel (Subtype.val ∘ fun y : U => F y.1) z v at hsv
    rw [hjv, hαz] at hpv
    have hv1 := mfderiv_subtype_val_apply (I := ThreeModel) (M := (H.stage i.succ).Carrier)
      ((H.stage i.succ).componentOpen c) (F z.1)
      (mfderiv ThreeModel ThreeModel (fun y : U => F y.1) z v)
    have hv2 := mfderiv_subtype_val_apply (I := ThreeModel) (M := (G.Parent c).Carrier) U z v
    exact (huv.trans (congrArg (mfderiv ThreeModel ThreeModel F z.1) hv2)).symm.trans
      (hv1.symm.trans (hfv.symm.trans (hsv.symm.trans (hsame.symm.trans hpv))))
  obtain ⟨hi, hjbij, hpos⟩ := G.transition.core_positive x.1 hx
  obtain ⟨hpbij, hppos⟩ := G.transition.presentation_positive (j x.1)
  let A := LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel a x.1).toLinearMap hi
  let B := LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel j x.1).toLinearMap hjbij
  let C := LinearEquiv.ofBijective
    (mfderiv ThreeModel ThreeModel G.transition.presentation (j x.1)).toLinearMap hpbij
  have hαinv (v : ThreeSpace) : mfderiv ThreeModel (𝓡∂ 3) α z v = A.symm v := by
    apply A.injective
    exact (hsource v).trans (A.apply_symm_apply v).symm
  have hf : Function.Bijective (mfderiv ThreeModel ThreeModel F z.1) := by
    have he : (fun v : ThreeSpace => mfderiv ThreeModel ThreeModel F z.1 v) =
        (fun v : ThreeSpace => C (B (A.symm v))) := by
      funext v
      exact (hout v).trans (congrArg (fun w => C (B w)) (hαinv v))
    change Function.Bijective (fun v : ThreeSpace => mfderiv ThreeModel ThreeModel F z.1 v)
    rw [he]
    exact C.bijective.comp (B.bijective.comp A.symm.bijective)
  refine ⟨hf, ?_⟩
  unfold PreservesTangentOrientationAt
  have hlin : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel F z.1).toLinearMap hf =
      (A.symm.trans B).trans C := by
    ext v
    exact (hout v).trans (congrArg (fun w => C (B w)) (hαinv v))
  have hq : G.transition.presentation (j x.1) = Sum.inl (F z.1).1 := by
    rw [G.transition.presentation_eq, G.transition.childCoreInclusionFun_eq]
    exact congrArg (fun q : (G.Child c).Carrier => Sum.inl q.1)
      (K.rfs_whole_parent_map_childCore x).symm
  have hor := congrArg (Orientation.map (Fin 3) C) hpos
  have hor' : Orientation.map (Fin 3) ((A.symm.trans B).trans C)
      ((H.stage i.castSucc).orientation.orientation x.1.1) =
      Orientation.map (Fin 3) C ((H.event i).capped.orientation.orientation (j x.1)) :=
    (DifferentialGeometry.orientation_map_trans (A.symm.trans B) C
      ((H.stage i.castSucc).orientation.orientation x.1.1)).trans hor
  rw [hq] at hppos
  change Orientation.map (Fin 3) _ ((H.stage i.castSucc).orientation.orientation x.1.1) =
    (H.stage i.succ).orientation.orientation (F z.1).1
  rw [hlin]
  exact hor'.trans hppos

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

end

end

section

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

theorem rfs_whole_parent_map_fundamentalClass :
    integralHomologyMap 3 K.canonicalWholeParentMap
      (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation := by
  let : ConnectedSpace (G.Child c).Carrier := (H.stage i.succ).component_connected c
  obtain ⟨x, hx, hfiber⟩ := K.exists_rfs_whole_parent_map_singleton_fiber
  let p := G.transition.childCoreIntoParent c x
  have heq : K.canonicalWholeParentMap p = G.transition.childCoreInclusion c x :=
    K.rfs_whole_parent_map_childCore x
  have hmaps : MapsTo K.canonicalWholeParentMap ({p}ᶜ)
      ({K.canonicalWholeParentMap p}ᶜ) := by
    intro z hz hzy
    apply hz
    have hzpre : z ∈ K.canonicalWholeParentMap ⁻¹' {G.transition.childCoreInclusion c x} := by
      exact hzy.trans heq
    rw [hfiber] at hzpre
    exact hzpre
  obtain ⟨_, hpos⟩ := K.rfs_whole_parent_map_preservesTangentOrientationAt_childCore x hx
  have hlocal := localOrientationClass_natural_of_isLocalDiffeomorphAt
    (G.Parent c).orientation (G.Child c).orientation (n := ∞) (by simp)
    K.canonicalWholeParentMap p
    (K.rfs_whole_parent_map_isLocalDiffeomorphAt_childCore x hx) hmaps hpos
  exact DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_relativeHomologyMap_eq
    3 K.canonicalWholeParentMap hmaps
    (fundamentalClass (G.Parent c).orientation) (fundamentalClass (G.Child c).orientation)
    (localOrientationClass (G.Parent c).orientation p)
    (localOrientationClass (G.Child c).orientation (K.canonicalWholeParentMap p))
    (fundamentalClass_local (G.Parent c).orientation p)
    (fundamentalClass_local (G.Child c).orientation (K.canonicalWholeParentMap p))
    hlocal (by
      intro a b hab
      obtain ⟨m, rfl⟩ := (fundamentalClass_generator (G.Child c).orientation).surjective a
      obtain ⟨n, rfl⟩ := (fundamentalClass_generator (G.Child c).orientation).surjective b
      change (absoluteToRelative (G.Child c).Carrier
        ({K.canonicalWholeParentMap p}ᶜ) 3).hom (m • fundamentalClass (G.Child c).orientation) =
        (absoluteToRelative (G.Child c).Carrier
          ({K.canonicalWholeParentMap p}ᶜ) 3).hom (n • fundamentalClass (G.Child c).orientation) at hab
      rw [map_zsmul, map_zsmul] at hab
      have hmn : m = n := (localOrientationClass_generator (G.Child c).orientation
        (K.canonicalWholeParentMap p)).injective (by
          simpa only [fundamentalClass_local] using hab)
      rw [hmn])


theorem rfs_whole_parent_map_orientedDegree :
    let : ConnectedSpace (G.Child c).Carrier := (H.stage i.succ).component_connected c
    orientedDegree (G.Parent c).orientation (G.Child c).orientation
      K.canonicalWholeParentMap = 1 := by
  let : ConnectedSpace (G.Child c).Carrier := (H.stage i.succ).component_connected c
  apply (orientedDegree_eq_iff (G.Parent c).orientation (G.Child c).orientation
    K.canonicalWholeParentMap 1).mpr
  simpa only [one_smul] using K.rfs_whole_parent_map_fundamentalClass

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

end

end
