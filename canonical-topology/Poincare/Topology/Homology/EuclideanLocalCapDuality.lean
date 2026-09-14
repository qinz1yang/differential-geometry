import Poincare.Topology.Homology.SphereCapDuality
import Poincare.Topology.Homology.EuclideanLocalTop
import Poincare.Topology.Homology.RelativeCapCohomologyConnecting
import Poincare.Topology.Homology.RelativeCohomologyVanishing
import Poincare.Topology.Homology.LocalStarConvex
import Poincare.Topology.Homology.RelativeComparison
import Poincare.Topology.Homology.CochainHomotopy
import Poincare.Topology.Homology.RelativeCapToAbsoluteHomology

noncomputable section

universe u

namespace Poincare.Topology

section

open Set Metric

theorem integralEuclideanLocalTopZeroEquiv_cap_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (n + 2) 0 α
        ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1)) := by
  let _ := unitSphere_pathConnected_of_finrank (E := E) (by omega)
  let A : Set E := {0}ᶜ
  let e := puncturedSpaceSphereHomotopyEquiv E
  let c := (integralEuclideanLocalTopZeroEquiv E n hd).symm 1
  let s := (integralSphereTopHomologyEquiv n E hd).symm 1
  have hc : integralSingularHomologyMap (n + 1) e.toFun
      (integralRelativeConnecting (n + 1) A c) = s := by
    apply (integralSphereTopHomologyEquiv n E hd).injective
    change integralEuclideanLocalTopZeroEquiv E n hd c =
      integralSphereTopHomologyEquiv n E hd s
    rw [(integralEuclideanLocalTopZeroEquiv E n hd).apply_symm_apply,
      (integralSphereTopHomologyEquiv n E hd).apply_symm_apply]
  let f := fun α : integralRelativeCohomology (n + 2) A =>
    integralRelativeCohomologyCapToAbsolute A (n + 2) 0 α c
  let h := integralRelativeCohomologyConnecting (n + 1) A ∘
    integralSingularCohomologyMap (n + 1) e.toFun
  have hh : Function.Bijective h :=
    (integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
      (n + 1) (by omega) A).comp
      (integralSingularCohomologyMap_bijective_of_homotopyEquiv e (n + 1))
  have heq : (fun α => integralZeroAugmentation (f α)) ∘ h =
      fun β : integralSingularCohomology (n + 1) (sphere (0 : E) 1) =>
        integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0 β s) := by
    funext β
    have hcap := integralRelativeCohomologyCapToAbsolute_connecting A (n + 1) 0
      (integralSingularCohomologyMap (n + 1) e.toFun β) c
    change f (h β) = integralSingularHomologyMap 0 (singularSubspaceInclusion A)
      (integralSingularCohomologyCapProduct (n + 1) 0
        (integralSingularCohomologyMap (n + 1) e.toFun β)
        (integralRelativeConnecting (n + 1) A c)) at hcap
    change integralZeroAugmentation (f (h β)) = _
    rw [hcap]
    calc
      _ = integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0
          (integralSingularCohomologyMap (n + 1) e.toFun β)
          (integralRelativeConnecting (n + 1) A c)) :=
        LinearMap.congr_fun (integralZeroAugmentation_natural (singularSubspaceInclusion A)) _
      _ = integralZeroAugmentation (integralSingularHomologyMap 0 e.toFun
          (integralSingularCohomologyCapProduct (n + 1) 0
            (integralSingularCohomologyMap (n + 1) e.toFun β)
            (integralRelativeConnecting (n + 1) A c))) :=
        (LinearMap.congr_fun (integralZeroAugmentation_natural e.toFun) _).symm
      _ = _ := by
        rw [integralSingularCohomologyCapProduct_natural]
        change integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0 β
          (integralSingularHomologyMap (n + 1) e.toFun
            (integralRelativeConnecting (n + 1) A c))) = _
        rw [hc]
  have hb : Function.Bijective ((fun α => integralZeroAugmentation (f α)) ∘ h) := by
    rw [heq]
    exact integralConnectedZeroAugmentationEquiv.bijective.comp
      (integralSphereTopHomologyEquiv_cap_bijective n E hd)
  have hf := (Function.Bijective.of_comp_iff (fun α => integralZeroAugmentation (f α)) hh).mp hb
  exact (Function.Bijective.of_comp_iff' integralConnectedZeroAugmentationEquiv.bijective f).mp hf

end

section

open Set

theorem integralBoundedStarConvexLocalHomologyIso_cap_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2)
    {K : Set E} (h0 : (0 : E) ∈ K) (hs : StarConvex ℝ 0 K) (hK : Bornology.IsBounded K) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) Kᶜ =>
      integralRelativeCohomologyCapToAbsolute Kᶜ (n + 2) 0 α
        ((integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv.symm
          ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1))) := by
  let hf : MapsTo (ContinuousMap.id E) Kᶜ ({0}ᶜ : Set E) :=
    compl_subset_compl.mpr (singleton_subset_iff.mpr h0)
  let e := boundedStarConvexComplementHomotopyEquiv h0 hs hK
  have he : singularPairRestriction (ContinuousMap.id E) hf = e.toFun := by
    rw [boundedStarConvexComplementHomotopyEquiv_toFun]
    rfl
  have hcoh : Function.Bijective
      (integralRelativeCohomologyMap (n + 2) (ContinuousMap.id E) hf) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro k
      rw [integralSingularCohomologyMap_id]
      exact Function.bijective_id
    · intro k
      rw [he]
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv e k
  let i := (integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv
  let c0 := (integralEuclideanLocalTopZeroEquiv E n hd).symm 1
  let c := i.symm c0
  have hc : integralRelativeHomologyMap (n + 2) (ContinuousMap.id E) hf c = c0 := by
    change i c = c0
    exact i.apply_symm_apply c0
  let f := fun α : integralRelativeCohomology (n + 2) Kᶜ =>
    integralRelativeCohomologyCapToAbsolute Kᶜ (n + 2) 0 α c
  have hcap : f ∘ integralRelativeCohomologyMap (n + 2) (ContinuousMap.id E) hf =
      fun β : integralRelativeCohomology (n + 2) ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (n + 2) 0 β c0 := by
    funext β
    have hn := integralRelativeCohomologyCapToAbsolute_natural (n + 2) 0
      (ContinuousMap.id E) hf β c
    rw [integralSingularHomologyMap_id] at hn
    change f (integralRelativeCohomologyMap (n + 2) (ContinuousMap.id E) hf β) =
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (n + 2) 0 β
        (integralRelativeHomologyMap (n + 2) (ContinuousMap.id E) hf c) at hn
    rw [hc] at hn
    exact hn
  apply (Function.Bijective.of_comp_iff f hcoh).mp
  rw [hcap]
  exact integralEuclideanLocalTopZeroEquiv_cap_bijective n E hd

end

end Poincare.Topology

end
