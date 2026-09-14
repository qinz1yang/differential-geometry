import Poincare.Algebra.Pairing
import Poincare.Topology.Homology.OneDimensionalLocalCapDuality
import Poincare.Topology.Homology.RelativeEmpty
import Poincare.Topology.Homology.ConnectedZeroCohomology
import Poincare.Topology.Homology.SphereCapDuality
import Poincare.Topology.Homology.EuclideanLocalTop
import Poincare.Topology.Homology.RelativeCapCohomologyConnecting
import Poincare.Topology.Homology.EuclideanLocalCohomologyVanishing

noncomputable section

universe u

namespace Poincare.Topology

section

open Set Metric

private theorem integralEuclideanLocalTopZeroEquiv_cap_top_bijective
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

private theorem integralBoundedStarConvexLocalHomologyIso_cap_top_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2)
    {K : Set E} (h0 : (0 : E) ∈ K) (hs : StarConvex ℝ 0 K) (hK : Bornology.IsBounded K) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) Kᶜ =>
      integralRelativeCohomologyCapToAbsolute Kᶜ (n + 2) 0 α
        ((integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv.symm
          ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1))) := by
  let hf : MapsTo (ContinuousMap.id E) Kᶜ ({0}ᶜ : Set E) :=
    compl_subset_compl.mpr (singleton_subset_iff.mpr h0)
  have hcoh : Function.Bijective
      (integralRelativeCohomologyMap (n + 2) (ContinuousMap.id E) hf) :=
    integralRelativeCohomologyMap_boundedStarConvex_bijective (n + 2) h0 hs hK
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
  exact integralEuclideanLocalTopZeroEquiv_cap_top_bijective n E hd

end

section

open CategoryTheory Metric Module Set

theorem integralEuclideanLocalTopZeroEquiv_cap_bijective_of_add_eq
    (n k m : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : finrank ℝ E = n + 2) (hkm : k + m = n + 2) :
    Function.Bijective (fun α : integralRelativeCohomology k ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) k m α
        ((eqToHom (congrArg (fun j => integralRelativeHomology j ({0}ᶜ : Set E)) hkm.symm))
          ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1))) := by
  by_cases hm : m = 0
  · subst m
    have hk : k = n + 2 := by omega
    subst k
    exact integralEuclideanLocalTopZeroEquiv_cap_top_bijective n E hd
  let _ := integralEuclideanRelativeCohomology_subsingleton n k E hd (by omega)
  let _ := integralSingularHomology_subsingleton_of_contractible m hm E
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun β => ⟨0, Subsingleton.elim _ β⟩⟩

theorem integralBoundedStarConvexLocalHomologyIso_cap_bijective_of_add_eq
    (n k m : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : finrank ℝ E = n + 2) (hkm : k + m = n + 2)
    {K : Set E} (h0 : (0 : E) ∈ K) (hs : StarConvex ℝ 0 K) (hK : Bornology.IsBounded K) :
    Function.Bijective (fun α : integralRelativeCohomology k Kᶜ =>
      integralRelativeCohomologyCapToAbsolute Kᶜ k m α
        ((eqToHom (congrArg (fun j => integralRelativeHomology j Kᶜ) hkm.symm))
          ((integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv.symm
            ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1)))) := by
  by_cases hm : m = 0
  · subst m
    have hk : k = n + 2 := by omega
    subst k
    exact integralBoundedStarConvexLocalHomologyIso_cap_top_bijective n E hd h0 hs hK
  let _ := integralBoundedStarConvexRelativeCohomology_subsingleton n k E hd (by omega) h0 hs hK
  let _ := integralSingularHomology_subsingleton_of_contractible m hm E
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun β => ⟨0, Subsingleton.elim _ β⟩⟩

end

section

open CategoryTheory Metric Module Set

private theorem exists_innerProduct_local_top_cap_bijective
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ c : integralLocalHomology (finrank ℝ E) (0 : E),
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (finrank ℝ E) 0 α c) := by
  by_cases hlarge : 2 ≤ finrank ℝ E
  · have hd : finrank ℝ E = (finrank ℝ E - 2) + 2 := by omega
    rw [hd]
    exact ⟨(integralEuclideanLocalTopZeroEquiv E (finrank ℝ E - 2) hd).symm 1,
      integralEuclideanLocalTopZeroEquiv_cap_top_bijective (finrank ℝ E - 2) E hd⟩
  by_cases hzero : finrank ℝ E = 0
  · have hempty : ({0}ᶜ : Set E) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hx (finrank_zero_iff_forall_zero.mp hzero x)).elim
      · intro hx
        exact hx.elim
    change ∃ c : integralRelativeHomology (finrank ℝ E) ({0}ᶜ : Set E),
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (finrank ℝ E) 0 α c)
    rw [hzero, hempty]
    let e := integralSingularHomologyZeroEquiv (X := E)
    let c := e.symm 1
    have hc : Function.Bijective (fun z : ℤ => z • c) := by
      have hfun : (fun z : ℤ => z • c) = e.symm := by
        funext z
        change z • e.symm 1 = e.symm z
        rw [← map_zsmul]
        congr 1
        exact mul_one z
      rw [hfun]
      exact e.symm.bijective
    have hcap : Function.Bijective (fun α : integralSingularCohomology 0 E =>
        integralSingularCohomologyCapProduct 0 0 α c) :=
      (integralSingularCohomologyCapProduct_zero_bijective_iff 0 c).mpr hc
    refine ⟨integralAbsoluteToRelative 0 (∅ : Set E) c, ?_⟩
    have hfun : (fun α : integralRelativeCohomology 0 (∅ : Set E) =>
        integralRelativeCohomologyCapToAbsolute (∅ : Set E) 0 0 α
          (integralAbsoluteToRelative 0 (∅ : Set E) c)) =
        (fun α : integralSingularCohomology 0 E =>
          integralSingularCohomologyCapProduct 0 0 α c) ∘
            integralRelativeToAbsoluteCohomology 0 (∅ : Set E) := by
      funext α
      exact integralRelativeCohomologyCapToAbsolute_absoluteToRelative (∅ : Set E) 0 0 α c
    rw [hfun]
    exact hcap.comp (integralRelativeToAbsoluteCohomologyEmptyEquiv 0 E).bijective
  have hone : finrank ℝ E = 1 := by omega
  change ∃ c : integralRelativeHomology (finrank ℝ E) ({0}ᶜ : Set E),
    Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
        ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (finrank ℝ E) 0 α c)
  rw [hone]
  exact exists_integralLocalHomology_cap_bijective_of_finrank_one E hone

private theorem exists_normed_local_top_cap_bijective
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) :
    ∃ c : integralLocalHomology (finrank ℝ E) p,
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({p}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (finrank ℝ E) 0 α c) := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    b.equivFunL.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let h := e.symm.toHomeomorph.trans (Homeomorph.addRight p)
  have hp : h 0 = p := by
    change e.symm 0 + p = p
    rw [map_zero, zero_add]
  have hex : ∃ c : integralLocalHomology (finrank ℝ E) (0 : EuclideanSpace ℝ ι),
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({0}ᶜ : Set (EuclideanSpace ℝ ι)) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set (EuclideanSpace ℝ ι))
          (finrank ℝ E) 0 α c) := by
    rw [e.toLinearEquiv.finrank_eq]
    exact exists_innerProduct_local_top_cap_bijective (EuclideanSpace ℝ ι)
  let f : ContinuousMap (EuclideanSpace ℝ ι) E := ⟨h, h.continuous⟩
  have hf : MapsTo f ({0}ᶜ : Set (EuclideanSpace ℝ ι)) ({h 0}ᶜ : Set E) :=
    fun _ hx => h.injective.ne hx
  let g := h.subtype (p := fun x : EuclideanSpace ℝ ι => x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ ι)))
    (q := fun y : E => y ∈ ({h 0}ᶜ : Set E)) (fun x => h.injective.ne_iff.symm)
  have hcoh : Function.Bijective (integralRelativeCohomologyMap (finrank ℝ E) f hf) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro n
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv h.toHomotopyEquiv n
    · intro n
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv g.toHomotopyEquiv n
  obtain ⟨c, hc⟩ := hex
  have hcap := integralRelativeCohomologyCapToAbsolute_bijective_map (finrank ℝ E) 0 f hf
    (integralSingularHomologyZeroMapEquiv f).bijective hcoh c hc
  have hout : ∃ d : integralLocalHomology (finrank ℝ E) (h 0),
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({h 0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({h 0}ᶜ : Set E) (finrank ℝ E) 0 α d) :=
    ⟨integralRelativeHomologyMap (finrank ℝ E) f hf c, hcap⟩
  rwa [hp] at hout

theorem integralLocalHomology_cap_bijective_of_generator
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) (c : integralLocalHomology (finrank ℝ E) p)
    (hc : Function.Bijective (fun z : ℤ => z • c)) :
    Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E) ({p}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (finrank ℝ E) 0 α c) := by
  let f : ℤ →+ integralLocalHomology (finrank ℝ E) p :=
    { toFun := fun z => z • c
      map_zero' := zero_zsmul c
      map_add' := fun z w => add_zsmul c z w }
  let e := (AddEquiv.ofBijective f hc).symm
  have he : e.symm 1 = c := one_zsmul c
  obtain ⟨d, hd⟩ := exists_normed_local_top_cap_bijective p
  let B := fun α : integralRelativeCohomology (finrank ℝ E) ({p}ᶜ : Set E) =>
    integralZeroAugmentation.toAddMonoidHom.comp
      ((integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (finrank ℝ E) 0 α).toAddMonoidHom)
  have hdB : Function.Bijective (fun α => B α d) :=
    integralConnectedZeroAugmentationEquiv.bijective.comp hd
  have h := additive_pairing_bijective_at_generator B e d hdB
  rw [he] at h
  exact (Function.Bijective.of_comp_iff' integralConnectedZeroAugmentationEquiv.bijective _).mp h

end

theorem integralEuclideanLocalTopZeroEquiv_cap_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (n + 2) 0 α
        ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1)) := by
  let e := integralEuclideanLocalTopZeroEquiv E n hd
  have hc : Function.Bijective (fun z : ℤ => z • e.symm 1) := by
    have heq : (fun z : ℤ => z • e.symm 1) = e.symm := by
      funext z
      rw [← map_zsmul]
      congr 1
      exact mul_one z
    rw [heq]
    exact e.symm.bijective
  have hcap : ∀ c : integralRelativeHomology (Module.finrank ℝ E) ({0}ᶜ : Set E),
      Function.Bijective (fun z : ℤ => z • c) →
      Function.Bijective (fun α : integralRelativeCohomology (Module.finrank ℝ E) ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (Module.finrank ℝ E) 0 α c) :=
    integralLocalHomology_cap_bijective_of_generator (0 : E)
  rw [hd] at hcap
  exact hcap (e.symm 1) hc

theorem integralBoundedStarConvexLocalHomologyIso_cap_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2)
    {K : Set E} (h0 : (0 : E) ∈ K) (hs : StarConvex ℝ 0 K) (hK : Bornology.IsBounded K) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) Kᶜ =>
      integralRelativeCohomologyCapToAbsolute Kᶜ (n + 2) 0 α
        ((integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv.symm
          ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1))) :=
  integralBoundedStarConvexLocalHomologyIso_cap_bijective_of_add_eq n (n + 2) 0 E hd rfl h0 hs hK

end Poincare.Topology

end
