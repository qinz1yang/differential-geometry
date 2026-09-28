/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarSourceCharts

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}
  {E : Type*} [TopologicalSpace E] [T2Space E]

open Classical in
theorem exists_branch_sections_of_compact_source_sheets
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {ι : M → E} (hιc : Continuous ι) (hι : Function.Injective ι)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : hD.branchPreimage c = J)
    (a₀ : hD.branchPreimage c) {I : Type*}
    (A : I → Bool → Set (EuclideanSpace ℝ (Fin 2))) (W : I → Set E)
    (hAc : ∀ i b, IsCompact (A i b)) (hAdom : ∀ i b, A i b ⊆ D.domain)
    (hAi : ∀ i b, InjOn D (A i b)) (hAA : ∀ i, Disjoint (A i false) (A i true))
    (hpre : ∀ i, ∀ x ∈ D.domain, ι (D x) ∈ W i → x ∈ A i false ∪ A i true)
    (hcore : ∀ i b, ∀ y ∈ hD.singularSet.branchCarrier c,
      ι y ∈ W i → y ∈ D '' (A i b ∩ J)) :
    ∃ s : I → Bool → (hD.singularSet.branchComplex c).space → hD.branchPreimage c,
      (∀ i b, ContinuousOn (s i b)
        {y | ι ((hD.singularSet.branchPieceIn c).map y) ∈ W i}) ∧
      (∀ i b (y : (hD.singularSet.branchComplex c).space),
      ι ((hD.singularSet.branchPieceIn c).map y) ∈ W i →
        ((s i b y : hD.branchPreimage c) : EuclideanSpace ℝ (Fin 2)) ∈ A i b ∧
          hD.branchProjection c (s i b y) = y) ∧
      (∀ i (y : (hD.singularSet.branchComplex c).space),
      ι ((hD.singularSet.branchPieceIn c).map y) ∈ W i →
        s i false y ≠ s i true y) ∧
      ∀ i (y : (hD.singularSet.branchComplex c).space),
        ι ((hD.singularSet.branchPieceIn c).map y) ∈ W i →
        ∀ x : hD.branchPreimage c, hD.branchProjection c x = y →
          x = s i false y ∨ x = s i true y := by
  let P := hD.singularSet.branchPieceIn c
  let f := ι ∘ D
  let F : (hD.singularSet.branchComplex c).space → E := fun y => ι (P.map y)
  have hFc : Continuous F := hιc.comp P.continuousOn.domRestrict
  have hfi : ∀ i b, InjOn f (A i b) := fun i b x hx y hy hxy => hAi i b hx hy (hι hxy)
  have hf : ∀ i b, ContinuousOn f (A i b) :=
    fun i b => hιc.comp_continuousOn (D.continuousOn.mono (hAdom i b))
  have hsurj : ∀ i b y, F y ∈ W i → F y ∈ f '' A i b := by
    intro i b y hy
    obtain ⟨x, hx, hxy⟩ := hcore i b (P.map y) (P.bijOn.mapsTo y.2) hy
    exact ⟨x, hx.1, congrArg ι hxy⟩
  have hinvmem : ∀ i b y, F y ∈ W i → Function.invFunOn f (A i b) (F y) ∈ hD.branchPreimage c := by
    intro i b y hy
    obtain ⟨x, hx, hxy⟩ := hcore i b (P.map y) (P.bijOn.mapsTo y.2) hy
    have hinv : Function.invFunOn f (A i b) (F y) = x := by
      have heq : f x = F y := congrArg ι hxy
      rw [← heq]
      exact (hfi i b).leftInvOn_invFunOn hx.1
    rw [hinv, hJ]
    exact hx.2
  let s : I → Bool → (hD.singularSet.branchComplex c).space → hD.branchPreimage c :=
    fun i b y => if hy : F y ∈ W i then
      ⟨Function.invFunOn f (A i b) (F y), hinvmem i b y hy⟩ else a₀
  have hsval : ∀ i b y, F y ∈ W i →
      (s i b y : EuclideanSpace ℝ (Fin 2)) = Function.invFunOn f (A i b) (F y) :=
    fun i b y hy => by simp only [s, dite_eq_left hy]
  have hsA : ∀ i b y, F y ∈ W i → (s i b y : EuclideanSpace ℝ (Fin 2)) ∈ A i b := by
    intro i b y hy
    rw [hsval i b y hy]
    exact Function.invFunOn_mem (hsurj i b y hy)
  have hsD : ∀ i b y, F y ∈ W i → D (s i b y : EuclideanSpace ℝ (Fin 2)) = P.map y := by
    intro i b y hy
    apply hι
    rw [hsval i b y hy]
    exact Function.invFunOn_eq (hsurj i b y hy)
  have hpD : ∀ x : hD.branchPreimage c,
      P.map (hD.branchProjection c x) = D (x : EuclideanSpace ℝ (Fin 2)) :=
    fun x => hD.branchPieceIn_map_branchCoordinate c x.2
  have hssec : ∀ i b y, F y ∈ W i → hD.branchProjection c (s i b y) = y := by
    intro i b y hy
    apply Subtype.ext
    exact P.bijOn.injOn (hD.branchProjection c (s i b y)).2 y.2
      ((hpD _).trans (hsD i b y hy))
  refine ⟨s, ?_, fun i b y hy => ⟨hsA i b y hy, hssec i b y hy⟩, ?_, ?_⟩
  · intro i b
    have hinvc : ContinuousOn (Function.invFunOn f (A i b)) (f '' A i b) :=
      continuousOn_invFunOn_of_isCompact_of_forall_eq (hAc i b) (hf i b) (Subset.refl _)
        (fun x hx y hy hxy _ => hfi i b hx hy hxy)
    have hvalc : ContinuousOn (fun y => (s i b y : EuclideanSpace ℝ (Fin 2)))
        {y | F y ∈ W i} :=
      (hinvc.comp hFc.continuousOn (fun y hy => hsurj i b y hy)).congr
        (fun y hy => hsval i b y hy)
    exact continuousOn_iff_continuous_domRestrict.mpr (hvalc.domRestrict.subtype_mk _)
  · intro i y hy heq
    exact disjoint_left.mp (hAA i) (hsA i false y hy)
      (congrArg Subtype.val heq ▸ hsA i true y hy)
  · intro i y hy x hxy
    have hDx : D (x : EuclideanSpace ℝ (Fin 2)) = P.map y := by
      rw [← hpD x, hxy]
    have hFx : f (x : EuclideanSpace ℝ (Fin 2)) = F y := congrArg ι hDx
    have hxW : ι (D x) ∈ W i := by
      change f (x : EuclideanSpace ℝ (Fin 2)) ∈ W i
      rw [hFx]
      exact hy
    rcases hpre i x x.2.1 hxW with hx | hx
    · exact Or.inl (Subtype.ext (hAi i false hx (hsA i false y hy)
        (hDx.trans (hsD i false y hy).symm)))
    · exact Or.inr (Subtype.ext (hAi i true hx (hsA i true y hy)
        (hDx.trans (hsD i true y hy).symm)))

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
