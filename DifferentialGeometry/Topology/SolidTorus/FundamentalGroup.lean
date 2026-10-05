import DifferentialGeometry.Topology.SolidTorus.Spine
import DifferentialGeometry.Topology.SolidTorus.Shell
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Int.Cast.Lemmas

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem fundamentalGroup_map_inclusion_bijective_of_isSpine
    {S J : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsSpine S J) (hJS : J ⊆ S) :
    ∀ x : J, Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) x) := by
  obtain ⟨e, hri⟩ := IsSpine.exists_homotopyEquiv_leftInverse hJ hJS
  intro x
  let i : C(J, S) :=
    ⟨Set.inclusion hJS, continuous_inclusion hJS⟩
  have hi := _root_.DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_leftInverse
    i e.toFun hri x
  have he :=
    _root_.DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
      e (i x) x (hri x)
  refine ⟨hi.injective, ?_⟩
  intro a
  exact ⟨FundamentalGroup.mapOfEq e.toFun (hri x) a, he.1 (hi _)⟩

private theorem fundamentalGroup_map_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  apply MonoidHom.ext
  intro p
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk (p.map (g.comp f).continuous) =
      Path.Homotopic.Quotient.mk ((p.map f.continuous).map g.continuous)
    congr 1

private theorem subset_of_isSpine
    {S J : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsSpine S J) : J ⊆ S := by
  obtain ⟨φ, _p, _hp, hJset⟩ := hJ
  intro x hx
  rw [hJset] at hx
  obtain ⟨_y, ⟨q, _hq, _hqφ⟩, _hxy⟩ := hx
  rw [← _hxy, ← _hqφ]
  exact (φ q).property

private theorem bijective_addMonoidHom_of_generator_eq
    (f : ℤ →+ ℤ) (h : f 1 = 1 ∨ f 1 = -1) : Function.Bijective f := by
  rcases h with h | h
  · have hf : f = AddMonoidHom.id ℤ := AddMonoidHom.ext_int h
    rw [hf]
    exact Function.bijective_id
  · constructor
    · intro x y hxy
      have h' := congrArg (fun z : ℤ => -z) hxy
      simpa [AddMonoidHom.apply_int, h] using h'
    · intro y
      refine ⟨-y, ?_⟩
      simp [AddMonoidHom.apply_int, h]

private theorem bijective_addMonoidHoms_of_bijective_comp
    (f g : ℤ →+ ℤ) (hcomp : Function.Bijective (g.comp f)) :
    Function.Bijective f ∧ Function.Bijective g := by
  obtain ⟨n, hn⟩ := hcomp.2 1
  have hpow : (g.comp f) n = n * (g.comp f) 1 := by
    rw [AddMonoidHom.apply_int]
    simp
  have hprod : (g.comp f) 1 * n = 1 := by
    calc
      (g.comp f) 1 * n = n * (g.comp f) 1 := mul_comm _ _
      _ = (g.comp f) n := hpow.symm
      _ = 1 := hn
  have hgen : (g.comp f) 1 = 1 ∨ (g.comp f) 1 = -1 := by
    exact Int.eq_one_or_neg_one_of_mul_eq_one hprod
  have hfactor : f 1 * g 1 = 1 ∨ f 1 * g 1 = -1 := by
    have hfg : g (f 1) = f 1 * g 1 := by
      rw [AddMonoidHom.apply_int]
      simp
    rcases hgen with h | h
    · exact Or.inl (hfg.symm.trans h)
    · exact Or.inr (hfg.symm.trans h)
  have hfgen : f 1 = 1 ∨ f 1 = -1 := by
    rcases hfactor with h | h
    · exact (Int.eq_one_or_neg_one_of_mul_eq_one' h).elim
        (fun q => Or.inl q.1) (fun q => Or.inr q.1)
    · exact (Int.eq_one_or_neg_one_of_mul_eq_neg_one' h).elim
        (fun q => Or.inl q.1) (fun q => Or.inr q.1)
  have hggen : g 1 = 1 ∨ g 1 = -1 := by
    rcases hfactor with h | h
    · exact (Int.eq_one_or_neg_one_of_mul_eq_one' h).elim
        (fun q => Or.inl q.2) (fun q => Or.inr q.2)
    · exact (Int.eq_one_or_neg_one_of_mul_eq_neg_one' h).elim
        (fun q => Or.inr q.2) (fun q => Or.inl q.2)
  exact ⟨bijective_addMonoidHom_of_generator_eq f hfgen,
    bijective_addMonoidHom_of_generator_eq g hggen⟩

private theorem bijective_cyclicMonoidHoms_of_bijective_comp
    (f g : Multiplicative ℤ →* Multiplicative ℤ)
    (hcomp : Function.Bijective (g.comp f)) :
    Function.Bijective f ∧ Function.Bijective g := by
  let fa : ℤ →+ ℤ := MonoidHom.toAdditiveRight f
  let ga : ℤ →+ ℤ := MonoidHom.toAdditiveRight g
  have hfg : MonoidHom.toAdditiveRight (g.comp f) = ga.comp fa := by
    apply AddMonoidHom.ext_int
    rfl
  have hcomp' : Function.Bijective (ga.comp fa) := by
    rw [← hfg]
    exact hcomp
  obtain ⟨hfa, hga⟩ := bijective_addMonoidHoms_of_bijective_comp fa ga hcomp'
  have hf : Function.Bijective f := by
    have heq : (f : Multiplicative ℤ → Multiplicative ℤ) =
        (Multiplicative.ofAdd : ℤ → Multiplicative ℤ) ∘ fa ∘
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) := by
      rfl
    rw [heq]
    exact Multiplicative.ofAdd.bijective.comp
      (hfa.comp Multiplicative.toAdd.bijective)
  have hg : Function.Bijective g := by
    have heq : (g : Multiplicative ℤ → Multiplicative ℤ) =
        (Multiplicative.ofAdd : ℤ → Multiplicative ℤ) ∘ ga ∘
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) := by
      rfl
    rw [heq]
    exact Multiplicative.ofAdd.bijective.comp
      (hga.comp Multiplicative.toAdd.bijective)
  exact ⟨hf, hg⟩

private theorem bijective_of_cyclic_conjugate
    {G H : Type} [Group G] [Group H]
    (eG : G ≃* Multiplicative ℤ) (eH : H ≃* Multiplicative ℤ)
    (f : G →* H)
    (hf : Function.Bijective
      (eH.toMonoidHom.comp (f.comp eG.symm.toMonoidHom))) :
    Function.Bijective f := by
  let f' := eH.toMonoidHom.comp (f.comp eG.symm.toMonoidHom)
  have heq : (f : G → H) =
      (eH.symm : Multiplicative ℤ → H) ∘ f' ∘
        (eG : G → Multiplicative ℤ) := by
    funext x
    simp [f']
  rw [heq]
  exact eH.symm.bijective.comp (hf.comp eG.bijective)

private theorem bijective_of_cyclic_factorization
    {G H K : Type} [Group G] [Group H] [Group K]
    (eG : G ≃* Multiplicative ℤ) (eH : H ≃* Multiplicative ℤ)
    (eK : K ≃* Multiplicative ℤ) (f : G →* H) (g : H →* K)
    (hcomp : Function.Bijective (g.comp f)) :
    Function.Bijective f ∧ Function.Bijective g := by
  let f' := eH.toMonoidHom.comp (f.comp eG.symm.toMonoidHom)
  let g' := eK.toMonoidHom.comp (g.comp eH.symm.toMonoidHom)
  have hconj : Function.Bijective (g'.comp f') := by
    have heq : g'.comp f' =
        eK.toMonoidHom.comp ((g.comp f).comp eG.symm.toMonoidHom) := by
      apply MonoidHom.ext
      intro z
      simp [f', g']
    rw [heq]
    exact eK.bijective.comp (hcomp.comp eG.symm.bijective)
  obtain ⟨hf', hg'⟩ := bijective_cyclicMonoidHoms_of_bijective_comp f' g' hconj
  exact ⟨bijective_of_cyclic_conjugate eG eH f hf',
    bijective_of_cyclic_conjugate eH eK g hg'⟩

open Classical in
private theorem isCompact_of_isTopologicalSolidTorus_nested
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S) :
    IsCompact S := by
  let φ : S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := Classical.choice hS
  let _ : CompactSpace S := φ.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

open Classical in
theorem fundamentalGroup_map_inclusion_bijective_of_nested
    {S₁ S S₂ J : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsTopologicalSolidTorus S₁) (hS₂ : IsTopologicalSolidTorus S₂)
    (hS : IsTopologicalSolidTorus S) (hS₁S : S₁ ⊆ interior S)
    (hSS₂ : S ⊆ interior S₂)
    (hshell : IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂))
    (hJ : IsSpine S₁ J) :
    ∀ hJS : J ⊆ S, ∀ x : J,
      Function.Bijective (FundamentalGroup.map
        (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) x) := by
  intro hJS x
  let hJ₁ : J ⊆ S₁ := subset_of_isSpine hJ
  let h₁S : S₁ ⊆ S := fun y hy => interior_subset (hS₁S hy)
  let hSsub₂ : S ⊆ S₂ := fun y hy => interior_subset (hSS₂ hy)
  let h₁₂ : S₁ ⊆ interior S₂ := fun y hy => hSS₂ (h₁S hy)
  let iJ₁ : C(J, S₁) := ⟨Set.inclusion hJ₁, continuous_inclusion hJ₁⟩
  let i₁₂ : C(S₁, S₂) :=
    ⟨Set.inclusion (h₁₂.trans interior_subset),
      continuous_inclusion (h₁₂.trans interior_subset)⟩
  let iJS : C(J, S) := ⟨Set.inclusion hJS, continuous_inclusion hJS⟩
  let iSS₂ : C(S, S₂) := ⟨Set.inclusion hSsub₂, continuous_inclusion hSsub₂⟩
  let iJ₂ : C(J, S₂) := iSS₂.comp iJS
  have hiJ₁ : Function.Bijective (FundamentalGroup.map iJ₁ x) :=
    fundamentalGroup_map_inclusion_bijective_of_isSpine hJ hJ₁ x
  have hclosed₁ : IsClosed S₁ :=
    (isCompact_of_isTopologicalSolidTorus_nested hS₁).isClosed
  have hclosed₂ : IsClosed S₂ :=
    (isCompact_of_isTopologicalSolidTorus_nested hS₂).isClosed
  obtain ⟨eShell, heShell⟩ :=
    exists_homotopyEquiv_leftInverse_inclusion_of_isToroidalShell hclosed₁ hclosed₂ h₁₂ hshell
  have hi₁₂ : Function.Bijective (FundamentalGroup.map i₁₂ (iJ₁ x)) :=
    DifferentialGeometry.Topology.bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
      eShell i₁₂ heShell (iJ₁ x)
  have hiJ₂ : Function.Bijective (FundamentalGroup.map iJ₂ x) := by
    have heq : i₁₂.comp iJ₁ = iJ₂ := by
      apply ContinuousMap.ext
      intro z
      rfl
    rw [← heq, fundamentalGroup_map_comp]
    exact hi₁₂.comp hiJ₁
  obtain ⟨eSpine, heSpine⟩ := IsSpine.exists_homotopyEquiv_leftInverse hJ hJ₁
  let eJ : FundamentalGroup J x ≃* Multiplicative ℤ :=
    (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      eSpine.symm x (eSpine.symm x) rfl).trans
      (IsTopologicalSolidTorus.fundamentalGroupEquivInt hS₁ (eSpine.symm x))
  let eS : FundamentalGroup S (iJS x) ≃* Multiplicative ℤ :=
    IsTopologicalSolidTorus.fundamentalGroupEquivInt hS (iJS x)
  let eS₂ : FundamentalGroup S₂ (iJ₂ x) ≃* Multiplicative ℤ :=
    IsTopologicalSolidTorus.fundamentalGroupEquivInt hS₂ (iJ₂ x)
  let f : FundamentalGroup J x →* FundamentalGroup S (iJS x) :=
    FundamentalGroup.map iJS x
  let g : FundamentalGroup S (iJS x) →* FundamentalGroup S₂ (iJ₂ x) :=
    FundamentalGroup.map iSS₂ (iJS x)
  have hfg : Function.Bijective f ∧ Function.Bijective g := by
    apply bijective_of_cyclic_factorization eJ eS eS₂ f g
    have heq : g.comp f = FundamentalGroup.map iJ₂ x := by
      simpa [f, g, iJ₂] using (fundamentalGroup_map_comp iJS iSS₂ x).symm
    rw [heq]
    exact hiJ₂
  exact hfg.1

open Classical in
theorem fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus
    {S T J : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsTopologicalSolidTorus S) (hT : IsTopologicalSolidTorus T)
    (hST : S ⊆ interior T) (hJ : IsSpine T J) (hJS : J ⊆ S) :
    ∀ x : J, Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) x) := by
  intro x
  let hJT : J ⊆ T := hJS.trans (hST.trans interior_subset)
  let hST' : S ⊆ T := hST.trans interior_subset
  let iJS : C(J, S) := ⟨Set.inclusion hJS, continuous_inclusion hJS⟩
  let iST : C(S, T) := ⟨Set.inclusion hST', continuous_inclusion hST'⟩
  let iJT : C(J, T) := iST.comp iJS
  have hiJT : Function.Bijective (FundamentalGroup.map iJT x) := by
    have hi := fundamentalGroup_map_inclusion_bijective_of_isSpine hJ hJT x
    have heq :
        (⟨Set.inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)) = iJT := by
      apply ContinuousMap.ext
      intro z
      rfl
    rw [← heq]
    exact hi
  obtain ⟨eSpine, _heSpine⟩ := IsSpine.exists_homotopyEquiv_leftInverse hJ hJT
  let eJ : FundamentalGroup J x ≃* Multiplicative ℤ :=
    (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      eSpine.symm x (eSpine.symm x) rfl).trans
      (IsTopologicalSolidTorus.fundamentalGroupEquivInt hT (eSpine.symm x))
  let eS : FundamentalGroup S (iJS x) ≃* Multiplicative ℤ :=
    IsTopologicalSolidTorus.fundamentalGroupEquivInt hS (iJS x)
  let eT : FundamentalGroup T (iJT x) ≃* Multiplicative ℤ :=
    IsTopologicalSolidTorus.fundamentalGroupEquivInt hT (iJT x)
  let f : FundamentalGroup J x →* FundamentalGroup S (iJS x) :=
    FundamentalGroup.map iJS x
  let g : FundamentalGroup S (iJS x) →* FundamentalGroup T (iJT x) :=
    FundamentalGroup.map iST (iJS x)
  have hfg : Function.Bijective f ∧ Function.Bijective g := by
    apply bijective_of_cyclic_factorization eJ eS eT f g
    have heq : g.comp f = FundamentalGroup.map iJT x := by
      simpa [f, g, iJT] using (fundamentalGroup_map_comp iJS iST x).symm
    rw [heq]
    exact hiJT
  exact hfg.1

end DifferentialGeometry.Topology.PiecewiseLinear
