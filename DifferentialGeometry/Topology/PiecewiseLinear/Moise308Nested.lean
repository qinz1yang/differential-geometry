/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.Moise308NestedShell
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorus
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.Homotopy.ConvexProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Piecewise

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

private abbrev DiskModel := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
private abbrev CircleModel := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

private noncomputable def circleModelHomeomorph : Circle ≃ₜ CircleModel := by
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  refine
    { toFun := fun z =>
        ⟨e z, by
          apply mem_sphere_zero_iff_norm.mpr
          rw [e.norm_map]
          exact Circle.norm_coe z⟩
      invFun := fun y =>
        ⟨e.symm y, by
          change e.symm (y : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere (0 : ℂ) 1
          apply mem_sphere_zero_iff_norm.mpr
          rw [e.symm.norm_map]
          exact mem_sphere_zero_iff_norm.mp y.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact e.symm_apply_apply z
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

private noncomputable def fundamentalGroupSolidTorusEquivInt
  {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S) (x : S) :
    FundamentalGroup S x ≃* Multiplicative ℤ := by
  let φ : S ≃ₜ (DiskModel × CircleModel) := Classical.choice hS
  let p : DiskModel := ⟨0, by simp⟩
  let e₁ : S ≃ₕ (DiskModel × CircleModel) := φ.toHomotopyEquiv
  let e₂ : (DiskModel × CircleModel) ≃ₕ (CircleModel × DiskModel) :=
    (Homeomorph.prodComm DiskModel CircleModel).toHomotopyEquiv
  let e₃ : (CircleModel × DiskModel) ≃ₕ CircleModel :=
    DifferentialGeometry.HomotopyEquiv.productConvex CircleModel
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) p
  let e₄ : CircleModel ≃ₕ Circle := circleModelHomeomorph.symm.toHomotopyEquiv
  let e := e₁.trans (e₂.trans (e₃.trans e₄))
  let q : Path (e x) (1 : Circle) := PathConnectedSpace.somePath _ _
  exact
    (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
        e x (e x) rfl).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath q).trans
        DifferentialGeometry.Topology.fundamentalGroupCircleEquivInt)

open Classical in
private theorem spine_homotopy_equiv
    {S J : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsSpine S J) (hJS : J ⊆ S) :
    ∃ (e : S ≃ₕ J), Function.LeftInverse e
      (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) := by
  obtain ⟨φ, p, hp, hJset⟩ := hJ
  let p' : DiskModel := ⟨p, interior_subset hp⟩
  let i : C(J, S) :=
    ⟨Set.inclusion hJS, continuous_inclusion hJS⟩
  let j : CircleModel ≃ₜ J :=
    { toFun := fun q =>
        ⟨(φ (p', q) : EuclideanSpace ℝ (Fin 3)), by
          rw [hJset]
          exact ⟨φ (p', q), ⟨(p', q), rfl, rfl⟩, rfl⟩⟩
      invFun := fun y =>
        (φ.symm (⟨(y : EuclideanSpace ℝ (Fin 3)), hJS y.property⟩ : S)).2
      left_inv := by
        intro q
        apply Subtype.ext
        change ((φ.symm (φ (p', q))).2 : EuclideanSpace ℝ (Fin 2)) = q
        exact congrArg Subtype.val (congrArg Prod.snd (φ.symm_apply_apply (p', q)))
      right_inv := by
        intro y
        let ys : S := ⟨(y : EuclideanSpace ℝ (Fin 3)), hJS y.property⟩
        have hy : (y : EuclideanSpace ℝ (Fin 3)) ∈
            Subtype.val '' (φ '' {q | q.1 = p}) := hJset ▸ y.property
        obtain ⟨z, ⟨q, hq, hqφ⟩, hyz⟩ := hy
        have hzy : z = ys := by
          apply Subtype.ext
          exact hyz
        have hqeq : q = φ.symm ys := by
          apply φ.injective
          rw [φ.apply_symm_apply]
          exact hqφ.trans hzy
        have hqp : q.1 = p' := Subtype.ext hq
        have harg : (p', (φ.symm ys).2) = q := by
          apply Prod.ext
          · exact hqp.symm
          · exact (congrArg Prod.snd hqeq).symm
        apply Subtype.ext
        change (φ (p', (φ.symm ys).2) : EuclideanSpace ℝ (Fin 3)) = y
        rw [harg]
        exact (congrArg Subtype.val hqφ).trans hyz }
  let e₁ : S ≃ₕ (DiskModel × CircleModel) := φ.symm.toHomotopyEquiv
  let e₂ : (DiskModel × CircleModel) ≃ₕ (CircleModel × DiskModel) :=
    (Homeomorph.prodComm DiskModel CircleModel).toHomotopyEquiv
  let e₃ : (CircleModel × DiskModel) ≃ₕ CircleModel :=
    DifferentialGeometry.HomotopyEquiv.productConvex CircleModel
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) p'
  let e₄ : CircleModel ≃ₕ J := j.toHomotopyEquiv
  let e := e₁.trans (e₂.trans (e₃.trans e₄))
  refine ⟨e, ?_⟩
  intro x
  have hx : (x : EuclideanSpace ℝ (Fin 3)) ∈
      Subtype.val '' (φ '' {q | q.1 = p}) := hJset ▸ x.property
  obtain ⟨y, ⟨q, hq, hqφ⟩, hxy⟩ := hx
  have hqeq : q = φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hJS x.property⟩ : S) := by
    apply φ.injective
    rw [φ.apply_symm_apply]
    exact hqφ.trans (Subtype.ext hxy)
  have hqp : q.1 = p' := Subtype.ext hq
  simp only [ContinuousMap.coe_mk]
  apply Subtype.ext
  change (φ (p', (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hJS x.property⟩ : S)).2) :
      EuclideanSpace ℝ (Fin 3)) = x
  have harg : (p', (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hJS x.property⟩ : S)).2) = q := by
    apply Prod.ext
    · exact hqp.symm
    · exact (congrArg Prod.snd hqeq).symm
  rw [harg]
  exact (congrArg Subtype.val hqφ).trans hxy

open Classical in
theorem fundamentalGroup_map_inclusion_bijective_of_isSpine
    {S J : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsSpine S J) (hJS : J ⊆ S) :
    ∀ x : J, Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) x) := by
  obtain ⟨e, hri⟩ := spine_homotopy_equiv hJ hJS
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
def Moise308Nested : Prop :=
  ∀ (S₁ S S₂ J : Set (EuclideanSpace ℝ (Fin 3))),
    IsTopologicalSolidTorus S₁ → IsTopologicalSolidTorus S₂ → IsCombinatorialSolidTorus S →
    S₁ ⊆ interior S → S ⊆ interior S₂ →
    IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂) →
    IsSpine S₁ J → ∀ hJS : J ⊆ S, ∀ x : J,
      Function.Bijective (FundamentalGroup.map
        (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) x)

open Classical in
private theorem isCompact_of_isTopologicalSolidTorus_nested
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S) :
    IsCompact S := by
  let φ : S ≃ₜ (DiskModel × CircleModel) := Classical.choice hS
  let _ : CompactSpace S := φ.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

open Classical in
private theorem fundamentalGroup_map_inclusion_bijective_of_nested
    {S₁ S S₂ J : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsTopologicalSolidTorus S₁) (hS₂ : IsTopologicalSolidTorus S₂)
    (hS : IsCombinatorialSolidTorus S) (hS₁S : S₁ ⊆ interior S)
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
    homotopyEquiv_inclusion_of_isToroidalShell hclosed₁ hclosed₂ h₁₂ hshell
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
  obtain ⟨eSpine, heSpine⟩ := spine_homotopy_equiv hJ hJ₁
  let eJ : FundamentalGroup J x ≃* Multiplicative ℤ :=
    (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      eSpine.symm x (eSpine.symm x) rfl).trans
      (fundamentalGroupSolidTorusEquivInt hS₁ (eSpine.symm x))
  let eS : FundamentalGroup S (iJS x) ≃* Multiplicative ℤ :=
    fundamentalGroupSolidTorusEquivInt hS.1 (iJS x)
  let eS₂ : FundamentalGroup S₂ (iJ₂ x) ≃* Multiplicative ℤ :=
    fundamentalGroupSolidTorusEquivInt hS₂ (iJ₂ x)
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

theorem moise308Nested : Moise308Nested := by
  intro S₁ S S₂ J hS₁ hS₂ hS hS₁S hSS₂ hshell hJ
  exact fundamentalGroup_map_inclusion_bijective_of_nested hS₁ hS₂ hS hS₁S hSS₂
    hshell hJ

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
  obtain ⟨eSpine, _heSpine⟩ := spine_homotopy_equiv hJ hJT
  let eJ : FundamentalGroup J x ≃* Multiplicative ℤ :=
    (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      eSpine.symm x (eSpine.symm x) rfl).trans
      (fundamentalGroupSolidTorusEquivInt hT (eSpine.symm x))
  let eS : FundamentalGroup S (iJS x) ≃* Multiplicative ℤ :=
    fundamentalGroupSolidTorusEquivInt hS (iJS x)
  let eT : FundamentalGroup T (iJT x) ≃* Multiplicative ℤ :=
    fundamentalGroupSolidTorusEquivInt hT (iJT x)
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
