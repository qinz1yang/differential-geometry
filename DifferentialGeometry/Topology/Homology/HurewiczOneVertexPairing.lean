import DifferentialGeometry.Topology.Homology.HurewiczOneAbelianization
import DifferentialGeometry.Topology.Homology.HurewiczOneKernel

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem quotientMk_eq_add_of_sub_sub_mem {M : Type*} [AddCommGroup M] [Module ℤ M]
    (P : Submodule ℤ M) {a b c : M} (h : a - b - c ∈ P) :
    P.mkQ a = P.mkQ b + P.mkQ c := by
  have h' : a - (b + c) ∈ P := by simpa [sub_sub] using h
  rw [← map_add]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq P).mpr h'

private theorem quotientMk_eq_neg_of_add_mem {M : Type*} [AddCommGroup M] [Module ℤ M]
    (P : Submodule ℤ M) {a b : M} (h : a + b ∈ P) :
    P.mkQ a = -P.mkQ b := by
  rw [← map_neg]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

section Cone

variable [PathConnectedSpace X]

def integralSourcePathCone (x : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralVertexPathCone x).comp integralSourceVertexMap

def integralTargetPathCone (x : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralVertexPathCone x).comp integralTargetVertexMap

theorem integralSourcePathCone_simplex (x : X) (σ : integralSingularSimplex 1 X) :
    integralSourcePathCone x (integralSimplexChain 1 σ) =
      integralPathChain (PathConnectedSpace.somePath x (simplexSourceVertex σ)) := by
  rw [integralSourcePathCone, LinearMap.comp_apply, integralSourceVertexMap_simplex,
    integralVertexChain_eq_zero_simplex, integralVertexPathCone_simplex]
  rw [Equiv.apply_symm_apply]

theorem integralTargetPathCone_simplex (x : X) (σ : integralSingularSimplex 1 X) :
    integralTargetPathCone x (integralSimplexChain 1 σ) =
      integralPathChain (PathConnectedSpace.somePath x (simplexTargetVertex σ)) := by
  rw [integralTargetPathCone, LinearMap.comp_apply, integralTargetVertexMap_simplex,
    integralVertexChain_eq_zero_simplex, integralVertexPathCone_simplex]
  rw [Equiv.apply_symm_apply]

end Cone

theorem integralPathChain_trans_trans_symm_sub_mem_range {x u v : X} (p : Path x u)
    (q : Path u v) (r : Path x v) :
    integralPathChain (p.trans (q.trans r.symm)) - integralPathChain p - integralPathChain q +
        integralPathChain r ∈ LinearMap.range ((integralSingularChains X).d 2 1).hom := by
  have h1 : integralPathChain (p.trans (q.trans r.symm)) - integralPathChain p -
      integralPathChain (q.trans r.symm) ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom :=
    exists_integralPathChain_trans_sub_mem_range p (q.trans r.symm)
  have h2 : integralPathChain (q.trans r.symm) - integralPathChain q -
      integralPathChain r.symm ∈ LinearMap.range ((integralSingularChains X).d 2 1).hom :=
    exists_integralPathChain_trans_sub_mem_range q r.symm
  have h3 : integralPathChain r + integralPathChain r.symm ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom :=
    exists_integralPathChain_add_symm_mem_range r
  have hgoal : (LinearMap.range ((integralSingularChains X).d 2 1).hom).mkQ
      (integralPathChain (p.trans (q.trans r.symm)) - integralPathChain p - integralPathChain q +
        integralPathChain r) = 0 := by
    rw [map_add, map_sub, map_sub, quotientMk_eq_add_of_sub_sub_mem _ h1,
      quotientMk_eq_add_of_sub_sub_mem _ h2, quotientMk_eq_neg_of_add_mem _ h3]
    abel
  exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa [Submodule.mkQ_apply] using hgoal)

theorem integralPathChain_pathLoopOfSimplex_sub_mem_range [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 1 X) :
    integralPathChain (pathLoopOfSimplex x σ) -
        integralPathChain (PathConnectedSpace.somePath x (simplexSourceVertex σ)) -
        integralPathChain (integralSimplexPath σ) +
        integralPathChain (PathConnectedSpace.somePath x (simplexTargetVertex σ)) ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom := by
  rw [pathLoopOfSimplex]
  exact integralPathChain_trans_trans_symm_sub_mem_range (x := x)
    (u := simplexSourceVertex σ) (v := simplexTargetVertex σ)
    (PathConnectedSpace.somePath x (simplexSourceVertex σ)) (integralSimplexPath σ)
    (PathConnectedSpace.somePath x (simplexTargetVertex σ))

private def integralLoopDefect [PathConnectedSpace X] (x : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  integralPathLoopChainMap x - integralSourcePathCone x - LinearMap.id + integralTargetPathCone x

private theorem integralLoopDefect_simplex [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 1 X) :
    integralLoopDefect x (integralSimplexChain 1 σ) ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom := by
  rw [integralLoopDefect, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sub_apply,
    LinearMap.id_apply, integralPathLoopChainMap_simplex, integralSourcePathCone_simplex,
    integralTargetPathCone_simplex]
  rw [← integralPathChain_simplexPath σ]
  exact integralPathChain_pathLoopOfSimplex_sub_mem_range x σ

private theorem integralLoopDefect_mem [PathConnectedSpace X] (x : X)
    (c : (integralSingularChains X).X 1) :
    integralLoopDefect x c ∈ LinearMap.range ((integralSingularChains X).d 2 1).hom := by
  have htop : Submodule.comap (integralLoopDefect x)
      (LinearMap.range ((integralSingularChains X).d 2 1).hom) = ⊤ := by
    rw [eq_top_iff, ← Basis.span_eq (integralSingularChainBasis 1 X)]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨σ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, integralSingularChainBasis_apply]
    exact integralLoopDefect_simplex x σ
  exact Submodule.mem_comap.mp ((Submodule.eq_top_iff'.mp htop) c)

theorem hurewiczOneVertexPairing [PathConnectedSpace X] (x : X) :
    HurewiczOneVertexPairing x := by
  unfold HurewiczOneVertexPairing
  intro z
  have hz : integralSourceVertexMap (z : (integralSingularChains X).X 1) =
      integralTargetVertexMap (z : (integralSingularChains X).X 1) :=
    integralSourceVertexMap_eq_targetVertexMap_of_cycle z
  have hcone : integralSourcePathCone x (z : (integralSingularChains X).X 1) =
      integralTargetPathCone x (z : (integralSingularChains X).X 1) := by
    rw [integralSourcePathCone, integralTargetPathCone, LinearMap.comp_apply,
      LinearMap.comp_apply, hz]
  have h := integralLoopDefect_mem x (z : (integralSingularChains X).X 1)
  rw [integralLoopDefect, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sub_apply,
    LinearMap.id_apply, hcone] at h
  have h2 : integralPathLoopChainMap x (z : (integralSingularChains X).X 1) -
      (z : (integralSingularChains X).X 1) =
      integralPathLoopChainMap x (z : (integralSingularChains X).X 1) -
        integralTargetPathCone x (z : (integralSingularChains X).X 1) -
        (z : (integralSingularChains X).X 1) +
        integralTargetPathCone x (z : (integralSingularChains X).X 1) := by
    abel
  have h3 : integralPathLoopChainMap x (z : (integralSingularChains X).X 1) -
      (z : (integralSingularChains X).X 1) ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom := by
    rw [h2]
    exact h
  simpa using neg_mem h3

private theorem mem_commutator_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {g : G}
    (h : e g ∈ commutator H) : g ∈ commutator G := by
  rw [← Abelianization.ker_of] at h ⊢
  rw [MonoidHom.mem_ker] at h ⊢
  rw [← abelianizationCongr_of e g] at h
  exact (MulEquiv.map_eq_one_iff e.abelianizationCongr).mp h

private theorem hurewiczPairing_range_le_ker [PathConnectedSpace X] (x : X) :
    LinearMap.range (integralSingularBoundaryToCycles 0 X) ≤
      ((hurewiczPairing x).comp (Submodule.subtype (integralSingularCycles 0 X))).ker := by
  rw [LinearMap.range_le_ker_iff]
  ext c
  rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    integralSingularBoundaryToCycles_coe, hurewiczPairing_boundary]

def hurewiczPairingHomology [PathConnectedSpace X] (x : X) :
    integralSingularHomology 1 X →+ Additive (Abelianization (FundamentalGroup X x)) :=
  AddMonoidHom.mk' (fun y =>
    (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 0 X))
      ((hurewiczPairing x).comp (Submodule.subtype (integralSingularCycles 0 X)))
      (hurewiczPairing_range_le_ker x)) ((integralSingularHomologyCycleEquiv 0 X) y)) (by
    intro y₁ y₂
    rw [map_add, map_add])

theorem hurewiczPairingHomology_integralSingularCycleClass [PathConnectedSpace X] (x : X)
    (z : integralSingularCycles 0 X) :
    hurewiczPairingHomology x (integralSingularCycleClass 0 X z) =
      hurewiczPairing x (z : (integralSingularChains X).X 1) := by
  change (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 0 X))
      ((hurewiczPairing x).comp (Submodule.subtype (integralSingularCycles 0 X)))
      (hurewiczPairing_range_le_ker x))
      ((integralSingularHomologyCycleEquiv 0 X) (integralSingularCycleClass 0 X z)) =
    hurewiczPairing x (z : (integralSingularChains X).X 1)
  rw [integralSingularCycleClass, AddEquiv.apply_symm_apply, Submodule.liftQ_apply,
    LinearMap.comp_apply, Submodule.subtype_apply]

def HurewiczOneSpherePairing (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] : Prop :=
  ∀ (x : X) (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (_ : IsSphereHomologyGenerator 0 c) (a : HomotopyGroup (Fin 1) X x),
    hurewiczPairingHomology x (sphereHurewicz 0 x c a) =
      Additive.ofMul (Abelianization.of (HomotopyGroup.pi1MulEquivFundamentalGroup a))

theorem hurewiczOneKernel_of_spherePairing [PathConnectedSpace X]
    (h : HurewiczOneSpherePairing X) : HurewiczOneKernel X := by
  intro x c hc a ha
  have h1 := h x c hc a
  rw [ha, map_zero] at h1
  have h2 : Abelianization.of (HomotopyGroup.pi1MulEquivFundamentalGroup a) = 1 := by
    have := congrArg Additive.toMul h1.symm
    simpa using this
  exact mem_commutator_of_mulEquiv
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x))
    (by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact h2)

theorem hurewiczOneSpherePairing_of_subsingleton [PathConnectedSpace X]
    (h : ∀ x : X, Subsingleton (HomotopyGroup (Fin 1) X x)) :
    HurewiczOneSpherePairing X := by
  intro x c hc a
  rw [Subsingleton.elim a 1, sphereHurewicz_one, map_zero, map_one, map_one]
  rfl

theorem hurewiczOneKernel_of_subsingleton [PathConnectedSpace X]
    (h : ∀ x : X, Subsingleton (HomotopyGroup (Fin 1) X x)) : HurewiczOneKernel X :=
  hurewiczOneKernel_of_spherePairing (hurewiczOneSpherePairing_of_subsingleton h)

theorem hurewiczOneSpherePairing_of_loopBridge_of_loopClassPairing [PathConnectedSpace X]
    (hbridge : ∀ (x : X) (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
      (_ : IsSphereHomologyGenerator 0 c) (a : HomotopyGroup (Fin 1) X x),
      ∃ γ : Path x x,
        HomotopyGroup.pi1MulEquivFundamentalGroup a =
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∧
        sphereHurewicz 0 x c a = integralPathLoopClass γ)
    (hloop : ∀ (x : X) (γ : Path x x),
      hurewiczPairingHomology x (integralPathLoopClass γ) =
        Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk γ)))) :
    HurewiczOneSpherePairing X := by
  intro x c hc a
  obtain ⟨γ, hγ, hsphere⟩ := hbridge x c hc a
  rw [hsphere, hloop x γ, hγ]

theorem abelianizationHomotopyGroupOne_equiv_of_spherePairing [PathConnectedSpace X] (x : X)
    (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (hc : IsSphereHomologyGenerator 0 c) (hpair : HurewiczOneSpherePairing X)
    (hmul : ∀ a b : HomotopyGroup (Fin 1) X x,
      sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b)
    (hsurj : Function.Surjective (sphereHurewicz 0 x c)) :
    Nonempty (Abelianization (HomotopyGroup (Fin 1) X x) ≃*
      Multiplicative (integralSingularHomology 1 X)) :=
  abelianizationHomotopyGroupOne_equiv_of_hurewiczOne x c hmul hsurj
    fun a ha => hurewiczOneKernel_of_spherePairing hpair x c hc a ha

end DifferentialGeometry.Topology
