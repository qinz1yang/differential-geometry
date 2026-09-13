import Poincare.Topology.Homology.RelativeCapHomology
import Poincare.Topology.Homology.ModuleHomologyConnecting

noncomputable section

open CategoryTheory

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem exists_relative_cycle_lifts (A : Set X) (n : ℕ)
    (c : LinearMap.ker ((integralRelativeChains A).sc (n + 1)).g.hom) :
    ∃ b : (integralSingularChains X).X (n + 1),
      ∃ a : LinearMap.ker ((integralSingularChains A).sc n).g.hom,
        (integralRelativeChainSequence A).g.f (n + 1) b = c.val ∧
        (integralSingularChainMap (singularSubspaceInclusion A)).f n a.val =
          (integralSingularChains X).d (n + 1) n b := by
  obtain ⟨b, hb⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) (n + 1) c.val
  change (integralRelativeChainSequence A).g.f (n + 1) b = c.val at hb
  have hc : (integralRelativeChains A).d (n + 1) n c.val = 0 := by
    have h := c.property
    change (integralRelativeChains A).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) c.val = 0 at h
    rwa [ChainComplex.next_nat_succ] at h
  have hdb : (integralRelativeChainSequence A).g.f n
      ((integralSingularChains X).d (n + 1) n b) = 0 := by
    have h := congrArg (fun f : (integralSingularChains X).X (n + 1) ⟶
      (integralRelativeChains A).X n => f b) ((integralRelativeChainSequence A).g.comm (n + 1) n)
    change (integralRelativeChains A).d (n + 1) n
      ((integralRelativeChainSequence A).g.f (n + 1) b) = _ at h
    erw [hb, hc] at h
    exact h.symm
  obtain ⟨a, ha⟩ := (chainCokernelπ_eq_zero_iff
    (integralSingularChainMap (singularSubspaceInclusion A)) n _).1 hdb
  have haCycle : a ∈ LinearMap.ker ((integralSingularChains A).sc n).g.hom :=
    (integralRelativeChainSequence_shortExact A).d_eq_zero_of_f_eq_d_apply
      (n + 1) n b a ha ((ComplexShape.down ℕ).next n)
  exact ⟨b, ⟨a, haCycle⟩, hb, ha⟩

private theorem cap_cocycle_boundary_signed (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0)
    (b : (integralSingularChains X).X (k + m + 1)) :
    (-1 : ℤ) ^ k • integralSingularCapProduct k m φ
        ((integralSingularChains X).d (k + m + 1) (k + m) b) =
      (integralSingularChains X).d (m + 1) m (integralSingularCapProduct k (m + 1) φ b) := by
  have h := LinearMap.congr_fun (integralSingularCapProduct_boundary k m φ) b
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h
  have heval := map_zsmul
    (LinearMap.applyₗ (R := ℤ) (M₂ := (integralSingularChains X).X m) b)
    ((-1 : ℤ) ^ k) (((integralSingularChains X).d (m + 1) m).hom.comp
      (integralSingularCapProduct k (m + 1) φ))
  rw [hφ, map_zero, LinearMap.zero_apply, zero_add] at h
  have hp : integralSingularCapProduct k m φ
      ((integralSingularChains X).d (k + m + 1) (k + m) b) =
      (-1 : ℤ) ^ k • (integralSingularChains X).d (m + 1) m
        (integralSingularCapProduct k (m + 1) φ b) := h.trans heval
  rcases Nat.even_or_odd k with hk | hk
  · simpa only [hk.neg_one_pow, one_zsmul] using hp
  · simpa only [hk.neg_one_pow, neg_one_zsmul, neg_neg] using congrArg Neg.neg hp

private theorem connecting_cocycle_closed (k : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom) :
    integralSingularCoboundary X k (k + 1) φ.val = 0 := by
  have h := φ.property
  change integralSingularCoboundary X k ((ComplexShape.up ℕ).next k) φ.val = 0 at h
  rwa [CochainComplex.next] at h

theorem integralRelativeCohomologyCapProduct_connecting (A : Set X) (k m : ℕ)
    (α : integralSingularCohomology k X) (c : integralRelativeHomology (k + (m + 1)) A) :
    integralRelativeConnecting m A (integralRelativeCohomologyCapProduct A k (m + 1) α c) =
      (-1 : ℤ) ^ k • integralSingularCohomologyCapProduct k m
        (integralSingularCohomologyMap k (singularSubspaceInclusion A) α)
        (integralRelativeConnecting (k + m) A c) := by
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralSingularCochains X).sc k) α
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeChains A).sc (k + (m + 1))) c
  obtain ⟨b, a, hb, ha⟩ := exists_relative_cycle_lifts A (k + m) c
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) k).map
    (integralSingularCochainMap (singularSubspaceInclusion A))
  let ψ := moduleCycleMap P φ
  let ac := integralSingularCapCycleMap k m ψ.val (connecting_cocycle_closed k ψ) a
  let bc := integralSingularCapProduct k (m + 1) φ.val b
  let cc := integralRelativeCapCycleMap A k (m + 1) φ c
  have hφ : integralSingularCohomologyMap k (singularSubspaceInclusion A)
      (moduleHomologyClass ((integralSingularCochains X).sc k) φ) =
      moduleHomologyClass ((integralSingularCochains A).sc k) ψ :=
    moduleHomologyClass_map P φ
  have hδ : integralRelativeConnecting (k + m) A
      (moduleHomologyClass ((integralRelativeChains A).sc (k + (m + 1))) c) =
      moduleHomologyClass ((integralSingularChains A).sc (k + m)) a :=
    moduleHomologyClass_connecting (integralRelativeChainSequence_shortExact A)
      (k + m + 1) (k + m) (by simp) c b hb a ha
  have hbc : (integralRelativeChainSequence A).g.f (m + 1) bc = cc.val := by
    dsimp only [bc, cc]
    rw [integralRelativeCapCycleMap_apply]
    exact (integralRelativeCapProduct_π A k (m + 1) φ.val b).symm.trans
      (congrArg (integralRelativeCapProduct A k (m + 1) φ.val) hb)
  have hnatural : (integralSingularChainMap (singularSubspaceInclusion A)).f m ac.val =
      integralSingularCapProduct k m φ.val
        ((integralSingularChainMap (singularSubspaceInclusion A)).f (k + m) a.val) := by
    exact congrArg (fun L : (integralSingularChains A).X (k + m) →ₗ[ℤ]
      (integralSingularChains X).X m => L a.val)
      (integralSingularCapProduct_natural k m (singularSubspaceInclusion A) φ.val)
  have hac : (integralRelativeChainSequence A).f.f m ((-1 : ℤ) ^ k • ac).val =
      (integralSingularChains X).d (m + 1) m bc := by
    change (integralSingularChainMap (singularSubspaceInclusion A)).f m
      ((-1 : ℤ) ^ k • ac.val) = _
    erw [map_zsmul, hnatural, ha]
    exact cap_cocycle_boundary_signed k m φ.val (connecting_cocycle_closed k φ) b
  have hδcap : integralRelativeConnecting m A
      (moduleHomologyClass ((integralRelativeChains A).sc (m + 1)) cc) =
      moduleHomologyClass ((integralSingularChains A).sc m) ((-1 : ℤ) ^ k • ac) :=
    moduleHomologyClass_connecting (integralRelativeChainSequence_shortExact A) (m + 1) m (by simp) cc bc hbc
      ((-1 : ℤ) ^ k • ac) hac
  rw [hφ, hδ]
  erw [integralRelativeCohomologyCapProduct_class, integralSingularCohomologyCapProduct_class]
  exact hδcap.trans (map_zsmul (moduleHomologyClass ((integralSingularChains A).sc m))
    ((-1 : ℤ) ^ k) ac)

end Poincare.Topology

end
