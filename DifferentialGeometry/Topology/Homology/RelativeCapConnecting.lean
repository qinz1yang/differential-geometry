import DifferentialGeometry.Topology.Homology.RelativeCapHomology
import DifferentialGeometry.Topology.Homology.ModuleHomologyConnecting

noncomputable section

open CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

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
  obtain ⟨b, a, hb, ha⟩ := exists_moduleCycle_connecting_lifts
    (integralRelativeChainSequence_shortExact A) (k + m + 1) (k + m) (by simp) c
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

end DifferentialGeometry.Topology

end
