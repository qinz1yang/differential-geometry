import DifferentialGeometry.Topology.VanKampen.TwoBoundaryCollars
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarInjection
import DifferentialGeometry.Topology.VanKampen.SmoothTwoSidedCollarBridge
import DifferentialGeometry.Topology.Manifold.SmoothBicollar
import Mathlib.Topology.Piecewise

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private def sumSelfHomeomorphBoolProd (S : Type*) [TopologicalSpace S] :
    (S ⊕ S) ≃ₜ Bool × S where
  toEquiv := (Equiv.boolProdEquivSum S).symm
  continuous_toFun :=
    (continuous_const.prodMk continuous_id).sumElim (continuous_const.prodMk continuous_id)
  continuous_invFun := by
    change Continuous (fun p : Bool × S ↦ if p.1 = true then Sum.inr p.2 else Sum.inl p.2)
    have hcl : IsClopen {p : Bool × S | p.1 = true} :=
      (isClopen_discrete ({true} : Set Bool)).preimage continuous_fst
    exact Continuous.if (by simp only [hcl.frontier_eq, mem_empty_iff_false, false_implies, implies_true])
      (continuous_inr.comp continuous_snd) (continuous_inl.comp continuous_snd)

theorem subsingleton_pathHomotopicQuotient_sum_sphereTwo (x y : SphereTwo ⊕ SphereTwo) :
    Subsingleton (Path.Homotopic.Quotient x y) :=
  subsingleton_pathHomotopicQuotient_of_homotopyEquiv
    (sumSelfHomeomorphBoolProd SphereTwo).toHomotopyEquiv
    (subsingleton_pathHomotopicQuotient_prod
      subsingleton_pathHomotopicQuotient_of_totallyDisconnected (fun _ _ ↦ inferInstance)) x y

theorem exists_outward_collar_of_two_spherical_boundaries
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {K : Set M} (hregular : closure (interior K) = K)
    (e₀ e₁ : SphereTwo → M)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hfront : frontier K = range e₀ ∪ range e₁)
    (hd : Disjoint (range e₀) (range e₁)) :
    ∃ c : ThreeManifold.TwoSidedCollar (Sum.elim e₀ e₁),
      ∀ p : (SphereTwo ⊕ SphereTwo) × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0 := by
  obtain ⟨c₀⟩ := exists_smoothTwoSidedCollar_of_smoothSphereEmbedding e₀ he₀
  obtain ⟨c₁⟩ := exists_smoothTwoSidedCollar_of_smoothSphereEmbedding e₁ he₁
  exact c₀.toTwoSidedCollar.exists_outward_collar_of_two_components c₁.toTwoSidedCollar
    hregular hfront hd

theorem injective_fundamentalGroup_map_of_two_spherical_boundaries
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {K : Set M} [PathConnectedSpace K] (hregular : closure (interior K) = K)
    (e₀ e₁ : SphereTwo → M)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hfront : frontier K = range e₀ ∪ range e₁)
    (hd : Disjoint (range e₀) (range e₁)) (x₀ : K) :
    Function.Injective (FundamentalGroup.map (VanKampen.subsetToAmbient K) x₀) := by
  obtain ⟨c, hside⟩ := exists_outward_collar_of_two_spherical_boundaries
    hregular e₀ e₁ he₀ he₁ hfront hd
  apply c.injective_fundamentalGroup_map_domain (hregular ▸ isClosed_closure) ?_
    hside subsingleton_pathHomotopicQuotient_sum_sphereTwo x₀
  rw [hfront]
  rintro x (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · exact ⟨Sum.inl s, rfl⟩
  · exact ⟨Sum.inr s, rfl⟩

end DifferentialGeometry.Topology
