import DifferentialGeometry.Topology.Covering.FiniteFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Manifold.OpenSphereCylinder

noncomputable section
open Set Metric Manifold
open scoped ContDiff ContinuousMap

namespace DifferentialGeometry.Topology

theorem simplyConnectedSpace_sphereTwo_prod_real : SimplyConnectedSpace (SphereTwo × ℝ) := by
  let e : SphereTwo × ℝ ≃ₕ SphereTwo :=
    ((ContinuousMap.HomotopyEquiv.refl SphereTwo).prodCongr
      (ContractibleSpace.hequiv_unit ℝ).some).trans
        (Homeomorph.prodUnique SphereTwo Unit).toHomotopyEquiv
  exact e.simplyConnectedSpace

inductive cylinderDeckModel
  | trivial
  | antipodal
  | twisted

namespace cylinderDeckModel

def transform : cylinderDeckModel → SphereTwo × ℝ → SphereTwo × ℝ
  | trivial, q => q
  | antipodal, q => (-q.1, q.2)
  | twisted, q => (-q.1, -q.2)

def rel : cylinderDeckModel → SphereTwo × ℝ → SphereTwo × ℝ → Prop
  | trivial, q, r => q = r
  | antipodal, q, r => q = r ∨ r = (-q.1, q.2)
  | twisted, q, r => q = r ∨ r = (-q.1, -q.2)

theorem mem_pair_of_rel (d : cylinderDeckModel) {q r : SphereTwo × ℝ}
    (h : d.rel q r) : r ∈ ({q, d.transform q} : Set (SphereTwo × ℝ)) := by
  cases d <;> simp only [rel, transform] at h ⊢
  · exact Or.inl h.symm
  · exact h.imp Eq.symm id
  · exact h.imp Eq.symm id

end cylinderDeckModel

structure smoothCylinderCover (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where
  projection : SphereTwo × ℝ → M
  isCoveringMap : IsCoveringMap projection
  surjective : Function.Surjective projection
  isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ projection
  deckModel : cylinderDeckModel
  fiber_iff : ∀ q r, projection q = projection r ↔ deckModel.rel q r

namespace smoothCylinderCover

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem finite_fiber (c : smoothCylinderCover M) (x : M) :
    Finite (c.projection ⁻¹' {x}) := by
  obtain ⟨q, hq⟩ := c.surjective x
  have hsub : c.projection ⁻¹' {x} ⊆ ({q, c.deckModel.transform q} : Set (SphereTwo × ℝ)) := by
    intro r hr
    exact c.deckModel.mem_pair_of_rel ((c.fiber_iff q r).mp (hq.trans hr.symm))
  exact ((Set.finite_singleton (c.deckModel.transform q)).insert q).subset hsub

theorem finite_fundamentalGroup (c : smoothCylinderCover M) (x : M) :
    Finite (FundamentalGroup M x) := by
  let : SimplyConnectedSpace (SphereTwo × ℝ) := simplyConnectedSpace_sphereTwo_prod_real
  let : Finite (c.projection ⁻¹' {x}) := c.finite_fiber x
  obtain ⟨q, hq⟩ := c.surjective x
  exact finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover
    c.projection c.isCoveringMap x ⟨q, hq⟩

theorem exists_euclidean_open_cover (c : smoothCylinderCover M) :
    ∃ p : DifferentialGeometry.Topology.Manifold.puncturedSpace (EuclideanSpace ℝ (Fin 3)) → M,
      IsCoveringMap p ∧ Function.Surjective p ∧
        IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let D := DifferentialGeometry.Topology.Manifold.sphereProdRealDiffeomorphPunctured (n := 2) sphereTwoNorth
  refine ⟨c.projection ∘ D.symm, c.isCoveringMap.comp_homeomorph D.symm.toHomeomorph,
    c.surjective.comp D.symm.surjective, ?_⟩
  intro x
  exact (D.symm.isLocalDiffeomorph x).comp (𝓡 3) M (c.isLocalDiffeomorph (D.symm x))

end smoothCylinderCover
end DifferentialGeometry.Topology
