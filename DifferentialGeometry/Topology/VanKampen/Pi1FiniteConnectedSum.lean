import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem subsingleton_fundamentalGroup_of_joined
    {X : Type u} [TopologicalSpace X] {z m : X} (β : Path z m)
    (h : Subsingleton (FundamentalGroup X z)) :
    Subsingleton (FundamentalGroup X m) :=
  @Equiv.subsingleton _ _ (fundamentalGroupChangeBasepoint β).toEquiv h

theorem subsingleton_of_finiteConnectedSum_factors
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ (F : ConnectedClosedOrientedManifold.{u} 3) (p : F.Carrier),
      F ∈ L → Subsingleton (FundamentalGroup F.Carrier p))
    (x : (i : Fin L.length) → (L.get i).Carrier)
    (y : (finiteConnectedSum L).Carrier) :
    Subsingleton (FundamentalGroup (finiteConnectedSum L).Carrier y) := by
  obtain ⟨e⟩ := fundamentalGroup_finiteConnectedSum_freeProduct L x y
  have hcoprod : Subsingleton (Monoid.CoprodI (fun i : Fin L.length =>
      FundamentalGroup (L.get i).Carrier (x i))) :=
    (DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff
      (fun i : Fin L.length => FundamentalGroup (L.get i).Carrier (x i))).mpr
      (fun i => h (L.get i) (x i) (List.get_mem L i))
  exact @Equiv.subsingleton _ _ e.toEquiv hcoprod

end DifferentialGeometry.Topology
