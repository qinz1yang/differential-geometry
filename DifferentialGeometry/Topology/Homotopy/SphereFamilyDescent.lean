import DifferentialGeometry.Topology.Homotopy.CubeSphereProjection



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]



theorem cubeSphereProjection_prod_quotient (n : ℕ) (K : Type*) [TopologicalSpace K] :
    _root_.Topology.IsQuotientMap (Prod.map (id : K → K) (cubeSphereProjection n)) := by
  have hp : IsProperMap (Prod.map (id : K → K) (cubeSphereProjection n)) :=
    isProperMap_id.prodMap (cubeSphereProjection n).continuous.isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous
    ((surjective_id : Surjective (id : K → K)).prodMap (cubeSphereProjection_surjective n))



def sphereFamilyDescendValue (n : ℕ)
    (F : C(K × (Fin (n + 1) → unitInterval), X)) (b : C(K, X))
    (z : K × Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) : X :=
  ((cubeInteriorSphereHomeomorph n).symm z.2).elim (b z.1) (fun u => F (z.1, u.val))


theorem sphereFamilyDescendValue_projection (n : ℕ)
    (F : C(K × (Fin (n + 1) → unitInterval), X)) (b : C(K, X))
    (hb : ∀ k v, v ∈ Cube.boundary (Fin (n + 1)) → F (k, v) = b k)
    (k : K) (v : Fin (n + 1) → unitInterval) :
    sphereFamilyDescendValue n F b (k, cubeSphereProjection n v) = F (k, v) := by
  classical
  change ((cubeInteriorSphereHomeomorph n).symm
    (cubeInteriorSphereHomeomorph n (openCollapse (cubeInterior _) v))).elim _ _ = _
  rw [Homeomorph.symm_apply_apply]
  by_cases hv : v ∈ cubeInterior (Fin (n + 1))
  · simp only [openCollapse, dif_pos hv, OnePoint.elim_some]
  · rw [openCollapse_of_notMem _ hv, OnePoint.elim_infty]
    exact (hb k v (by
      simpa only [cubeInterior_eq_compl_boundary, mem_compl_iff, not_not] using hv)).symm



theorem continuous_sphereFamilyDescendValue (n : ℕ)
    (F : C(K × (Fin (n + 1) → unitInterval), X)) (b : C(K, X))
    (hb : ∀ k v, v ∈ Cube.boundary (Fin (n + 1)) → F (k, v) = b k) :
    Continuous (sphereFamilyDescendValue n F b) := by
  apply (cubeSphereProjection_prod_quotient n K).continuous_iff.mpr
  apply F.continuous.congr
  intro z
  exact (sphereFamilyDescendValue_projection n F b hb z.1 z.2).symm


theorem sphereFamilyDescendValue_basepoint (n : ℕ)
    (F : C(K × (Fin (n + 1) → unitInterval), X)) (b : C(K, X)) (k : K) :
    sphereFamilyDescendValue n F b (k, cubeSphereBasepoint n) = b k := by
  change ((cubeInteriorSphereHomeomorph n).symm
    (cubeInteriorSphereHomeomorph n OnePoint.infty)).elim _ _ = _
  rw [Homeomorph.symm_apply_apply, OnePoint.elim_infty]

end DifferentialGeometry.Topology
