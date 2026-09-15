import DifferentialGeometry.Topology.Homology.TriangleSphereFacePairing
import DifferentialGeometry.Topology.Simplex.TetrahedronFill
import DifferentialGeometry.Topology.Simplex.BoundarySphereFilling

noncomputable section

namespace DifferentialGeometry.Topology

universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem nullhomotopic_of_freeSphereHomologyImage_simplexBoundary_eq_zero
    (x : X) (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X))
    (hf : freeSphereHomologyImage 1 (simplexBoundarySphereClass.{u} 1)
      (ZerothHomotopy.mk f) = 0) : f.Nullhomotopic := by
  obtain ⟨g, hg, H, hcones⟩ := exists_sphere_cone_terminal_faces f x
  have hs := integralSingularTriangleSphereHomologyPairing_terminal_faces x f g hg hcones
  rw [hf, map_zero] at hs
  let q : Fin 4 → HomotopyGroup (Fin 2) X x :=
    fun i => ⟦Simplex.triangleGenLoop (g i) x (hg i)⟧
  have hq : q 0 * q 2 = q 1 * q 3 := by
    have hsum : (∑ i : Fin 4, (-1 : ℤ) ^ i.val • Additive.ofMul (q i)) = 0 := hs.symm
    rw [Fin.sum_univ_four] at hsum
    norm_num at hsum
    apply Additive.ofMul.injective
    change Additive.ofMul (q 0) + Additive.ofMul (q 2) =
      Additive.ofMul (q 1) + Additive.ofMul (q 3)
    have heq : Additive.ofMul (q 0) - Additive.ofMul (q 1) +
        Additive.ofMul (q 2) - Additive.ofMul (q 3) = 0 := by
      convert hsum using 1
      abel
    have he : (Additive.ofMul (q 0) + Additive.ofMul (q 2)) -
        (Additive.ofMul (q 1) + Additive.ofMul (q 3)) = 0 := by
      calc
        _ = Additive.ofMul (q 0) - Additive.ofMul (q 1) +
            Additive.ofMul (q 2) - Additive.ofMul (q 3) := by abel
        _ = 0 := heq
    exact sub_eq_zero.mp he
  obtain ⟨F, hF⟩ := exists_tetrahedron_extension_of_triangleGenLoop_relation g hg hq
  obtain ⟨y, hy⟩ := Simplex.boundarySphereDesc_nullhomotopic_of_extension g _ F hF
  exact ⟨y, H.trans hy⟩

end DifferentialGeometry.Topology
