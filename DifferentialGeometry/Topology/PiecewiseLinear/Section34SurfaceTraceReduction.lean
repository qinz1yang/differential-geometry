import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceInessentialFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceDiskCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceDiskTraceDeletion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_strict_surface_trace_reduction_of_inessential_disk
    (S K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite S.faces] [Finite K.faces] [Finite L.faces]
    (hS : IsCombinatorialManifoldWithBoundary 3 S) (hsolid : IsTopologicalSolidTorus S.space)
    (hK : IsCombinatorialManifold 2 K) (hL : IsCombinatorialManifold 2 L)
    (hconn : IsConnected K.space) (hKS : K.space ⊆ interior S.space)
    (hgen : CarriesFundamentalGroupOnto K.space S.space)
    {ι : Type*} [Finite ι] {J : ι → Set (EuclideanSpace ℝ (Fin 3))}
    (hJ : ∀ j, IsPLSphere 1 (J j)) (hdis : Pairwise fun j k => Disjoint (J j) (J k))
    (htrace : K.space ∩ L.space = ⋃ j, J j) (i : ι)
    {D E : Set (EuclideanSpace ℝ (Fin 3))}
    {d e : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hd : IsPLHomeomorphOn d (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (he : IsPLHomeomorphOn e (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) E)
    (hdJ : d '' stdSimplexBoundary 2 = J i) (heJ : e '' stdSimplexBoundary 2 = J i)
    (hDS : D ⊆ L.space ∩ interior S.space) (hEK : E ⊆ K.space)
    (hDK : D ∩ K.space = J i) :
    ∃ (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (I : Set ι),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id (interior S.space)ᶜ ∧
      Nat.card I < Nat.card ι ∧ Φ '' K.space ∩ L.space = ⋃ j : I, J j.1 := by
  have hJK (j : ι) : J j ⊆ K.space :=
    fun _ hx => (htrace.superset (mem_iUnion.mpr ⟨j, hx⟩)).1
  obtain ⟨I, hcard, hrest, -, hclosed⟩ :=
    hK.exists_strict_trace_subfamily_after_disk K i he heJ hEK hJ hJK hdis
  obtain ⟨C, hC, hCS, hfront, hmeet, hcap⟩ :=
    exists_surface_inessential_disk_filling_in_solid_torus S K hS hsolid hK hconn hKS hgen
      hd he (heJ.trans hdJ.symm) (hDS.trans inter_subset_right) hEK (hDK.trans hdJ.symm)
  have hdiff : (K.space \ C) ∩ L.space = (⋃ j, J j) \ E := by
    rw [← htrace, ← hmeet]
    ext x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  have hEC : K.space ∩ C ⊆ frontier C := by
    rw [hmeet, hfront]
    exact subset_union_right
  have hball : IsPLBall 2 (K.space ∩ C) := hmeet.symm ▸ ⟨e, he⟩
  obtain ⟨Φ, hΦ, hfix, -, hnew⟩ := hC.exists_relative_surface_disk_cancellation
    K L hK hL hball hEC (hcap ▸ hDS.trans inter_subset_left)
      (hdiff.symm ▸ hclosed) isOpen_interior hCS
  exact ⟨Φ, I, hΦ, hfix, hcard, hnew.trans (hdiff.trans hrest)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
