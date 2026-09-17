import DifferentialGeometry.Topology.PiecewiseLinear.HeightFreeSlab
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSlab
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCellPush
import DifferentialGeometry.Topology.ConvexFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLSphere_frontier_slab_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hS : IsPLSphere 2 (frontier K.space)) (hdim : Module.finrank ℝ E = 3)
    (hreg : closure (interior K.space) = K.space) (hconn : IsPreconnected (interior K.space))
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex (frontier K.space) ℓ = 0) {a b : ℝ} (hab : a < b)
    (hbelow : ∃ x ∈ frontier K.space, ℓ x < a) (habove : ∃ y ∈ frontier K.space, b < ℓ y) :
    IsPLSphere 2 (frontier (K.space ∩ ℓ ⁻¹' Icc a b)) := by
  classical
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hfront : frontier K.space = B.space := frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK
  have hB : IsPLSphere 2 B.space := hfront ▸ hS
  have hBinj : InjOn ℓ B.vertices := hinj.mono (fun _ hv => boundaryComplex_faces_subset 3 K hv)
  have hbelowB : ∃ x ∈ B.space, ℓ x < a := hfront ▸ hbelow
  have haboveB : ∃ x ∈ B.space, b < ℓ x := hfront ▸ habove
  have hfiber (r : ℝ) (hr : r ∈ Icc a b) :
      ∃ g : (Fin 3 → ℝ) → E, IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3))
        (K.space ∩ {x | ℓ x = r}) ∧ g '' stdSimplexBoundary 2 = B.space ∩ {x | ℓ x = r} := by
    exact exists_isPLHomeomorphOn_filling_fiber_of_heightIndex_eq_zero B K hB hdim hfront hreg hconn
      ℓ hℓ hBinj (hfront ▸ hzero) r
      (hbelowB.imp fun _ hx => ⟨hx.1, hx.2.trans_le hr.1⟩)
      (haboveB.imp fun _ hx => ⟨hx.1, hr.2.trans_lt hx.2⟩)
  obtain ⟨g₀, hg₀, hg₀Bd⟩ := hfiber a ⟨le_rfl, hab.le⟩
  obtain ⟨g₁, hg₁, hg₁Bd⟩ := hfiber b ⟨hab.le, le_rfl⟩
  have h := isPLSphere_slab_of_heightIndex_eq_zero B hB hdim ℓ hℓ hBinj (hfront ▸ hzero)
    hab hbelowB haboveB hg₀ hg₁ inter_subset_right inter_subset_right hg₀Bd hg₁Bd
  rw [Topology.frontier_inter_preimage_Icc_of_ne_zero (isPolyhedron_space K).isClosed ℓ hℓ hab.le, hfront]
  convert h using 1
  ext x
  simp only [mem_union, mem_inter_iff, mem_preimage, mem_Icc, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
  tauto

theorem exists_isPLHomeomorphOn_delete_slab_cell (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hS : IsPLSphere 2 (frontier K.space))
    (hreg : closure (interior K.space) = K.space) (hconn : IsPreconnected (interior K.space))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex (frontier K.space) ℓ = 0)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : {p} ∈ K.faces)
    {a b : ℝ} (hab : a < b) (hpheight : ℓ p ∈ Icc a b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ b < ℓ v)
    (hbelow : ∃ x ∈ frontier K.space, ℓ x < a) (habove : ∃ y ∈ frontier K.space, b < ℓ y)
    (hne : closedStar K p ∩ {x | ℓ x = ℓ p} ≠ K.space ∩ {x | ℓ x = ℓ p})
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hWconv : Convex ℝ W)
    (hSW : frontier (K.space ∩ ℓ ⁻¹' Icc a b) ⊆ W) :
    ∃ T ∈ K.faces, T.card = 4 ∧ p ∉ T ∧
      let C := convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) ∩ ℓ ⁻¹' Icc a b
      let S := frontier (K.space ∩ ℓ ⁻¹' Icc a b)
      ∃ H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn H univ univ ∧ EqOn H id Wᶜ ∧ EqOn H id (closure (S \ C)) ∧
        H '' S = closure (S \ C) ∪ closure (frontier C \ S) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨_, _, _, _, g, hg, hgBd⟩ := exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero
    K hK hS hdim hreg hconn ℓ hℓ hinj hzero (ℓ p)
    (hbelow.imp fun _ hx => ⟨hx.1, hx.2.trans_le hpheight.1⟩)
    (habove.imp fun _ hx => ⟨hx.1, hpheight.2.trans_lt hx.2⟩)
  obtain ⟨T, hT, hcard, hpnot, hconv, hC, hpatch, hpatchBd⟩ :=
    exists_convex_slab_cell_of_ne_closedStar K hK hdim hreg ℓ hℓ hinj hp hab hpheight hgap hg hgBd hne
  have hSlab := isPLSphere_frontier_slab_of_heightIndex_eq_zero K hK hS hdim hreg hconn
    ℓ hℓ hinj hzero hab hbelow habove
  have hKW : K.space ∩ ℓ ⁻¹' Icc a b ⊆ W :=
    Topology.subset_of_isCompact_of_frontier_subset_open_convex
      ((isPolyhedron_space K).isCompact.inter_right (isClosed_Icc.preimage ℓ.continuous))
      hW hWconv (hSlab.nonempty.mono hSW) hSW
  obtain ⟨H, hH, hfix, hfixS, himage⟩ := exists_isPLHomeomorphOn_sphere_surgery_of_convex I
    hSlab hC hconv hpatch hpatchBd hW
    ((inter_subset_inter_left _ (K.convexHull_subset_space hT)).trans hKW)
  exact ⟨T, hT, hcard, hpnot, H, hH, hfix, hfixS, himage⟩

end DifferentialGeometry.Topology.PiecewiseLinear
