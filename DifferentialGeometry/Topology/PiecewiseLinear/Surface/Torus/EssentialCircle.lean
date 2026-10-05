import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalCircle
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLTorus.exists_cylindrical_diagram_of_nonseparating_circle
    {T J : Set E3} (hT : IsPLTorus T) (hJ : IsPLSphere 1 J) (hJT : J ⊆ T)
    (hconn : IsPreconnected (T \ J)) :
    ∃ g : (Fin 3 → ℝ) × ℝ → E3, IsCylindricalDiagram g (stdSimplexBoundary 2) T ∧
      (∀ x ∈ stdSimplexBoundary 2, g (x, 0) = g (x, 1)) ∧
      g '' (stdSimplexBoundary 2 ×ˢ {(3 / 4 : ℝ)}) = J := by
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hLo := hL.isOrientable_euclidean_three L hLc
  have hβ := hT.bettiOne_le_two
  rw [← hLT] at hβ
  have hχ := hL.eulerChar_eq_two_sub_bettiOne_of_isOrientable L hLc hLo
  have hJL : J ⊆ L.space := hLT ▸ hJT
  have hnonsep : IsPreconnected (L.space \ J) := hLT ▸ hconn
  have hU : L.space ∈ 𝓝ˢ[L.space] J :=
    mem_nhdsSetWithin.mpr ⟨univ, isOpen_univ, subset_univ _, inter_subset_right⟩
  obtain ⟨R, hRfin, hR, -, hRc, hRχ, W, ρ, -, -, -, -, hρ, hzero, -, -, hRbd,
      hWR, hcover, hGm, hGp, hdis⟩ :=
    hL.exists_connected_annulus_complement L hLo hJ hJL hnonsep hU
  let _ : Finite R.faces := hRfin.to_subtype
  have hRbd' := hRbd.trans (show ρ '' (J ×ˢ {(-1 : ℝ), 1}) =
      ρ '' (J ×ˢ {(-1 : ℝ)}) ∪ ρ '' (J ×ˢ {(1 : ℝ)}) by
    rw [← singleton_union, prod_union, image_union])
  have hRχ0 : eulerChar R = 0 := by
    have hle := hR.eulerChar_nonpos_of_boundary_eq_union R hRc hGm hGp hdis hRbd'
    omega
  obtain ⟨h, hh, hh0, hh1⟩ :=
    hR.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero R hRc hRχ0 hGm hGp hdis hRbd'
  obtain ⟨g, hg, -, hgJ⟩ :=
    exists_isCylindricalDiagram_of_annulus_bicollar hh hh0 hh1 hJ.isPolyhedron hρ hzero hWR
  have hRW : R.space ∪ W = T := by rw [union_comm, hcover, hLT]
  obtain ⟨g', hg', hends, heq⟩ := hg.exists_eq_ends_of_isOrientable L
    hL.isCombinatorialManifoldWithBoundary hLo (hRW.trans hLT.symm).subset
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
  refine ⟨g', hRW ▸ hg', hends, ?_⟩
  rw [image_congr fun z hz => heq z ⟨hz.1, by
    rw [mem_singleton_iff.mp hz.2]
    norm_num⟩, hgJ]

theorem IsPLTorus.not_nullhomotopic_inclusion_of_nonseparating_circle
    {T J : Set E3} (hT : IsPLTorus T) (hJ : IsPLSphere 1 J) (hJT : J ⊆ T)
    (hconn : IsPreconnected (T \ J)) :
    ¬ (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)).Nullhomotopic := by
  obtain ⟨g, hg, hends, hgJ⟩ :=
    hT.exists_cylindrical_diagram_of_nonseparating_circle hJ hJT hconn
  have ht : (3 / 4 : ℝ) ∈ Icc 0 1 := by norm_num
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hB : IsPLSphere 1 (stdSimplexBoundary 2) := ⟨id, hBpoly.isPLHomeomorphOn_id⟩
  have hmem : ∀ x ∈ stdSimplexBoundary 2, g (x, (3 / 4 : ℝ)) ∈ J :=
    fun x hx => hgJ ▸ ⟨(x, 3 / 4), ⟨hx, rfl⟩, rfl⟩
  let p : C(stdSimplexBoundary 2, J) :=
    ⟨fun x => ⟨g (x, 3 / 4), hmem x x.2⟩,
      (hg.isPiecewiseAffineOn.continuousOn.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun x => ⟨x.2, ht⟩)).subtype_mk _⟩
  intro hnull
  exact hg.not_nullhomotopic_slice hB hends ht (hnull.comp_left p)

theorem IsPLTorus.exists_isPLHomeomorphOn_disk_of_nullhomotopic_inclusion
    {T J : Set E3} (hT : IsPLTorus T) (hJ : IsPLSphere 1 J) (hJT : J ⊆ T)
    (hnull : (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)).Nullhomotopic) :
    ∃ (D : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ T ∧
        J = r '' stdSimplexBoundary 2 := by
  exact hT.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hJ hJT
    (fun hconn => hT.not_nullhomotopic_inclusion_of_nonseparating_circle hJ hJT hconn hnull)

end DifferentialGeometry.Topology.PiecewiseLinear
