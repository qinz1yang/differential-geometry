import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierAlignedCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceAlignedBandFilling

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem Section34SolidBandFilling.toFaceAlignedBandFilling_of_carrying_rims
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp As Bs S T D F J₀ J₁ : Set M}
    (hfill : Section34SolidBandFilling Cc Cp As Bs T D F)
    (hS : IsTopologicalSolidTorus S) (hTS : T ⊆ S)
    (hJ₀ : IsPolyhedralSphere (n := 3) 1 J₀)
    (hJ₁ : IsPolyhedralSphere (n := 3) 1 J₁)
    (hdis : Disjoint J₀ J₁)
    (hcarry₀ : CarriesFundamentalGroupOnto J₀ S)
    (hcarry₁ : CarriesFundamentalGroupOnto J₁ S)
    (hF : IsAnnulusOn F J₀ J₁) (hD : IsClosed D) (hDF : D ∩ F = J₀ ∪ J₁) :
    Section34FaceAlignedBandFilling Cc Cp As Bs T D F J₀ J₁ := by
  classical
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  obtain ⟨P, u, R, g, hP, hu, hCc, hRfin, hR, hRP, hsolid, hg, hends,
    -, hfront, hT, hfirst, hsecond, hcontact, hposition⟩ := hfill
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨B, hBfin, hBspace⟩ := isPLBall_unit_square.isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsPLBall 2 B.space := hBspace.symm ▸ isPLBall_unit_square
  have hgB : IsCylindricalDiagram g B.space R.space := hBspace.symm ▸ hg
  have hendsB : ∀ x ∈ B.space, g (x, 0) = g (x, 1) := hBspace.symm ▸ hends
  let L : Fin 2 → Set M := ![J₀, J₁]
  have hL (k : Fin 2) : IsPolyhedralSphere (n := 3) 1 (L k) := by
    fin_cases k
    · exact hJ₀
    · exact hJ₁
  have hLC (k : Fin 2) : L k ⊆ u '' frontier R.space := by
    rw [hfront]
    fin_cases k
    · exact hF.first_subset.trans subset_union_right
    · exact hF.second_subset.trans subset_union_right
  have hpair : Pairwise fun k l => Disjoint (L k) (L l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact (hkl rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hkl rfl).elim
  have hcarry (k : Fin 2) : CarriesFundamentalGroupOnto (L k) S := by
    fin_cases k
    · exact hcarry₀
    · exact hcarry₁
  obtain ⟨g', a, hg', hends', hinj, hfiber⟩ :=
    hu.exists_aligned_cylinder_of_carrying_rims B R hB hR hgB hendsB hRP hS
      (hT.trans hTS) L hL hLC hpair hcarry
  have hBd : (boundaryComplex 2 B).space =
      frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank (by simp [Module.finrank_prod])
      B hB.isCombinatorialManifoldWithBoundary, hBspace]
  have hgfront := hg'.frontier_eq_image_side B R hB hR (by simp)
  rw [hBd] at hgfront
  rw [hBspace] at hg' hends'
  have halign : Section34AlignedBandFilling Cc Cp As Bs T D F J₀ J₁ := by
    refine ⟨P, u, R, g', fun k => (a k : ℝ × ℝ), hP, hu, hCc, hRfin, hR, hRP,
      hsolid, hg', hends', hgfront, hfront, hT, hfirst, hsecond, hcontact, hposition,
      fun k => hBd ▸ (a k).2, ?_, hfiber 0, hfiber 1⟩
    exact fun k l hkl => hinj (Subtype.ext hkl)
  exact halign.toFaceAlignedBandFilling hF hD hDF

end DifferentialGeometry.Topology.PiecewiseLinear
