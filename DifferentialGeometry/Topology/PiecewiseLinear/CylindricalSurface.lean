/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCylindricalDiagram.exists_surface_annulus_pair {J : Set E} (hJ : IsPLSphere 1 J)
    {f : E × ℝ → F} {S : Set F} (hf : IsCylindricalDiagram f J S)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ K A R : Geometry.SimplicialComplex ℝ F,
      K.faces.Finite ∧ A.faces.Finite ∧ R.faces.Finite ∧
      IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧ K.space = S ∧
      IsCombinatorialManifoldWithBoundary 2 A ∧ IsConnected A.space ∧
      IsCombinatorialManifoldWithBoundary 2 R ∧ IsConnected R.space ∧
      A.space = f '' (J ×ˢ Icc 0 a) ∧ R.space = f '' (J ×ˢ Icc a 1) ∧
      A.space ∪ R.space = K.space ∧ A.space ∩ R.space = f '' (J ×ˢ {0, a}) ∧
      (boundaryComplex 2 A).space = f '' (J ×ˢ {0, a}) ∧
      (boundaryComplex 2 R).space = f '' (J ×ˢ {0, a}) := by
  have hleft := hf.isPLHomeomorphOn_strip hJ.isPolyhedron le_rfl ha.2.le (Or.inr ha.2)
  have hright := hf.isPLHomeomorphOn_strip hJ.isPolyhedron ha.1.le le_rfl (Or.inl ha.1)
  obtain ⟨A, hAfin, hA, hAc, hAsp, hAbd⟩ := hleft.exists_annulus_complex hJ ha.1
  obtain ⟨R, hRfin, hR, hRc, hRsp, hRbd⟩ := hright.exists_annulus_complex hJ ha.2
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite R.faces := hRfin.to_subtype
  have hpair : f '' (J ×ˢ {0, a}) = f '' (J ×ˢ {0}) ∪ f '' (J ×ˢ {a}) := by
    rw [← image_union, ← prod_union, singleton_union]
  have hRbd' : (boundaryComplex 2 R).space = f '' (J ×ˢ {0, a}) := by
    rw [hRbd, hpair, ← hf.image_top_eq_bottom, union_comm]
    rw [← image_union, ← prod_union, singleton_union]
  have hinter : A.space ∩ R.space = f '' (J ×ˢ {0, a}) := by
    rw [hAsp, hRsp, hf.image_strip_inter ha, hpair]
  obtain ⟨K, hKfin, hK, hKsp⟩ := exists_isCombinatorialManifold_space_union A R hA hR
    (hinter.trans hAbd.symm) (hinter.trans hRbd'.symm)
  have hKc : IsConnected K.space := by
    rw [hKsp]
    apply IsConnected.union ?_ hAc hRc
    obtain ⟨x, hx⟩ := hJ.nonempty
    exact ⟨f (x, a), by rw [hinter]; exact ⟨(x, a), ⟨hx, Or.inr rfl⟩, rfl⟩⟩
  have hKspace : K.space = S := by
    rw [hKsp, hAsp, hRsp, hf.image_strip_union ⟨ha.1.le, ha.2.le⟩]
  exact ⟨K, A, R, hKfin, hAfin, hRfin, hK, hKc, hKspace, hA, hAc, hR, hRc,
    hAsp, hRsp, hKsp.symm, hinter, hAbd, hRbd'⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem IsCylindricalDiagram.image_subcylinder_inter_slice {P J : Set E} {S : Set F}
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f P S) (hJP : J ⊆ P)
    (hends : f '' (J ×ˢ {(1 : ℝ)}) = f '' (J ×ˢ {(0 : ℝ)}))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    f '' (J ×ˢ Icc (0 : ℝ) 1) ∩ f '' (P ×ˢ {t}) = f '' (J ×ˢ {t}) := by
  have hinj₀ : InjOn f (P ×ˢ {(0 : ℝ)}) := by
    simpa only [Icc_self] using hf.injOn_strip (a := 0) (b := 0)
      le_rfl zero_le_one (Or.inr zero_lt_one)
  have hinj₁ : InjOn f (P ×ˢ {(1 : ℝ)}) := by
    simpa only [Icc_self] using hf.injOn_strip (a := 1) (b := 1)
      zero_le_one le_rfl (Or.inl zero_lt_one)
  apply Subset.antisymm
  · rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
    rcases hf.eq_or_endpoints x ⟨hJP hx.1, hx.2⟩ y ⟨hy.1, hy.2.symm ▸ ht⟩
      hyx.symm with hxy | hend | hend
    · exact ⟨y, ⟨(congrArg Prod.fst hxy) ▸ hx.1, hy.2⟩, hyx⟩
    · have hx0 : f x ∈ f '' (J ×ˢ {(0 : ℝ)}) := ⟨x, ⟨hx.1, hend.1⟩, rfl⟩
      obtain ⟨w, hw, hwx⟩ := hends.symm ▸ hx0
      have hwy := hinj₁ ⟨hJP hw.1, hw.2⟩ ⟨hy.1, hend.2⟩ (hwx.trans hyx.symm)
      exact ⟨y, ⟨(congrArg Prod.fst hwy) ▸ hw.1, hy.2⟩, hyx⟩
    · have hx1 : f x ∈ f '' (J ×ˢ {(1 : ℝ)}) := ⟨x, ⟨hx.1, hend.1⟩, rfl⟩
      obtain ⟨w, hw, hwx⟩ := hends ▸ hx1
      have hwy := hinj₀ ⟨hJP hw.1, hw.2⟩ ⟨hy.1, hend.2⟩ (hwx.trans hyx.symm)
      exact ⟨y, ⟨(congrArg Prod.fst hwy) ▸ hw.1, hy.2⟩, hyx⟩
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, ⟨hx.1, hx.2.symm ▸ ht⟩, rfl⟩, ⟨x, ⟨hJP hx.1, hx.2⟩, rfl⟩⟩

omit [FiniteDimensional ℝ F] in
theorem IsCylindricalDiagram.closure_sdiff_image_strip {P : Set E} {S : Set F}
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f P S) (hP : IsCompact P)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    closure (S \ f '' (P ×ˢ Icc 0 a)) = f '' (P ×ˢ Icc a 1) := by
  have hset : S \ f '' (P ×ˢ Icc 0 a) = f '' (P ×ˢ Ioo a 1) := by
    apply Subset.antisymm
    · rintro z ⟨hz, hn⟩
      obtain ⟨x, hx, rfl⟩ := hf.image_eq.symm ▸ hz
      have hax : a < x.2 := lt_of_not_ge fun h => hn ⟨x, ⟨hx.1, hx.2.1, h⟩, rfl⟩
      have hx1 : x.2 ≠ 1 := by
        intro h
        have hb : f x ∈ f '' (P ×ˢ {0}) := hf.image_top_eq_bottom ▸ ⟨x, ⟨hx.1, h⟩, rfl⟩
        have hsub : P ×ˢ {(0 : ℝ)} ⊆ P ×ˢ Icc 0 a :=
          fun _ hy => ⟨hy.1, hy.2.symm ▸ ⟨le_rfl, ha.1.le⟩⟩
        exact hn (image_mono hsub hb)
      exact ⟨x, ⟨hx.1, hax, lt_of_le_of_ne hx.2.2 hx1⟩, rfl⟩
    · rintro z ⟨x, hx, rfl⟩
      have hxI : x ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hx.1, ha.1.le.trans hx.2.1.le, hx.2.2.le⟩
      refine ⟨hf.image_eq ▸ ⟨x, hxI, rfl⟩, ?_⟩
      rintro ⟨y, hy, hyx⟩
      rcases hf.eq_or_endpoints x hxI y ⟨hy.1, hy.2.1, hy.2.2.trans ha.2.le⟩
        hyx.symm with hxy | hend | hend
      · have hs := congrArg Prod.snd hxy
        exact hx.2.1.not_ge (hs.symm ▸ hy.2.2)
      · exact (ha.1.trans hx.2.1).ne' hend.1
      · exact hx.2.2.ne hend.1
  rw [hset]
  have hc : ContinuousOn f (P ×ˢ Icc a 1) := hf.isPiecewiseAffineOn.continuousOn.mono
    (fun _ hz => ⟨hz.1, ha.1.le.trans hz.2.1, hz.2.2⟩)
  have hcl : closure (P ×ˢ Ioo a 1) = P ×ˢ Icc a 1 := by
    rw [closure_prod_eq, hP.isClosed.closure_eq, closure_Ioo ha.2.ne]
  apply Subset.antisymm
  · exact closure_minimal (image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self))
      ((hP.prod isCompact_Icc).image_of_continuousOn hc).isClosed
  · have h := (hcl.symm ▸ hc).image_closure
    rwa [hcl] at h

end DifferentialGeometry.Topology.PiecewiseLinear
