/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalMonodromy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isCylindricalDiagram_stdTriangleLoop :
    IsCylindricalDiagram (fun z : ℝ × ℝ => (stdTriangleLoop z.2, z.1)) (Icc 0 1)
      (stdSimplexBoundary 2 ×ˢ Icc 0 1) := by
  have hend : stdTriangleLoop 0 = stdTriangleLoop 1 := by norm_num [stdTriangleLoop]
  have hloop {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1)
      (hst : stdTriangleLoop s = stdTriangleLoop t) :
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    by_cases hs1 : s = 1
    · by_cases ht1 : t = 1
      · exact Or.inl (hs1.trans ht1.symm)
      · have ht0 : t = 0 := injOn_stdTriangleLoop ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
          ⟨le_rfl, zero_lt_one⟩ (hst.symm.trans (hs1 ▸ hend.symm))
        exact Or.inr (Or.inr ⟨hs1, ht0⟩)
    · by_cases ht1 : t = 1
      · have hs0 : s = 0 := injOn_stdTriangleLoop ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
          ⟨le_rfl, zero_lt_one⟩ (hst.trans (ht1 ▸ hend.symm))
        exact Or.inr (Or.inl ⟨hs0, ht1⟩)
      · exact Or.inl (injOn_stdTriangleLoop ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
          ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ hst)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hswap : IsPiecewiseAffineOn (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        (Icc 0 1 ×ˢ Icc 0 1) :=
      isPiecewiseAffineOn_of_affine_of_isHPolytope
        (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap.toAffineMap
        (isHPolytope_Icc.prod isHPolytope_Icc)
    have hid : IsPiecewiseAffineOn (id : ℝ → ℝ) (Icc 0 1) :=
      isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id.isPiecewiseAffineOn
    have h := (isPiecewiseAffineOn_stdTriangleLoop.prodMap hid).comp hswap
    have hsub : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆
        Prod.swap ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := fun _ hx => ⟨hx.2, hx.1⟩
    rwa [inter_eq_left.mpr hsub] at h
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨stdTriangleLoop_image.subset ⟨x.2, hx.2, rfl⟩, hx.1⟩
    · rintro ⟨y, s⟩ ⟨hy, hs⟩
      obtain ⟨t, ht, hty⟩ := stdTriangleLoop_image.symm.subset hy
      exact ⟨(s, t), ⟨hs, ht⟩, Prod.ext hty rfl⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
      change t = 1 at ht
      subst t
      exact ⟨(s, 0), ⟨hs, rfl⟩, Prod.ext hend rfl⟩
    · rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
      change t = 0 at ht
      subst t
      exact ⟨(s, 1), ⟨hs, rfl⟩, Prod.ext hend.symm rfl⟩
  · intro x hx y hy hxy
    have hfst := congrArg Prod.snd hxy
    rcases hloop hx.2 hy.2 (congrArg Prod.fst hxy) with htime | hends | hends
    · exact Or.inl (Prod.ext hfst htime)
    · exact Or.inr (Or.inl hends)
    · exact Or.inr (Or.inr hends)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCylindricalDiagram.exists_isPLHomeomorphOn_annulus_of_eq_ends
    {f : ℝ × ℝ → E} {S : Set E} (hf : IsCylindricalDiagram f (Icc 0 1) S)
    (hends : ∀ x ∈ Icc 0 1, f (x, 0) = f (x, 1)) :
    ∃ H : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn H (stdSimplexBoundary 2 ×ˢ Icc 0 1) S ∧
      ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 1, H (stdTriangleLoop t, x) = f (x, t) := by
  have hid : IsPLHomeomorphOn (id : ℝ → ℝ) (Icc 0 1) (Icc 0 1) :=
    isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  obtain ⟨H, hH, hHf⟩ := exists_isPLHomeomorphOn_of_eq_endMap isHPolytope_Icc.isPolyhedron
    isCylindricalDiagram_stdTriangleLoop hf hid
    (fun x _ => Prod.ext (by norm_num [stdTriangleLoop]) rfl) hends
  exact ⟨H, hH, fun x hx t ht => hHf (x, t) ⟨hx, ht⟩⟩

theorem IsCylindricalDiagram.exists_isPLHomeomorphOn_annulus_of_isOrientable
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    {f : ℝ × ℝ → E} {S : Set E} (hf : IsCylindricalDiagram f (Icc 0 1) S) (hSK : S ⊆ K.space) :
    ∃ H : (Fin 3 → ℝ) × ℝ → E, IsPLHomeomorphOn H (stdSimplexBoundary 2 ×ˢ Icc 0 1) S := by
  obtain ⟨g, hg, hends⟩ := hf.exists_endMap_id_of_isOrientable_interval K hK hor hSK
  obtain ⟨H, hH, _⟩ := hg.exists_isPLHomeomorphOn_annulus_of_eq_ends hends
  exact ⟨H, hH⟩

end DifferentialGeometry.Topology.PiecewiseLinear
