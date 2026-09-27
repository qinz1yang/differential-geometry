/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.DisjointGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_annulus_of_isPLCirclePositive
    {S : Set E} {A : Set F} {ρ : E × ℝ → F} {u : E → E}
    (hS : IsPLSphere 1 S) (hρ : IsPLHomeomorphOn ρ (S ×ˢ Icc (0 : ℝ) 1) A)
    (hu : IsPLHomeomorphOn u S S) (hpos : IsPLCirclePositive S u) :
    ∃ g : F → F, IsPLHomeomorphOn g A A ∧
      (∀ x ∈ S, g (ρ (x, 0)) = ρ (x, 0)) ∧
      (∀ x ∈ S, g (ρ (x, 1)) = ρ (u x, 1)) := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := isPLPseudoIsotopicToId_of_isPLCirclePositive hS hu hpos
  refine ⟨ρ ∘ Φ ∘ Function.invFunOn ρ (S ×ˢ Icc (0 : ℝ) 1),
    (hρ.symm.trans hΦ).trans hρ, ?_, ?_⟩
  · intro x hx
    change ρ (Φ (Function.invFunOn ρ (S ×ˢ Icc (0 : ℝ) 1) (ρ (x, 0)))) = ρ (x, 0)
    rw [hρ.bijOn.invOn_invFunOn.1 ⟨hx, by norm_num⟩, hΦ0 x hx]
  · intro x hx
    change ρ (Φ (Function.invFunOn ρ (S ×ˢ Icc (0 : ℝ) 1) (ρ (x, 1)))) = ρ (u x, 1)
    rw [hρ.bijOn.invOn_invFunOn.1 ⟨hx, by norm_num⟩, hΦ1 x hx]

theorem exists_isPLHomeomorphOn_of_circle_collars
    {ι : Type*} [Finite ι] {S : ι → Set E} {A : ι → Set F} {B : Set F}
    {ρ : ι → E × ℝ → F} {u : ι → E → E}
    (hS : ∀ i, IsPLSphere 1 (S i)) (hB : IsPolyhedron B)
    (hρ : ∀ i, IsPLHomeomorphOn (ρ i) (S i ×ˢ Icc (0 : ℝ) 1) (A i))
    (hdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hinter : ∀ i, A i ∩ B ⊆ ρ i '' (S i ×ˢ ({0} : Set ℝ)))
    (hu : ∀ i, IsPLHomeomorphOn (u i) (S i) (S i))
    (hpos : ∀ i, IsPLCirclePositive (S i) (u i)) :
    ∃ g : F → F, IsPLHomeomorphOn g (B ∪ ⋃ i, A i) (B ∪ ⋃ i, A i) ∧
      EqOn g id B ∧
      (∀ i, EqOn g id (ρ i '' (S i ×ˢ ({0} : Set ℝ)))) ∧
      (∀ i x, x ∈ S i → g (ρ i (x, 1)) = ρ i (u i x, 1)) ∧
      ∀ i, g '' A i = A i := by
  classical
  have hA (i : ι) : IsPolyhedron (A i) := by
    rw [← (hρ i).image_eq]
    exact ((hS i).isPolyhedron.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      (hρ i).isPiecewiseAffineOn (hρ i).bijOn.injOn
  have hlocal (i : ι) :=
    exists_isPLHomeomorphOn_annulus_of_isPLCirclePositive (hS i) (hρ i) (hu i) (hpos i)
  choose f hf hf0 hf1 using hlocal
  obtain ⟨q, hq, hqf⟩ :=
    exists_isPLHomeomorphOn_iUnion_of_pairwise_disjoint hA hf hdis hdis
  have hq0 (i : ι) : EqOn q id (ρ i '' (S i ×ˢ ({0} : Set ℝ))) := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have ht0 : t = 0 := ht
    subst t
    exact (hqf i ((hρ i).bijOn.mapsTo ⟨hx, by norm_num⟩)).trans (hf0 i x hx)
  have hqB : EqOn q id ((⋃ i, A i) ∩ B) := by
    rintro x ⟨hx, hxB⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hq0 i (hinter i ⟨hi, hxB⟩)
  have hidq : EqOn id q (B ∩ ⋃ i, A i) := by
    intro x hx
    exact (hqB ⟨hx.2, hx.1⟩).symm
  obtain ⟨g, hg, hgB, hgq⟩ := exists_isPLHomeomorphOn_union hB (IsPolyhedron.iUnion hA)
    hB.isPLHomeomorphOn_id hq hidq (fun x hx => ⟨x, hx, rfl⟩)
  refine ⟨g, hg, hgB, ?_, ?_, ?_⟩
  · intro i x hx
    have hxA : x ∈ A i := by
      obtain ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩ := hx
      have ht0 : t = 0 := ht
      subst t
      exact (hρ i).bijOn.mapsTo ⟨hy, by norm_num⟩
    exact (hgq (mem_iUnion.mpr ⟨i, hxA⟩)).trans (hq0 i hx)
  · intro i x hx
    have hxA := (hρ i).bijOn.mapsTo (show (x, (1 : ℝ)) ∈ S i ×ˢ Icc (0 : ℝ) 1 from
      ⟨hx, by norm_num⟩)
    exact (hgq (mem_iUnion.mpr ⟨i, hxA⟩)).trans ((hqf i hxA).trans (hf1 i x hx))
  · intro i
    calc
      g '' A i = f i '' A i := image_congr fun x hx =>
        (hgq (mem_iUnion.mpr ⟨i, hx⟩)).trans (hqf i hx)
      _ = A i := (hf i).image_eq

theorem IsPLHomeomorphOn.exists_extension_of_positive_boundary_corrections
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    {ι : Type*} [Finite ι] {S : ι → Set E} {A : ι → Set F} {B : Set F} {P : Set D}
    {ρ : ι → E × ℝ → F} {u : ι → E → E} {σ : ι → E → D} {f : D → F}
    (hf : IsPLHomeomorphOn f P (B ∪ ⋃ i, A i))
    (hS : ∀ i, IsPLSphere 1 (S i)) (hB : IsPolyhedron B)
    (hρ : ∀ i, IsPLHomeomorphOn (ρ i) (S i ×ˢ Icc (0 : ℝ) 1) (A i))
    (hdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hinter : ∀ i, A i ∩ B ⊆ ρ i '' (S i ×ˢ ({0} : Set ℝ)))
    (hu : ∀ i, IsPLHomeomorphOn (u i) (S i) (S i))
    (hpos : ∀ i, IsPLCirclePositive (S i) (u i))
    (hboundary : ∀ i x, x ∈ S i → f (σ i x) = ρ i (x, 1)) :
    ∃ g : D → F, IsPLHomeomorphOn g P (B ∪ ⋃ i, A i) ∧
      EqOn g f (f ⁻¹' B) ∧
      ∀ i x, x ∈ S i → g (σ i x) = ρ i (u i x, 1) := by
  obtain ⟨q, hq, hqB, -, hq1, -⟩ :=
    exists_isPLHomeomorphOn_of_circle_collars hS hB hρ hdis hinter hu hpos
  refine ⟨q ∘ f, hf.trans hq, ?_, ?_⟩
  · intro x hx
    exact hqB hx
  · intro i x hx
    change q (f (σ i x)) = ρ i (u i x, 1)
    rw [hboundary i x hx]
    exact hq1 i x hx

end DifferentialGeometry.Topology.PiecewiseLinear
