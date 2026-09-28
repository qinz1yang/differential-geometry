/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightHalfDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSpanningDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLSphere_slab_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) {a b : ℝ} (hab : a < b)
    (hbelow : ∃ y ∈ K.space, ℓ y < a) (habove : ∃ z ∈ K.space, b < ℓ z)
    {D₀ D₁ : Set E} {g₀ g₁ : (Fin 3 → ℝ) → E}
    (hg₀ : IsPLHomeomorphOn g₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hg₁ : IsPLHomeomorphOn g₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hD₀ : D₀ ⊆ {x | ℓ x = a}) (hD₁ : D₁ ⊆ {x | ℓ x = b})
    (hg₀J : g₀ '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = a})
    (hg₁J : g₁ '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = b}) :
    IsPLSphere 2 ((K.space ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}) ∪ D₀ ∪ D₁) := by
  have hbelowb : ∃ y ∈ K.space, ℓ y < b := hbelow.imp fun _ h => ⟨h.1, h.2.trans hab⟩
  have habovea : ∃ z ∈ K.space, a < ℓ z := habove.imp fun _ h => ⟨h.1, hab.trans h.2⟩
  obtain ⟨f₀, f₁, hf₀, hf₁, hf₀J, -⟩ :=
    exists_isPLHomeomorphOn_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero a hbelow
        habovea
  obtain ⟨f₂, f₃, hf₂, hf₃, -, hf₃J⟩ :=
    exists_isPLHomeomorphOn_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero b hbelowb
        habove
  let A := K.space ∩ {x | a ≤ ℓ x}
  let B := K.space ∩ {x | ℓ x ≤ a}
  let C := K.space ∩ {x | b ≤ ℓ x}
  let P := K.space ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}
  have hJ₀D : K.space ∩ {x | ℓ x = a} ⊆ D₀ := by
    rw [← hg₀J]
    rintro _ ⟨x, hx, rfl⟩
    exact hg₀.bijOn.mapsTo hx.1
  have hJ₁D : K.space ∩ {x | ℓ x = b} ⊆ D₁ := by
    rw [← hg₁J]
    rintro _ ⟨x, hx, rfl⟩
    exact hg₁.bijOn.mapsTo hx.1
  have hAB : A ∪ B = K.space := by
    apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro x hx
    exact (le_total a (ℓ x)).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  have hABinter : A ∩ B = K.space ∩ {x | ℓ x = a} := by
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      exact ⟨hxA.1, le_antisymm hxB.2 hxA.2⟩
    · rintro ⟨hx, hxa⟩
      have hxa' : ℓ x = a := hxa
      exact ⟨⟨hx, hxa'.ge⟩, hx, hxa'.le⟩
  have hAD : A ∩ D₀ = K.space ∩ {x | ℓ x = a} := by
    ext x
    constructor
    · rintro ⟨hxA, hxD⟩
      exact ⟨hxA.1, hD₀ hxD⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hx, (show ℓ x = a from hxa).ge⟩, hJ₀D ⟨hx, hxa⟩⟩
  obtain ⟨F, hF, -⟩ := exists_isPLHomeomorphOn_replace_ball
    (show IsPLBall 2 A from ⟨f₁, hf₁⟩).isPolyhedron hf₀ hg₀ hf₀J hg₀J hABinter hAD
  have hcap : IsPLSphere 2 (A ∪ D₀) := (hAB.symm ▸ hK).of_isPLHomeomorphOn hF
  have hP : IsPolyhedron P := by
    have hpoly := (show IsPLBall 2 A from ⟨f₁, hf₁⟩).isPolyhedron.inter
      (show IsPLBall 2 (K.space ∩ {x | ℓ x ≤ b}) from ⟨f₂, hf₂⟩).isPolyhedron
    have heq : A ∩ (K.space ∩ {x | ℓ x ≤ b}) = P := by
      ext x
      simp only [A, P, mem_inter_iff, mem_ofPred_eq]
      tauto
    exact heq ▸ hpoly
  have hPC : (P ∪ D₀) ∪ C = A ∪ D₀ := by
    ext x
    constructor
    · rintro ((hxP | hxD) | hxC)
      · exact Or.inl ⟨hxP.1, hxP.2.1⟩
      · exact Or.inr hxD
      · exact Or.inl ⟨hxC.1, hab.le.trans hxC.2⟩
    · rintro (hxA | hxD)
      · rcases le_total (ℓ x) b with hle | hge
        · exact Or.inl (Or.inl ⟨hxA.1, hxA.2, hle⟩)
        · exact Or.inr ⟨hxA.1, hge⟩
      · exact Or.inl (Or.inr hxD)
  have hPCinter : (P ∪ D₀) ∩ C = K.space ∩ {x | ℓ x = b} := by
    ext x
    constructor
    · rintro ⟨hxP | hxD, hxC⟩
      · exact ⟨hxP.1, le_antisymm hxP.2.2 hxC.2⟩
      · have hxa := hD₀ hxD
        have hbx : b ≤ ℓ x := hxC.2
        change ℓ x = a at hxa
        exact (hab.not_ge (hxa ▸ hbx)).elim
    · rintro ⟨hxK, hxb⟩
      have hxb' : ℓ x = b := hxb
      exact ⟨Or.inl ⟨hxK, hxb' ▸ hab.le, hxb'.le⟩, hxK, hxb'.ge⟩
  have hPD : (P ∪ D₀) ∩ D₁ = K.space ∩ {x | ℓ x = b} := by
    ext x
    constructor
    · rintro ⟨hxP | hxD₀, hxD₁⟩
      · exact ⟨hxP.1, hD₁ hxD₁⟩
      · exact (hab.ne ((hD₀ hxD₀).symm.trans (hD₁ hxD₁))).elim
    · rintro ⟨hxK, hxb⟩
      have hxb' : ℓ x = b := hxb
      exact ⟨Or.inl ⟨hxK, hxb' ▸ hab.le, hxb'.le⟩, hJ₁D ⟨hxK, hxb⟩⟩
  obtain ⟨G, hG, -⟩ := exists_isPLHomeomorphOn_replace_ball
    (hP.union (show IsPLBall 2 D₀ from ⟨g₀, hg₀⟩).isPolyhedron) hf₃ hg₁ hf₃J hg₁J hPCinter hPD
  exact (hPC.symm ▸ hcap).of_isPLHomeomorphOn hG

theorem exists_isPLSphere_slab_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) {a b : ℝ} (hab : a < b)
    (hbelow : ∃ y ∈ K.space, ℓ y < a) (habove : ∃ z ∈ K.space, b < ℓ z)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (D₀ D₁ : Set E) (g₀ g₁ : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn g₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn g₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      g₀ '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = a} ∧
      g₁ '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = b} ∧
      D₀ ⊆ W ∩ {x | ℓ x = a} ∧ D₁ ⊆ W ∩ {x | ℓ x = b} ∧
      IsPLSphere 2 ((K.space ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}) ∪ D₀ ∪ D₁) := by
  have hbelowb : ∃ y ∈ K.space, ℓ y < b := hbelow.imp fun _ h => ⟨h.1, h.2.trans hab⟩
  have habovea : ∃ z ∈ K.space, a < ℓ z := habove.imp fun _ h => ⟨h.1, hab.trans h.2⟩
  have hJ₀ := isPLSphere_one_fiber_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero a hbelow
      habovea
  have hJ₁ := isPLSphere_one_fiber_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero b hbelowb
      habove
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) h
  obtain ⟨D₀, g₀, hg₀, hg₀J, hD₀⟩ := hJ₀.exists_isPLHomeomorphOn_disk_of_subset_fiber hdimE
    ℓ.toLinearMap hlinear inter_subset_right hW hWconv (inter_subset_left.trans hKW)
  obtain ⟨D₁, g₁, hg₁, hg₁J, hD₁⟩ := hJ₁.exists_isPLHomeomorphOn_disk_of_subset_fiber hdimE
    ℓ.toLinearMap hlinear inter_subset_right hW hWconv (inter_subset_left.trans hKW)
  exact ⟨D₀, D₁, g₀, g₁, hg₀, hg₁, hg₀J, hg₁J, hD₀, hD₁,
    isPLSphere_slab_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero hab hbelow habove hg₀ hg₁
      (hD₀.trans inter_subset_right) (hD₁.trans inter_subset_right) hg₀J hg₁J⟩

end DifferentialGeometry.Topology.PiecewiseLinear
