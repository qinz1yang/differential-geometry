/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity
import DifferentialGeometry.Topology.PiecewiseLinear.PrismLateralCircleSides
import DifferentialGeometry.Topology.PiecewiseLinear.TubeOfGraphDualCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem isConnected_prism_lateral_sdiff_iUnion {ι : Type*} [Finite ι]
    {D : ι → Set ((Fin 3 → ℝ) × ℝ)} (hD : ∀ i, IsPLBall 2 (D i))
    (hDA : ∀ i, D i ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j)) :
    IsConnected ((stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) \ ⋃ i, D i) := by
  let A₀ := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ)
  let A₁ := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)
  let S := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
    stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let Q : Option (Option ι) → Set ((Fin 3 → ℝ) × ℝ)
    | none => A₀
    | some none => A₁
    | some (some i) => D i
  have hΔ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := isPLBall_stdSimplex 2
  have hQ : ∀ i, IsPLBall 2 (Q i) := by
    intro i
    cases i with
    | none => exact hΔ.of_isPLHomeomorphOn (hΔ.isPolyhedron.isPLHomeomorphOn_prod_const 0)
    | some i =>
      cases i with
      | none => exact hΔ.of_isPLHomeomorphOn (hΔ.isPolyhedron.isPLHomeomorphOn_prod_const 1)
      | some i => exact hD i
  have hQS : ∀ i, Q i ⊆ S := by
    intro i
    cases i with
    | none => exact fun x hx => Or.inl ⟨hx.1, Or.inl hx.2⟩
    | some i =>
      cases i with
      | none => exact fun x hx => Or.inl ⟨hx.1, Or.inr hx.2⟩
      | some i => exact fun x hx => Or.inr ⟨(hDA i hx).1, (hDA i hx).2.1.le,
          (hDA i hx).2.2.le⟩
  have h₀₁ : Disjoint A₀ A₁ := by
    apply disjoint_left.mpr
    rintro x ⟨-, hx₀⟩ ⟨-, hx₁⟩
    have h₀ : x.2 = 0 := hx₀
    have h₁ : x.2 = 1 := hx₁
    linarith
  have h₀D : ∀ i, Disjoint A₀ (D i) := by
    intro i
    apply disjoint_left.mpr
    rintro x ⟨-, hx₀⟩ hxD
    have h₀ : x.2 = 0 := hx₀
    have hpos := (hDA i hxD).2.1
    linarith
  have h₁D : ∀ i, Disjoint A₁ (D i) := by
    intro i
    apply disjoint_left.mpr
    rintro x ⟨-, hx₁⟩ hxD
    have h₁ : x.2 = 1 := hx₁
    have hlt := (hDA i hxD).2.2
    linarith
  have hQdis : Pairwise fun i j => Disjoint (Q i) (Q j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        cases j with
        | none => exact h₀₁
        | some j => exact h₀D j
    | some i =>
      cases i with
      | none =>
        cases j with
        | none => exact h₀₁.symm
        | some j =>
          cases j with
          | none => exact (hij rfl).elim
          | some j => exact h₁D j
      | some i =>
        cases j with
        | none => exact (h₀D i).symm
        | some j =>
          cases j with
          | none => exact (h₁D i).symm
          | some j => exact hdisj (fun h => hij (congrArg (some ∘ some) h))
  have hconn := isPLSphere_stdSimplex_prism_boundary.isConnected_sdiff_iUnion_of_isPLBall_two
    hQ hQS hQdis
  have heq : S \ ⋃ i, Q i = (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) \ ⋃ i, D i := by
    ext x
    constructor
    · rintro ⟨hxS, hxQ⟩
      have hn₀ : x ∉ A₀ := fun h => hxQ (mem_iUnion.mpr ⟨none, h⟩)
      have hn₁ : x ∉ A₁ := fun h => hxQ (mem_iUnion.mpr ⟨some none, h⟩)
      have hxlat : x ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
        rcases hxS with ⟨hxΔ, hx₀ | hx₁⟩ | hxlat
        · exact (hn₀ ⟨hxΔ, hx₀⟩).elim
        · exact (hn₁ ⟨hxΔ, hx₁⟩).elim
        · exact hxlat
      refine ⟨⟨hxlat.1, ?_, ?_⟩, ?_⟩
      · exact lt_of_le_of_ne hxlat.2.1 (fun h => hn₀ ⟨hxlat.1.1, h.symm⟩)
      · exact lt_of_le_of_ne hxlat.2.2 (fun h => hn₁ ⟨hxlat.1.1, h⟩)
      · intro hxD
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxD
        exact hxQ (mem_iUnion.mpr ⟨some (some i), hi⟩)
    · rintro ⟨hxlat, hxD⟩
      refine ⟨Or.inr ⟨hxlat.1, hxlat.2.1.le, hxlat.2.2.le⟩, ?_⟩
      intro hxQ
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxQ
      cases i with
      | none => exact hxlat.2.1.ne' hi.2
      | some i =>
        cases i with
        | none => exact hxlat.2.2.ne hi.2
        | some i => exact hxD (mem_iUnion.mpr ⟨i, hi⟩)
  rwa [heq] at hconn

theorem IsPLAnnulusWithEnds.isConnected_sdiff_ends_iUnion_of_isPLBall_two
    {ι : Type*} [Finite ι] {A J₀ J₁ : Set E3} (hA : IsPLAnnulusWithEnds A J₀ J₁)
    {D : ι → Set E3} (hD : ∀ i, IsPLBall 2 (D i))
    (hDA : ∀ i, D i ⊆ A \ (J₀ ∪ J₁))
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j)) :
    IsConnected ((A \ (J₀ ∪ J₁)) \ ⋃ i, D i) := by
  classical
  obtain ⟨J, ρ, hJ, hρ, h₀, h₁⟩ := hA
  obtain ⟨f, hf⟩ := hJ
  let g := ρ ∘ Prod.map f id
  let L := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let O := stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1
  have hg : IsPLHomeomorphOn g L A :=
    (hf.prodMap (isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id)).trans hρ
  have hg₀ : g '' (stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ)) = J₀ := by
    simp only [g, image_comp, prodMap_image_prod, image_id, hf.image_eq, ← h₀]
  have hg₁ : g '' (stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ)) = J₁ := by
    simp only [g, image_comp, prodMap_image_prod, image_id, hf.image_eq, ← h₁]
  have hOL : O ⊆ L := fun x hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  have hgO : g '' O = A \ (J₀ ∪ J₁) := by
    have hdiff : O = L \ (stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ) ∪
        stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ)) := by
      ext x
      simp only [O, L, mem_prod, mem_Ioo, mem_sdiff, mem_Icc, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨hx, hlo, hhi⟩
        exact ⟨⟨hx, hlo.le, hhi.le⟩, fun h => h.elim (fun h => hlo.ne' h.2)
          (fun h => hhi.ne h.2)⟩
      · rintro ⟨⟨hx, hlo, hhi⟩, hn⟩
        exact ⟨hx, lt_of_le_of_ne hlo (fun h => hn (Or.inl ⟨hx, h.symm⟩)),
          lt_of_le_of_ne hhi (fun h => hn (Or.inr ⟨hx, h⟩))⟩
    have hends : stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ) ∪
        stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ) ⊆ L := by
      rintro x (⟨hx, hxt⟩ | ⟨hx, hxt⟩)
      · have ht : x.2 = 0 := hxt
        exact ⟨hx, by rw [ht]; exact ⟨le_rfl, zero_le_one⟩⟩
      · have ht : x.2 = 1 := hxt
        exact ⟨hx, by rw [ht]; exact ⟨zero_le_one, le_rfl⟩⟩
    rw [hdiff, hg.bijOn.injOn.image_sdiff_subset hends, hg.image_eq,
      image_union, hg₀, hg₁]
  let Q i := Function.invFunOn g L '' D i
  have hQA : ∀ i, D i ⊆ A := fun i => (hDA i).trans sdiff_subset
  have hQ : ∀ i, IsPLBall 2 (Q i) := fun i =>
    (hD i).of_isPLHomeomorphOn (hg.symm.restrict (hD i).isPolyhedron (hQA i))
  have hQO : ∀ i, Q i ⊆ O := by
    rintro i _ ⟨x, hxD, rfl⟩
    obtain ⟨y, hyO, hgy⟩ := hgO.symm.subset (hDA i hxD)
    rw [← hgy, hg.bijOn.invOn_invFunOn.1 (hOL hyO)]
    exact hyO
  have hQdis : Pairwise fun i j => Disjoint (Q i) (Q j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro _ ⟨x, hxi, rfl⟩ ⟨y, hyj, hxy⟩
    have hxy' : y = x := hg.symm.bijOn.injOn (hQA j hyj) (hQA i hxi) hxy
    exact disjoint_left.mp (hdisj hij) hxi (hxy' ▸ hyj)
  have hconn := isConnected_prism_lateral_sdiff_iUnion hQ hQO hQdis
  have hQmap (i : ι) : g '' Q i = D i := by
    change g '' (Function.invFunOn g L '' D i) = D i
    rw [image_image]
    calc
      (g ∘ Function.invFunOn g L) '' D i = id '' D i :=
        image_congr fun x hx => hg.bijOn.invOn_invFunOn.2 (hQA i hx)
      _ = D i := image_id _
  have heq : g '' (O \ ⋃ i, Q i) = (A \ (J₀ ∪ J₁)) \ ⋃ i, D i := by
    rw [(hg.bijOn.injOn.mono hOL).image_sdiff_subset (iUnion_subset hQO), hgO, image_iUnion]
    simp only [hQmap]
  rw [← heq]
  exact hconn.image g (hg.isPiecewiseAffineOn.continuousOn.mono (sdiff_subset.trans hOL))

theorem IsPLAnnulusWithEnds.ends_subset_closure_sdiff_ends_sdiff
    {A J₀ J₁ : Set E3} (hA : IsPLAnnulusWithEnds A J₀ J₁) {D : Set E3}
    (hD : IsClosed D) (hdis : Disjoint (J₀ ∪ J₁) D) :
    J₀ ∪ J₁ ⊆ closure ((A \ (J₀ ∪ J₁)) \ D) := by
  classical
  obtain ⟨K, hKfin, hK, -, hKA, hKb⟩ := hA.exists_complex
  let _ : Finite K.faces := hKfin.to_subtype
  have hdense : A ⊆ closure (A \ (J₀ ∪ J₁)) := by
    rw [← hKA, ← hKb]
    exact hK.space_subset_closure_sdiff_boundaryComplex_space
  have hends : J₀ ∪ J₁ ⊆ A := by
    rw [← hKA, ← hKb]
    exact boundaryComplex_space_subset 2 K
  intro x hx
  have hxO : x ∈ Dᶜ := disjoint_left.mp hdis hx
  have hxcl : x ∈ closure (Dᶜ ∩ (A \ (J₀ ∪ J₁))) :=
    hD.isOpen_compl.inter_closure ⟨hxO, hdense (hends hx)⟩
  exact closure_mono (show Dᶜ ∩ (A \ (J₀ ∪ J₁)) ⊆ (A \ (J₀ ∪ J₁)) \ D from
    fun _ hy => ⟨hy.2, hy.1⟩) hxcl

end DifferentialGeometry.Topology.PiecewiseLinear
