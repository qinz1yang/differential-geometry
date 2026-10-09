/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section FiniteUnion

theorem interior_iUnion_eq_empty_of_isClosed {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] {F : ι → Set X} (hclosed : ∀ i, IsClosed (F i))
    (hint : ∀ i, interior (F i) = ∅) : interior (⋃ i, F i) = ∅ := by
  classical
  have hfin : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, interior (⋃ i ∈ s, F i) = ∅ := by
    intro s
    refine Finset.induction_on s (by simp) ?_
    intro a t _ ih
    rw [Finset.set_biUnion_insert, interior_union_isClosed_of_interior_empty (hclosed a) ih]
    exact hint a
  have h := key Finset.univ
  simpa using h

end FiniteUnion

section EuclideanModel

theorem exists_isPLHomeomorphOn_euclidean_of_isPLBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ} {P : Set E} (hP : IsPLBall k P) :
    ∃ (Q : Set (EuclideanSpace ℝ (Fin k))) (ρ : E → EuclideanSpace ℝ (Fin k)),
      IsPLBall k Q ∧ IsPLHomeomorphOn ρ P Q := by
  obtain ⟨r, hr⟩ := hP
  set L : (Fin (k + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
    (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi fun i : Fin k => LinearMap.proj i.castSucc) with hLdef
  have hLval : ∀ x : Fin (k + 1) → ℝ,
      L x = (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm fun i : Fin k => x i.castSucc :=
    fun _ => rfl
  have hinj : InjOn (L : (Fin (k + 1) → ℝ) → EuclideanSpace ℝ (Fin k))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin (k + 1))) := by
    intro x hx y hy hxy
    have hco : (fun i : Fin k => x i.castSucc) = fun i : Fin k => y i.castSucc :=
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.injective (by rw [← hLval, ← hLval]; exact hxy)
    have hcoord : ∀ i : Fin k, x i.castSucc = y i.castSucc := fun i => congrFun hco i
    funext j
    refine Fin.lastCases ?_ hcoord j
    have hx1 : ∑ i, x i = 1 := hx.2
    have hy1 : ∑ i, y i = 1 := hy.2
    rw [Fin.sum_univ_castSucc] at hx1 hy1
    have hsum : ∑ i : Fin k, x i.castSucc = ∑ i : Fin k, y i.castSucc :=
      Finset.sum_congr rfl fun i _ => hcoord i
    linarith
  have hA : IsPiecewiseAffineOn (L : (Fin (k + 1) → ℝ) → EuclideanSpace ℝ (Fin k))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin (k + 1))) :=
    (isPiecewiseAffineOn_of_affine_of_isHPolytope L.toAffineMap
      (isHPolytope_stdSimplex (Fin (k + 1)))).congr fun _ _ => rfl
  have hL : IsPLHomeomorphOn (L : (Fin (k + 1) → ℝ) → EuclideanSpace ℝ (Fin k))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin (k + 1))) (L '' Convexity.StdSimplex.coordinateSet ℝ (Fin (k + 1))) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
      (isHPolytope_stdSimplex (Fin (k + 1))).isPolyhedron hA hinj.bijOn_image
  exact ⟨L '' Convexity.StdSimplex.coordinateSet ℝ (Fin (k + 1)),
    (L : (Fin (k + 1) → ℝ) → EuclideanSpace ℝ (Fin k)) ∘
      Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (k + 1))),
    (isPLBall_stdSimplex k).of_isPLHomeomorphOn hL, hr.symm.trans hL⟩

end EuclideanModel

section Surface

variable {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]

theorem IsPLCellOn.inter_eq_empty_of_subset_iUnion {S B : Set M₁} (hS : IsPLCellOn 2 S B)
    {ι : Type*} [Finite ι] {n : ι → ℕ} {C : ι → Set M₁}
    (hC : ∀ i, ∃ Bi : Set M₁, IsPLCellOn (n i) (C i) Bi) (hn : ∀ i, n i ≤ 1)
    (hCS : ∀ i, C i ⊆ S) {V : Set M₁} (hV : IsOpen V) (hsub : V ∩ S ⊆ ⋃ i, C i) :
    V ∩ S = ∅ := by
  classical
  obtain ⟨P, r, u, hr, hu, hSP, -⟩ := hS
  obtain ⟨Q, ρ, hQ, hρ⟩ := exists_isPLHomeomorphOn_euclidean_of_isPLBall (P := P) ⟨r, hr⟩
  set q : M₁ → EuclideanSpace ℝ (Fin 3) := Function.invFunOn u P with hqdef
  set Φ : M₁ → EuclideanSpace ℝ (Fin 2) := ρ ∘ q with hΦdef
  set Ψ : EuclideanSpace ℝ (Fin 2) → M₁ := u ∘ Function.invFunOn ρ P with hΨdef
  have hbu : BijOn u P (u '' P) := hu.injOn.bijOn_image
  have hqP : MapsTo q S P := by
    rw [hSP]
    exact hbu.surjOn.mapsTo_invFunOn
  have huq : ∀ y ∈ S, u (q y) = y := by
    intro y hy
    exact hbu.invOn_invFunOn.2 (hSP ▸ hy)
  have hρP : MapsTo (Function.invFunOn ρ P) Q P := hρ.bijOn.surjOn.mapsTo_invFunOn
  have hρinv : ∀ z ∈ Q, ρ (Function.invFunOn ρ P z) = z := fun z hz =>
    hρ.bijOn.invOn_invFunOn.2 hz
  have hΦQ : ∀ y ∈ S, Φ y ∈ Q := fun y hy => hρ.bijOn.mapsTo (hqP hy)
  have hΨS : ∀ z ∈ Q, Ψ z ∈ S := fun z hz => hSP ▸ mem_image_of_mem u (hρP hz)
  have hΨΦ : ∀ y ∈ S, Ψ (Φ y) = y := by
    intro y hy
    have h1 : Function.invFunOn ρ P (ρ (q y)) = q y := hρ.bijOn.invOn_invFunOn.1 (hqP hy)
    simp only [hΨdef, hΦdef, Function.comp_apply, h1, huq y hy]
  have hΦΨ : ∀ z ∈ Q, Φ (Ψ z) = z := by
    intro z hz
    have h1 : q (u (Function.invFunOn ρ P z)) = Function.invFunOn ρ P z :=
      hu.injOn.leftInvOn_invFunOn (hρP hz)
    simp only [hΨdef, hΦdef, Function.comp_apply, h1, hρinv z hz]
  have hΨcont : ContinuousOn Ψ Q :=
    hu.continuousOn.comp (hρ.isPiecewiseAffineOn_invFunOn.continuousOn) hρP
  have hcells : ∀ i, ∃ F : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall (n i) F ∧ Φ '' C i = F := by
    intro i
    obtain ⟨Bi, Pi, ri, ui, hri, hui, hCi, -⟩ := hC i
    have hbi : IsPLBall (n i) Pi := ⟨ri, hri⟩
    have hsubi : ui '' Pi ⊆ u '' P := by
      rw [← hCi, ← hSP]
      exact hCS i
    have h1 := hui.isPLHomeomorphOn_invFunOn_comp hbi.isPolyhedron hu hsubi
    have himg : (q ∘ ui) '' Pi = q '' C i := by rw [image_comp, ← hCi]
    have hb1 : IsPLBall (n i) (q '' C i) := himg ▸ hbi.of_isPLHomeomorphOn h1
    have hqCP : q '' C i ⊆ P := by
      rintro _ ⟨y, hy, rfl⟩
      exact hqP (hCS i hy)
    have h2 := hρ.restrict hb1.isPolyhedron hqCP
    exact ⟨ρ '' (q '' C i), hb1.of_isPLHomeomorphOn h2, image_comp ρ q (C i)⟩
  choose F hFball hFimg using hcells
  have hFclosed : ∀ i, IsClosed (F i) := fun i => (hFball i).isPolyhedron.isClosed
  have hFint : ∀ i, interior (F i) = ∅ := by
    intro i
    refine (hFball i).interior_eq_empty_of_lt_finrank ?_
    rw [finrank_euclideanSpace_fin]
    exact lt_of_le_of_lt (hn i) one_lt_two
  by_contra hcon
  obtain ⟨y₀, hy₀⟩ := nonempty_iff_ne_empty.mpr hcon
  obtain ⟨V', hV'open, hV'eq⟩ := (continuousOn_iff'.mp hΨcont) V hV
  have hz₀Q : Φ y₀ ∈ Q := hΦQ y₀ hy₀.2
  have hz₀V' : Φ y₀ ∈ V' := by
    have hmem : Φ y₀ ∈ Ψ ⁻¹' V ∩ Q :=
      ⟨by rw [mem_preimage, hΨΦ y₀ hy₀.2]; exact hy₀.1, hz₀Q⟩
    rw [hV'eq] at hmem
    exact hmem.1
  have hclos : Φ y₀ ∈ closure (interior Q) := by
    rw [hQ.closure_interior]
    exact hz₀Q
  obtain ⟨z₁, hz₁⟩ := mem_closure_iff.mp hclos V' hV'open hz₀V'
  have hOopen : IsOpen (V' ∩ interior Q) := hV'open.inter isOpen_interior
  have hOsub : V' ∩ interior Q ⊆ ⋃ i, F i := by
    intro z hz
    have hzQ : z ∈ Q := interior_subset hz.2
    have hzV : Ψ z ∈ V := by
      have hmem : z ∈ V' ∩ Q := ⟨hz.1, hzQ⟩
      rw [← hV'eq] at hmem
      exact hmem.1
    obtain ⟨i, hW⟩ := mem_iUnion.mp (hsub ⟨hzV, hΨS z hzQ⟩)
    exact mem_iUnion.mpr ⟨i, hFimg i ▸ ⟨Ψ z, hW, hΦΨ z hzQ⟩⟩
  have hempty := interior_iUnion_eq_empty_of_isClosed hFclosed hFint
  have : z₁ ∈ interior (⋃ i, F i) := interior_maximal hOsub hOopen hz₁
  rw [hempty] at this
  exact this

end Surface

end DifferentialGeometry.Topology.PiecewiseLinear
