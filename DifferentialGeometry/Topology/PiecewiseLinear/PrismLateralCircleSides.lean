/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem isPLSphere_stdSimplex_prism_boundary :
    IsPLSphere 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  have hΔ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := isPLBall_stdSimplex 2
  have hΔpoly : IsPolyhedron (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hΔ.isPolyhedron
  obtain ⟨Kd, hKdfin, hKdspace⟩ := hΔpoly.exists_simplicialComplex
  let _ : Finite Kd.faces := hKdfin.to_subtype
  have hKd : IsPLBall 2 Kd.space := hKdspace ▸ hΔ
  have hid : IsPLHomeomorphOn id (Convexity.StdSimplex.coordinateSet ℝ (Fin (1 + 2))) Kd.space := by
    rw [hKdspace]
    exact isPLHomeomorphOn_id_of_isHPolytope (isHPolytope_stdSimplex _)
  have hprism := isPLBall_three_prod hΔ (isPLBall_Icc (zero_lt_one' ℝ))
  obtain ⟨A, hAfin, hAspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 3 A.space := hAspace ▸ hprism
  have hAbd : (boundaryComplex 3 A).space = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {0, 1} ∪
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
    have h := boundaryComplex_space_prism Kd hKd (zero_lt_one' ℝ) A (by rw [hAspace, hKdspace])
    have h2 := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex (n := 1) Kd hid
    rw [image_id, simplexBoundary_stdVertices_space] at h2
    rw [← hKdspace, ← h2]
    convert h using 5
  have hS : IsPLSphere 2 (boundaryComplex 3 A).space := by
    convert isPLSphere_boundaryComplex_space_of_isPLBall A hA
  rwa [hAbd] at hS

theorem exists_isPLHomeomorphOn_lateral_side_of_disk_decomposition
    {K D D' : Set ((Fin 3 → ℝ) × ℝ)} (hKA : K ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
    (hDD' : D ∪ D' = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
    (hDI : D ∩ D' = K) {f' : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ}
    (hf' : IsPLHomeomorphOn f' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D') (hf'b : f' '' stdSimplexBoundary 2 = K)
    {c c' : ℝ} (hcc : c = 0 ∧ c' = 1 ∨ c = 1 ∧ c' = 0)
    (hc : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ) ⊆ D)
    (hc' : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c'} : Set ℝ) ⊆ D') :
    ∃ ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ,
      IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (D ∩ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ stdSimplexBoundary 2, ψ (x, c) = (x, c)) ∧
      ψ '' (stdSimplexBoundary 2 ×ˢ {c'}) = K := by
  set A := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 with hAdef
  set Sg := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ A with hSgdef
  have hSig : IsPLSphere 2 Sg := isPLSphere_stdSimplex_prism_boundary
  have hΔ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := isPLBall_stdSimplex 2
  have hΔpoly : IsPolyhedron (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hΔ.isPolyhedron
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hApoly : IsPolyhedron A := hBpoly.prod isHPolytope_Icc.isPolyhedron
  have hASg : A ⊆ Sg := subset_union_right
  have hpair : ({0, 1} : Set ℝ) = {c, c'} := by
    rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact pair_comm 0 1
  have hcI : c ∈ Icc (0 : ℝ) 1 := by
    rcases hcc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hc'I : c' ∈ Icc (0 : ℝ) 1 := by
    rcases hcc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hcK : c ∉ Ioo (0 : ℝ) 1 := by
    rcases hcc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hcc' : c ≠ c' := by
    rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hEc : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ)) :=
    hΔ.of_isPLHomeomorphOn (hΔpoly.isPLHomeomorphOn_prod_const c)
  have hιc' := hΔpoly.isPLHomeomorphOn_prod_const c'
  have hEc' : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c'} : Set ℝ)) := hΔ.of_isPLHomeomorphOn hιc'
  have hEcSg : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ) ⊆ Sg := by
    intro y hy
    refine Or.inl ⟨hy.1, ?_⟩
    rw [hpair]
    exact Or.inl hy.2
  have hEc'Sg : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c'} : Set ℝ) ⊆ Sg := by
    intro y hy
    refine Or.inl ⟨hy.1, ?_⟩
    rw [hpair]
    exact Or.inr hy.2
  have hEcK : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ)) K := by
    refine disjoint_left.mpr fun y hy hyK => hcK ?_
    have h : y.2 = c := hy.2
    rw [← h]
    exact (hKA hyK).2
  have hEE : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c'} : Set ℝ)) := by
    refine disjoint_left.mpr fun y hy hy' => hcc' ?_
    have h : y.2 = c := hy.2
    have h' : y.2 = c' := hy'.2
    exact h.symm.trans h'
  have hD'Sg : D' ⊆ Sg := by
    rw [← hDD']
    exact subset_union_right
  have hKA' : K ⊆ A := fun y hy => ⟨(hKA hy).1, Ioo_subset_Icc_self (hKA hy).2⟩
  have hKSg : K ⊆ Sg := hKA'.trans hASg
  have hdis0 : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ)) D' := by
    refine disjoint_left.mpr fun y hy hyD' => disjoint_left.mp hEcK hy ?_
    rw [← hDI]
    exact ⟨hc hy, hyD'⟩
  obtain ⟨Φ, hΦ, hΦid, hΦD'⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk hSig hSig hEc
    hEcSg ⟨f', hf'⟩ hD'Sg hdis0 hEc' hEc'Sg hEE hEc.isPolyhedron.isPLHomeomorphOn_id hEcSg
  have hΦD'pl : IsPLHomeomorphOn Φ D' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c'} : Set ℝ)) := by
    have h := hΦ.restrict (IsPLBall.isPolyhedron ⟨f', hf'⟩) hD'Sg
    rwa [hΦD'] at h
  have hrim : Φ '' K = stdSimplexBoundary 2 ×ˢ ({c'} : Set ℝ) := by
    have h := IsPLHomeomorphOn.image_image_stdSimplexBoundary hf' hιc' hΦD'pl
    rw [hf'b] at h
    rw [h, prod_singleton]
  have hψ : IsPLHomeomorphOn (Function.invFunOn Φ Sg) Sg Sg := hΦ.symm
  have himg : Function.invFunOn Φ Sg '' A = D ∩ A := by
    apply Subset.antisymm
    · rintro _ ⟨z, hzA, rfl⟩
      have hySg : Function.invFunOn Φ Sg z ∈ Sg := hψ.bijOn.mapsTo (hASg hzA)
      have hΦy : Φ (Function.invFunOn Φ Sg z) = z := hΦ.bijOn.invOn_invFunOn.2 (hASg hzA)
      have hyD : Function.invFunOn Φ Sg z ∈ D := by
        by_contra hyD
        have hyD' : Function.invFunOn Φ Sg z ∈ D' := by
          have h : Function.invFunOn Φ Sg z ∈ D ∪ D' := by
            rw [hDD']
            exact hySg
          exact Or.resolve_left h hyD
        have hzE : z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c'} : Set ℝ) := by
          rw [← hΦD', ← hΦy]
          exact mem_image_of_mem Φ hyD'
        have hzrim : z ∈ stdSimplexBoundary 2 ×ˢ ({c'} : Set ℝ) := ⟨hzA.1, hzE.2⟩
        rw [← hrim] at hzrim
        obtain ⟨k, hk, hkz⟩ := hzrim
        have hky := hΦ.bijOn.injOn (hKSg hk) hySg (hkz.trans hΦy.symm)
        have hkD : k ∈ D ∩ D' := by
          rw [hDI]
          exact hk
        exact hyD (hky ▸ hkD.1)
      refine ⟨hyD, ?_⟩
      rcases (show Function.invFunOn Φ Sg z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ A
          from hySg) with ⟨hyΔ, hy01⟩ | hyA
      · rw [hpair] at hy01
        rcases hy01 with h | h
        · have hfix := hΦid (show Function.invFunOn Φ Sg z ∈
            Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ) from ⟨hyΔ, h⟩)
          rw [id_eq, hΦy] at hfix
          rw [← hfix]
          exact hzA
        · have hyK : Function.invFunOn Φ Sg z ∈ D ∩ D' := ⟨hyD, hc' ⟨hyΔ, h⟩⟩
          rw [hDI] at hyK
          exact hKA' hyK
      · exact hyA
    · rintro y ⟨hyD, hyA⟩
      have hySg : y ∈ Sg := hASg hyA
      have hΦySg : Φ y ∈ Sg := hΦ.bijOn.mapsTo hySg
      refine ⟨Φ y, ?_, hΦ.bijOn.invOn_invFunOn.1 hySg⟩
      rcases (show Φ y ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ A from hΦySg) with
        ⟨hΦyΔ, hΦy01⟩ | hΦyA
      · rw [hpair] at hΦy01
        rcases hΦy01 with h | h
        · have hfix := hΦid (show Φ y ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ) from ⟨hΦyΔ, h⟩)
          rw [id_eq] at hfix
          have hyy := hΦ.bijOn.injOn (hΦ.bijOn.mapsTo hySg) hySg hfix
          rw [hyy]
          exact hyA
        · have hmem : Φ y ∈ Φ '' D' := by
            rw [hΦD']
            exact ⟨hΦyΔ, h⟩
          obtain ⟨w, hw, hwy⟩ := hmem
          have hwy' := hΦ.bijOn.injOn (hD'Sg hw) hySg hwy
          have hyK : y ∈ D ∩ D' := ⟨hyD, hwy' ▸ hw⟩
          rw [hDI] at hyK
          have hΦK : Φ y ∈ Φ '' K := mem_image_of_mem Φ hyK
          rw [hrim] at hΦK
          exact ⟨hΦK.1, hΦK.2 ▸ hc'I⟩
      · exact hΦyA
  refine ⟨Function.invFunOn Φ Sg, himg ▸ hψ.restrict hApoly hASg, fun x hx => ?_, ?_⟩
  · have hxE : (x, c) ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({c} : Set ℝ) :=
      ⟨hx.1, rfl⟩
    have hfix := hΦid hxE
    rw [id_eq] at hfix
    calc Function.invFunOn Φ Sg (x, c) = Function.invFunOn Φ Sg (Φ (x, c)) := by rw [hfix]
      _ = (x, c) := hΦ.bijOn.invOn_invFunOn.1 (hEcSg hxE)
  · rw [← hrim]
    exact hΦ.bijOn.injOn.invFunOn_image hKSg

theorem IsPLSphere.exists_lateral_sides_of_subset_prism_lateral
    {K : Set ((Fin 3 → ℝ) × ℝ)} (hK : IsPLSphere 1 K)
    (hKA : K ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
    (hess : ¬ ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧ r '' stdSimplexBoundary 2 = K) :
    ∃ ψ₀ ψ₁ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ,
      IsPLHomeomorphOn ψ₀ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (ψ₀ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      IsPLHomeomorphOn ψ₁ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (ψ₁ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      ψ₀ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
        ψ₁ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧
      ψ₀ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∩
        ψ₁ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = K ∧
      (∀ x ∈ stdSimplexBoundary 2, ψ₀ (x, 0) = (x, 0)) ∧
      (∀ x ∈ stdSimplexBoundary 2, ψ₁ (x, 1) = (x, 1)) ∧
      ψ₀ '' (stdSimplexBoundary 2 ×ˢ {1}) = K ∧ ψ₁ '' (stdSimplexBoundary 2 ×ˢ {0}) = K := by
  set A := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 with hAdef
  set Sg := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ A with hSgdef
  have hSig : IsPLSphere 2 Sg := isPLSphere_stdSimplex_prism_boundary
  have hASg : A ⊆ Sg := subset_union_right
  have hKA' : K ⊆ A := fun y hy => ⟨(hKA hy).1, Ioo_subset_Icc_self (hKA hy).2⟩
  have hE₀Sg : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) ⊆ Sg :=
    fun y hy => Or.inl ⟨hy.1, Or.inl hy.2⟩
  have hE₁Sg : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ) ⊆ Sg :=
    fun y hy => Or.inl ⟨hy.1, Or.inr hy.2⟩
  have hE₀K : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ)) K := by
    refine disjoint_left.mpr fun y hy hyK => ?_
    have h := (hKA hyK).2.1
    rw [mem_singleton_iff.mp hy.2] at h
    exact lt_irrefl _ h
  have hE₁K : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)) K := by
    refine disjoint_left.mpr fun y hy hyK => ?_
    have h := (hKA hyK).2.2
    rw [mem_singleton_iff.mp hy.2] at h
    exact lt_irrefl _ h
  obtain ⟨D₁, D₂, hU, hI, f₁, f₂, hf₁, hf₂, hf₁b, hf₂b⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hSig hK (hKA'.trans hASg)
  have hside : ∀ C, C ⊆ Sg → IsPreconnected C → Disjoint C K → C ⊆ D₁ ∨ C ⊆ D₂ := by
    intro C hCSg hC hCK
    refine isPreconnected_iff_subset_of_disjoint_closed.mp hC D₁ D₂
      (IsPLBall.isPolyhedron ⟨f₁, hf₁⟩).isClosed (IsPLBall.isPolyhedron ⟨f₂, hf₂⟩).isClosed
      (by rw [hU]; exact hCSg) ?_
    rw [hI]
    exact hCK.inter_eq
  have hΔ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := isPLBall_stdSimplex 2
  have hE₀ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ)) :=
    hΔ.of_isPLHomeomorphOn (hΔ.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hE₁ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)) :=
    hΔ.of_isPLHomeomorphOn (hΔ.isPolyhedron.isPLHomeomorphOn_prod_const 1)
  have hdisk : ∀ (D D' : Set ((Fin 3 → ℝ) × ℝ)) (f : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → f '' stdSimplexBoundary 2 = K →
      D ∪ D' = Sg → D ∩ D' = K →
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) ⊆ D' →
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ) ⊆ D' → False := by
    intro D D' f hf hfb hDD' hDI h0 h1
    refine hess ⟨D, f, hf, fun y hy => ?_, hfb⟩
    have hySg : y ∈ D ∪ D' := Or.inl hy
    rw [hDD'] at hySg
    rcases (show y ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ A from hySg) with
      ⟨hyΔ, hy01⟩ | hyA
    · have hyD' : y ∈ D' := by
        rcases hy01 with hy0 | hy1
        · exact h0 ⟨hyΔ, hy0⟩
        · exact h1 ⟨hyΔ, hy1⟩
      have hyK : y ∈ D ∩ D' := ⟨hy, hyD'⟩
      rw [hDI] at hyK
      exact hKA' hyK
    · exact hyA
  have hann : ∀ (D D' : Set ((Fin 3 → ℝ) × ℝ)) (f f' : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → f '' stdSimplexBoundary 2 = K →
      IsPLHomeomorphOn f' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' → f' '' stdSimplexBoundary 2 = K →
      D ∪ D' = Sg → D ∩ D' = K →
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) ⊆ D →
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ) ⊆ D' →
      ∃ ψ₀ ψ₁ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ,
        IsPLHomeomorphOn ψ₀ A (ψ₀ '' A) ∧ IsPLHomeomorphOn ψ₁ A (ψ₁ '' A) ∧
        ψ₀ '' A ∪ ψ₁ '' A = A ∧ ψ₀ '' A ∩ ψ₁ '' A = K ∧
        (∀ x ∈ stdSimplexBoundary 2, ψ₀ (x, 0) = (x, 0)) ∧
        (∀ x ∈ stdSimplexBoundary 2, ψ₁ (x, 1) = (x, 1)) ∧
        ψ₀ '' (stdSimplexBoundary 2 ×ˢ {1}) = K ∧ ψ₁ '' (stdSimplexBoundary 2 ×ˢ {0}) = K := by
    intro D D' f f' hf hfb hf' hf'b hDD' hDI h0 h1
    obtain ⟨ψ₀, hψ₀, hψ₀0, hψ₀1⟩ := exists_isPLHomeomorphOn_lateral_side_of_disk_decomposition
      hKA hDD' hDI hf' hf'b (Or.inl ⟨rfl, rfl⟩) h0 h1
    obtain ⟨ψ₁, hψ₁, hψ₁1, hψ₁0⟩ := exists_isPLHomeomorphOn_lateral_side_of_disk_decomposition
      hKA (by rw [union_comm]; exact hDD') (by rw [inter_comm]; exact hDI) hf hfb
      (Or.inr ⟨rfl, rfl⟩) h1 h0
    have hi₀ : ψ₀ '' A = D ∩ A := hψ₀.image_eq
    have hi₁ : ψ₁ '' A = D' ∩ A := hψ₁.image_eq
    refine ⟨ψ₀, ψ₁, hi₀ ▸ hψ₀, hi₁ ▸ hψ₁, ?_, ?_, hψ₀0, hψ₁1, hψ₀1, hψ₁0⟩
    · rw [hi₀, hi₁, ← union_inter_distrib_right, hDD']
      exact inter_eq_right.mpr hASg
    · rw [hi₀, hi₁, ← inter_inter_distrib_right, hDI]
      exact inter_eq_left.mpr hKA'
  rcases hside _ hE₀Sg hE₀.isConnected.isPreconnected hE₀K with h0 | h0 <;>
    rcases hside _ hE₁Sg hE₁.isConnected.isPreconnected hE₁K with h1 | h1
  · exact (hdisk D₂ D₁ f₂ hf₂ hf₂b (by rw [union_comm]; exact hU)
      (by rw [inter_comm]; exact hI) h0 h1).elim
  · exact hann D₁ D₂ f₁ f₂ hf₁ hf₁b hf₂ hf₂b hU hI h0 h1
  · exact hann D₂ D₁ f₂ f₁ hf₂ hf₂b hf₁ hf₁b (by rw [union_comm]; exact hU)
      (by rw [inter_comm]; exact hI) h0 h1
  · exact (hdisk D₁ D₂ f₁ hf₁ hf₁b hU hI h0 h1).elim

end DifferentialGeometry.Topology.PiecewiseLinear
