/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordElimination
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CutAndPaste

open CategoryTheory

namespace DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordConnectors

universe u

variable {X : Type u} [TopologicalSpace X]

def pathArrow {a b : X} (p : Path a b) :
    FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b :=
  Path.Homotopic.Quotient.mk p

def basedPathClass {a : X} (p : Path a a) : FundamentalGroup X a :=
  pathArrow p

theorem basedPathClass_boundaryWord_caseThree {a b : X} (c σ υ : Path a b) (τ φ : Path b a) :
    basedPathClass (σ.trans (τ.trans (υ.trans φ))) =
      basedPathClass (c.trans φ) * basedPathClass (υ.trans c.symm) *
        basedPathClass (c.trans τ) * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (pathArrow σ ≫ (pathArrow τ ≫ (pathArrow υ ≫ pathArrow φ))) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      ((pathArrow c ≫ pathArrow τ) ≫
      ((pathArrow υ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      (pathArrow c ≫ pathArrow φ)))
  simp

theorem basedPathClass_firstCandidate_caseThree {a b : X} (c σ υ : Path a b) :
    basedPathClass (σ.trans υ.symm) =
      (basedPathClass (υ.trans c.symm))⁻¹ * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow υ) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      CategoryTheory.Groupoid.inv
        (pathArrow υ ≫ CategoryTheory.Groupoid.inv (pathArrow c))
  simp

theorem basedPathClass_secondCandidate_caseThree {a b : X} (c σ υ : Path a b)
    (τ φ : Path b a) :
    basedPathClass (σ.trans (φ.trans (υ.trans τ))) =
      basedPathClass (c.trans τ) * basedPathClass (υ.trans c.symm) *
        basedPathClass (c.trans φ) * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (pathArrow σ ≫ (pathArrow φ ≫ (pathArrow υ ≫ pathArrow τ))) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      ((pathArrow c ≫ pathArrow φ) ≫
      ((pathArrow υ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      (pathArrow c ≫ pathArrow τ)))
  simp

theorem basedPathClass_boundaryWord_caseFour {a b : X} (c σ : Path a b) (τ : Path b b)
    (υ : Path b a) (φ : Path a a) :
    basedPathClass (σ.trans (τ.trans (υ.trans φ))) =
      basedPathClass φ * basedPathClass (c.trans υ) *
        basedPathClass (c.trans (τ.trans c.symm)) * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (pathArrow σ ≫ (pathArrow τ ≫ (pathArrow υ ≫ pathArrow φ))) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      ((pathArrow c ≫
        (pathArrow τ ≫ CategoryTheory.Groupoid.inv (pathArrow c))) ≫
      ((pathArrow c ≫ pathArrow υ) ≫ pathArrow φ))
  simp

theorem basedPathClass_firstCandidate_caseFour {a b : X} (c σ : Path a b) (υ : Path b a) :
    basedPathClass (σ.trans υ) =
      basedPathClass (c.trans υ) * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change pathArrow σ ≫ pathArrow υ =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      (pathArrow c ≫ pathArrow υ)
  simp

theorem basedPathClass_secondCandidate_caseFour {a b : X} (c σ : Path a b) (τ : Path b b)
    (υ : Path b a) (φ : Path a a) :
    basedPathClass (σ.trans (τ.symm.trans (υ.trans φ.symm))) =
      (basedPathClass φ)⁻¹ * basedPathClass (c.trans υ) *
        (basedPathClass (c.trans (τ.trans c.symm)))⁻¹ *
        basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change (pathArrow σ ≫ (CategoryTheory.Groupoid.inv (pathArrow τ) ≫
      (pathArrow υ ≫ CategoryTheory.Groupoid.inv (pathArrow φ)))) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      (CategoryTheory.Groupoid.inv
        (pathArrow c ≫ (pathArrow τ ≫ CategoryTheory.Groupoid.inv (pathArrow c))) ≫
      ((pathArrow c ≫ pathArrow υ) ≫ CategoryTheory.Groupoid.inv (pathArrow φ)))
  simp

theorem basedPathClass_boundaryWord_mem_of_caseThree_mem {a b : X}
    {N : Subgroup (FundamentalGroup X a)} [N.Normal] (σ υ : Path a b) (τ φ : Path b a)
    (h₁ : basedPathClass (σ.trans υ.symm) ∈ N)
    (h₂ : basedPathClass (σ.trans (φ.trans (υ.trans τ))) ∈ N) :
    basedPathClass (σ.trans (τ.trans (υ.trans φ))) ∈ N := by
  rw [basedPathClass_firstCandidate_caseThree σ σ υ] at h₁
  rw [basedPathClass_secondCandidate_caseThree σ σ υ τ φ] at h₂
  rw [basedPathClass_boundaryWord_caseThree σ σ υ τ φ]
  set S := basedPathClass (σ.trans σ.symm)
  set T := basedPathClass (σ.trans τ)
  set U := basedPathClass (υ.trans σ.symm)
  set P := basedPathClass (σ.trans φ)
  have k₁ : S⁻¹ * (U⁻¹)⁻¹ ∈ N := by
    have h := N.inv_mem h₁
    rwa [show (U⁻¹ * S)⁻¹ = S⁻¹ * (U⁻¹)⁻¹ by group] at h
  have k₂ : S⁻¹ * P⁻¹ * U⁻¹ * T⁻¹ ∈ N := by
    have h := N.inv_mem h₂
    rwa [show (T * U * P * S)⁻¹ = S⁻¹ * P⁻¹ * U⁻¹ * T⁻¹ by group] at h
  have key : S⁻¹ * T⁻¹ * U⁻¹ * P⁻¹ ∈ N :=
    BoundaryWordElimination.boundaryWord_mem_of_caseThree_mem k₁ k₂
  have h := N.inv_mem key
  rwa [show (S⁻¹ * T⁻¹ * U⁻¹ * P⁻¹)⁻¹ = P * U * T * S by group] at h

theorem basedPathClass_boundaryWord_mem_of_caseFour_mem {a b : X}
    {N : Subgroup (FundamentalGroup X a)} [N.Normal] (σ : Path a b) (τ : Path b b)
    (υ : Path b a) (φ : Path a a) (h₁ : basedPathClass (σ.trans υ) ∈ N)
    (h₂ : basedPathClass (σ.trans (τ.symm.trans (υ.trans φ.symm))) ∈ N) :
    basedPathClass (σ.trans (τ.trans (υ.trans φ))) ∈ N := by
  rw [basedPathClass_firstCandidate_caseFour σ σ υ] at h₁
  rw [basedPathClass_secondCandidate_caseFour σ σ τ υ φ] at h₂
  rw [basedPathClass_boundaryWord_caseFour σ σ τ υ φ]
  set S := basedPathClass (σ.trans σ.symm)
  set T := basedPathClass (σ.trans (τ.trans σ.symm))
  set U := basedPathClass (σ.trans υ)
  set P := basedPathClass φ
  have k₁ : S⁻¹ * U⁻¹ ∈ N := by
    have h := N.inv_mem h₁
    rwa [show (U * S)⁻¹ = S⁻¹ * U⁻¹ by group] at h
  have k₂ : S⁻¹ * (T⁻¹)⁻¹ * U⁻¹ * (P⁻¹)⁻¹ ∈ N := by
    have h := N.inv_mem h₂
    rwa [show (P⁻¹ * U * T⁻¹ * S)⁻¹ = S⁻¹ * (T⁻¹)⁻¹ * U⁻¹ * (P⁻¹)⁻¹ by group] at h
  have key : S⁻¹ * T⁻¹ * U⁻¹ * P⁻¹ ∈ N :=
    BoundaryWordElimination.boundaryWord_mem_of_caseFour_mem k₁ k₂
  have h := N.inv_mem key
  rwa [show (S⁻¹ * T⁻¹ * U⁻¹ * P⁻¹)⁻¹ = P * U * T * S by group] at h

theorem loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap [PathConnectedSpace X]
    {x a : X} (q : Path x a) (N : Subgroup (FundamentalGroup X x)) [N.Normal] (p : Path a a) :
    loopClassMeets (pathToCircle p) x N ↔
      basedPathClass p ∈
        N.comap (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).toMonoidHom := by
  have hiff := loopRepresentativeAlong_mem_iff_loopClassMeets_basedCircle q
    (⟨pathToCircle p, pathToCircle_zero p⟩ : basedCircleLoop a) N
  rw [loopRepresentativeAlong_pathToCircle q p] at hiff
  exact hiff.symm

theorem loopClassMeets_boundaryWord_of_caseThree [PathConnectedSpace X] {x a b : X}
    (σ υ : Path a b) (τ φ : Path b a) (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (h₁ : loopClassMeets (pathToCircle (σ.trans υ.symm)) x N)
    (h₂ : loopClassMeets (pathToCircle (σ.trans (φ.trans (υ.trans τ)))) x N) :
    loopClassMeets (pathToCircle (σ.trans (τ.trans (υ.trans φ)))) x N := by
  have q : Path x a := PathConnectedSpace.somePath x a
  have : (N.comap
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).toMonoidHom).Normal :=
    ‹N.Normal›.comap _
  refine (loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mpr ?_
  exact basedPathClass_boundaryWord_mem_of_caseThree_mem σ υ τ φ
    ((loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mp h₁)
    ((loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mp h₂)

theorem loopClassMeets_boundaryWord_of_caseFour [PathConnectedSpace X] {x a b : X}
    (σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a)
    (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (h₁ : loopClassMeets (pathToCircle (σ.trans υ)) x N)
    (h₂ : loopClassMeets (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))) x N) :
    loopClassMeets (pathToCircle (σ.trans (τ.trans (υ.trans φ)))) x N := by
  have q : Path x a := PathConnectedSpace.somePath x a
  have : (N.comap
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).toMonoidHom).Normal :=
    ‹N.Normal›.comap _
  refine (loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mpr ?_
  exact basedPathClass_boundaryWord_mem_of_caseFour_mem σ τ υ φ
    ((loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mp h₁)
    ((loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mp h₂)

end DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordConnectors
