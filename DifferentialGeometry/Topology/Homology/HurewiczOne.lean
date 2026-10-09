/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.PathHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

noncomputable def integralLoopCycle {x : X} (p : Path x x) : integralSingularCycles 0 X :=
  ⟨integralPathChain p, by rw [LinearMap.mem_ker, integralPathChain_boundary, sub_self]⟩

noncomputable def integralLoopHomologyClass {x : X} (p : Path x x) :
    integralSingularHomology 1 X :=
  (integralSingularHomologyCycleEquiv 0 X).symm
    (Submodule.Quotient.mk (integralLoopCycle p))

theorem integralLoopHomologyClass_eq_of_sub_mem_range {x : X} {p q : Path x x}
    (h : integralPathChain p - integralPathChain q ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom) :
    integralLoopHomologyClass p = integralLoopHomologyClass q := by
  apply (integralSingularHomologyCycleEquiv 0 X).injective
  simp only [integralLoopHomologyClass, AddEquiv.apply_symm_apply]
  change Submodule.Quotient.mk (integralLoopCycle p) =
    (Submodule.Quotient.mk (integralLoopCycle q) :
      integralSingularCycles 0 X ⧸ LinearMap.range (integralSingularBoundaryToCycles 0 X))
  apply (Submodule.Quotient.eq _).mpr
  obtain ⟨c, hc⟩ := h
  exact ⟨c, Subtype.ext hc⟩

theorem integralLoopHomologyClass_eq_of_homotopic {x : X} {p q : Path x x}
    (h : Path.Homotopic p q) : integralLoopHomologyClass p = integralLoopHomologyClass q :=
  integralLoopHomologyClass_eq_of_sub_mem_range (integralPathChain_sub_mem_range_of_homotopic h)

theorem integralLoopHomologyClass_refl (x : X) :
    integralLoopHomologyClass (Path.refl x) = 0 := by
  apply (integralSingularHomologyCycleEquiv 0 X).injective
  rw [map_zero]
  simp only [integralLoopHomologyClass, AddEquiv.apply_symm_apply]
  change (Submodule.Quotient.mk (integralLoopCycle (Path.refl x)) :
    integralSingularCycles 0 X ⧸ LinearMap.range (integralSingularBoundaryToCycles 0 X)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨integralSimplexChain 2 (pathConcatenationSimplex (Path.refl x) (Path.refl x)), ?_⟩
  apply Subtype.ext
  change (integralSingularChains X).d 2 1 _ = integralPathChain (Path.refl x)
  rw [pathConcatenationSimplex_boundary, Path.refl_trans_refl, sub_self, zero_add]

theorem integralLoopHomologyClass_trans {x : X} (p q : Path x x) :
    integralLoopHomologyClass (p.trans q) = integralLoopHomologyClass p +
      integralLoopHomologyClass q := by
  apply (integralSingularHomologyCycleEquiv 0 X).injective
  rw [map_add]
  simp only [integralLoopHomologyClass, AddEquiv.apply_symm_apply]
  change Submodule.Quotient.mk (integralLoopCycle (p.trans q)) =
    (Submodule.Quotient.mk (integralLoopCycle p) + Submodule.Quotient.mk (integralLoopCycle q) :
      integralSingularCycles 0 X ⧸ LinearMap.range (integralSingularBoundaryToCycles 0 X))
  rw [← Submodule.Quotient.mk_add]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-integralSimplexChain 2 (pathConcatenationSimplex p q), ?_⟩
  apply Subtype.ext
  change (integralSingularChains X).d 2 1 _ =
    integralPathChain (p.trans q) - (integralPathChain p + integralPathChain q)
  rw [map_neg, pathConcatenationSimplex_boundary]
  abel

noncomputable def hurewiczOne (x : X) :
    FundamentalGroup X x →* Multiplicative (integralSingularHomology 1 X) where
  toFun := Quotient.lift (fun p => Multiplicative.ofAdd (integralLoopHomologyClass p))
    (fun _ _ h => congrArg Multiplicative.ofAdd (integralLoopHomologyClass_eq_of_homotopic h))
  map_one' := congrArg Multiplicative.ofAdd (integralLoopHomologyClass_refl x)
  map_mul' p q := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction q using Path.Homotopic.Quotient.ind with
      | mk q =>
        change Multiplicative.ofAdd (integralLoopHomologyClass (q.trans p)) =
          Multiplicative.ofAdd (integralLoopHomologyClass p + integralLoopHomologyClass q)
        rw [integralLoopHomologyClass_trans, add_comm]

theorem hurewiczOne_apply {x : X} (p : Path x x) :
    (hurewiczOne x (Path.Homotopic.Quotient.mk p)).toAdd = integralLoopHomologyClass p := rfl

private noncomputable def oneChainClass :
    (integralSingularChains X).X 1 →+
      (integralSingularChains X).X 1 ⧸
        LinearMap.range ((integralSingularChains X).d 2 1).hom :=
  (LinearMap.range ((integralSingularChains X).d 2 1).hom).mkQ.toAddMonoidHom

private theorem oneChainClass_path_trans {a b c : X} (p : Path a b) (q : Path b c) :
    oneChainClass (integralPathChain (p.trans q)) =
      oneChainClass (integralPathChain p) + oneChainClass (integralPathChain q) := by
  rw [← map_add]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-integralSimplexChain 2 (pathConcatenationSimplex p q), ?_⟩
  rw [map_neg, pathConcatenationSimplex_boundary]
  abel

private theorem oneChainClass_path_refl (x : X) :
    oneChainClass (integralPathChain (Path.refl x)) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨integralSimplexChain 2 (pathConcatenationSimplex (Path.refl x) (Path.refl x)), ?_⟩
  rw [pathConcatenationSimplex_boundary, Path.refl_trans_refl, sub_self, zero_add]

private theorem oneChainClass_path_symm {a b : X} (p : Path a b) :
    oneChainClass (integralPathChain p.symm) = -oneChainClass (integralPathChain p) := by
  have h : oneChainClass (integralPathChain (p.trans p.symm)) =
      oneChainClass (integralPathChain (Path.refl a)) :=
    (Submodule.Quotient.eq _).mpr
      (integralPathChain_sub_mem_range_of_homotopic (Path.Homotopic.trans_symm p))
  rw [oneChainClass_path_trans, oneChainClass_path_refl] at h
  exact eq_neg_of_add_eq_zero_right h

theorem hurewiczOne_surjective [PathConnectedSpace X] (x : X) :
    Function.Surjective (hurewiczOne x) := by
  classical
  let r := PathConnectedSpace.somePath x
  let loops (σ : integralSingularSimplex 1 X) : Path x x :=
    (r _).trans ((integralSimplexPath σ).trans (r _).symm)
  let g : (integralSingularChains X).X 1 →ₗ[ℤ] integralSingularCycles 0 X :=
    (integralSingularChainBasis 1 X).constr ℕ (fun σ => integralLoopCycle (loops σ))
  let v : (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 1 :=
    (integralSingularChainBasis 0 X).constr ℕ (fun σ =>
      integralPathChain (r (TopCat.toSSetObj₀Equiv σ)))
  have hg (σ : integralSingularSimplex 1 X) :
      g (integralSimplexChain 1 σ) = integralLoopCycle (loops σ) := by
    rw [← integralSingularChainBasis_apply]
    exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ
  have hv (σ : integralSingularSimplex 0 X) :
      v (integralSimplexChain 0 σ) = integralPathChain (r (TopCat.toSSetObj₀Equiv σ)) := by
    rw [← integralSingularChainBasis_apply]
    exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ
  let _ : Module ℤ ((integralSingularChains X).X 1 ⧸
      LinearMap.range ((integralSingularChains X).d 2 1).hom) := Submodule.Quotient.module _
  let q := (LinearMap.range ((integralSingularChains X).d 2 1).hom).mkQ
  have hlinear : q.comp ((integralSingularCycles 0 X).subtype.comp g) =
      q - q.comp (v.comp ((integralSingularChains X).d 1 0).hom) := by
    apply (integralSingularChainBasis 1 X).ext
    intro σ
    rw [integralSingularChainBasis_apply]
    change oneChainClass (g (integralSimplexChain 1 σ)).val =
      oneChainClass (integralSimplexChain 1 σ) -
        oneChainClass (v ((integralSingularChains X).d 1 0 (integralSimplexChain 1 σ)))
    rw [hg, integralSimplexChain_boundary_one, map_sub, hv, hv, map_sub]
    change oneChainClass (integralPathChain ((r _).trans
      ((integralSimplexPath σ).trans (r _).symm))) = _
    rw [oneChainClass_path_trans, oneChainClass_path_trans, oneChainClass_path_symm,
      integralPathChain_simplexPath]
    abel
  let e := integralSingularHomologyCycleEquiv 0 X
  let _ : Module ℤ (integralSingularCycles 0 X ⧸
      LinearMap.range (integralSingularBoundaryToCycles 0 X)) := Submodule.Quotient.module _
  let _ : Module ℤ (integralSingularHomology 1 X) := AddCommGroup.toIntModule _
  let h := e.symm.toIntLinearEquiv.toLinearMap.comp
      (LinearMap.range (integralSingularBoundaryToCycles 0 X)).mkQ
  have hclass (c : integralSingularCycles 0 X) : h (g c.val) = h c := by
    apply e.injective
    change e (e.symm _) = e (e.symm _)
    simp only [AddEquiv.apply_symm_apply]
    apply (Submodule.Quotient.eq _).mpr
    have hc : (integralSingularChains X).d 1 0 c.val = 0 := c.property
    have heq := LinearMap.congr_fun hlinear c.val
    change oneChainClass (g c.val).val = oneChainClass c.val -
      oneChainClass (v ((integralSingularChains X).d 1 0 c.val)) at heq
    rw [hc, map_zero, map_zero, sub_zero] at heq
    obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp heq
    exact ⟨b, Subtype.ext hb⟩
  let S := (hurewiczOne x).toAdditiveLeft.range.toIntSubmodule
  have hmem (c : (integralSingularChains X).X 1) : h (g c) ∈ S := by
    have hc : c ∈ Submodule.span ℤ (Set.range (integralSingularChainBasis 1 X)) := by
      rw [(integralSingularChainBasis 1 X).span_eq]
      exact Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨σ, rfl⟩ := hc
      rw [integralSingularChainBasis_apply, hg]
      exact ⟨Additive.ofMul (Path.Homotopic.Quotient.mk (loops σ)), rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add c d _ _ hc hd =>
      simpa only [map_add] using S.add_mem hc hd
    | smul a c _ hc =>
      rw [g.map_smul, h.map_smul]
      exact S.smul_mem a hc
  intro a
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (e a.toAdd)
  have hca : h c = a.toAdd := by
    change e.symm (Submodule.Quotient.mk c) = a.toAdd
    rw [hc, AddEquiv.symm_apply_apply]
  have ha : a.toAdd ∈ S := by rw [← hca, ← hclass c]; exact hmem c.val
  obtain ⟨b, hb⟩ := ha
  exact ⟨b.toMul, congrArg Multiplicative.ofAdd hb⟩

end DifferentialGeometry.Topology
