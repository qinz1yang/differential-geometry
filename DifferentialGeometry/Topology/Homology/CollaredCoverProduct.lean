/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.CollaredCover
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.Homology.MayerVietorisProduct
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCollarHomotopy

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology

private noncomputable def collarZeroHomotopyEquiv
    {C X : Type} [TopologicalSpace C] [TopologicalSpace X] {e : C → X}
    (c : ThreeManifold.TwoSidedCollar e) : C ≃ₕ c.range := by
  let q : (C × ℝ) ≃ₕ C :=
    { toFun := ⟨Prod.fst, continuous_fst⟩
      invFun := ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩
      left_inv := ⟨{
        toFun := fun p => (p.2.1, p.1.val * p.2.2)
        continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
          ((continuous_subtype_val.comp continuous_fst).mul
            (continuous_snd.comp continuous_snd))
        map_zero_left := by intro x; simp
        map_one_left := by intro x; simp }⟩
      right_inv := ContinuousMap.Homotopic.refl _ }
  exact q.symm.trans c.homeomorphRange.toHomotopyEquiv

theorem bijective_integralSingularHomologyMap_pair_of_collared_closed_cover
    {X : Type} [TopologicalSpace X] {P Q C : Set X} [ConnectedSpace C]
    (c : ThreeManifold.TwoSidedCollar (Subtype.val : C → X))
    (hcover : P ∪ Q = univ) (hmeet : P ∩ Q = C)
    (hPcl : closure (P \ Q) = P) (hQcl : closure (Q \ P) = Q) (n : ℕ)
    (hn : Subsingleton (integralSingularHomology n X))
    (hn' : Subsingleton (integralSingularHomology (n + 1) X)) :
    Function.Bijective (fun a : integralSingularHomology n C =>
      (integralSingularHomologyMap n
        (⟨inclusion (hmeet.symm.subset.trans inter_subset_left), continuous_inclusion _⟩ :
          C(C, P)) a,
      integralSingularHomologyMap n
        (⟨inclusion (hmeet.symm.subset.trans inter_subset_right), continuous_inclusion _⟩ :
          C(C, Q)) a)) := by
  have hmeet' : P ∩ Q = Set.range (Subtype.val : C → X) := by
    rw [Subtype.range_coe]
    exact hmeet
  have hP : IsClosed P := hPcl ▸ isClosed_closure
  have hQ : IsClosed Q := hQcl ▸ isClosed_closure
  have hPf : frontier P = Set.range (Subtype.val : C → X) :=
    (frontier_eq_inter_of_closure_sdiff_eq hcover hPcl hQcl).trans hmeet'
  have hQf : frontier Q = Set.range (Subtype.val : C → X) :=
    (frontier_eq_inter_of_closure_sdiff_eq ((union_comm _ _).trans hcover) hQcl hPcl).trans
      ((inter_comm _ _).trans hmeet')
  obtain ⟨d, -, hdP, hdQ, hUV, hI⟩ :=
    c.exists_open_cover_of_closed_cover hcover hmeet' hPcl hQcl
  let U := d.domainNeighborhood P
  let V := d.reverse.domainNeighborhood Q
  let f : C(C, P) := ⟨inclusion (hmeet.symm.subset.trans inter_subset_left),
    continuous_inclusion _⟩
  let g : C(C, Q) := ⟨inclusion (hmeet.symm.subset.trans inter_subset_right),
    continuous_inclusion _⟩
  let i : C((U ∩ V : Set X), U) := ⟨inclusion inter_subset_left, continuous_inclusion _⟩
  let j : C((U ∩ V : Set X), V) := ⟨inclusion inter_subset_right, continuous_inclusion _⟩
  let eP := integralSingularHomologyHomotopyEquiv n
    (d.domainHomotopyEquiv hP hPf.subset hdP)
  let eQ := integralSingularHomologyHomotopyEquiv n
    (d.reverse.domainHomotopyEquiv hQ hQf.subset hdQ)
  let q : C ≃ₕ (U ∩ V : Set X) :=
    (collarZeroHomotopyEquiv d).trans (Homeomorph.setCongr hI.symm).toHomotopyEquiv
  let eC := integralSingularHomologyHomotopyEquiv n q
  have hif : i.comp q.toFun = (d.domainInclusion hP hPf.subset).comp f := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact d.zero_eq x
  have hjg : j.comp q.toFun = (d.reverse.domainInclusion hQ hQf.subset).comp g := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact d.zero_eq x
  have hf (a : integralSingularHomology n C) :
      integralSingularHomologyMap n i (eC a) = eP (integralSingularHomologyMap n f a) := by
    change (integralSingularHomologyMap n i).comp
        (integralSingularHomologyMap n q.toFun) a =
      (integralSingularHomologyMap n (d.domainInclusion hP hPf.subset)).comp
        (integralSingularHomologyMap n f) a
    rw [← integralSingularHomologyMap_comp, ← integralSingularHomologyMap_comp, hif]
  have hg (a : integralSingularHomology n C) :
      integralSingularHomologyMap n j (eC a) = eQ (integralSingularHomologyMap n g a) := by
    change (integralSingularHomologyMap n j).comp
        (integralSingularHomologyMap n q.toFun) a =
      (integralSingularHomologyMap n (d.reverse.domainInclusion hQ hQf.subset)).comp
        (integralSingularHomologyMap n g) a
    rw [← integralSingularHomologyMap_comp, ← integralSingularHomologyMap_comp, hjg]
  have hbij := bijective_integralSingularHomologyMap_intersection
    (d.isOpen_domainNeighborhood P) (d.reverse.isOpen_domainNeighborhood Q) hUV n hn hn'
  constructor
  · intro a b hab
    apply eC.injective
    apply hbij.1
    apply Prod.ext
    · change integralSingularHomologyMap n i (eC a) =
        integralSingularHomologyMap n i (eC b)
      exact (hf a).trans ((congrArg eP (congrArg Prod.fst hab)).trans (hf b).symm)
    · change integralSingularHomologyMap n j (eC a) =
        integralSingularHomologyMap n j (eC b)
      exact (hg a).trans ((congrArg eQ (congrArg Prod.snd hab)).trans (hg b).symm)
  · rintro ⟨a, b⟩
    obtain ⟨z, hz⟩ := hbij.2 (eP a, eQ b)
    obtain ⟨w, rfl⟩ := eC.surjective z
    refine ⟨w, Prod.ext (eP.injective ?_) (eQ.injective ?_)⟩
    · exact (hf w).symm.trans (congrArg Prod.fst hz)
    · exact (hg w).symm.trans (congrArg Prod.snd hz)

end DifferentialGeometry.Topology
