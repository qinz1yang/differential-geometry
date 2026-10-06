/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCutTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremComp

set_option autoImplicit false

/-!
# LT-P4: discharging the cut contract from LT-P3

Given a triangulation `h₀ : |K₀| ≃ₜ M` and a surface complex `L` for the tori (LT-R2), LT-P3 cuts
`M` along the tori; here the cut manifold is identified with `W` and the boundary components with
the individual tori.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1
open GC.Topology

theorem cut_data_of_triangulation_LTP4 {M : Type*} [TopologicalSpace M] [T2Space M]
    {ι : Type} [Finite ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (σ : OpenPartialHomeomorph ((ι × Torus) × ℝ) M)
    (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (W : Set M) (hWc : IsClosed W)
    (hside : ∀ p ∈ σ.source, σ p ∈ W ↔ 0 ≤ p.2)
    (hfront : W \ range (fun x : ι × Torus => σ (x, 0)) ⊆ interior W)
    {N₀ : ℕ} [hdec : DecidableEq (EuclideanSpace ℝ (Fin N₀))] (K₀ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N₀)))
    [Finite K₀.faces] (h₀ : K₀.space ≃ₜ M) (hK₀ : IsCombinatorialManifold 3 K₀)
    (hKo₀ : IsOrientable 3 K₀)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N₀))) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L)
    (hLY : L.space = ((↑) : K₀.space → EuclideanSpace ℝ (Fin N₀)) ''
      (h₀ ⁻¹' range (fun x : ι × Torus => σ (x, 0)))) :
    ∃ (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N₀)))
      (_ : Finite R.faces) (h : R.space ≃ₜ ↥W),
      IsCombinatorialManifoldWithBoundary 3 R ∧ IsOrientable 3 R ∧
      ∀ j : ι, ∃ c : ConnectedComponents (boundaryComplex 3 R).space,
        ∀ k : R.space, (k : EuclideanSpace ℝ (Fin N₀)) ∈
            (connectedComponentComplex (boundaryComplex 3 R) c).space ↔
          ((h k : ↥W) : M) ∈ range (fun z : Torus => σ ((j, z), 0)) := by
  obtain rfl : hdec = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  classical
  have hVe : Topology.IsClosedEmbedding (Subtype.val : K₀.space → EuclideanSpace ℝ (Fin N₀)) :=
    (isPolyhedron_space K₀).isClosed.isClosedEmbedding_subtypeVal
  obtain ⟨hdense, hone⟩ := sideHyps_of_bicollar_LTP3 σ hσ W hside
  obtain ⟨R, hRfin, hRsp, hRb, hRbd, hRo, hRcomp⟩ :=
    exists_cut_manifold_of_side_LTP3 h₀ hK₀ hL hLY hWc hfront hdense hone
  letI : Finite R.faces := hRfin.to_subtype
  have hsrc : ∀ (j : ι) (z : Torus), ((j, z), (0 : ℝ)) ∈ σ.source := fun j z => by
    rw [hσ]; exact ⟨by norm_num, by norm_num⟩
  -- the homeomorphism `R.space ≃ₜ W`
  have hsub : (W ⊆ range h₀) := fun w _ => ⟨h₀.symm w, h₀.apply_symm_apply w⟩
  let e : (h₀ ⁻¹' W) ≃ₜ W := h₀.isEmbedding.homeomorphOfSubsetRange hsub
  let f : (h₀ ⁻¹' W) ≃ₜ Subtype.val '' (h₀ ⁻¹' W) := hVe.isEmbedding.homeomorphImage _
  let hh : R.space ≃ₜ ↥W := (Homeomorph.setCongr hRsp).trans (f.symm.trans e)
  have hkey : ∀ k : R.space, ∃ k' : K₀.space, (k : EuclideanSpace ℝ (Fin N₀)) = (k' : EuclideanSpace ℝ (Fin N₀)) ∧
      ((hh k : ↥W) : M) = h₀ k' := by
    intro k
    let u := f.symm (Homeomorph.setCongr hRsp k)
    refine ⟨(u : K₀.space), ?_, ?_⟩
    · have := congrArg Subtype.val (f.apply_symm_apply (Homeomorph.setCongr hRsp k))
      exact this.symm
    · rfl
  let g : ι × Torus → EuclideanSpace ℝ (Fin N₀) := fun p => (h₀.symm (σ (p, 0)) : K₀.space)
  have hσc : Continuous fun p : ι × Torus => σ (p, 0) :=
    σ.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun p => hsrc p.1 p.2
  have hgc : Continuous g :=
    continuous_subtype_val.comp (h₀.symm.continuous.comp hσc)
  have hginj : Function.Injective g := by
    intro p q hpq
    have h1 : h₀.symm (σ (p, 0)) = h₀.symm (σ (q, 0)) := Subtype.ext hpq
    have h2 := h₀.symm.injective h1
    have := σ.injOn (hsrc p.1 p.2) (hsrc q.1 q.2) h2
    exact (Prod.ext_iff.mp this).1 |> fun e => Prod.ext (by simpa using congrArg Prod.fst e)
      (by simpa using congrArg Prod.snd e)
  have hLg : L.space = range g := by
    rw [hLY]
    ext y; constructor
    · rintro ⟨k, ⟨p, hp⟩, rfl⟩
      exact ⟨p, by simp only [g, hp, h₀.symm_apply_apply]⟩
    · rintro ⟨p, rfl⟩
      exact ⟨h₀.symm (σ (p, 0)), ⟨p, by simp⟩, rfl⟩
  refine ⟨R, hRfin, hh, hRb, hRo hKo₀, fun j => ?_⟩
  have hx : g (j, (1, 1)) ∈ R.space ∩ L.space := by
    refine ⟨?_, by rw [hLg]; exact mem_range_self _⟩
    rw [hRsp]
    refine ⟨h₀.symm (σ ((j, (1, 1)), 0)), ?_, rfl⟩
    show h₀ (h₀.symm _) ∈ W
    rw [h₀.apply_symm_apply]
    exact (hside _ (hsrc j (1, 1))).mpr le_rfl
  obtain ⟨c, hc⟩ := hRcomp _ hx
  refine ⟨c, fun k => ?_⟩
  rw [hc, hLg, connectedComponentIn_range_family_LTP4 g hgc hginj j (1, 1)]
  obtain ⟨k', hk', hhk⟩ := hkey k
  rw [hk', hhk]
  constructor
  · rintro ⟨z, hz⟩
    have : h₀.symm (σ ((j, z), 0)) = k' := Subtype.ext hz
    exact ⟨z, by rw [← this, h₀.apply_symm_apply]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [← h₀.symm_apply_apply k', ← hz]⟩

end GC.LongTime.CuspP1
