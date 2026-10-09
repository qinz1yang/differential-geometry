/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFixedPLEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceCapping
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceAnnulus
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusEnds

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasBoundaryFixedPLEmbedding.of_circle_capping [DecidableEq E3]
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hKconn : IsConnected K.space)
    (hQ : IsCombinatorialManifoldWithBoundary 2 Q) (hQconn : IsConnected Q.space)
    {T Θ : Set E3} (hΘ : IsPLTorus Θ) (h : HasBoundaryFixedPLEmbedding 2 K Θ)
    (hcap : IsCircleCapping K.space Q.space T (boundaryComplex 2 K).space)
    (hnull : ∀ G ∈ traceCircles K.space T, boundsDiskIn G T → boundsDiskIn G Θ)
    {H : Set E3} (hH : IsPLSphere 1 H) (hHQ : H ⊆ (boundaryComplex 2 Q).space)
    (hess : ¬ boundsDiskIn H Θ) : HasBoundaryFixedPLEmbedding 2 Q Θ := by
  obtain ⟨R, hRfin, hR, hRconn, hRΘ, hRb, f, hf, hfix⟩ := h.exists_subsurface K hK hKconn
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨R', -, -, -, hR'Θ, hR'b, g, hg, hgfix⟩ :=
    hcap.exists_subsurface_of_essential_boundary K Q R hK hQ hQconn hR hRconn.isPreconnected
      hΘ hRΘ hf hRb hfix hnull hH hHQ hess
  exact HasBoundaryFixedPLEmbedding.of_subsurface Q R' hR'Θ hg hR'b hgfix

theorem HasBoundaryFixedPLEmbedding.exists_annulus_of_essential_boundary [DecidableEq E3]
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {S : Set E3} (hS : IsCombinatorialSolidTorus S)
    (h : HasBoundaryFixedPLEmbedding 2 K (frontier S))
    (h286 : Moise286) (n : ℕ) (G : Fin n → Set E3) (hn : 0 < n)
    (hG : ∀ i, IsPLSphere 1 (G i)) (hdis : Pairwise fun i j => Disjoint (G i) (G j))
    (hboundary : (boundaryComplex 2 K).space = ⋃ i, G i)
    (hess : ∀ i, ¬ boundsDiskIn (G i) (frontier S)) :
    ∃ i j : Fin n, i ≠ j ∧ IsPLAnnulusWithEnds K.space (G i) (G j) := by
  obtain ⟨R, hRfin, hR, hRconn, hRS, hRb, f, hf, hfix⟩ := h.exists_subsurface K hK hconn
  let _ : Finite R.faces := hRfin.to_subtype
  have hRboundary := hRb.trans hboundary
  obtain ⟨i, j, hij, hann⟩ := hR.exists_annulus_of_essential_torus_boundary R hRconn
    hS hRS h286 n G hn hG hdis hRboundary hess
  refine ⟨i, j, hij, hann.of_isPLHomeomorphOn_eqOn hf ?_⟩
  exact hfix.mono (union_subset ((subset_iUnion G i).trans hRboundary.symm.subset)
    ((subset_iUnion G j).trans hRboundary.symm.subset))

end DifferentialGeometry.Topology.PiecewiseLinear
