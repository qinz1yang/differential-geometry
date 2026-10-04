import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PrimitiveFillingPieceMaps

/-!
# Common widths and actual cut collar formulas

A positive common width controls finitely many filling germs, including the empty filling case.
The labelled cut diffeomorphism inherits the actual host and solid collar formulas directly from
their piece maps. These are the exact inputs to the quotient comparison construction.
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u

namespace GC.Seifert

theorem exists_primitiveFilling_common_width {n : ℕ} (δ₀ : ℝ) (δ : Fin n → ℝ)
    (hδ₀ : 0 < δ₀) (hδ : ∀ m, 0 < δ m) :
    ∃ ε, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ δ₀ ∧ ∀ m, ε ≤ δ m := by
  let d : Option (Fin n) → ℝ := fun i => i.elim δ₀ δ
  have hd (i : Option (Fin n)) : 0 < d i := by
    cases i with
    | none => exact hδ₀
    | some m => exact hδ m
  have hne : (Finset.univ : Finset (Option (Fin n))).Nonempty := ⟨none, Finset.mem_univ none⟩
  let ε := min (Finset.univ.inf' hne d) 1
  have hε : 0 < ε := lt_min ((Finset.lt_inf'_iff hne).mpr fun i hi => by
    simp only [Finset.mem_univ] at hi
    cases hi
    exact hd i) one_pos
  have hi (i : Option (Fin n)) : ε ≤ d i :=
    (min_le_left _ _).trans (Finset.inf'_le d (Finset.mem_univ i))
  exact ⟨ε, hε, min_le_right _ _, hi none, fun m => hi (some m)⟩

namespace PrimitiveFillingPresentation

variable {W W' : CompactCarrier.{u}} {n r : ℕ}
  (B : PrimitiveFillingPresentation W n r) (B' : PrimitiveFillingPresentation W' n r)
  (g : (i : Option (Fin n)) →
    B.presentation.components.piece (B.piece i) ≃ₘ⟮B.presentation.cutCarrier.model,
      B'.presentation.cutCarrier.model⟯
        B'.presentation.components.piece (B'.piece i))
  (ψ : Fin r ⊕ Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) (δ : ℝ)

theorem cutDiffeomorph_host_germ
    (hgerm : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ →
      g none (B.presentation.pieceCollar (B.piece none) (B.product.port (B.port a)) p) =
        B'.presentation.pieceCollar (B'.piece none) (B'.product.port (B'.port a))
          (ψ a p.1, p.2))
    (a : Fin r ⊕ Fin n) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) (hlt : p.2.val 0 < δ) :
    B.cutDiffeomorph B' g
      (B.presentation.sideCollar (B.product.port (B.port a)).val p) =
        B'.presentation.sideCollar (B'.product.port (B'.port a)).val (ψ a p.1, p.2) := by
  have h := B.cutDiffeomorph_piece B' g none
    (B.presentation.pieceCollar (B.piece none) (B.product.port (B.port a)) p)
  rw [hgerm a p hp hlt] at h
  rw [B.presentation.pieceCollar_apply (B.piece none) (B.product.port (B.port a)) hp,
    B'.presentation.pieceCollar_apply (B'.piece none) (B'.product.port (B'.port a))
      (show (ψ a p.1, p.2) ∈ halfCollarSource from hp)] at h
  exact h

theorem cutDiffeomorph_solid_germ
    (hgerm : ∀ m p, p ∈ halfCollarSource → p.2.val 0 < δ →
      g (some m) (B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port 0) p) =
        B'.presentation.pieceCollar (B'.piece (some m)) ((B'.solid m).port 0)
          (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
            (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2))
    (m : Fin n) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) (hlt : p.2.val 0 < δ) :
    B.cutDiffeomorph B' g (B.presentation.pairing.leftCollar (B.seam m) p) =
      B'.presentation.pairing.leftCollar (B'.seam m)
        (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
          (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2) := by
  let f := primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
    (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m))
  have h := B.cutDiffeomorph_piece B' g (some m)
    (B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port 0) p)
  rw [hgerm m p hp hlt] at h
  rw [B.presentation.pieceCollar_apply (B.piece (some m)) ((B.solid m).port 0) hp,
    B'.presentation.pieceCollar_apply (B'.piece (some m)) ((B'.solid m).port 0)
      (show (f p.1, p.2) ∈ halfCollarSource from hp), B.solid_port, B'.solid_port] at h
  exact h

end PrimitiveFillingPresentation

end GC.Seifert
