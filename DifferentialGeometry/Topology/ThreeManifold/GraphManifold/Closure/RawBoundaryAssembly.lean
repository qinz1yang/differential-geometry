import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawBoundaryGluing

/-!
Joint coarse and raw boundary gluing on one actual carrier. The coarse quotient is chosen once;
its literal reconstruction square and full port ledger survive actual local raw face assembly.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
  [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]

omit [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier] in
private theorem rawBoundaryAssemblyPieces {N : CompactCarrier.{u}}
    (T : TorusPresentation N) (hc : T.components.count = 2)
    (eC : C.Carrier ≃ₘ⟮C.model, (T.Component (Fin.cast hc.symm 0)).model⟯
      (T.Component (Fin.cast hc.symm 0)).Carrier)
    (eD : D.Carrier ≃ₘ⟮D.model, (T.Component (Fin.cast hc.symm 1)).model⟯
      (T.Component (Fin.cast hc.symm 1)).Carrier)
    (hposC : eC.preservesOrientation C.orientation
      (T.Component (Fin.cast hc.symm 0)).orientation)
    (hposD : eD.preservesOrientation D.orientation
      (T.Component (Fin.cast hc.symm 1)).orientation)
    (GC : RawGraphPresentation C) (GD : RawGraphPresentation D) :
    Nonempty (∀ i, RawGraphPresentation (T.Component i)) := by
  have hR : ∀ i : Fin T.components.count, Nonempty (RawGraphPresentation (T.Component i)) := by
    intro i
    have hi : i.val < 2 := hc ▸ i.isLt
    have hcases : i = Fin.cast hc.symm 0 ∨ i = Fin.cast hc.symm 1 := by
      by_cases hi0 : i.val = 0
      · exact Or.inl (Fin.ext hi0)
      · exact Or.inr (Fin.ext (by change i.val = 1; omega))
    rcases hcases with rfl | rfl
    · exact ⟨GC.transport eC hposC⟩
    · exact ⟨GD.transport eD hposD⟩
  exact ⟨fun i => Classical.choice (hR i)⟩

private theorem rawBoundaryAssemblyScale {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (s : EuclideanHalfSpace 1) :
    halfSpaceScale hδ (halfSpaceScale hε s) = halfSpaceScale (mul_pos hδ hε) s := by
  apply Subtype.ext
  ext i
  fin_cases i
  change (halfSpaceScale hδ (halfSpaceScale hε s)).val 0 =
    (halfSpaceScale (mul_pos hδ hε) s).val 0
  simp only [halfSpaceScale_coord, mul_assoc]

variable {n : ℕ} (E1 : BoundaryTori C 1) (E2 : BoundaryTori D (n + 1))
  (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hrev : ReversesBoundaryOrientation (C.withBoundarySum D hC hD)
    (boundaryPortLeftCollar C D hC hD E1)
    (fun p => boundaryPortRightCollar C D hC hD E2 0 (f p.1, p.2)))

set_option backward.isDefEq.respectTransparency false in
theorem exists_rawBoundaryAssembly
    (hbC : C.model.boundary C.Carrier = E1.image)
    (hbD : D.model.boundary D.Carrier = E2.image)
    (GC : RawGraphPresentation C) (GD : RawGraphPresentation D) :
    ∃ N : CompactCarrier.{u}, N.kind = .withBoundary ∧ ConnectedSpace N.Carrier ∧
      ∃ T : TorusPresentation N, ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ hδ1 : δ ≤ 1,
        ∃ hcut : T.cutCarrier = C.withBoundarySum D hC hD,
          ∃ hn : T.externalCount = n, ∃ hc : T.components.count = 2,
            (hcut ▸ T.components) = rawBoundarySumComponents C D hC hD ∧
            (hcut ▸ T.pairing) = (boundaryPortPairing C D hC hD E1 E2 f hrev).shrink hδ hδ1 ∧
            (hcut ▸ (hn ▸ T.cutExternal)) = (boundaryPortRemaining C D hC hD E2).shrink hδ hδ1 ∧
            T.pairing.count = 1 ∧ (∀ j, T.pairing.matching j = f) ∧
            (∀ j, (T.leftPiece j).val = 0 ∧ (T.rightPiece j).val = 1) ∧
            (∀ i, (T.externalPiece i).val = 1) ∧
            ∃ eC : C.Carrier ≃ₘ⟮C.model, (T.Component (Fin.cast hc.symm 0)).model⟯
                (T.Component (Fin.cast hc.symm 0)).Carrier,
              ∃ eD : D.Carrier ≃ₘ⟮D.model, (T.Component (Fin.cast hc.symm 1)).model⟯
                  (T.Component (Fin.cast hc.symm 1)).Carrier,
                eC.preservesOrientation C.orientation
                  (T.Component (Fin.cast hc.symm 0)).orientation ∧
                eD.preservesOrientation D.orientation
                  (T.Component (Fin.cast hc.symm 1)).orientation ∧
                ∃ e : (boundaryPortPairing C D hC hD E1 E2 f hrev).QuotientSpace ≃ₜ N.Carrier,
                  (∀ x, e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap x) =
                    T.cutMap (hcut.symm ▸ x)) ∧
                  (∀ i p, p ∈ halfCollarSource →
                    T.external.collar (Fin.cast hn.symm i) p =
                      e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
                        (Sum.inr (E2.collar i.succ (p.1, halfSpaceScale hδ p.2))))) ∧
                  ∃ R : ∀ i, RawGraphPresentation (T.Component i),
                    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ _hε1 : ε ≤ 1,
                      ∃ G : RawGraphPresentation N, ∃ hcount : G.externalCount = n,
                        ∃ edge : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃
                            Fin G.pairing.count,
                          (∀ i p, p ∈ halfCollarSource →
                            G.external.collar (Fin.cast hcount.symm i) p =
                              e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
                                (Sum.inr (E2.collar i.succ
                                  (p.1, halfSpaceScale (mul_pos hδ hε) p.2))))) ∧
                          (∀ j p, p ∈ signedCollarSource →
                            G.seam (edge (.inl j)) p = T.seam j (p.1, ε * p.2)) ∧
                          (∀ j, G.pairing.matching (edge (.inl j)) = f) := by
  obtain ⟨N, hN, hconn, T, δ, hδ, hδ1, hcut, hn, hc, hcomponents, hpairing,
    hexternal, hcoarseCount, hmatching, howners, hexowner, eC, eD, hposC, hposD,
    e, hsquare, hport⟩ :=
    exists_rawBoundaryTorusPresentation C D hC hD E1 E2 f hrev hbC hbD
  obtain ⟨R⟩ := rawBoundaryAssemblyPieces C D T hc eC eD hposC hposD GC GD
  obtain ⟨port, ψ, Φ, hΦ, ε, hε, hε1, hzero, hgerm, hfull, G, hG, edge,
    hmarked, hold, hnew, hmatch, hmatchnew⟩ := exists_rawFacesAssembly T R
  refine ⟨N, hN, hconn, T, δ, hδ, hδ1, hcut, hn, hc, hcomponents, hpairing,
    hexternal, hcoarseCount, hmatching, howners, hexowner, eC, eD, hposC, hposD,
    e, hsquare, hport, R, ε, hε, hε1, G, hG.trans hn, edge, ?_, hold, ?_⟩
  · intro i p hp
    have hidx : Fin.cast (hG.trans hn).symm i =
        Fin.cast hG.symm (Fin.cast hn.symm i) := Fin.ext rfl
    rw [hidx, hmarked (Fin.cast hn.symm i) p hp]
    have hscaled : (p.1, halfSpaceScale hε p.2) ∈ halfCollarSource :=
      halfSpaceScale_mem hε hε1 hp
    rw [hport i (p.1, halfSpaceScale hε p.2) hscaled]
    rw [rawBoundaryAssemblyScale]
  · intro j
    exact (hmatch j).trans (hmatching j)

end GC.GraphManifold
