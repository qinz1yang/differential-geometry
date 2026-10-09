import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugDoubleBoundaryAssembly

/-!
The actual boundary gluing seam has exact coordinates at its physical collar depth.
The same chosen seam and the same normal width are retained on both sides.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology
universe u
namespace GC.GraphManifold

variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary)
  (hD : D.kind = .withBoundary) [Nonempty C.Carrier] [Nonempty D.Carrier]
  {n : ℕ} (E1 : BoundaryTori C 1) (E2 : BoundaryTori D (n + 1))
  (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hr : ReversesBoundaryOrientation (C.withBoundarySum D hC hD)
    (boundaryPortLeftCollar C D hC hD E1)
    (fun p => boundaryPortRightCollar C D hC hD E2 0 (f p.1, p.2)))
  {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  {N : CompactCarrier.{u}} (T : TorusPresentation N)
  (hcut : T.cutCarrier = C.withBoundarySum D hC hD)
  (hpair : (hcut ▸ T.pairing) =
    (boundaryPortPairing C D hC hD E1 E2 f hr).shrink hδ hδ1)


private theorem boundaryPairing_physicalCollars (A : CompactCarrier.{u}) (P : TorusPairing A)
    (hA : A = C.withBoundarySum D hC hD)
    (hP : (hA ▸ P) = (boundaryPortPairing C D hC hD E1 E2 f hr).shrink hδ hδ1) :
    ∃ j : Fin P.count, P.matching j = f ∧
      (∀ p, P.leftCollar j p = hA.symm ▸
        Sum.inl (E1.collar 0 (p.1, halfSpaceScale hδ p.2))) ∧
      ∀ p, P.rightCollar j p = hA.symm ▸
        Sum.inr (E2.collar 0 (p.1, halfSpaceScale hδ p.2)) := by
  subst A
  cases hP
  refine ⟨(0 : Fin 1), rfl, ?_, ?_⟩
  · intro p
    exact boundaryPortLeftCollar_apply C D hC hD E1 (p.1, halfSpaceScale hδ p.2)
  · intro p
    exact boundaryPortRightCollar_apply C D hC hD E2 0 (p.1, halfSpaceScale hδ p.2)

private theorem physicalDepth_halfPoint {s : ℝ} (hs : 0 ≤ s) :
    halfSpaceScale hδ (halfPoint (s / δ) (div_nonneg hs hδ.le)) = halfPoint s hs := by
  apply Subtype.ext
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rw [halfSpaceScale_coord]
  change δ * (s / δ) = s
  exact mul_div_cancel₀ s hδ.ne'

include hpair in
theorem exists_boundaryGluingSeamCoordinates :
    ∃ j : Fin T.pairing.count, T.pairing.matching j = f ∧
      (∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < δ →
        T.seam j (t, -(s / δ)) =
          T.cutMap (hcut.symm ▸ Sum.inl (E1.collar 0 (t, halfPoint s hs)))) ∧
      ∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < δ →
        T.seam j (t, s / δ) =
          T.cutMap (hcut.symm ▸ Sum.inr (E2.collar 0 (f t, halfPoint s hs))) := by
  obtain ⟨j, hj, hL, hR⟩ := boundaryPairing_physicalCollars C D hC hD E1 E2 f hr
    hδ hδ1 T.cutCarrier T.pairing hcut hpair
  refine ⟨j, hj, ?_, ?_⟩
  · intro t s hs hsδ
    have hs0 := div_nonneg hs hδ.le
    have hs1 : s / δ < 1 := (div_lt_one hδ).mpr hsδ
    rw [T.seam_negative j t (-(s / δ)) (neg_nonpos.mpr hs0) (by linarith)]
    change T.cutMap (T.pairing.leftCollar j _) = _
    rw [hL]
    have he : halfSpaceScale hδ
        (halfPoint (- -(s / δ)) (neg_nonneg.mpr (neg_nonpos.mpr hs0))) = halfPoint s hs := by
      convert physicalDepth_halfPoint hδ hs using 1
      simp only [neg_neg]
    rw [he]
  · intro t s hs hsδ
    have hs0 := div_nonneg hs hδ.le
    have hs1 : s / δ < 1 := (div_lt_one hδ).mpr hsδ
    rw [T.seam_positive j t (s / δ) hs0 hs1]
    change T.cutMap (T.pairing.rightCollar j (T.pairing.matching j t, _)) = _
    rw [hR, hj, physicalDepth_halfPoint hδ hs]

end GC.GraphManifold
