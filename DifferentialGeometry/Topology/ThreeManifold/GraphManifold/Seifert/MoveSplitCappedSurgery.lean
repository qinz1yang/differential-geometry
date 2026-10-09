import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MergedSolidTorus

/-!
# Sphere surgery along the split sphere

Lane N2c, tier 2 (first step). The cut-cap constructor `sphereSystemCapping` applied to the
explicit split tube `splitSeamTube` gives a spherical cut-cap transition of `Q` whose tube system
is that tube on the nose, with middle sphere `splitSeamSphere`, and the dichotomy of
`singleSphereSurgery`: `Q ≅ A # B` for the two capped sides when they lie in different
components, `Q ≅ A # S² × S¹` otherwise (`exists_splitSeamSurgery`). Unlike
`exists_sphereSurgery`, the tube is the explicit one, so the cores and caps of the transition
are related to the presentation through `SplitTube.SplitCharts`.

The tube avoids every piece other than the solid torus and the host (`tubeMap_ne_cutMap`): its
points are reconstruction images of interior points of the two pieces or of points of the seam
torus `j`.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem exists_splitSeamSurgery (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) :
    ∃ (P : ClosedOrientedManifold.{u} 3)
      (X : SphericalCutCapTransition Q.toClosedOrientedManifold P) (a : X.tubes.Index),
      Subsingleton X.tubes.Index ∧ X.tubes = E.splitSeamTube j b h hlin ∧
        tubeMiddleSphere X.tubes a = E.splitSeamSphere j b h hlin ∧
        ((X.cutCapVertex a false ≠ X.cutCapVertex a true ∧
          Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (connectedSum (X.capped.component (X.cutCapVertex a false))
              (X.capped.component (X.cutCapVertex a true))).Carrier)) ∨
        (X.cutCapVertex a false = X.cutCapVertex a true ∧
          Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (connectedSum (X.capped.component (X.cutCapVertex a false))
              sphereTwoTimesCircleLift.ulift.{0, u}).Carrier))) := by
  obtain ⟨P, X, hX⟩ := sphereSystemCapping Q (E.splitSeamTube j b h hlin) ⟨()⟩
  have hsub : Subsingleton X.tubes.Index := by
    rw [hX]
    exact inferInstanceAs (Subsingleton Unit)
  let a : X.tubes.Index := hX ▸ ()
  have key : ∀ (T : SphericalTubeSystem Q.toClosedOrientedManifold)
      (_ : T = E.splitSeamTube j b h hlin) (a' : T.Index),
      tubeMiddleSphere T a' = E.splitSeamSphere j b h hlin := by
    rintro T rfl a'
    rfl
  exact ⟨P, X, a, hsub, hX, key X.tubes hX a, singleSphereSurgery X a⟩

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem seamMap_zero_ne_cutMap (E : ElementaryPresentation (NoCuts.carrier Q))
    {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b) (t : Torus)
    {k : Fin E.toTorus.components.count} (hkV : k ≠ E.seamPiece j b)
    (hkH : k ≠ E.hostPiece j b) {y : E.toTorus.cutCarrier.Carrier}
    (hy : y ∈ E.toTorus.components.piece k) : E.seamMap j b (t, 0) ≠ E.toTorus.cutMap y := by
  intro he
  rw [E.seamMap_zero] at he
  have hy0 := (E.toTorus.sideCollar_zero_mem (E.seamSide j b) t).2
  rw [E.sidePiece_seamSide] at hy0
  rcases E.toTorus.cutMap_eq_cases he with he' | ⟨k', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · rw [he'] at hy0
    exact hkV (TorusPresentation.eq_of_mem_piece' _ hy hy0)
  · have hV : E.seamPiece k' true = E.seamPiece j b :=
      TorusPresentation.eq_of_mem_piece' _ (E.toTorus.left_owned k' h1) hy0
    obtain ⟨rfl, rfl⟩ := E.eq_of_seamPiece_eq_of_isSplitSeam h hV
    exact hkH (TorusPresentation.eq_of_mem_piece' _ hy (E.toTorus.right_owned _ h2))
  · have hV : E.seamPiece k' false = E.seamPiece j b :=
      TorusPresentation.eq_of_mem_piece' _ (E.toTorus.right_owned k' h1) hy0
    obtain ⟨rfl, rfl⟩ := E.eq_of_seamPiece_eq_of_isSplitSeam h hV
    exact hkH (TorusPresentation.eq_of_mem_piece' _ hy (E.toTorus.left_owned _ h2))

theorem pieceChart_ne_cutMap {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (i : Fin T.components.count) {k₀ : ℕ} (B : PlanarBase.{u} k₀)
    (Θ : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i) (g : ℂ → B.surface.Carrier) {q : ℂ × Circle}
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model B.surface.kind) ∞ g q.1)
    {k : Fin T.components.count} (hk : k ≠ i) {y : T.cutCarrier.Carrier}
    (hy : y ∈ T.components.piece k) : T.pieceChart i B Θ g q ≠ T.cutMap y := by
  intro he
  obtain ⟨hint, -⟩ := T.pieceChart_isInteriorPoint i B Θ g hg
  have e := T.cutMap_eq_of_isInteriorPoint hint he
  have h1 := (Θ (g q.1, q.2)).property
  rw [e] at h1
  exact hk (TorusPresentation.eq_of_mem_piece' _ hy h1)

theorem tubeMap_ne_cutMap (E : ElementaryPresentation (NoCuts.carrier Q))
    {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) {q : S2 × ℝ} (hq : |q.2| < 3)
    {k : Fin E.toTorus.components.count} (hkV : k ≠ E.seamPiece j b)
    (hkH : k ≠ E.hostPiece j b) {y : E.toTorus.cutCarrier.Carrier}
    (hy : y ∈ E.toTorus.components.piece k) :
    (E.splitCharts h hlin).tubeMap q ≠ E.toTorus.cutMap y := by
  set C := E.splitCharts h hlin
  rcases lt_trichotomy (SplitTube.seamHeight (SplitTube.heightOf q.1)) 0 with h1 | h1 | h1
  · rw [C.tubeMap_of_neg h1]
    have hn : ‖(SplitTube.capModel C.e₀ (SplitTube.SplitCharts.side q) q).1‖ < 3 := by
      simp only [SplitTube.capModel, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      have := (SplitTube.seamHeight_neg_iff q.1).mp h1
      linarith
    exact pieceChart_ne_cutMap _ _ _ _ _ (isLocalDiffeomorphAt_clampDisc hn) hkV hy
  · rw [C.tubeMap_of_zero h1, SplitTube.SplitCharts.seamModel_of_zero h1]
    exact E.seamMap_zero_ne_cutMap h _ hkV hkH hy
  · rw [C.tubeMap_of_pos h1]
    have hmem := (SplitTube.hostChart_strip_mem C.host
      (SplitTube.abs_heightOf_lt_of_seamHeight_pos h1) h1 hq).1
    exact pieceChart_ne_cutMap _ _ _ _ _ (isLocalDiffeomorphAt_clampPants hmem) hkH hy

end ElementaryPresentation

end GC.Seifert
