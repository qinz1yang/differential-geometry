import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplit
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.IrreducibleOfPrime

/-!
# The split move through sphere surgery

Lane N2b, for `MoveSplit` of `Seifert/Normalize.lean` after `Seifert/MoveSplit.lean`.

Sphere surgery (tier 2). Let `X` be a spherical cut-cap transition of a closed connected oriented
`M` with a single tube `a`. If the two capped sides of `a` lie in different components `A`, `B`
of the capped manifold, then `M ≅ A # B` (`nonempty_diffeomorph_connectedSum_of_cutCapVertex_ne`):
the merge step of the paired-ball gluing (`exists_quotient_homeomorph_merge`,
`exists_smooth_distinct_merge_of_factor_representatives`) followed by the empty gluing, as in
the loop case `nonempty_diffeomorph_connectedSum_sphereTwoTimesCircle_of_cutCapVertex_eq`, which
gives `M ≅ A # S² × S¹` when both sides lie in one component `A` (restated with the lifted
`S² × S¹`). `singleSphereSurgery` is the dichotomy, and the capped manifold has no component
besides the two sides (`eq_cutCapVertex_of_subsingleton`, from the same gluing: the component
index of the merged or looped gluing is a singleton since `M` is connected). For a smoothly
embedded sphere `e` the tube (`sphereTubeExtension`) and the capping (`sphereSystemCapping`)
exist, so `exists_sphereSurgery` gives a single-tube transition with middle sphere `e` and one of
the two identifications.

Interface with the normalization. `splitsBelow_of_cutCapVertex_ne` and
`splitsBelow_of_cutCapVertex_eq`: if a single-tube transition of `Q` has capped sides carrying
elementary presentations with fewer seams than `E`, then `E.SplitsBelow`. For a split seam the
sphere of `MoveSplit.lean`, `S = D_a ∪ γ × S¹ ∪ D_b'`, gives counts `n_A + n_B + 1 = n` or
`n_A + 1 = n`, so these are the inputs `MoveSplit` needs from tiers 1 and 3.

Not built here. Tier 1: the meridians of the solid torus `V` reach the host torus through the
matching of the seam, an arbitrary diffeomorphism of `T²` with the right matrix, so `S` needs the
matching isotoped to a linear map (`TorusMappingClassLinear`, unproved), and a parametrization
of `S` by the round sphere needs a collar of the planar bases compatible with their embeddings.
Tier 3: the capped sides are known only through the core inclusion and the caps, and no
constructor gives a torus presentation of such a manifold (nor a smooth assembly of a torus
gluing of a cut carrier); this is the step from the region of the other pieces
(`restrictCarrier`) plus two solid tori to a closed elementary presentation.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Endpoint

private theorem nonempty_diffeomorph_sigma_fiber_of_connected
    {M : ConnectedClosedOrientedManifold.{u} 3}
    {W : Type u} (X : W → ConnectedClosedOrientedManifold.{u} 3)
    (D : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Σ w, (X w).Carrier)) :
    ∃ w₀ : W, (∀ w, w = w₀) ∧
      Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (X w₀).Carrier) := by
  have : ConnectedSpace (Σ w, (X w).Carrier) :=
    D.toHomeomorph.connectedSpace_iff.mp inferInstance
  obtain ⟨p⟩ := (inferInstance : Nonempty (Σ w, (X w).Carrier))
  have hfst : IsLocallyConstant (Sigma.fst : (Σ w, (X w).Carrier) → W) :=
    isOpen_sigma_fst_preimage
  have hall : ∀ w, w = p.1 := fun w => by
    obtain ⟨x⟩ := (inferInstance : Nonempty (X w).Carrier)
    exact hfst.apply_eq_of_preconnectedSpace ⟨w, x⟩ p
  have hf := isLocalDiffeomorph_sigmaMk (I := 𝓡 3) (M := fun w => (X w).Carrier) (n := ∞) p.1
  have hbij : Function.Bijective (Sigma.mk (β := fun w => (X w).Carrier) p.1) := by
    refine ⟨sigma_mk_injective, ?_⟩
    rintro ⟨w, x⟩
    obtain rfl := hall w
    exact ⟨x, rfl⟩
  exact ⟨p.1, hall, ⟨D.trans (hf.diffeomorphOfBijective hbij).symm⟩⟩

private theorem cutCapVertex_ne_aux
    {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hsep : E.cutCapVertex a false ≠ E.cutCapVertex a true) :
    (∀ K, K = E.cutCapVertex a false ∨ K = E.cutCapVertex a true) ∧
      Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum (E.capped.component (E.cutCapVertex a false))
          (E.capped.component (E.cutCapVertex a true))).Carrier) := by
  classical
  let N := E.capped.component
  let ep := E.cutCapVertex
  let ch := fun a t => E.capComponentBallChart (a, t)
  let hd := E.pairwise_disjoint_capComponentBallChart_image
  let C := fun K =>
    (PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N ep ch hd K).choose
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N ep ch v) := fun v => (C v).toChartedSpace
  obtain ⟨b, hbL, hbR, hd', H, hfirst, hsecond, hu, -, J, hJ⟩ :=
    PairedBallGluing.exists_quotient_homeomorph_merge N ep ch a hd
      (fun e => boundaryAttachment) hsep
  let N' := PairedBallGluing.mergeFactor N ep ch a boundaryAttachment
  let ep' := fun e t => (PairedBallGluing.mergeFlag N ep ch a boundaryAttachment b e t).fst
  let ch' := fun e t => (PairedBallGluing.mergeFlag N ep ch a boundaryAttachment b e t).snd
  let C' := fun v =>
    (PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N' ep' ch' hd' v).choose
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N' ep' ch' v) := fun v => (C' v).toChartedSpace
  have : IsEmpty {e : E.tubes.Index // e ≠ a} :=
    ⟨fun e => e.property (Subsingleton.elim _ _)⟩
  obtain ⟨Qcharts', hm', hc', hs', D', -⟩ :=
    PairedBallGluing.exists_smooth_quotient_atlas_of_isEmpty N' ep' ch' hd'
      (fun e => boundaryAttachment) C'
  let _ := Qcharts'
  let _ := hm'
  have hbd := PairedBallGluing.pairwise_disjoint_survivorChart_of_mergeFlag N ep ch a
    boundaryAttachment hsep b hd'
  obtain ⟨A, -, hcH, hsH, G, hG⟩ :=
    PairedBallGluing.exists_smooth_distinct_merge_of_factor_representatives N ep ch hd a
      boundaryAttachment hsep b C C' H hfirst hsecond hu hbd hbL hbR
  let _ := A
  have hGc : (fun q => G q) = H := funext hG
  have hcoreH : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (H ∘ PairedBallGluing.seamCoreInclusion N ep ch hd a boundaryAttachment) := by
    have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hcH
    simpa only [hGc] using hh
  have hseamH : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
      (H ∘ PairedBallGluing.seamChart N ep ch hd a boundaryAttachment) := by
    have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hsH
    simpa only [hGc] using hh
  have hrad := PairedBallGluing.merge_homeomorph_radialPoint N ep ch hd a boundaryAttachment
    hsep b H hfirst hsecond hu hbL hbR hd'
  obtain ⟨Qcharts, -, hc, hs, D, -⟩ :=
    PairedBallGluing.exists_smooth_quotient_step_atlas N ep ch hd (fun e => boundaryAttachment) a
      N' ep' ch' hd' H J hJ (𝓡 3) hcoreH hseamH hrad hc' hs'
  let _ := Qcharts
  obtain ⟨U⟩ := E.exists_pairedBallQuotient_diffeomorph C Qcharts hc
    (fun e z => hs e ⟨(z, 0), Set.mem_univ _, by
      norm_num [SelfAttachment.directSeamDomain]⟩)
  obtain ⟨w₀, hall, ⟨K⟩⟩ :=
    nonempty_diffeomorph_sigma_fiber_of_connected N' ((U.symm.trans D).trans D')
  obtain rfl := hall none
  obtain ⟨F⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    (ch a false) (orientedBallChart (N (ep a false))) (ch a true)
    (orientedBallChart (N (ep a true))) boundaryAttachment
  refine ⟨fun K' => ?_, ⟨K.trans F.1⟩⟩
  by_contra hK'
  rw [not_or] at hK'
  exact Option.some_ne_none _ (hall (some ⟨K', hK'.1, hK'.2⟩))

private theorem cutCapVertex_eq_aux
    {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hloop : E.cutCapVertex a false = E.cutCapVertex a true) :
    ∀ K, K = E.cutCapVertex a false := by
  classical
  let N := E.capped.component
  let ep := E.cutCapVertex
  let ch := fun a t => E.capComponentBallChart (a, t)
  let hd := E.pairwise_disjoint_capComponentBallChart_image
  let C := fun K =>
    (PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N ep ch hd K).choose
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N ep ch v) := fun v => (C v).toChartedSpace
  obtain ⟨S, F, b, hb, hd', H, hfirst, hu, -, J, hJ⟩ :=
    PairedBallGluing.exists_quotient_homeomorph_loop N ep ch a hloop.symm hd
      (fun e => boundaryAttachment) rfl
  let N' := PairedBallGluing.loopFactor N ep a
  let ep' := fun e t => (PairedBallGluing.loopFlag N ep ch a b e t).fst
  let ch' := fun e t => (PairedBallGluing.loopFlag N ep ch a b e t).snd
  let C' := fun v =>
    (PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N' ep' ch' hd' v).choose
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N' ep' ch' v) := fun v => (C' v).toChartedSpace
  have : IsEmpty {e : E.tubes.Index // e ≠ a} :=
    ⟨fun e => e.property (Subsingleton.elim _ _)⟩
  obtain ⟨Qcharts', hm', hc', hs', D', -⟩ :=
    PairedBallGluing.exists_smooth_quotient_atlas_of_isEmpty N' ep' ch' hd'
      (fun e => boundaryAttachment) C'
  let _ := Qcharts'
  let _ := hm'
  obtain ⟨A, -, hcH, hsH, G, hG⟩ :=
    PairedBallGluing.exists_loop_smooth_atlas_of_factor_representatives N ep ch a hloop.symm
      hd S F b hb C C' H hfirst hu
  let _ := A
  have hGc : (fun q => G q) = H := funext hG
  have hcoreH : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (H ∘ PairedBallGluing.seamCoreInclusion N ep ch hd a boundaryAttachment) := by
    have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hcH
    simpa only [hGc] using hh
  have hseamH : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
      (H ∘ PairedBallGluing.seamChart N ep ch hd a boundaryAttachment) := by
    have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hsH
    simpa only [hGc] using hh
  have hrad := PairedBallGluing.loop_homeomorph_radialPoint N ep ch a hloop.symm hd
    S F b hb H hfirst hu hd'
  obtain ⟨Qcharts, -, hc, hs, D, -⟩ :=
    PairedBallGluing.exists_smooth_quotient_step_atlas N ep ch hd (fun e => boundaryAttachment) a
      N' ep' ch' hd' H J hJ (𝓡 3) hcoreH hseamH hrad hc' hs'
  let _ := Qcharts
  obtain ⟨U⟩ := E.exists_pairedBallQuotient_diffeomorph C Qcharts hc
    (fun e z => hs e ⟨(z, 0), Set.mem_univ _, by
      norm_num [SelfAttachment.directSeamDomain]⟩)
  obtain ⟨w₀, hall, -⟩ :=
    nonempty_diffeomorph_sigma_fiber_of_connected N' ((U.symm.trans D).trans D')
  obtain rfl := hall none
  intro K'
  by_contra hK'
  exact Option.some_ne_none _ (hall (some ⟨K', hK'⟩))

theorem nonempty_diffeomorph_connectedSum_of_cutCapVertex_ne
    {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hsep : E.cutCapVertex a false ≠ E.cutCapVertex a true) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum (E.capped.component (E.cutCapVertex a false))
        (E.capped.component (E.cutCapVertex a true))).Carrier) :=
  (cutCapVertex_ne_aux E a hsep).2

theorem eq_cutCapVertex_of_subsingleton
    {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (K : ConnectedComponents E.capped.Carrier) :
    K = E.cutCapVertex a false ∨ K = E.cutCapVertex a true := by
  by_cases h : E.cutCapVertex a false = E.cutCapVertex a true
  · exact Or.inl (cutCapVertex_eq_aux E a h K)
  · exact (cutCapVertex_ne_aux E a h).1 K

theorem nonempty_diffeomorph_connectedSum_sphereTwoTimesCircle_ulift_of_cutCapVertex_eq
    {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hloop : E.cutCapVertex a false = E.cutCapVertex a true) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum (E.capped.component (E.cutCapVertex a false))
        sphereTwoTimesCircleLift.ulift.{0, u}).Carrier) := by
  obtain ⟨d⟩ := nonempty_diffeomorph_connectedSum_sphereTwoTimesCircle_of_cutCapVertex_eq E a
    hloop
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
    (M := E.capped.component (E.cutCapVertex a false))
    (M' := E.capped.component (E.cutCapVertex a false))
    (N := sphereTwoTimesCircleLift) (N' := sphereTwoTimesCircleLift.ulift.{0, u})
    (ClosedOrientedManifold.OrientedDiffeomorph.refl
      (E.capped.component (E.cutCapVertex a false)).toClosedOrientedManifold)
    (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
      sphereTwoTimesCircleLift.toClosedOrientedManifold)
  exact ⟨d.trans g.1⟩

theorem singleSphereSurgery {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3}
    (X : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : X.tubes.Index)
    [Subsingleton X.tubes.Index] :
    (X.cutCapVertex a false ≠ X.cutCapVertex a true ∧
      Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum (X.capped.component (X.cutCapVertex a false))
          (X.capped.component (X.cutCapVertex a true))).Carrier)) ∨
    (X.cutCapVertex a false = X.cutCapVertex a true ∧
      Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum (X.capped.component (X.cutCapVertex a false))
          sphereTwoTimesCircleLift.ulift.{0, u}).Carrier)) := by
  by_cases h : X.cutCapVertex a false = X.cutCapVertex a true
  · exact Or.inr ⟨h,
      nonempty_diffeomorph_connectedSum_sphereTwoTimesCircle_ulift_of_cutCapVertex_eq X a h⟩
  · exact Or.inl ⟨h, nonempty_diffeomorph_connectedSum_of_cutCapVertex_ne X a h⟩

theorem exists_sphereSurgery (M : ConnectedClosedOrientedManifold.{u} 3)
    (e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M.Carrier)
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ (Q : ClosedOrientedManifold.{u} 3)
      (X : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : X.tubes.Index),
      Subsingleton X.tubes.Index ∧ tubeMiddleSphere X.tubes a = e ∧
        ((X.cutCapVertex a false ≠ X.cutCapVertex a true ∧
          Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (connectedSum (X.capped.component (X.cutCapVertex a false))
              (X.capped.component (X.cutCapVertex a true))).Carrier)) ∨
        (X.cutCapVertex a false = X.cutCapVertex a true ∧
          Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (connectedSum (X.capped.component (X.cutCapVertex a false))
              sphereTwoTimesCircleLift.ulift.{0, u}).Carrier))) := by
  obtain ⟨T, hT, a, rfl⟩ := sphereTubeExtension M e he
  obtain ⟨Q, X, rfl⟩ := sphereSystemCapping M T ⟨a⟩
  exact ⟨Q, X, a, hT, rfl, singleSphereSurgery X a⟩

end GC.Endpoint

namespace GC.Seifert

open ElementaryPresentation

theorem splitsBelow_of_cutCapVertex_ne {Q : ConnectedClosedOrientedManifold.{u} 3}
    {E : ElementaryPresentation (NoCuts.carrier Q)} {P : ClosedOrientedManifold.{u} 3}
    (X : SphericalCutCapTransition Q.toClosedOrientedManifold P) (a : X.tubes.Index)
    [Subsingleton X.tubes.Index] (hsep : X.cutCapVertex a false ≠ X.cutCapVertex a true)
    (EA : ElementaryPresentation (NoCuts.carrier (X.capped.component (X.cutCapVertex a false))))
    (EB : ElementaryPresentation (NoCuts.carrier (X.capped.component (X.cutCapVertex a true))))
    (hA : EA.complexity < E.complexity) (hB : EB.complexity < E.complexity) :
    E.SplitsBelow := by
  obtain ⟨d⟩ := nonempty_diffeomorph_connectedSum_of_cutCapVertex_ne X a hsep
  exact splitsBelow_of_diffeomorph d (elementaryBelow_of_complexity_lt EA hA)
    (elementaryBelow_of_complexity_lt EB hB)

theorem splitsBelow_of_cutCapVertex_eq {Q : ConnectedClosedOrientedManifold.{u} 3}
    {E : ElementaryPresentation (NoCuts.carrier Q)} {P : ClosedOrientedManifold.{u} 3}
    (X : SphericalCutCapTransition Q.toClosedOrientedManifold P) (a : X.tubes.Index)
    [Subsingleton X.tubes.Index] (hloop : X.cutCapVertex a false = X.cutCapVertex a true)
    (EA : ElementaryPresentation (NoCuts.carrier (X.capped.component (X.cutCapVertex a false))))
    (hA : EA.complexity < E.complexity) : E.SplitsBelow := by
  obtain ⟨d⟩ :=
    nonempty_diffeomorph_connectedSum_sphereTwoTimesCircle_ulift_of_cutCapVertex_eq X a hloop
  exact splitsBelow_of_diffeomorph d (elementaryBelow_of_complexity_lt EA hA)
    ⟨Or.inl seifertFactor_sphereTwoTimesCircle,
      Or.inl seifertFactor_sphereTwoTimesCircle_opposite⟩

end GC.Seifert
