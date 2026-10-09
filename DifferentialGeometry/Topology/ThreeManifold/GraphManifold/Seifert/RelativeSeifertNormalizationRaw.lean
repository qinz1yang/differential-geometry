import DifferentialGeometry.Topology.ThreeManifold.CapComponentDiffeomorph

/-!
# The uncapping diffeomorphism with its core formula

Lane BR, tier R7, first step (review 26 §7.2). `exists_pairedBallQuotient_diffeomorph` gives the
diffeomorphism from the paired-ball quotient of the capped components onto the source manifold
only as `Nonempty`. Its construction is the paired-ball uncapping homeomorphism followed by the
uncapping homeomorphism `U₀` of `exists_uncapping_homeomorph_localDiffeomorph`, which is the
identity on the tube core. `exists_pairedBallQuotient_diffeomorph_core` re-runs that construction
and keeps the formula: a point of the all-core of the punctured capped components whose value is
the core inclusion of a core point `y` goes to `y` itself.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff

universe u

namespace GC.Seifert.RelativeNormalization

local notation "E3" => EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

private def seamCoordinates :
    Diffeomorph IC IC SelfAttachment.directSeamDomain ConnectedSumQuotient.CollarDomain ∞ where
  toFun p := (p.val.1, ⟨p.val.2, p.property.2⟩)
  invFun p := ⟨(p.1, p.2.val), mem_univ _, p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply ContMDiff.prodMk (contMDiff_fst.comp contMDiff_subtype_val)
    intro p
    exact DifferentialGeometry.codRestr_contMDiffAt
      (V := ConnectedSumQuotient.collarInterval) (fun p => p.property.2)
      ((contMDiff_snd.comp contMDiff_subtype_val).contMDiffAt)
  contMDiff_invFun := by
    intro p
    change ContMDiffAt IC IC ∞
      (fun p : ConnectedSumQuotient.CollarDomain =>
        (⟨(p.1, p.2.val), mem_univ _, p.2.property⟩ : SelfAttachment.directSeamDomain)) p
    exact DifferentialGeometry.codRestr_contMDiffAt
      (V := SelfAttachment.directSeamDomain) (fun p => ⟨mem_univ _, p.2.property⟩)
      ((contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)).contMDiffAt)

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_pairedBallQuotient_diffeomorph_core
    (C : ∀ K, SmoothBoundaryAtlas (𝓡 3) 3
      {x : (E.capped.component K).Carrier | (⟨K, x⟩ : Σ K, (E.capped.component K).Carrier) ∉
        ⋃ p, PairedBallGluing.flagMap E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t)) p '' ball (0 : E3) 1})
    (charts : ChartedSpace E3 (Quot (fun x y => ∃ a,
      PairedBallGluing.seamRel E.capped.component E.cutCapVertex
        (fun a t => E.capComponentBallChart (a, t)) E.pairwise_disjoint_capComponentBallChart_image
        a boundaryAttachment x y)))
    (hcore :
      let _ : ∀ K, ChartedSpace (EuclideanHalfSpace 3)
        (PairedBallGluing.PuncturedFactor E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t)) K) := fun K => (C K).toChartedSpace
      let _ := charts
      IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞
        (PairedBallGluing.allCoreInclusion E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t))
          E.pairwise_disjoint_capComponentBallChart_image (fun _ => boundaryAttachment)))
    (hseam :
      let _ := charts
      ∀ a z, IsLocalDiffeomorphAt IC (𝓡 3) ∞
        (PairedBallGluing.allSeamChart E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t))
          E.pairwise_disjoint_capComponentBallChart_image (fun _ => boundaryAttachment) a)
        ⟨(z, 0), mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩) :
    let _ := charts
    ∃ U : Diffeomorph (𝓡 3) (𝓡 3) (Quot (fun x y => ∃ a,
        PairedBallGluing.seamRel E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t))
          E.pairwise_disjoint_capComponentBallChart_image a boundaryAttachment x y)) M.Carrier ∞,
      ∀ (x : PairedBallGluing.allCore E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t))
          E.pairwise_disjoint_capComponentBallChart_image) (y : E.tubes.core),
        x.val.snd.val.val = E.capping.coreInclusion y →
          U (PairedBallGluing.allCoreInclusion E.capped.component E.cutCapVertex
            (fun a t => E.capComponentBallChart (a, t))
            E.pairwise_disjoint_capComponentBallChart_image (fun _ => boundaryAttachment) x) =
            y.val := by
  let _ := charts
  let _ : ∀ K, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) K) := fun K => (C K).toChartedSpace
  obtain ⟨U, hUcore, hUi, hUs⟩ := E.capping.exists_uncapping_homeomorph_localDiffeomorph
  let H := E.pairedBallUncappingHomeomorph.trans U
  have heq : H ∘ PairedBallGluing.allCoreInclusion E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t))
      E.pairwise_disjoint_capComponentBallChart_image (fun _ => boundaryAttachment) =
        E.capping.uncappingInteriorMap U ∘ E.capAllCoreMap := by
    funext x
    exact congrArg U (E.pairedBallUncappingHomeomorph_allCore x)
  have hH : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ H := by
    intro q
    rcases PairedBallGluing.all_local_maps_cover E.capped.component E.cutCapVertex
        (fun a t => E.capComponentBallChart (a, t))
        E.pairwise_disjoint_capComponentBallChart_image
        (fun _ => boundaryAttachment) q with ⟨x, hx⟩ | ⟨a, z, hz⟩
    · subst q
      have hg := (E.isLocalDiffeomorph_capAllCoreMap C x).comp (𝓡 3) M.Carrier
        (hUi (E.capAllCoreMap x))
      have hh : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞
          (H ∘ PairedBallGluing.allCoreInclusion E.capped.component E.cutCapVertex
            (fun a t => E.capComponentBallChart (a, t))
            E.pairwise_disjoint_capComponentBallChart_image (fun _ => boundaryAttachment)) x :=
        heq.symm ▸ hg
      exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp hh (hcore x)
    · subst q
      let p : SelfAttachment.directSeamDomain :=
        ⟨(z, 0), mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩
      have heqs : H ∘ PairedBallGluing.allSeamChart E.capped.component E.cutCapVertex
          (fun a t => E.capComponentBallChart (a, t))
          E.pairwise_disjoint_capComponentBallChart_image (fun _ => boundaryAttachment) a =
            (U ∘ E.capping.uncappingSeam a) ∘ seamCoordinates := by
        funext x
        exact congrArg U (E.pairedBallUncappingHomeomorph_allSeam a x)
      have hg := (seamCoordinates.isLocalDiffeomorph p).comp (𝓡 3) M.Carrier (hUs a z)
      have hh : IsLocalDiffeomorphAt IC (𝓡 3) ∞
          (H ∘ PairedBallGluing.allSeamChart E.capped.component E.cutCapVertex
            (fun a t => E.capComponentBallChart (a, t))
            E.pairwise_disjoint_capComponentBallChart_image (fun _ => boundaryAttachment) a) p :=
        heqs.symm ▸ hg
      exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp hh (hseam a z)
  refine ⟨hH.diffeomorphOfBijective H.bijective, fun x y hxy => ?_⟩
  change H _ = y.val
  have h1 := congrFun heq x
  simp only [Function.comp_apply] at h1
  rw [h1]
  have h2 : E.capAllCoreMap x =
      ⟨E.capping.coreInclusion y, E.capping.coreInclusion_mem_uncappingInterior y⟩ :=
    Subtype.ext hxy
  rw [h2]
  exact E.capping.uncappingInteriorMap_core U hUcore y

end GC.Seifert.RelativeNormalization
