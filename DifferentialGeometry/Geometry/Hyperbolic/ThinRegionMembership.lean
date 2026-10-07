import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveQuotient
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveDeckGroup
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionNeighborhoods
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionQuotient

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open OrbifoldThinRegions (thinRegion)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "B₃" => HyperbolicBoundary.BoundaryH 3

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
  (κ : ℝ) (hκ : κ < 0) (x₀ : M)
  (hsec : ∀ (x : M) (X Y : TangentSpace I x),
    Curvature.metricRm04StandardAt g x X Y Y X =
      κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem projective_displacement_eq_deck_displacement :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
      ∀ (γ : FundamentalGroup M (default : M)) (y : H₃),
        ENNReal.ofReal (dist ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (σ γ) y) y) =
          riemannianEDistOf ĝ (e (Hyperboloid.hUpperIsometryEquiv 3 y))
            (γ • e (Hyperboloid.hUpperIsometryEquiv 3 y)) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i γ y
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  let J := Hyperboloid.hUpperIsometryEquiv 3
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  have hconj := Hyperboloid.projectiveOrthogonalGroupEquiv_smul 2 (ρ γ) y
  change J ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (σ γ) y) = ρ γ (J y) at hconj
  have haction := (congrArg e hconj).trans
    (normalizedUniversalCoverIsometryEquiv_deckRepresentation g hg κ hκ x₀ hsec i γ (J y))
  calc
    _ = edist ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (σ γ) y) y := (edist_dist _ _).symm
    _ = edist (J ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (σ γ) y)) (J y) := (J.edist_eq _ _).symm
    _ = edist (e (J ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (σ γ) y))) (e (J y)) := (e.edist_eq _ _).symm
    _ = edist (UniversalCover.deckDiffeo (I := I) γ (e (J y))) (e (J y)) := congrArg (fun z => edist z (e (J y))) haction
    _ = edist (e (J y)) (UniversalCover.deckDiffeo (I := I) γ (e (J y))) := edist_comm _ _
    _ = _ := rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_mem_image_interior_thinRegion_of_short_deck_displacement :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
      ∀ (r ε : ℝ), r < ε →
        (∀ y : H₃, BoundaryStabilizer.ElementaryGeometry (by decide : 1 ≤ 3)
          (Margulis.smallSubgroup (by decide : 1 ≤ 3) σ.range ε y)) →
        ∀ (x : UniversalCover M) (γ : FundamentalGroup M (default : M)), γ ≠ 1 →
          riemannianEDistOf ĝ x (γ • x) < ENNReal.ofReal r →
          ∃ S : Set B₃, UniversalCover.proj x ∈ pH '' interior (thinRegion (by decide : 1 ≤ 3) σ.range r S) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i r ε hrε hgeom x γ hγ hshort
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  let J := Hyperboloid.hUpperIsometryEquiv 3
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
  let y := J.symm (e.symm x)
  have hexy : e (J y) = x := by simp only [y, IsometryEquiv.apply_symm_apply]
  have hproj : pH y = UniversalCover.proj x := congrArg UniversalCover.proj hexy
  have hdist : ENNReal.ofReal (dist ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (σ γ) y) y) =
      riemannianEDistOf ĝ x (UniversalCover.deckDiffeo (I := I) γ x) :=
    (projective_displacement_eq_deck_displacement g hg κ hκ x₀ hsec i γ y).trans
      (congrArg (fun z : UniversalCover M => riemannianEDistOf ĝ z (UniversalCover.deckDiffeo (I := I) γ z)) hexy)
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hshort)
  have hdshort : dist ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (σ γ) y) y < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr).mp (hdist.trans_lt hshort)
  have hσinj : Function.Injective σ :=
    (Hyperboloid.projectiveOrthogonalGroupEquiv 2).injective.comp
      (normalizedUniversalCoverDeckRepresentation_injective g hg κ hκ x₀ hsec i)
  have hσne : σ γ ≠ 1 := by
    intro he
    apply hγ
    apply hσinj
    exact he.trans (map_one σ).symm
  let a : σ.range := ⟨σ γ, ⟨γ, rfl⟩⟩
  have hinfinite : ¬ IsOfFinOrder (σ γ) := by
    intro hfin
    have ha : IsOfFinOrder a := (σ.range.subtype_injective.isOfFinOrder_iff).mp hfin
    have haone := (projective_range_normalizedUniversalCoverDeckRepresentation_isOfFinOrder_iff_eq_one
      g hg κ hκ x₀ hsec i a).mp ha
    exact hσne (congrArg Subtype.val haone)
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  have hΓ : IsDiscrete (SetLike.coe σ.range) := by
    have hd : IsDiscrete (SetLike.coe ρ.range) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
    rw [show σ = (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
      (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ from rfl,
      MonoidHom.range_comp]
    exact hd.image (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toHomeomorph.isInducing
  obtain ⟨δ, hdδ, hδr⟩ := exists_between hdshort
  have hgeomδ := OrbifoldStrata.closedSmallSubgroup_geometry (by decide : 1 ≤ 3) σ.range
    (hδr.trans hrε) y (hgeom y)
  obtain ⟨S, hyS⟩ := OrbifoldThinRegions.exists_thinRegion_of_short_infinite_order
    (by decide : 1 ≤ 3) σ.range y hgeomδ (σ γ) ⟨γ, rfl⟩ hinfinite hdδ.le
  have hyint := OrbifoldThinRegions.thinRegion_subset_interior (by decide : 1 ≤ 3) σ.range hΓ hδr
    (fun z => OrbifoldStrata.closedSmallSubgroup_geometry (by decide : 1 ≤ 3) σ.range hrε z (hgeom z)) S hyS
  exact ⟨S, y, hyint, hproj⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_subset_image_interior_thinRegion_of_isConnected_of_short_deck_displacement :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
      ∀ (r ε : ℝ), r < ε →
        (∀ y : H₃, BoundaryStabilizer.ElementaryGeometry (by decide : 1 ≤ 3)
          (Margulis.smallSubgroup (by decide : 1 ≤ 3) σ.range ε y)) →
        ∀ C : Set M, IsConnected C →
          (∀ x : UniversalCover M, UniversalCover.proj x ∈ C →
            ∃ γ : FundamentalGroup M (default : M), γ ≠ 1 ∧
              riemannianEDistOf ĝ x (γ • x) < ENNReal.ofReal r) →
          ∃ S : Set B₃, C ⊆ pH '' interior (thinRegion (by decide : 1 ≤ 3) σ.range r S) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i r ε hrε hgeom C hC hshort
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
  let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) σ.range
  let piQ : H₃ → MulAction.orbitRel.Quotient σ.range H₃ := Quotient.mk _
  let F := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i
  have hF (y : H₃) : F (piQ y) = pH y :=
    normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i y
  have hC' : IsConnected (F.symm '' C) := hC.image F.symm F.symm.continuous.continuousOn
  have hthin : F.symm '' C ⊆ ⋃ S : Set B₃, piQ '' interior (thinRegion (by decide : 1 ≤ 3) σ.range r S) := by
    rintro y ⟨p, hp, rfl⟩
    have honto : Function.Surjective (UniversalCover.proj : UniversalCover M → M) := by
      let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
      intro q
      exact ⟨⟨q, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ q)⟩, rfl⟩
    obtain ⟨x, hxp⟩ := honto p
    obtain ⟨γ, hγ, hd⟩ := hshort x (hxp.symm ▸ hp)
    have hpoint := exists_mem_image_interior_thinRegion_of_short_deck_displacement
      g hg κ hκ x₀ hsec i r ε hrε hgeom x γ hγ hd
    obtain ⟨S, z, hz, hzx⟩ := hpoint
    apply Set.mem_iUnion.mpr
    refine ⟨S, z, hz, ?_⟩
    apply F.injective
    exact (hF z).trans ((hzx.trans hxp).trans (F.apply_symm_apply p).symm)
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  have hΓ : IsDiscrete (SetLike.coe σ.range) := by
    have hd : IsDiscrete (SetLike.coe ρ.range) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
    rw [show σ = (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
      (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ from rfl,
      MonoidHom.range_comp]
    exact hd.image (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toHomeomorph.isInducing
  obtain ⟨S, hS⟩ := OrbifoldThinRegions.exists_quotient_interior_thinRegion_of_isConnected
    (by decide : 1 ≤ 3) σ.range hΓ r hC' hthin
  refine ⟨S, ?_⟩
  intro p hp
  obtain ⟨z, hz, hzp⟩ := hS ⟨p, hp, rfl⟩
  exact ⟨z, hz, (hF z).symm.trans ((congrArg F hzp).trans (F.apply_symm_apply p))⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem not_mem_image_thinRegion_of_forall_deck_displacement_gt :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
      ∀ (y : M) (δ r : ℝ), r ≤ δ →
        (∀ x : UniversalCover M, UniversalCover.proj x = y →
          ∀ γ : FundamentalGroup M (default : M), γ ≠ 1 →
            ENNReal.ofReal δ < riemannianEDistOf ĝ x (γ • x)) →
        ∀ S : Set B₃, y ∉ pH '' thinRegion (by decide : 1 ≤ 3) σ.range r S := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i y δ r hrδ hthick S hy
  obtain ⟨z, hz, hzy⟩ := hy
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  let J := Hyperboloid.hUpperIsometryEquiv 3
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  obtain ⟨a, ha, hshort⟩ := OrbifoldThinRegions.exists_short_ne_one_of_mem_thinRegion
    (by decide : 1 ≤ 3) σ.range hz
  obtain ⟨γ, hγ⟩ := a.property
  have hγne : γ ≠ 1 := by
    intro he
    apply ha
    apply Subtype.ext
    exact hγ.symm.trans (he ▸ map_one σ)
  have hlong := hthick (e (J z)) hzy γ hγne
  have hd := projective_displacement_eq_deck_displacement g hg κ hκ x₀ hsec i γ z
  have hshort' : dist ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (σ γ) z) z ≤ r := by
    exact (congrArg (fun a : ProjectiveOrthogonalGroup.PO 3 1 =>
      dist ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul a z) z) hγ).trans_le hshort
  have hle := (ENNReal.ofReal_le_ofReal (hshort'.trans hrδ))
  exact (not_lt_of_ge (hd.symm.trans_le hle)) hlong

end DifferentialGeometry.Geometry.Hyperbolic
