import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckRepresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderFreeGroupClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitSurface

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
private abbrev CylinderI := (𝓡 2).prod (𝓘(ℝ, ℝ))
local notation "OrthogonalThree" => SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient
local notation "LineIsometry" => ℝ ≃ᵃⁱ[ℝ] ℝ
local notation "CylinderIsometry" => OrthogonalThree × LineIsometry
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)
local notation "antipodal" => sphereDiffeo (n := 2)
  (LinearIsometryEquiv.neg ℝ : OrthogonalThree)

private local instance ancientDeckClassificationSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

private theorem ancientDeck_identity_action (p : SphereTwo × ℝ) :
    (sphereDiffeo (n := 2) (1 : CylinderIsometry).1 p.1,
      (1 : CylinderIsometry).2 p.2) = p := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

section ActualFibres

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [IsManifold I ∞ M] in
private theorem ancientDeck_proj_eq_iff_exists
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (rho : FundamentalGroup M (default : M) →* CylinderIsometry)
    (hdeck : ∀ (gamma : FundamentalGroup M (default : M)) (x : SphereTwo) (s : ℝ),
      gamma • Psi (x, s) = Psi (sphereDiffeo (n := 2) (rho gamma).1 x, (rho gamma).2 s))
    (p q : SphereTwo × ℝ) :
    UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
      ∃ gamma : FundamentalGroup M (default : M),
        q = (sphereDiffeo (n := 2) (rho gamma).1 p.1, (rho gamma).2 p.2) := by
  constructor
  · intro h
    obtain ⟨gamma, hgamma⟩ := (UniversalCover.proj_eq_iff_smul (Psi p) (Psi q)).mp h
    refine ⟨gamma, ?_⟩
    exact (Psi.injective ((hdeck gamma p.1 p.2).symm.trans hgamma)).symm
  · rintro ⟨gamma, hgamma⟩
    apply (UniversalCover.proj_eq_iff_smul (Psi p) (Psi q)).mpr
    refine ⟨gamma, ?_⟩
    rw [hgamma]
    exact hdeck gamma p.1 p.2

omit [IsManifold I ∞ M] in
private theorem ancientDeck_proj_eq_iff_two_elements
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (rho : FundamentalGroup M (default : M) →* CylinderIsometry)
    (hdeck : ∀ (gamma : FundamentalGroup M (default : M)) (x : SphereTwo) (s : ℝ),
      gamma • Psi (x, s) = Psi (sphereDiffeo (n := 2) (rho gamma).1 x, (rho gamma).2 s))
    (gamma₀ : FundamentalGroup M (default : M))
    (helements : ∀ gamma : FundamentalGroup M (default : M), gamma = 1 ∨ gamma = gamma₀)
    (p q : SphereTwo × ℝ) :
    UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
      q = p ∨ q = (sphereDiffeo (n := 2) (rho gamma₀).1 p.1, (rho gamma₀).2 p.2) := by
  rw [ancientDeck_proj_eq_iff_exists Psi rho hdeck p q]
  constructor
  · rintro ⟨gamma, hgamma⟩
    rcases helements gamma with rfl | rfl
    · left
      simpa only [map_one, ancientDeck_identity_action] using hgamma
    · exact Or.inr hgamma
  · rintro (h | h)
    · refine ⟨1, ?_⟩
      simpa only [map_one, ancientDeck_identity_action] using h
    · exact ⟨gamma₀, h⟩

end ActualFibres

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientDeckClassificationBaseTopology : TopologicalSpace F.M := F.topology
local instance ancientDeckClassificationBaseCharted : ChartedSpace H F.M := F.charted
local instance ancientDeckClassificationBaseSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientDeckClassificationBaseInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance ancientDeckClassificationBaseT2 : T2Space F.M := F.t2
local instance ancientDeckClassificationBaseSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientDeckClassificationBaseLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance ancientDeckClassificationBaseSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

theorem ancientKappa_fixed_cylinder_deck_fibres {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (T : ℝ) (hT : 0 < T)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b) :
    Function.Surjective (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p)) ∧
      (((∀ gamma : FundamentalGroup F.M (default : F.M), gamma = 1) ∧
        ∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔ q = p) ∨
      ((∃ gamma₀ : FundamentalGroup F.M (default : F.M),
          gamma₀ ≠ 1 ∧ gamma₀ * gamma₀ = 1 ∧
            ∀ gamma : FundamentalGroup F.M (default : F.M), gamma = 1 ∨ gamma = gamma₀) ∧
        ((∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (antipodal p.1, p.2)) ∨
        ∃ c : ℝ, ∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (antipodal p.1, 2 * c - p.2)))) := by
  classical
  let _ : ConnectedSpace F.M := hF.connected
  let _ : PathConnectedSpace F.M := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨rho, hinjective, hdeck, hfree, hnoTranslation⟩ :=
    ancientKappa_exists_cylinderDeckRepresentation F hF hdim T hT Psi hproduct
  constructor
  · intro y
    let _ : PathConnectedSpace F.M := PathConnectedSpace.of_locallyPathConnectedSpace
    let y' : UniversalCover F.M :=
      ⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (default : F.M) y)⟩
    refine ⟨Psi.symm y', ?_⟩
    change UniversalCover.proj (Psi (Psi.symm y')) = y
    rw [Psi.apply_symm_apply]
    rfl
  · by_cases htrivial : ∀ gamma : FundamentalGroup F.M (default : F.M), gamma = 1
    · left
      refine ⟨htrivial, ?_⟩
      intro p q
      rw [ancientDeck_proj_eq_iff_exists Psi rho hdeck p q]
      constructor
      · rintro ⟨gamma, hgamma⟩
        simpa only [htrivial gamma, map_one, ancientDeck_identity_action] using hgamma
      · intro h
        refine ⟨1, ?_⟩
        simpa only [map_one, ancientDeck_identity_action] using h
    · push Not at htrivial
      obtain ⟨gamma₀, hgamma₀⟩ := htrivial
      have hmem : rho gamma₀ ∈ rho.range := MonoidHom.mem_range.mpr ⟨gamma₀, rfl⟩
      have hne : rho gamma₀ ≠ 1 := by
        intro h
        exact hgamma₀ (hinjective (h.trans rho.map_one.symm))
      have htwo := cylinderFreeGroup_eq_zpowers_and_two_elements
        rho.range hfree hnoTranslation (rho gamma₀) hmem hne
      have hsquare : gamma₀ * gamma₀ = 1 := by
        apply hinjective
        rw [map_mul, map_one]
        exact htwo.2.1
      have helements (gamma : FundamentalGroup F.M (default : F.M)) :
          gamma = 1 ∨ gamma = gamma₀ := by
        rcases (htwo.2.2 (rho gamma)).mp (MonoidHom.mem_range.mpr ⟨gamma, rfl⟩) with h | h
        · exact Or.inl (hinjective (h.trans rho.map_one.symm))
        · exact Or.inr (hinjective h)
      have hsphere := cylinderFreeGroup_sphere_eq_antipodal
        rho.range hfree hnoTranslation (rho gamma₀) hmem hne
      have hfibres := ancientDeck_proj_eq_iff_two_elements Psi rho hdeck gamma₀ helements
      right
      refine ⟨⟨gamma₀, hgamma₀, hsquare, helements⟩, ?_⟩
      rcases cylinderFreeGroup_line_eq_one_or_reflection
        rho.range hnoTranslation (rho gamma₀) hmem with hline | ⟨c, hline⟩
      · left
        intro p q
        simpa [hsphere, hline] using hfibres p q
      · right
        refine ⟨c, ?_⟩
        have hreflection (s : ℝ) : AffineIsometryEquiv.pointReflection ℝ c s = 2 * c - s := by
          change (c - s) + c = 2 * c - s
          ring
        intro p q
        simpa only [hsphere, hline, hreflection] using hfibres p q

theorem ancientKappa_null_plane_fixed_cylinder_deck_fibres {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∃ T : ℝ, 0 < T ∧ ∃ Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M,
      (∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
        (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
            (mfderiv CylinderI I Psi (x, s) (v, a))
            (mfderiv CylinderI I Psi (x, s) (w, b)) =
          (2 * (T - t)) * (sphereMetric).inner x v w + a * b) ∧
      Function.Surjective (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p)) ∧
      (((∀ gamma : FundamentalGroup F.M (default : F.M), gamma = 1) ∧
        ∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔ q = p) ∨
      ((∃ gamma₀ : FundamentalGroup F.M (default : F.M),
          gamma₀ ≠ 1 ∧ gamma₀ * gamma₀ = 1 ∧
            ∀ gamma : FundamentalGroup F.M (default : F.M), gamma = 1 ∨ gamma = gamma₀) ∧
        ((∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (antipodal p.1, p.2)) ∨
        ∃ c : ℝ, ∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (antipodal p.1, 2 * c - p.2)))) := by
  obtain ⟨T, hT, Psi, hproduct⟩ := ancientKappa_null_plane_fixed_round_cylinder
    F hF hdim t₀ ht₀ x₀ v₀ w₀ hplane hnull
  exact ⟨T, hT, Psi, hproduct,
    ancientKappa_fixed_cylinder_deck_fibres F hF hdim T hT Psi hproduct⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
