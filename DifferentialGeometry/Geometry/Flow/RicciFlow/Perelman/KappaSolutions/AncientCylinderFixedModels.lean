import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderTopologicalModels
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance fixedCylinderSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

private theorem fixedCylinder_antipodal (x : SphereTwo) :
    sphereDiffeo (n := 2) (LinearIsometryEquiv.neg ℝ : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
        x = -x := by
  apply Subtype.ext
  rfl

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance fixedCylinderTopology : TopologicalSpace F.M := F.topology
local instance fixedCylinderCharted : ChartedSpace H F.M := F.charted
local instance fixedCylinderSmooth : IsManifold I ∞ F.M := F.smooth
local instance fixedCylinderInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance fixedCylinderT2 : T2Space F.M := F.t2
local instance fixedCylinderSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance fixedCylinderLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance fixedCylinderSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

private theorem fixedCylinder_local
    (Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M) :
    IsLocalDiffeomorph CylinderI I ∞
      (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
  isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I) (M := F.M))
    Psi.isLocalDiffeomorph

private theorem fixedCylinder_covering
    (Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M) :
    IsCoveringMap (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
  (UniversalCover.proj_isCoveringMap (X := F.M)).comp_homeomorph Psi.toHomeomorph

theorem ancientKappa_null_plane_fixed_cylinder_smooth_models {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∃ T : ℝ, 0 < T ∧ ∃ Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M,
      (∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
        (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
            (mfderiv CylinderI I Psi (x, s) (v, a))
            (mfderiv CylinderI I Psi (x, s) (w, b)) =
          (2 * (T - t)) * (sphereMetric).inner x v w + a * b) ∧
      IsLocalDiffeomorph CylinderI I ∞ (fun p : Cylinder => UniversalCover.proj (Psi p)) ∧
      IsCoveringMap (fun p : Cylinder => UniversalCover.proj (Psi p)) ∧
      Function.Surjective (fun p : Cylinder => UniversalCover.proj (Psi p)) ∧
      (((∃ d : Cylinder ≃ₘ⟮CylinderI, I⟯ F.M,
          ∀ p : Cylinder, d p = UniversalCover.proj (Psi p)) ∧
        (∀ p q : Cylinder, UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
          q = p)) ∨
      ((∃ d : (SphereAntipodalQuotient × ℝ) ≃ₘ⟮CylinderI, I⟯ F.M,
          ∀ p : Cylinder, d (SphereAntipodalQuotient.productProjection p) =
            UniversalCover.proj (Psi p)) ∧
        (∀ p q : Cylinder, UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
          q = p ∨ q = (-p.1, p.2))) ∨
      ((∃ d : CylinderDiagonalQuotient ≃ₘ⟮CylinderI, I⟯ F.M,
          ∀ p : Cylinder, d (CylinderDiagonalQuotient.proj p) =
            UniversalCover.proj (Psi p)) ∧
        (∀ p q : Cylinder, UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
          q = p ∨ q = (-p.1, -p.2)))) := by
  obtain ⟨T, hT, Psi, hproduct, hsurj, hcases⟩ :=
    ancientKappa_null_plane_fixed_cylinder_deck_fibres F hF hdim
      t₀ ht₀ x₀ v₀ w₀ hplane hnull
  have hlocal := fixedCylinder_local F Psi
  have hcover := fixedCylinder_covering F Psi
  rcases hcases with ⟨_, hsingle⟩ | ⟨_, hsphere | ⟨c, hdiagonal⟩⟩
  · have hinj : Function.Injective (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
      fun p q hpq => ((hsingle p q).mp hpq).symm
    obtain ⟨d, hd⟩ := cylinderCover_exists_diffeomorph_of_injective Psi hinj hsurj
    exact ⟨T, hT, Psi, hproduct, hlocal, hcover, hsurj, Or.inl ⟨⟨d, hd⟩, hsingle⟩⟩
  · have hfibres : ∀ p q : Cylinder,
        UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
          q = p ∨ q = (-p.1, p.2) := by
      simpa only [fixedCylinder_antipodal] using hsphere
    obtain ⟨d, hd⟩ := SphereAntipodalQuotient.exists_product_homeomorph
      (fun p : Cylinder => UniversalCover.proj (Psi p))
      hlocal.contMDiff.continuous hlocal.isOpenMap hsurj hfibres
    have hq : IsLocalDiffeomorph CylinderI CylinderI ∞
        SphereAntipodalQuotient.productProjection :=
      isLocalDiffeomorph_prod_real SphereAntipodalQuotient.proj
        SphereAntipodalQuotient.isLocalDiffeomorph_proj
    obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      SphereAntipodalQuotient.productProjection hq
      SphereAntipodalQuotient.surjective_productProjection
      (fun p : Cylinder => UniversalCover.proj (Psi p)) hlocal d hd
    refine ⟨T, hT, Psi, hproduct, hlocal, hcover, hsurj,
      Or.inr (Or.inl ⟨⟨D, ?_⟩, hfibres⟩)⟩
    intro p
    rw [hD]
    exact hd p
  · let Psi' := (cylinderLineTranslation c).trans Psi
    have hlocal' := fixedCylinder_local F Psi'
    have hcover' := fixedCylinder_covering F Psi'
    have hsurj' := cylinderDeck_recenter_surjective Psi hsurj c
    have hfibres : ∀ p q : Cylinder,
        UniversalCover.proj (Psi' p) = UniversalCover.proj (Psi' q) ↔
          q = p ∨ q = (-p.1, -p.2) := by
      simpa only [fixedCylinder_antipodal] using
        cylinderDeck_recenter_fibres Psi c hdiagonal
    obtain ⟨d, hd⟩ := CylinderDiagonalQuotient.exists_homeomorph
      (fun p : Cylinder => UniversalCover.proj (Psi' p))
      hlocal'.contMDiff.continuous hlocal'.isOpenMap hsurj' hfibres
    obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      CylinderDiagonalQuotient.proj CylinderDiagonalQuotient.isLocalDiffeomorph_proj
      CylinderDiagonalQuotient.surjective_proj
      (fun p : Cylinder => UniversalCover.proj (Psi' p)) hlocal' d hd
    have hproduct' := cylinderLineTranslation_trans_pullback
      F.S.family.metric T Psi hproduct c
    refine ⟨T, hT, Psi', hproduct', hlocal', hcover', hsurj',
      Or.inr (Or.inr ⟨⟨D, ?_⟩, hfibres⟩)⟩
    intro p
    rw [hD]
    exact hd p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
