import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderFixedModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureDichotomy
import DifferentialGeometry.Topology.ProjectiveSpace.AntipodalCylinderOrientation
import DifferentialGeometry.Topology.Covering.TwoPointDeckHomeomorphs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderNullPlane

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => S × ℝ
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance cylinderBranchSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u uE uH

section General

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance cylinderBranchTopology : TopologicalSpace F.M := F.topology
local instance cylinderBranchCharted : ChartedSpace H F.M := F.charted
local instance cylinderBranchSmooth : IsManifold I ∞ F.M := F.smooth
local instance cylinderBranchInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance cylinderBranchT2 : T2Space F.M := F.t2
local instance cylinderBranchLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance cylinderBranchSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

structure ShrinkingCylinderCover where
  extinctionTime : ℝ
  extinctionTime_pos : 0 < extinctionTime
  parametrization : Cylinder ≃ₘ⟮CI, I⟯ UniversalCover F.M
  metric : ∀ t : ℝ, t ≤ 0 → ∀ (y : S) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner
        (parametrization (y, s))
        (mfderiv CI I parametrization (y, s) (v, a))
        (mfderiv CI I parametrization (y, s) (w, b)) =
      (2 * (extinctionTime - t)) * (gS).inner y v w + a * b
  surjective : Function.Surjective
    (fun p : Cylinder => UniversalCover.proj (parametrization p))

namespace ShrinkingCylinderCover

variable {F} (C : ShrinkingCylinderCover F)

def projection : Cylinder → F.M :=
  fun p => UniversalCover.proj (C.parametrization p)

theorem projection_local : IsLocalDiffeomorph CI I ∞ C.projection :=
  isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I) (M := F.M))
    C.parametrization.isLocalDiffeomorph

theorem projection_covering : IsCoveringMap C.projection :=
  (UniversalCover.proj_isCoveringMap (X := F.M)).comp_homeomorph
    C.parametrization.toHomeomorph

theorem projection_metric (t : ℝ) (ht : t ≤ 0) (y : S) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a b : ℝ) :
    (F.S.family.metric t).inner (C.projection (y, s))
        (mfderiv CI I C.projection (y, s) (v, a))
        (mfderiv CI I C.projection (y, s) (w, b)) =
      (2 * (C.extinctionTime - t)) * (gS).inner y v w + a * b :=
  (cylinderCover_projection_inner (F.S.family.metric t) C.parametrization
    (y, s) (v, a) (w, b)).trans (C.metric t ht y s v w a b)

def TrivialModel : Prop :=
  (∃ d : Cylinder ≃ₘ⟮CI, I⟯ F.M, ∀ p : Cylinder, d p = C.projection p) ∧
    ∀ d : Cylinder ≃ₜ Cylinder,
      C.projection ∘ d = C.projection ↔ d = Homeomorph.refl Cylinder

def AntipodalProductModel : Prop :=
  (∃ d : (SphereAntipodalQuotient × ℝ) ≃ₘ⟮CI, I⟯ F.M,
      ∀ p : Cylinder, d (SphereAntipodalQuotient.productProjection p) = C.projection p) ∧
    ∀ d : Cylinder ≃ₜ Cylinder, C.projection ∘ d = C.projection ↔
      d = Homeomorph.refl Cylinder ∨ d = cylinderAntipodalProductDiffeomorph.toHomeomorph

def DiagonalModel : Prop :=
  (∃ d : CylinderDiagonalQuotient ≃ₘ⟮CI, I⟯ F.M,
      ∀ p : Cylinder, d (CylinderDiagonalQuotient.proj p) = C.projection p) ∧
    ∀ d : Cylinder ≃ₜ Cylinder, C.projection ∘ d = C.projection ↔
      d = Homeomorph.refl Cylinder ∨ d = cylinderDiagonalDiffeomorph.toHomeomorph

include C in
theorem not_positive (hdim : Module.finrank ℝ E = 3) :
    ¬ AncientPositiveCurvatureOperator F := by
  obtain ⟨x, a, b, hgram, hnull⟩ := cylinderCover_exists_null_plane
    (F.S.family.metric 0) (2 * (C.extinctionTime - 0))
    (mul_pos (by norm_num) (sub_pos.mpr C.extinctionTime_pos))
    C.parametrization (C.metric 0 le_rfl)
  intro hpos
  exact ancientPositiveCurvatureOperator_not_null_plane F hpos hdim
    0 le_rfl x a b hgram hnull

end ShrinkingCylinderCover

def AncientCylinderBranch : Prop :=
  ∃ C : ShrinkingCylinderCover F,
    C.TrivialModel ∨ C.AntipodalProductModel ∨ C.DiagonalModel

theorem ancientKappa_null_plane_cylinder_branch {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (t : ℝ) (ht : t ≤ 0) (x : F.M) (a b : TangentSpace I x)
    (hgram : 0 < (F.S.family.metric t).inner x a a *
      (F.S.family.metric t).inner x b b - ((F.S.family.metric t).inner x a b) ^ 2)
    (hnull : F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0) :
    AncientCylinderBranch F := by
  obtain ⟨T, hT, Psi, hmetric, _, hcover, hsurj, hcases⟩ :=
    ancientKappa_null_plane_fixed_cylinder_smooth_models F hF hdim
      t ht x a b hgram hnull
  let _ : PreconnectedSpace S := Subtype.preconnectedSpace
    (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp :
        1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
      (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let _ : Nonempty S := ⟨sphereEquator 0⟩
  let C : ShrinkingCylinderCover F := ⟨T, hT, Psi, hmetric, hsurj⟩
  refine ⟨C, ?_⟩
  rcases hcases with ⟨hmodel, hfibres⟩ | ⟨hmodel, hfibres⟩ | ⟨hmodel, hfibres⟩
  · refine Or.inl ⟨hmodel, ?_⟩
    intro d
    constructor
    · intro hd
      apply Homeomorph.ext
      intro p
      exact (hfibres p (d p)).mp (congrFun hd p).symm
    · rintro rfl
      rfl
  · refine Or.inr (Or.inl ⟨hmodel, ?_⟩)
    intro d
    exact covering_deck_iff_self_or_fibre_swap C.projection hcover
      cylinderAntipodalProductDiffeomorph.toHomeomorph hfibres d
  · refine Or.inr (Or.inr ⟨hmodel, ?_⟩)
    intro d
    exact covering_deck_iff_self_or_fibre_swap C.projection hcover
      cylinderDiagonalDiffeomorph.toHomeomorph hfibres d

theorem ancientKappa_three_dimensional_split_branch {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3) :
    Xor (AncientPositiveCurvatureOperator F) (AncientCylinderBranch F) := by
  apply (xor_iff_or_and_not_and _ _).mpr
  constructor
  · rcases ancientKappa_positive_or_null_plane F hF hdim with hpos | hnull
    · exact Or.inl hpos
    · obtain ⟨t, ht, x, a, b, hgram, hzero⟩ := hnull
      exact Or.inr (ancientKappa_null_plane_cylinder_branch F hF hdim
        t ht x a b hgram hzero)
  · rintro ⟨hpos, C, _⟩
    exact C.not_positive hdim hpos

end General

section Oriented

variable (F : PointedFlowData.{u, 0, 0} (I := ThreeModel) ancientTimeInterval)

local instance orientedCylinderTopology : TopologicalSpace F.M := F.topology
local instance orientedCylinderCharted : ChartedSpace ThreeSpace F.M := F.charted
local instance orientedCylinderSmooth : IsManifold ThreeModel ∞ F.M := F.smooth

theorem ShrinkingCylinderCover.not_antipodalProductModel
    (C : ShrinkingCylinderCover F) (o : TangentOrientationSection F.M) :
    ¬ C.AntipodalProductModel := by
  intro hmodel
  have hdeck := (hmodel.2 cylinderAntipodalProductDiffeomorph.toHomeomorph).mpr
    (Or.inr rfl)
  exact not_antipodal_product_localDiffeomorph o C.projection C.projection_local
    (fun p => congrFun hdeck p)

theorem ancientKappa_three_dimensional_split_branch_oriented {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (horientable : Nonempty (TangentOrientationSection F.M)) :
    Xor (AncientPositiveCurvatureOperator F)
      (∃ C : ShrinkingCylinderCover F, C.TrivialModel ∨ C.DiagonalModel) := by
  obtain ⟨o⟩ := horientable
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have h := (xor_iff_or_and_not_and _ _).mp
    (ancientKappa_three_dimensional_split_branch F hF hdim)
  apply (xor_iff_or_and_not_and _ _).mpr
  constructor
  · rcases h.1 with hpos | ⟨C, hmodel⟩
    · exact Or.inl hpos
    · right
      refine ⟨C, ?_⟩
      rcases hmodel with htrivial | hantipodal | hdiagonal
      · exact Or.inl htrivial
      · exact (ShrinkingCylinderCover.not_antipodalProductModel F C o hantipodal).elim
      · exact Or.inr hdiagonal
  · rintro ⟨hpos, C, _⟩
    exact C.not_positive hdim hpos

end Oriented

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
