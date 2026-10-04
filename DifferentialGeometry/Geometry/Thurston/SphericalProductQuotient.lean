import DifferentialGeometry.Geometry.Thurston.SphericalProductDeckGroups
import DifferentialGeometry.Geometry.Thurston.SphericalStructureStandard
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleFactor
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.PoincareStandardDiscardedModels

/-!
# Closed `S² × ℝ` manifolds from their deck presentation

Chapter 7, packet P8, tier 4. A `CylinderQuotientPresentation G Z` presents `Z` as the quotient
of the cylinder `S² × ℝ` by a group `G` of product isometries: a surjective local
diffeomorphism whose fibres are the `G`-orbits. For compact Hausdorff `Z` and a free action,
the group is discrete and infinite, so the algebraic classification
`cylinderCocompactGroup_classification` applies (`CylinderQuotientPresentation.classification`).

The developing-map step (complete `S² × ℝ` structure ⇒ universal cover by `S² × ℝ` with deck
group of orientation-preserving product isometries) is the named input
`SphericalProductUniversalCover`. The identifications of the cyclic quotient with `S² × S¹` and
of the dihedral quotient with `RP³ # RP³` are the named inputs
`CyclicCylinderQuotientIsSphereTwoTimesCircle` and `DihedralCylinderQuotientIsProjectiveSum`.
Together they give `GC.Endpoint.SphericalProductStandardConnectedSum`
(`sphericalProductStandardConnectedSum_of_universalCover`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace GC.Geometry.SphericalProduct

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

universe u

def cylinderAct (γ : CylinderIsometry) (p : SpatialNeckCylinder) : SpatialNeckCylinder :=
  (⟨γ.1 (p.1 : E3), by
    simpa only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] using p.1.2⟩, γ.2 p.2)

@[simp] theorem cylinderAct_fst (γ : CylinderIsometry) (p : SpatialNeckCylinder) :
    ((cylinderAct γ p).1 : E3) = γ.1 (p.1 : E3) := rfl

@[simp] theorem cylinderAct_snd (γ : CylinderIsometry) (p : SpatialNeckCylinder) :
    (cylinderAct γ p).2 = γ.2 p.2 := rfl

theorem cylinderAct_one (p : SpatialNeckCylinder) : cylinderAct 1 p = p := by
  refine Prod.ext (Subtype.ext ?_) ?_ <;> simp

theorem cylinderAct_mul (γ δ : CylinderIsometry) (p : SpatialNeckCylinder) :
    cylinderAct (γ * δ) p = cylinderAct γ (cylinderAct δ p) := by
  refine Prod.ext (Subtype.ext ?_) ?_ <;> simp

theorem cylinderAct_inv_cylinderAct (γ : CylinderIsometry) (p : SpatialNeckCylinder) :
    cylinderAct γ⁻¹ (cylinderAct γ p) = p := by
  rw [← cylinderAct_mul, inv_mul_cancel, cylinderAct_one]

theorem free_iff_cylinderAct (γ : CylinderIsometry) :
    (∀ p : S2 × ℝ, (γ.1 (p.1 : E3), γ.2 p.2) ≠ ((p.1 : E3), p.2)) ↔
      ∀ p : SpatialNeckCylinder, cylinderAct γ p ≠ p := by
  refine forall_congr' fun p => not_congr ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : γ.1 (p.1 : E3) = (p.1 : E3) := congrArg Prod.fst h
    have h2 : γ.2 p.2 = p.2 := congrArg Prod.snd h
    exact Prod.ext (Subtype.ext h1) h2
  · have h1 : γ.1 (p.1 : E3) = (p.1 : E3) :=
      congrArg (fun q : SpatialNeckCylinder => (q.1 : E3)) h
    have h2 : γ.2 p.2 = p.2 := congrArg Prod.snd h
    exact Prod.ext h1 h2

structure CylinderQuotientPresentation (G : Subgroup CylinderIsometry) (Z : Type*)
    [TopologicalSpace Z] [ChartedSpace E3 Z] where
  proj : SpatialNeckCylinder → Z
  isLocalDiffeomorph : IsLocalDiffeomorph SpatialNeckCylinderModel (𝓡 3) ∞ proj
  surjective : Function.Surjective proj
  fibres : ∀ a b, proj a = proj b ↔ ∃ γ ∈ G, cylinderAct γ a = b

namespace CylinderQuotientPresentation

variable {G : Subgroup CylinderIsometry} {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z]

private def basePoint : S2 :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    simp only [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩

theorem discrete [T2Space Z] (pr : CylinderQuotientPresentation G Z)
    (hfree : ∀ γ ∈ G, γ ≠ 1 → ∀ p : SpatialNeckCylinder, cylinderAct γ p ≠ p) (R : ℝ) :
    {γ : CylinderIsometry | γ ∈ G ∧ |γ.2 0| ≤ R}.Finite := by
  let a₀ : SpatialNeckCylinder := (basePoint, 0)
  let F : Set SpatialNeckCylinder := pr.proj ⁻¹' {pr.proj a₀}
  let K : Set SpatialNeckCylinder := Set.univ ×ˢ Metric.closedBall (0 : ℝ) R
  have hcont : Continuous pr.proj := pr.isLocalDiffeomorph.isLocalHomeomorph.continuous
  have hKF : IsCompact (K ∩ F) :=
    (isCompact_univ.prod (isCompact_closedBall (0 : ℝ) R)).inter_right
      (isClosed_singleton.preimage hcont)
  have hfin : (K ∩ F).Finite := by
    choose e he hfe using pr.isLocalDiffeomorph.isLocalHomeomorph
    obtain ⟨t, ht, hcover⟩ := hKF.elim_nhds_subcover (fun x => (e x).source)
      (fun x _ => (e x).open_source.mem_nhds (he x))
    refine t.finite_toSet.subset fun b hb => ?_
    obtain ⟨x, hxt, hbx⟩ := Set.mem_iUnion₂.mp (hcover hb)
    have hx := ht x hxt
    have hxb : x = b := by
      apply (e x).injOn (he x) hbx
      rw [← hfe x]
      exact hx.2.trans hb.2.symm
    rw [← hxb]
    exact hxt
  apply Set.Finite.of_finite_image (f := fun γ : CylinderIsometry => cylinderAct γ a₀)
  · refine hfin.subset ?_
    rintro _ ⟨γ, ⟨hγ, hR⟩, rfl⟩
    refine ⟨⟨Set.mem_univ _, ?_⟩, ?_⟩
    · change γ.2 0 ∈ Metric.closedBall (0 : ℝ) R
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hR
    · exact ((pr.fibres a₀ _).mpr ⟨γ, hγ, rfl⟩).symm
  · rintro γ ⟨hγ, -⟩ δ ⟨hδ, -⟩ h
    by_contra hne
    apply hfree (δ⁻¹ * γ) (G.mul_mem (G.inv_mem hδ) hγ)
      (fun h1 => hne (inv_mul_eq_one.mp h1).symm) a₀
    rw [cylinderAct_mul, show cylinderAct γ a₀ = cylinderAct δ a₀ from h,
      cylinderAct_inv_cylinderAct]

theorem infinite [CompactSpace Z] (pr : CylinderQuotientPresentation G Z) :
    (G : Set CylinderIsometry).Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image fun γ : CylinderIsometry => |γ.2 0|).bddAbove
  let U : ℕ → Set Z := fun n => pr.proj '' (Set.univ ×ˢ Metric.ball (0 : ℝ) n)
  have hopen : ∀ n, IsOpen (U n) := fun n =>
    pr.isLocalDiffeomorph.isLocalHomeomorph.isOpenMap _ (isOpen_univ.prod Metric.isOpen_ball)
  have hcover : (Set.univ : Set Z) ⊆ ⋃ n, U n := by
    intro z _
    obtain ⟨a, rfl⟩ := pr.surjective z
    obtain ⟨n, hn⟩ := exists_nat_gt |a.2|
    refine Set.mem_iUnion.mpr ⟨n, a, ⟨Set.mem_univ _, ?_⟩, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hn
  have hdir : Directed (· ⊆ ·) U := by
    apply Monotone.directed_le
    intro n m hnm
    apply Set.image_mono
    apply Set.prod_mono le_rfl
    exact Metric.ball_subset_ball (by exact_mod_cast hnm)
  obtain ⟨N, hN⟩ := isCompact_univ.elim_directed_cover U hopen hcover hdir
  let a : SpatialNeckCylinder := (basePoint, (N : ℝ) + M + 1)
  obtain ⟨b, ⟨-, hb⟩, hba⟩ := hN (Set.mem_univ (pr.proj a))
  obtain ⟨γ, hγ, hγb⟩ := (pr.fibres b a).mp hba
  have h2 : γ.2 b.2 = (N : ℝ) + M + 1 := congrArg Prod.snd hγb
  have hγM : |γ.2 0| ≤ M := hM ⟨γ, hγ, rfl⟩
  have hbN : |b.2| < N := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hb
  have hsign : |lineSign γ.2| = 1 := by
    rcases lineSign_eq_one_or_neg_one γ.2 with h | h <;> simp [h]
  have hbound : |γ.2 b.2| ≤ |b.2| + |γ.2 0| := by
    rw [line_apply γ.2 b.2]
    calc |lineSign γ.2 * b.2 + γ.2 0| ≤ |lineSign γ.2 * b.2| + |γ.2 0| := abs_add_le _ _
      _ = |b.2| + |γ.2 0| := by rw [abs_mul, hsign, one_mul]
  rw [h2] at hbound
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hγM
  rw [abs_of_pos (by positivity)] at hbound
  linarith

theorem classification [T2Space Z] [CompactSpace Z] (pr : CylinderQuotientPresentation G Z)
    (hfree : ∀ γ ∈ G, γ ≠ 1 → ∀ p : SpatialNeckCylinder, cylinderAct γ p ≠ p)
    (horient : ∀ γ ∈ G, LinearMap.det (γ.1.toLinearEquiv : E3 →ₗ[ℝ] E3) = lineSign γ.2) :
    (∃ (A : E3 ≃ₗᵢ[ℝ] E3) (c : ℝ), LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 ∧
        c ≠ 0 ∧ G = Subgroup.zpowers (A, AffineIsometryEquiv.vaddConst ℝ c)) ∨
      ∃ c₁ c₂ : ℝ, c₁ ≠ c₂ ∧ G = Subgroup.closure
        {(LinearIsometryEquiv.neg ℝ, AffineIsometryEquiv.pointReflection ℝ c₁),
          (LinearIsometryEquiv.neg ℝ, AffineIsometryEquiv.pointReflection ℝ c₂)} :=
  cylinderCocompactGroup_classification G
    (fun γ hγ hne => (free_iff_cylinderAct γ).mpr (hfree γ hγ hne)) horient
    (pr.discrete hfree) pr.infinite

end CylinderQuotientPresentation

def SphericalProductUniversalCover : Prop :=
  ∀ (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GeometricStructure (𝓡 3) P.Carrier), g.model = .sphericalProduct →
    ∃ G : Subgroup CylinderIsometry,
      (∀ γ ∈ G, γ ≠ 1 → ∀ p : SpatialNeckCylinder, cylinderAct γ p ≠ p) ∧
      (∀ γ ∈ G, LinearMap.det (γ.1.toLinearEquiv : E3 →ₗ[ℝ] E3) = lineSign γ.2) ∧
      Nonempty (CylinderQuotientPresentation G P.Carrier)

def CyclicCylinderQuotientIsSphereTwoTimesCircle : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z]
    (A : E3 ≃ₗᵢ[ℝ] E3) (c : ℝ), LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 → c ≠ 0 →
    CylinderQuotientPresentation (Subgroup.zpowers (A, AffineIsometryEquiv.vaddConst ℝ c)) Z →
    Nonempty (Z ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle)

def DihedralCylinderQuotientIsProjectiveSum : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z]
    (c₁ c₂ : ℝ), c₁ ≠ c₂ →
    CylinderQuotientPresentation (Subgroup.closure
      {(LinearIsometryEquiv.neg ℝ, AffineIsometryEquiv.pointReflection ℝ c₁),
        (LinearIsometryEquiv.neg ℝ, AffineIsometryEquiv.pointReflection ℝ c₂)}) Z →
    Nonempty (Z ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier)

theorem exists_classified_presentation_of_universalCover
    (hU : SphericalProductUniversalCover.{u}) (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .sphericalProduct) :
    ∃ G : Subgroup CylinderIsometry, Nonempty (CylinderQuotientPresentation G P.Carrier) ∧
      ((∃ (A : E3 ≃ₗᵢ[ℝ] E3) (c : ℝ), LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 ∧
        c ≠ 0 ∧ G = Subgroup.zpowers (A, AffineIsometryEquiv.vaddConst ℝ c)) ∨
      ∃ c₁ c₂ : ℝ, c₁ ≠ c₂ ∧ G = Subgroup.closure
        {(LinearIsometryEquiv.neg ℝ, AffineIsometryEquiv.pointReflection ℝ c₁),
          (LinearIsometryEquiv.neg ℝ, AffineIsometryEquiv.pointReflection ℝ c₂)}) := by
  obtain ⟨G, hfree, horient, ⟨pr⟩⟩ := hU P g hg
  exact ⟨G, ⟨pr⟩, pr.classification hfree horient⟩

theorem sphericalProductStandardConnectedSum_of_universalCover
    (hU : SphericalProductUniversalCover.{u})
    (hC : CyclicCylinderQuotientIsSphereTwoTimesCircle.{u})
    (hD : DihedralCylinderQuotientIsProjectiveSum.{u}) :
    GC.Endpoint.SphericalProductStandardConnectedSum.{u} := by
  intro P g hg
  obtain ⟨G, ⟨pr⟩, hcls⟩ := exists_classified_presentation_of_universalCover hU P g hg
  rcases hcls with ⟨A, c, hA, hc, rfl⟩ | ⟨c₁, c₂, hne, rfl⟩
  · obtain ⟨f⟩ := hC P.Carrier A c hA hc pr
    exact isStandardConnectedSum_of_standard_factor P
      (isStandardFactor_of_diffeomorph_sphereTwoTimesCircle P f)
  · obtain ⟨f⟩ := hD P.Carrier c₁ c₂ hne pr
    exact isStandardConnectedSum_of_diffeomorph f
      isStandardConnectedSum_connectedSum_projectiveThreeSpaceLift

theorem geometrizes_of_sphericalProductStructure_of_universalCover
    (hU : SphericalProductUniversalCover.{u})
    (hC : CyclicCylinderQuotientIsSphereTwoTimesCircle.{u})
    (hD : DihedralCylinderQuotientIsProjectiveSum.{u})
    (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .sphericalProduct) :
    GC.Endpoint.Geometrizes P :=
  GC.Endpoint.geometrizes_of_sphericalProductStructure
    (sphericalProductStandardConnectedSum_of_universalCover hU hC hD) P g hg

end GC.Geometry.SphericalProduct
