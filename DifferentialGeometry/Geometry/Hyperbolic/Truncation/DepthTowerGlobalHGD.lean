import DifferentialGeometry.Geometry.Hyperbolic.Truncation.DepthTowerHGD
import DifferentialGeometry.Geometry.Hyperbolic.Truncation.NonemptyHG03

/-!
# HG03 派生项 G1b：无条件 depth tower（S-HG-DERIV G1，后缀 `_HGD`）

把 `DepthTowerHGD.exists_depth_tower_of_thick_thin_HGD`（thick–thin 分解 `D` 显式）与 O-HG-HG03
的 G1–G4 同样的消前提链接起来：

* `exists_depth_tower_of_hypotheses_HGD`：`D` 由 Margulis 常数与 `exists_finite_cusp_truncation`
  产生（对应 `truncation_of_hypotheses_HG03`）；
* `exists_depth_tower_of_peripheral_HGD`：normalized universal cover 给出全部 uniformization 数据
  （与 `exists_truncation_of_peripheral_HG03` 同一段构造；那里结论只是 `Nonempty`，拿不到 `D`，
  所以这里重述一遍）；
* `exists_depth_tower_HGD`：周边格条件 (P) 由 G3a/G3b 消去。**无任何显式前提**。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal
open MeasureTheory Set

namespace DifferentialGeometry.Geometry.Hyperbolic

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Horospherical (Horizontal)
open GC.Endpoint
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

local notation "Q[" G "]" => MulAction.orbitRel.Quotient G (HUpper 3)
local notation "π[" G "]" => Quotient.mk (MulAction.orbitRel G (HUpper 3))

/-- depth tower（thick–thin 分解由 Margulis 产生，周边格条件对所有 parabolic 不动点陈述）。 -/
theorem exists_depth_tower_of_hypotheses_HGD (H : FiniteVolumeHyperbolicModel.{u})
    (Γ : Subgroup (PO 3 1)) [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper 3)]
    [HasFundamentalDomain Γ (PO 3 1)] (hcov : covolume Γ (PO 3 1) ≠ ⊤)
    (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ π[Γ]) p)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (hper : ∀ ξ : HyperbolicBoundary.BoundaryH 3,
      CuspCorrespondence.IsCuspCenter (Nat.le_add_left 1 2) Γ ξ → ∃ a : PO 3 1,
        (HyperbolicBoundary.poBoundaryMulAction (Nat.le_add_left 1 2)).smul a ξ =
          MobiusBoundary.ptInfty ∧
        ∃ (Λ : Submodule ℤ (Horizontal 2)) (hΛ : DiscreteTopology Λ),
          letI := hΛ
          IsZLattice ℝ Λ ∧
            (endStabilizer (Nat.le_add_left 1 2) Γ {ξ}).map (MulAut.conj a).toMonoidHom =
              TranslationLattices.latticeGroup Λ) :
    ∃ Tr₀ : HyperbolicTruncation H, ∀ S : ℝ, 0 ≤ S → ∃ Tr : HyperbolicTruncation H,
      (range Tr.inclusion)ᶜ =
        ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | S < p.2.val 0} := by
  have hΓ : IsDiscrete (SetLike.coe Γ) :=
    isDiscrete_iff_discreteTopology.mpr inferInstance
  obtain ⟨ε, hε, hgeom⟩ :=
    BoundaryStabilizer.exists_margulis_geometry_constant (Nat.le_add_left 1 2)
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := half_lt_self hε
  obtain ⟨D⟩ := CuspTruncation.exists_finite_cusp_truncation (Nat.le_add_left 1 2)
    (by norm_num) Γ hΓ hcov hr hrε (hgeom Γ hΓ)
  exact exists_depth_tower_of_thick_thin_HGD H D e he hmetric fun ξ =>
    hper ξ.val (CuspCorrespondence.isCuspCenter_of_thinRegion (Nat.le_add_left 1 2)
      (by norm_num) Γ hΓ hcov hr hrε (hgeom Γ hΓ) (D.region_nonempty ξ))

private theorem curvature_identity_HGD (H : FiniteVolumeHyperbolicModel.{u})
    (x : H.Carrier) (v w : TangentSpace (𝓡 3) x) :
    Curvature.metricRm04StandardAt H.metric x v w w v =
      (-1 / 4 : ℝ) * (H.metric.inner x v v * H.metric.inner x w w -
        H.metric.inner x v w * H.metric.inner x v w) := by
  simpa only [neg_div] using
    Curvature.metricRm04StandardAt_eq_of_sectionalCurvature_eq
      H.metric (-(1 / 4 : ℝ)) x (H.curvature x) v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- depth tower producer，唯一显式前提 = 周边格条件 (P)（对所有 uniformization 量化）。 -/
theorem exists_depth_tower_of_peripheral_HGD (H : FiniteVolumeHyperbolicModel.{u})
    (hper : ∀ (Γ : Subgroup (PO 3 1)) [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper 3)]
      [HasFundamentalDomain Γ (PO 3 1)], covolume Γ (PO 3 1) ≠ ⊤ →
      ∀ e : Q[Γ] ≃ₜ H.Carrier, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]) →
      ∀ ξ : HyperbolicBoundary.BoundaryH 3,
        CuspCorrespondence.IsCuspCenter (Nat.le_add_left 1 2) Γ ξ → ∃ a : PO 3 1,
          (HyperbolicBoundary.poBoundaryMulAction (Nat.le_add_left 1 2)).smul a ξ =
            MobiusBoundary.ptInfty ∧
          ∃ (Λ : Submodule ℤ (Horizontal 2)) (hΛ : DiscreteTopology Λ),
            letI := hΛ
            IsZLattice ℝ Λ ∧
              (endStabilizer (Nat.le_add_left 1 2) Γ {ξ}).map (MulAut.conj a).toMonoidHom =
                TranslationLattices.latticeGroup Λ) :
    ∃ Tr₀ : HyperbolicTruncation H, ∀ S : ℝ, 0 ≤ S → ∃ Tr : HyperbolicTruncation H,
      (range Tr.inclusion)ᶜ =
        ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | S < p.2.val 0} := by
  classical
  have hκ : (-1 / 4 : ℝ) < 0 := by norm_num
  let M := H.Carrier
  let g := H.metric
  let o := H.basepoint
  let _ : Inhabited M := ⟨o⟩
  let _ : LocallyPathConnectedSpace E₃ :=
    (𝓡 3).toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E₃ M
  let _ : SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := 𝓡 3)
  let _ : SecondCountableTopology E₃ := ModelWithCorners.secondCountableTopology (𝓡 3)
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E₃ M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := 𝓡 3) gN
  let hĝ : RiemannianMetricComplete ĝ :=
    UniversalCover.liftedMetric_complete gN (H.complete.scaleMetric _ _)
  let _ : IsManifold (𝓡 3) 1 (UniversalCover M) :=
    IsManifold.of_le (I := 𝓡 3) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) :=
    Manifold.metrizableSpace (𝓡 3) (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : UniversalCover M → Type _) :=
    ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace (𝓡 3) : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  let b : OrthonormalBasis (Fin 3) ℝ
      (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M))) :=
    (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M)))).reindex
      (finCongr (show Module.finrank ℝ
        (TangentSpace (𝓡 3) (UniversalCover.basePoint (X := M))) = 3 from
          finrank_euclideanSpace_fin))
  let i := b.repr.symm
  have hsec := curvature_identity_HGD H
  let ρ := normalizedUniversalCoverDeckRepresentation g H.complete (-1 / 4) hκ o hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  have hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g H.complete (-1 / 4) hκ o hsec i).choose
  let _ : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let _ : IsCancelSMul σ.range (HUpper 3) :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation
      g H.complete (-1 / 4) hκ o hsec i
  obtain ⟨hfd, hcov⟩ := hasFundamentalDomain_and_covolume_ne_top_normalized_universal_cover
    g H.complete (-1 / 4) hκ o hsec H.finite_volume i
  let _ : HasFundamentalDomain σ.range (PO 3 1) := hfd
  have hcov' : covolume σ.range (PO 3 1) ≠ ⊤ := hcov
  let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g H.complete (-1 / 4) hκ o hsec i
  have hproj : (e ∘ π[σ.range]) =
      normalizedUniversalCoverProjection g H.complete (-1 / 4) hκ o hsec i :=
    funext (normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk
      g H.complete (-1 / 4) hκ o hsec i)
  have he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[σ.range]) := by
    rw [hproj]
    exact normalizedUniversalCoverProjection_isLocalDiffeomorph g H.complete (-1 / 4) hκ o hsec i
  have hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ π[σ.range]) p)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[σ.range]) p v)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[σ.range]) p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w) := by
    intro p v w
    rw [hproj, normalizedUniversalCoverProjection_inner g H.complete (-1 / 4) hκ o hsec i p v w]
    norm_num
  exact exists_depth_tower_of_hypotheses_HGD H σ.range hcov' e he hmetric
    (hper σ.range hcov' e he)


/-- **无条件 depth tower**：对每个有限体积双曲 3-流形模型 `H`，存在参考截断 `Tr₀`，使得对每个
`S ≥ 0` 有截断 `Tr` 的核心补 = `Tr₀` 各 cusp 在深度 `> S` 的尾部之并。 -/
theorem exists_depth_tower_HGD (H : FiniteVolumeHyperbolicModel.{u}) :
    ∃ Tr₀ : HyperbolicTruncation H, ∀ S : ℝ, 0 ≤ S → ∃ Tr : HyperbolicTruncation H,
      (range Tr.inclusion)ᶜ =
        ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | S < p.2.val 0} := by
  refine exists_depth_tower_of_peripheral_HGD H ?_
  intro Γ _ _ _ hcov e he ξ hξ
  exact peripheral_lattice_of_det_pos_HG03 Γ hcov
    (fun a δ hδ f hf => det_pos_of_orientation_HG03 H Γ e he a δ hδ f hf) ξ hξ

end DifferentialGeometry.Geometry.Hyperbolic
