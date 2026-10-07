import DifferentialGeometry.Geometry.Hyperbolic.Truncation.ProducerHG03
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveQuotient
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveDeckGroup
import DifferentialGeometry.Geometry.Hyperbolic.HaarCovolume
import DifferentialGeometry.Geometry.Hyperbolic.ThinRegionCharts
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalIdentity

/-!
# HG03：消去 uniformization 前提 (U)（O-HG-HG03 G2，后缀 `_HG03`）

`exists_truncation_of_peripheral_HG03`：对 `H : FiniteVolumeHyperbolicModel`，用 donor 的
normalized universal cover（曲率 −1/4 rescale 到 −1，deck 群经 `projectiveOrthogonalGroupEquiv`
进 `PO 3 1`）给出 G1 的全部 (U) 数据：离散（`exists_normalizedUniversalCoverThinRegionCharts`）、
free（`isCancelSMul_projective_range_…`）、fundamental domain + covolume < ∞（`HaarCovolume`）、
`e = normalizedUniversalCoverProjectiveQuotientHomeomorph`、`e ∘ πΓ` = projection（local diffeo，
度量系数 `(-(-1/4))⁻¹ = 4`）。剩下的唯一显式前提是 (P)：对**每个** uniformization
（normalized Γ 依赖 basepoint 与正交基的内部选择，所以对所有 Γ 量化），每个 parabolic
不动点的周边稳定子共轭后恰为满秩平移格。(P) 由 G3（free action + orientation）消去。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal
open MeasureTheory

namespace DifferentialGeometry.Geometry.Hyperbolic

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Horospherical (Horizontal)
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

local notation "Q[" G "]" => MulAction.orbitRel.Quotient G (HUpper 3)
local notation "π[" G "]" => Quotient.mk (MulAction.orbitRel G (HUpper 3))

private theorem curvature_identity_HG03 (H : FiniteVolumeHyperbolicModel.{u})
    (x : H.Carrier) (v w : TangentSpace (𝓡 3) x) :
    Curvature.metricRm04StandardAt H.metric x v w w v =
      (-1 / 4 : ℝ) * (H.metric.inner x v v * H.metric.inner x w w -
        H.metric.inner x v w * H.metric.inner x v w) := by
  simpa only [neg_div] using
    Curvature.metricRm04StandardAt_eq_of_sectionalCurvature_eq
      H.metric (-(1 / 4 : ℝ)) x (H.curvature x) v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- HG03 producer，唯一显式前提 = 周边格条件 (P)（对所有 uniformization 量化）。 -/
theorem exists_truncation_of_peripheral_HG03 (H : FiniteVolumeHyperbolicModel.{u})
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
    Nonempty (HyperbolicTruncation H) := by
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
  have hsec := curvature_identity_HG03 H
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
  exact truncation_of_hypotheses_HG03 H σ.range hcov' e he hmetric (hper σ.range hcov' e he)

/-- consumer（ch12 D-R3-20 形状）：(P) 的族 ⇒ ch12 的 binder
`∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H)`。 -/
example (hfam : ∀ H : FiniteVolumeHyperbolicModel.{u},
    ∀ (Γ : Subgroup (PO 3 1)) [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper 3)]
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
    ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H) :=
  fun H => exists_truncation_of_peripheral_HG03 H (hfam H)

end DifferentialGeometry.Geometry.Hyperbolic
