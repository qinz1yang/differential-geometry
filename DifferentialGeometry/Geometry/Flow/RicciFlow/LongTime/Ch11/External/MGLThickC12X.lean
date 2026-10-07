import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveQuotient
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveDeckGroup
import DifferentialGeometry.Geometry.Hyperbolic.ThinRegionCharts
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalIdentity
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegions
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.ThickPartCompactness
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Stabilizer

/-!
# MGL 前半 (A)：uniformization 数据 + 一致 thick 点（O-C12X-MGLA G1，后缀 `_C12X`）

`exists_thick_uniformization_C12X`：存在 `ε > 0`（只依赖维数，取 Margulis-geometry 常数的一半），
使每个 `H : FiniteVolumeHyperbolicModel` 都有 uniformization `Γ ≤ PO 3 1`（离散、free）、
`e : Q[Γ] ≃ₜ H.Carrier`，`e ∘ π[Γ]` 是 local diffeomorphism 且度量拉回 = `4 ×` hyperboloid 度量，
并且 `HUpper 3` 中有一点 `x ∈ thickPart Γ ε`。

uniformization prelude 逐行照抄 `Truncation/UniformizationHG03.lean`（normalized universal cover，
曲率 −1/4 rescale 到 −1，deck 群经 `projectiveOrthogonalGroupEquiv` 进 `PO 3 1`）。thick 点：
`finiteLocus_nonempty` 给 `x` 使 `closedSmallSubgroup Γ (ε₀/2) x` 有限；位移 `< ε₀/2` 的 `γ` 落在
该有限群里 ⇒ 有限阶 ⇒ `γ = 1`（deck 群无挠，
`projective_range_normalizedUniversalCoverDeckRepresentation_isOfFinOrder_iff_eq_one`）。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal

open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open DifferentialGeometry.LatticeCompactness (thickPart)
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

namespace GC.LongTime.Ch11.External

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

local notation "Q[" G "]" => MulAction.orbitRel.Quotient G (HUpper 3)
local notation "π[" G "]" => Quotient.mk (MulAction.orbitRel G (HUpper 3))

private theorem curvature_identity_C12X (H : FiniteVolumeHyperbolicModel.{u})
    (x : H.Carrier) (v w : TangentSpace (𝓡 3) x) :
    Curvature.metricRm04StandardAt H.metric x v w w v =
      (-1 / 4 : ℝ) * (H.metric.inner x v v * H.metric.inner x w w -
        H.metric.inner x v w * H.metric.inner x v w) := by
  simpa only [neg_div] using
    Curvature.metricRm04StandardAt_eq_of_sectionalCurvature_eq
      H.metric (-(1 / 4 : ℝ)) x (H.curvature x) v w

/-- 无挠离散群里，`finiteLocus` 的点是 thick 点（同一半径）。 -/
private theorem mglA_mem_thickPart_of_mem_finiteLocus (Γ : Subgroup (PO 3 1))
    (htf : ∀ a : Γ, IsOfFinOrder a → a = 1) {r : ℝ} {x : HUpper 3}
    (hx : x ∈ OrbifoldStrata.finiteLocus (Nat.le_add_left 1 2) Γ r) :
    x ∈ thickPart (Nat.le_add_left 1 2) Γ r := by
  intro γ hγ
  by_contra hlt
  let K := OrbifoldStrata.closedSmallSubgroup (Nat.le_add_left 1 2) Γ r x
  let _ : Finite K := hx
  have hmem : (γ : PO 3 1) ∈ K :=
    Subgroup.subset_closure ⟨γ.2, by rw [dist_comm]; exact (not_le.mp hlt).le⟩
  have hle : K ≤ Γ := OrbifoldStrata.closedSmallSubgroup_le (Nat.le_add_left 1 2) Γ r x
  have hfin : IsOfFinOrder γ :=
    (Subgroup.inclusion hle).isOfFinOrder (isOfFinOrder_of_finite (⟨γ, hmem⟩ : K))
  exact hγ (htf γ hfin)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **MGL (A)**：一致 `ε` 下，每个有限体积双曲 3-流形的 uniformization 数据与一个 thick 点。 -/
theorem exists_thick_uniformization_C12X :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : FiniteVolumeHyperbolicModel.{u},
      ∃ (Γ : Subgroup (PO 3 1)) (_ : DiscreteTopology Γ) (_ : IsCancelSMul Γ (HUpper 3))
        (e : Q[Γ] ≃ₜ H.Carrier),
        IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]) ∧
        (∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
          H.metric.inner ((e ∘ π[Γ]) p)
              (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
              (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
            4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
              (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
              (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w)) ∧
        ∃ x : HUpper 3, x ∈ thickPart (Nat.le_add_left 1 2) Γ ε := by
  obtain ⟨ε₀, hε₀, hgeom⟩ :=
    BoundaryStabilizer.exists_margulis_geometry_constant (Nat.le_add_left 1 2)
  refine ⟨ε₀ / 2, half_pos hε₀, fun H => ?_⟩
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
  have hsec := curvature_identity_C12X H
  let ρ := normalizedUniversalCoverDeckRepresentation g H.complete (-1 / 4) hκ o hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  have hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g H.complete (-1 / 4) hκ o hsec i).choose
  let _ : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let _ : IsCancelSMul σ.range (HUpper 3) :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation
      g H.complete (-1 / 4) hκ o hsec i
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
  have htf : ∀ a : σ.range, IsOfFinOrder a → a = 1 := fun a ha =>
    (projective_range_normalizedUniversalCoverDeckRepresentation_isOfFinOrder_iff_eq_one
      g H.complete (-1 / 4) hκ o hsec i a).mp ha
  obtain ⟨x, hx⟩ := OrbifoldThinRegions.finiteLocus_nonempty (Nat.le_add_left 1 2)
    (by norm_num) σ.range hΓ (half_pos hε₀).le (half_lt_self hε₀) (hgeom σ.range hΓ)
  exact ⟨σ.range, inferInstance, inferInstance, e, he, hmetric, x,
    mglA_mem_thickPart_of_mem_finiteLocus σ.range htf hx⟩

/-- consumer：一致 `ε` 下取出 uniformization 与 thick 点，展开 `thickPart` 得非平凡元素的
位移下界（`γ • x` 是 `subAction` 的作用）。 -/
example : ∃ ε : ℝ, 0 < ε ∧ ∀ H : FiniteVolumeHyperbolicModel.{u},
    ∃ (Γ : Subgroup (PO 3 1)) (e : Q[Γ] ≃ₜ H.Carrier) (x : HUpper 3),
      DiscreteTopology Γ ∧ IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]) ∧
      ∀ γ : Γ, γ ≠ 1 → ε ≤ dist x (γ • x) := by
  obtain ⟨ε, hε, h⟩ := exists_thick_uniformization_C12X.{u}
  refine ⟨ε, hε, fun H => ?_⟩
  obtain ⟨Γ, hd, _, e, he, _, x, hx⟩ := h H
  exact ⟨Γ, e, x, hd, he, hx⟩

end GC.LongTime.Ch11.External
