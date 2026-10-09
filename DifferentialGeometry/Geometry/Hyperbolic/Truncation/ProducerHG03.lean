import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.HyperbolicTruncation
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Correspondence
import DifferentialGeometry.Geometry.Hyperbolic.TruncationEnds

/-!
# HG03 条件 producer（O-HG-HG03 G1，后缀 `_HG03`）

从 uniformization 数据 (U) 与周边格条件 (P) 造 `HyperbolicTruncation H`。
设计见 `docs/geometrization/chapter8/design-HG03-truncation-20261006.md` §4。

* `exists_truncation_of_thick_thin_HG03`：thick–thin 分解 `D : FiniteCuspTruncation` 显式给出，
  每个 cusp center 的周边稳定子共轭后 = 满秩平移格（`hper`）⇒ `Nonempty (HyperbolicTruncation H)`。
* `truncation_of_hypotheses_HG03`：thick–thin 分解由 donor 的 Margulis 常数
  （`exists_margulis_geometry_constant`）与 `exists_finite_cusp_truncation` 产生；
  `hper` 改为对所有 parabolic 不动点（`IsCuspCenter`）陈述，与 Margulis 半径无关。

显式前提只有 (U) = `Γ`、离散 / free / fundamental domain / covolume、`e`、`he`、`hmetric`
与 (P) = `hper`；它们由 G2（normalized universal cover）与 G3（free action + orientation）消去。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory

namespace DifferentialGeometry.Geometry.Hyperbolic

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Horospherical (Horizontal)

universe u

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

local notation "Q[" G "]" => MulAction.orbitRel.Quotient G (HUpper 3)
local notation "π[" G "]" => Quotient.mk (MulAction.orbitRel G (HUpper 3))

/-- HG03 条件 producer（thick–thin 分解 `D` 显式）：`D` 的每个 cusp center 的周边稳定子
共轭到 ∞ 后恰为满秩平移格时，donor 的 horoball-cylinder 构造给出 `HyperbolicTruncation H`
（cusp 深度取 `R ≡ 1`）。 -/
theorem exists_truncation_of_thick_thin_HG03 (H : FiniteVolumeHyperbolicModel.{u})
    {Γ : Subgroup (PO 3 1)} [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper 3)] {r : ℝ}
    (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r)
    (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ π[Γ]) p)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (hper : ∀ ξ : D.centers, ∃ a : PO 3 1,
      (HyperbolicBoundary.poBoundaryMulAction (Nat.le_add_left 1 2)).smul a ξ.val =
        MobiusBoundary.ptInfty ∧
      ∃ (Λ : Submodule ℤ (Horizontal 2)) (hΛ : DiscreteTopology Λ),
        letI := hΛ
        IsZLattice ℝ Λ ∧
          (endStabilizer (Nat.le_add_left 1 2) Γ {ξ.val}).map (MulAut.conj a).toMonoidHom =
            TranslationLattices.latticeGroup Λ) :
    Nonempty (HyperbolicTruncation H) := by
  choose a ha Λ hΛd hΛ hP using hper
  obtain ⟨_, _, _, _, Tr, _⟩ :=
    D.exists_hyperbolicTruncation_of_translation_lattices H e he hmetric a ha Λ hP
      (fun _ => 1) (fun _ => one_pos)
  exact ⟨Tr⟩

/-- HG03 条件 producer（thick–thin 分解由 Margulis 产生）：离散、free、有限 covolume 的
`Γ ≤ PO 3 1` 给出 `H` 的 uniformization，且每个 parabolic 不动点的周边稳定子共轭后恰为
满秩平移格时，`HyperbolicTruncation H` 非空。 -/
theorem truncation_of_hypotheses_HG03 (H : FiniteVolumeHyperbolicModel.{u})
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
    Nonempty (HyperbolicTruncation H) := by
  have hΓ : IsDiscrete (SetLike.coe Γ) :=
    isDiscrete_iff_discreteTopology.mpr inferInstance
  obtain ⟨ε, hε, hgeom⟩ :=
    BoundaryStabilizer.exists_margulis_geometry_constant (Nat.le_add_left 1 2)
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := half_lt_self hε
  obtain ⟨D⟩ := CuspTruncation.exists_finite_cusp_truncation (Nat.le_add_left 1 2)
    (by norm_num) Γ hΓ hcov hr hrε (hgeom Γ hΓ)
  exact exists_truncation_of_thick_thin_HG03 H D e he hmetric fun ξ =>
    hper ξ.val (CuspCorrespondence.isCuspCenter_of_thinRegion (Nat.le_add_left 1 2)
      (by norm_num) Γ hΓ hcov hr hrε (hgeom Γ hΓ) (D.region_nonempty ξ))

/-- consumer：条件 producer 的截断接到 `endCount`（S-HG-INTAKE G1 的 `endCount_eq_count`）。 -/
example (H : FiniteVolumeHyperbolicModel.{u})
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
    ∃ Tr : HyperbolicTruncation H,
      DifferentialGeometry.Geometry.Topology.endCount H.Carrier = (Tr.count : ℕ∞) := by
  obtain ⟨Tr⟩ := truncation_of_hypotheses_HG03 H Γ hcov e he hmetric hper
  exact ⟨Tr, Tr.endCount_eq_count⟩

end DifferentialGeometry.Geometry.Hyperbolic
