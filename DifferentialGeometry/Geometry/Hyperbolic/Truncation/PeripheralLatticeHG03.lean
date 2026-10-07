import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Charts
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.HorosphericalGroups
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Correspondence
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-!
# HG03：周边稳定子恰为平移格（代数半，O-HG-HG03 G3a，后缀 `_HG03`）

设计 §2 的 L2。`Γ ≤ PO 3 1` 离散、free、有限 covolume，ξ 是 parabolic 不动点。donor 的
`exists_cobounded_chart` 给出把 ξ 送到 ∞ 的 `a`，共轭后的周边群 `P' = a·Stab_Γ(ξ)·a⁻¹` 在
horospherical 坐标作用为水平仿射等距 `x ↦ A x + b`（`affineAction`）。

* `linearIsometryEquiv_eq_one_of_fixed_HG03`：2 维正 det 线性等距（= rotation）有非零不动向量 ⇒ 恒等。
* `exists_fixed_of_linear_ne_one_HG03`：正 det 且线性部分 ≠ 1 的平面仿射等距有不动点。
* `peripheral_lattice_of_det_pos_HG03`：若每个共轭元素的线性部分 det > 0（orientation 半，G3b），
  free action 排除 rotation，线性部分全平凡 ⇒ `P' = latticeGroup (translationModule …)`，
  离散 / 满秩由 donor `translationModule_{discrete,full}`。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Geometry.Hyperbolic

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Horospherical (Horizontal ofCoords)
open CrystallographicActions (linearPart translationModule affine_eq_linear_add)

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

/-- 2 维：正 det 的线性等距若有非零不动向量则为恒等（mathlib：正 det ⇒ rotation）。 -/
theorem linearIsometryEquiv_eq_one_of_fixed_HG03 (A : Horizontal 2 ≃ₗᵢ[ℝ] Horizontal 2)
    (hA : 0 < LinearMap.det (A.toLinearEquiv : Horizontal 2 →ₗ[ℝ] Horizontal 2))
    {v : Horizontal 2} (hv : v ≠ 0) (hAv : A v = v) : A = 1 := by
  have : Fact (Module.finrank ℝ (Horizontal 2) = 2) := ⟨finrank_euclideanSpace_fin⟩
  let o : Orientation ℝ (Horizontal 2) (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  obtain ⟨θ, rfl⟩ := o.exists_linearIsometryEquiv_eq_of_det_pos hA
  have hθ : θ = 0 := ((o.rotation_eq_self_iff v θ).mp hAv).resolve_left hv
  subst hθ
  rw [o.rotation_zero]
  rfl

/-- 正 det、线性部分 ≠ 1 的平面仿射等距有不动点（`A − 1` 单 ⇒ 满）。 -/
theorem exists_fixed_of_linear_ne_one_HG03 (f : Horizontal 2 ≃ᵃⁱ[ℝ] Horizontal 2)
    (hdet : 0 < LinearMap.det
      (f.linearIsometryEquiv.toLinearEquiv : Horizontal 2 →ₗ[ℝ] Horizontal 2))
    (hne : f.linearIsometryEquiv ≠ 1) : ∃ x : Horizontal 2, f x = x := by
  let L : Horizontal 2 →ₗ[ℝ] Horizontal 2 :=
    (f.linearIsometryEquiv.toLinearEquiv : Horizontal 2 →ₗ[ℝ] Horizontal 2) - LinearMap.id
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    apply hne
    refine linearIsometryEquiv_eq_one_of_fixed_HG03 _ hdet hv0 ?_
    have h : f.linearIsometryEquiv v - v = 0 := hv
    exact sub_eq_zero.mp h
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hinj) (-f 0)
  refine ⟨x, ?_⟩
  have hx' : f.linearIsometryEquiv x - x = -f 0 := hx
  rw [affine_eq_linear_add f x]
  calc f.linearIsometryEquiv x + f 0 = (f.linearIsometryEquiv x - x) + x + f 0 := by abel
    _ = -f 0 + x + f 0 := by rw [hx']
    _ = x := by abel

/-- 周边格（代数半）：若共轭到 ∞ 的周边元素的水平线性部分 det > 0（由 orientation 给出，G3b），
则 free action 给出 `(endStabilizer Γ {ξ}).map (conj a) = latticeGroup Λ`，Λ 离散满秩。 -/
theorem peripheral_lattice_of_det_pos_HG03
    (Γ : Subgroup (PO 3 1)) [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper 3)]
    [hfd : HasFundamentalDomain Γ (PO 3 1)] (hcov : covolume Γ (PO 3 1) ≠ ⊤)
    (hdet : ∀ (a δ : PO 3 1), δ ∈ Γ → ∀ f : Horizontal 2 ≃ᵃⁱ[ℝ] Horizontal 2,
      (∀ (x : Horizontal 2) (h : ℝ) (hh : 0 < h),
        (HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul (a * δ * a⁻¹)
          (ofCoords x h hh) = ofCoords (f x) h hh) →
      0 < LinearMap.det
        (f.linearIsometryEquiv.toLinearEquiv : Horizontal 2 →ₗ[ℝ] Horizontal 2))
    (ξ : HyperbolicBoundary.BoundaryH 3)
    (hξ : CuspCorrespondence.IsCuspCenter (Nat.le_add_left 1 2) Γ ξ) :
    ∃ a : PO 3 1,
      (HyperbolicBoundary.poBoundaryMulAction (Nat.le_add_left 1 2)).smul a ξ =
        MobiusBoundary.ptInfty ∧
      ∃ (Λ : Submodule ℤ (Horizontal 2)) (hΛ : DiscreteTopology Λ),
        letI := hΛ
        IsZLattice ℝ Λ ∧
          (endStabilizer (Nat.le_add_left 1 2) Γ {ξ}).map (MulAut.conj a).toMonoidHom =
            TranslationLattices.latticeGroup Λ := by
  classical
  let _ : MulAction (PO 3 1) (HUpper 3) := HyperbolicAction.poMulAction (Nat.le_add_left 1 2)
  have hΓ : IsDiscrete (SetLike.coe Γ) := isDiscrete_iff_discreteTopology.mpr inferInstance
  obtain ⟨ε, hε, hgeom⟩ :=
    BoundaryStabilizer.exists_margulis_geometry_constant (Nat.le_add_left 1 2)
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := half_lt_self hε
  have hcgeom (x : HUpper 3) :=
    OrbifoldStrata.closedSmallSubgroup_geometry (Nat.le_add_left 1 2) Γ hrε x (hgeom Γ hΓ x)
  have hthin := hξ.thinRegion_nonempty hΓ hr hcgeom
  obtain ⟨a, ha, hfix, hco⟩ :=
    @CuspCharts.exists_cobounded_chart 2 (by norm_num) Γ hΓ hfd hcov _ _ hr hrε (hgeom Γ hΓ) ξ
      hthin
  let P' := (endStabilizer (Nat.le_add_left 1 2) Γ {ξ}).map (MulAut.conj a).toMonoidHom
  have hΓ' : IsDiscrete (SetLike.coe P') :=
    ProjectiveOrthogonalGroup.Lattices.isDiscrete_map_conj a (hΓ.mono inf_le_left)
  have hlin : ∀ γ : P', linearPart (HorosphereGroups.affineAction P' hfix γ) = 1 := by
    intro γ
    obtain ⟨δ, hδ, hγ⟩ := γ.property
    change a * δ * a⁻¹ = (γ : PO 3 1) at hγ
    have hδΓ : δ ∈ Γ := (Subgroup.mem_inf.mp hδ).1
    let f := HorosphereGroups.affineAction P' hfix γ
    have hspec : ∀ (x : Horizontal 2) (h : ℝ) (hh : 0 < h),
        (a * δ * a⁻¹) • ofCoords x h hh = ofCoords (f x) h hh := by
      intro x h hh
      rw [hγ]
      exact HorosphereGroups.affineAction_spec P' hfix γ x h hh
    by_contra hne
    obtain ⟨x, hx⟩ := exists_fixed_of_linear_ne_one_HG03 f (hdet a δ hδΓ f hspec) hne
    let q : HUpper 3 := a⁻¹ • ofCoords x 1 one_pos
    have hq : (⟨δ, hδΓ⟩ : Γ) • q = q := by
      change δ • (a⁻¹ • ofCoords x 1 one_pos) = a⁻¹ • ofCoords x 1 one_pos
      calc δ • (a⁻¹ • ofCoords x 1 one_pos)
          = a⁻¹ • ((a * δ * a⁻¹) • ofCoords x 1 one_pos) := by
            simp only [mul_smul, inv_smul_smul]
        _ = a⁻¹ • ofCoords x 1 one_pos := by rw [hspec, hx]
    have hδ1 : δ = 1 := congrArg Subtype.val (IsCancelSMul.eq_one_of_smul hq)
    have hγ1 : γ = 1 := by
      apply Subtype.ext
      rw [← hγ, hδ1, mul_one, mul_inv_cancel]
      rfl
    apply hne
    rw [hγ1, map_one, map_one]
  have hker : (linearPart.comp (HorosphereGroups.affineAction P' hfix)).ker = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    exact hlin γ
  have hmap := HorosphereGroups.translationKernel_map_eq_latticeGroup P' hfix
  rw [hker, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  have : DiscreteTopology (translationModule (HorosphereGroups.affineAction P' hfix)) :=
    HorosphereGroups.translationModule_discrete P' hfix hΓ'
  exact ⟨a, ha, _, inferInstance,
    HorosphereGroups.translationModule_full P' hfix hco
      (HorosphereGroups.virtuallyNilpotent_of_cobounded P' hfix hΓ' hco), hmap⟩

end DifferentialGeometry.Geometry.Hyperbolic
