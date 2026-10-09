import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Hyperbolic.HorosphericalCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Manifold
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Existence
import DifferentialGeometry.Geometry.Affine.Crystallographic.CocompactActions
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue

/-!
# HG03：orientation ⇒ 周边元素的水平线性部分 det > 0（O-HG-HG03 G3b，后缀 `_HG03`）

设计 §2 的 L2（orientation 半）。`e : QΓ ≃ₜ H.Carrier` 使 `p = e ∘ πΓ` 为 local diffeo，
`a δ a⁻¹`（δ ∈ Γ）在 horospherical 坐标作用为 `ofCoords x h ↦ ofCoords (f x) h`。令
`q := p ∘ (a⁻¹ • ·) ∘ Ψ`，`Ψ (x, s) = ofCoords x (exp s)`（donor `horosphericalLogDiffeomorph`），
则 `q` 是 `Horizontal 2 × ℝ → H.Carrier` 的 local diffeo 且 `q ∘ T = q`，`T (x, s) = (f x, s)`。
把 `H.orientation` 沿 `q` 拉回（`pullbackSmoothOrientation`），在连通的 `Horizontal 2 × ℝ` 上
为常值 c（`smoothOrientation_eq_of_eq_at`）；链式法则给 `map (dT) c = c`，即
`0 < det (A ⊕ 1) = det A`。这一步排除 glide reflection（Klein bottle cusp，blueprint MGL32）。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open Horospherical (Horizontal ofCoords)
open CrystallographicActions (affine_eq_linear_add)
open DifferentialGeometry.Topology.Manifold (smoothOrientationOfManifoldOrientation
  pullbackSmoothOrientation smoothOrientation_eq_of_eq_at euclideanSmoothOrientation
  tangentOrientationEquiv tangentOrientationEquiv_trans tangentOrientationEquiv_symm
  tangentOrientationEquiv_self differentialEquivOfBijective)

universe u

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

local notation "Q[" G "]" => MulAction.orbitRel.Quotient G (HUpper 3)
local notation "π[" G "]" => Quotient.mk (MulAction.orbitRel G (HUpper 3))

/-- `PO 3 1` 元素在 `HUpper 3` 上的作用是 diffeomorphism（donor `contMDiff_po_smul`）。 -/
private def poSmulDiffeomorph_HG03 (c : PO 3 1) : HUpper 3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ HUpper 3 where
  toFun := (HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul c
  invFun := (HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul c⁻¹
  left_inv y := by
    let _ : MulAction (PO 3 1) (HUpper 3) := HyperbolicAction.poMulAction (Nat.le_add_left 1 2)
    exact inv_smul_smul c y
  right_inv y := by
    let _ : MulAction (PO 3 1) (HUpper 3) := HyperbolicAction.poMulAction (Nat.le_add_left 1 2)
    exact smul_inv_smul c y
  contMDiff_toFun := HyperbolicAction.contMDiff_po_smul 2 ∞ c
  contMDiff_invFun := HyperbolicAction.contMDiff_po_smul 2 ∞ c⁻¹

/-- orientation 半：`H` 的 orientation 使每个 `a δ a⁻¹`（δ ∈ Γ，作用为水平仿射等距 `f`）的
线性部分 det > 0。 -/
theorem det_pos_of_orientation_HG03 (H : FiniteVolumeHyperbolicModel.{u})
    (Γ : Subgroup (PO 3 1)) (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]))
    (a δ : PO 3 1) (hδ : δ ∈ Γ) (f : Horizontal 2 ≃ᵃⁱ[ℝ] Horizontal 2)
    (hf : ∀ (x : Horizontal 2) (h : ℝ) (hh : 0 < h),
      (HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul (a * δ * a⁻¹)
        (ofCoords x h hh) = ofCoords (f x) h hh) :
    0 < LinearMap.det
      (f.linearIsometryEquiv.toLinearEquiv : Horizontal 2 →ₗ[ℝ] Horizontal 2) := by
  classical
  let _ : MulAction (PO 3 1) (HUpper 3) := HyperbolicAction.poMulAction (Nat.le_add_left 1 2)
  let Ψ : (Horizontal 2 × ℝ) ≃ₘ⟮𝓘(ℝ, Horizontal 2 × ℝ), 𝓡 3⟯ HUpper 3 :=
    (Hyperboloid.horosphericalLogDiffeomorph 2).symm.trans (Hyperboloid.hUpperDiffeomorph 3).symm
  have hΨ : ∀ (x : Horizontal 2) (s : ℝ), Ψ (x, s) = ofCoords x (Real.exp s) (Real.exp_pos s) :=
    fun x s => (Hyperboloid.hUpperDiffeomorph 3).symm_apply_apply _
  let q : Horizontal 2 × ℝ → H.Carrier := (e ∘ π[Γ]) ∘ (poSmulDiffeomorph_HG03 a⁻¹) ∘ Ψ
  have hq : IsLocalDiffeomorph 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) ∞ q :=
    isLocalDiffeomorph_comp he (isLocalDiffeomorph_comp
      (poSmulDiffeomorph_HG03 a⁻¹).isLocalDiffeomorph Ψ.isLocalDiffeomorph)
  have hqT : ∀ (x : Horizontal 2) (s : ℝ), q (f x, s) = q (x, s) := by
    intro x s
    change e (π[Γ] (a⁻¹ • Ψ (f x, s))) = e (π[Γ] (a⁻¹ • Ψ (x, s)))
    rw [hΨ, hΨ, ← hf x (Real.exp s) (Real.exp_pos s)]
    congr 1
    apply Quotient.sound
    refine ⟨⟨δ, hδ⟩, ?_⟩
    change δ • (a⁻¹ • ofCoords x (Real.exp s) (Real.exp_pos s)) =
      a⁻¹ • ((a * δ * a⁻¹) • ofCoords x (Real.exp s) (Real.exp_pos s))
    simp only [mul_smul, inv_smul_smul]
  have hqs : ContMDiff 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) ∞ q := hq.contMDiff
  have hbij : ∀ v, Function.Bijective (mfderiv 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) q v) := by
    intro v
    obtain ⟨L, hL⟩ := hq.isInvertible_mfderiv (by simp) v
    rw [← hL, ContinuousLinearEquiv.coe_coe]
    exact L.bijective
  -- 水平仿射映射 T 与它的（常值）导数
  let LinE : (Horizontal 2 × ℝ) ≃ₗ[ℝ] (Horizontal 2 × ℝ) :=
    f.linearIsometryEquiv.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)
  let Lin : (Horizontal 2 × ℝ) →L[ℝ] (Horizontal 2 × ℝ) :=
    (f.linearIsometryEquiv : Horizontal 2 →L[ℝ] Horizontal 2).prodMap
      (ContinuousLinearMap.id ℝ ℝ)
  let T : Horizontal 2 × ℝ → Horizontal 2 × ℝ := fun v => (f v.1, v.2)
  have hTeq : T = fun v => Lin v + (f 0, 0) := by
    funext v
    change (f v.1, v.2) = (f.linearIsometryEquiv v.1 + f 0, v.2 + 0)
    rw [affine_eq_linear_add f v.1, add_zero]
  have hT : ∀ v, HasMFDerivAt 𝓘(ℝ, Horizontal 2 × ℝ) 𝓘(ℝ, Horizontal 2 × ℝ) T v Lin := by
    intro v
    rw [hTeq]
    exact (Lin.hasFDerivAt.add_const _).hasMFDerivAt
  have hqTfun : q ∘ T = q := funext fun v => hqT v.1 v.2
  have hD : ∀ v, mfderiv 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) q v =
      (mfderiv 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) q (T v)).comp Lin := by
    intro v
    have hc := ((hq.mdifferentiable (by simp) (T v)).hasMFDerivAt).comp v (hT v)
    rw [hqTfun] at hc
    exact hc.mfderiv
  -- 拉回 orientation，并在连通的 `Horizontal 2 × ℝ` 上为常值
  let so := smoothOrientationOfManifoldOrientation (𝓡 3)
    (OrientationAssembly.reindexManifoldOrientation (𝓡 3)
      (finCongr H.orientation.dimension_eq.symm) H.orientation)
  let oq := pullbackSmoothOrientation 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) q hqs hbij so
  have hconst : ∀ v, oq.val v = oq.val 0 :=
    smoothOrientation_eq_of_eq_at 𝓘(ℝ, Horizontal 2 × ℝ) oq
      (euclideanSmoothOrientation (Horizontal 2 × ℝ) (oq.val 0)) 0 rfl
  let D := differentialEquivOfBijective 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) q hbij
  have hDv : ∀ v, tangentOrientationEquiv (D v).toLinearEquiv (oq.val v) = so.val (q v) := by
    intro v
    have h := tangentOrientationEquiv_symm (D v).symm.toLinearEquiv (so.val (q v))
    exact h
  have hsplit : (D 0).toLinearEquiv = LinE.trans (D (T 0)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro w
    change mfderiv 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) q 0 w =
      mfderiv 𝓘(ℝ, Horizontal 2 × ℝ) (𝓡 3) q (T 0) (Lin w)
    rw [hD 0]
    rfl
  have hmap : Orientation.map _ LinE (oq.val 0) = oq.val 0 := by
    have h1 := hDv 0
    rw [hsplit, tangentOrientationEquiv_trans] at h1
    have h2 := hDv (T 0)
    rw [show q (T 0) = q 0 from hqT _ _] at h2
    have h3 := (tangentOrientationEquiv (D (T 0)).toLinearEquiv).injective (h1.trans h2.symm)
    rw [tangentOrientationEquiv_self, hconst (T 0)] at h3
    exact h3
  have hdet := (Orientation.map_eq_iff_det_pos (oq.val 0) LinE (Fintype.card_fin _)).mp hmap
  have hLin : (LinE : (Horizontal 2 × ℝ) →ₗ[ℝ] (Horizontal 2 × ℝ)) =
      LinearMap.prodMap (f.linearIsometryEquiv.toLinearEquiv : Horizontal 2 →ₗ[ℝ] Horizontal 2)
        LinearMap.id := LinearMap.ext fun _ => rfl
  rw [hLin, LinearMap.det_prodMap, LinearMap.det_id, mul_one] at hdet
  exact hdet

end DifferentialGeometry.Geometry.Hyperbolic
