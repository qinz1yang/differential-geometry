/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalDiffeomorphStraightening
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.External.Schoenflies.Plane

open Set Metric Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

theorem exists_openPartialHomeomorph_of_continuousOn_injOn {U : Set Plane} (hU : IsOpen U)
    {f : Plane → Plane} (hf : ContinuousOn f U) (hinj : InjOn f U) :
    ∃ κ : OpenPartialHomeomorph Plane Plane, κ.source = U ∧ EqOn κ f U := by
  classical
  let e₀ := hinj.toPartialEquiv f U
  have hopen : IsOpenMap (U.domRestrict f) := by
    intro W hW
    have hW' : IsOpen (Subtype.val '' W) := hU.isOpenMap_subtype_val W hW
    have hWU : Subtype.val '' W ⊆ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have himage : U.domRestrict f '' W = f '' (Subtype.val '' W) := by
      rw [← image_comp]
      rfl
    rw [himage]
    exact DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hW' (hf.mono hWU)
      (hinj.mono hWU)
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict e₀ hf hopen hU, rfl, fun _ _ => rfl⟩

theorem det_eq_planeDet (A : Plane →L[ℝ] Plane) :
    LinearMap.det (A : Plane →ₗ[ℝ] Plane) =
      Schoenflies.Plane.det (A (EuclideanSpace.single 0 1)) (A (EuclideanSpace.single 1 1)) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, Schoenflies.Plane.det]
  ring

theorem exists_diffeomorph_affine_near {e : Plane → Plane} {V : Set Plane} (hV : IsOpen V)
    (he : ContDiffOn ℝ ∞ e V) (hinv : ∀ x ∈ V, (fderiv ℝ e x).IsInvertible) {p : Plane}
    (hp : p ∈ V) {N : Set Plane} (hN : IsOpen N) (hpN : e p ∈ N) :
    ∃ J : Diffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane Plane ∞, ∃ K : Set Plane,
      IsCompact K ∧ K ⊆ N ∧ (∀ y, y ∉ K → J y = y ∧ J.symm y = y) ∧
      ∃ r > 0, ∀ x ∈ ball p r, J.symm (e x) = e p + fderiv ℝ e p (x - p) := by
  let f : Plane → Plane := fun x => e (x + p)
  let U : Set Plane := (fun x => x + p) ⁻¹' V
  have hU : IsOpen U := hV.preimage (continuous_id.add continuous_const)
  have h0U : (0 : Plane) ∈ U := by
    change 0 + p ∈ V
    rwa [zero_add]
  have hfd : ∀ y ∈ U, HasFDerivAt f (fderiv ℝ e (y + p)) y := by
    intro y hy
    have hd : DifferentiableAt ℝ e (y + p) :=
      ((he.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp))
    have h2 := hd.hasFDerivAt.comp y ((hasFDerivAt_id y).add_const p)
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hfs : ContDiffOn ℝ ∞ f U :=
    he.comp (contDiff_id.add contDiff_const).contDiffOn (fun y hy => hy)
  have hfm : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ f U := contMDiffOn_iff_contDiffOn.mpr hfs
  have hinvf : ∀ y ∈ U, (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) y f)
      (extChartAt 𝓘(ℝ, Plane) y y)).IsInvertible := by
    intro y hy
    rw [writtenInExtChartAt_model_space, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      id_eq, (hfd y hy).fderiv]
    exact hinv (y + p) hy
  obtain ⟨Φ, h0Φ, hΦU, hΦf⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty hU h0U hfm
      hinvf
  have hΦ0 : Φ 0 = e p := by
    rw [← hΦf h0Φ]
    change e (0 + p) = e p
    rw [zero_add]
  obtain ⟨A, hA, J, hJ, K, hK, hKN, hJfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_diffeomorph_straightening_partialDiffeomorph Φ
      h0Φ hN (by rw [hΦ0]; exact hpN)
  have hΦeq : (Φ : Plane → Plane) =ᶠ[𝓝 0] f :=
    Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds h0Φ) fun x hx => (hΦf hx).symm
  have hA' : (A : Plane →L[ℝ] Plane) = fderiv ℝ e p := by
    rw [hA, hΦeq.fderiv_eq, (hfd 0 h0U).fderiv, zero_add]
  have hev : ∀ᶠ x in 𝓝 (0 : Plane), J (A x + e p) = e (x + p) := by
    filter_upwards [hJ, hΦeq] with x hx hx'
    rw [← hΦ0, hx, hx']
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨J, K, hK, hKN, hJfix, r, hr, fun x hx => ?_⟩
  have hx' : x - p ∈ ball (0 : Plane) r := by
    rw [mem_ball, dist_zero_right, ← dist_eq_norm]
    exact mem_ball.mp hx
  have h := hball (x - p) hx'
  rw [sub_add_cancel] at h
  rw [← h, Diffeomorph.symm_apply_apply, ← hA', add_comm]
  rfl

end DifferentialGeometry.Topology.PlanarJordan
