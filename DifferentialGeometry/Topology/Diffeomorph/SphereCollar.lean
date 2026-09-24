import DifferentialGeometry.Analysis.Calculus.BallBoundary
import DifferentialGeometry.Tensor.LinearAlgebra.HyperplaneInterpolation
import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Fiberwise
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Diffeomorph.CompactLocalIsotopy
import DifferentialGeometry.Topology.Homeomorph.LevelIsotopy
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

open Set Metric Filter
open scoped Topology RealInnerProductSpace ContDiff Manifold

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem hasFDerivAt_radial_extension {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasFDerivAt f L x) (hx : ‖x‖ = 1) :
    HasFDerivAt (fun y => ‖y‖ • f (‖y‖⁻¹ • y))
      ((innerSL ℝ x).smulRight (f x) +
        L.comp (ContinuousLinearMap.id ℝ E - (innerSL ℝ x).smulRight x)) x := by
  have hn : HasFDerivAt (fun y : E => ‖y‖) (innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by rw [hx]; norm_num)
    convert! h using 1
    · ext y
      simp only [Real.sqrt_sq (norm_nonneg y)]
    · ext v
      simp [hx, two_smul]
      ring
  have hni : HasFDerivAt (fun y : E => ‖y‖⁻¹)
      (-(innerSL ℝ x)) x := by
    convert! (hasDerivAt_inv (by rw [hx]; norm_num)).comp_hasFDerivAt x hn using 1
    rw [hx]
    simp
  have hnrm : HasFDerivAt (fun y : E => ‖y‖⁻¹ • y)
      (ContinuousLinearMap.id ℝ E - (innerSL ℝ x).smulRight x) x := by
    convert! hni.smul (hasFDerivAt_id x) using 1
    ext v
    simp [hx, sub_eq_add_neg]
  have hfx : HasFDerivAt f L (‖x‖⁻¹ • x) := by simpa only [hx, inv_one, one_smul] using hf
  convert! hn.smul (hfx.comp (f := fun y : E => ‖y‖⁻¹ • y) x hnrm) using 1
  simp [hx, add_comm]

theorem injective_fderiv_radial_interpolation
    (B : E ≃ₘ[ℝ] E) (hB : MapsTo B (closedBall 0 1) (closedBall 0 1))
    {x : E} (hx : ‖x‖ = 1) (hBx : ‖B x‖ = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Injective (fderiv ℝ (fun y => (1 - t) • B y + t • (‖y‖ • B (‖y‖⁻¹ • y))) x) := by
  let A := fderiv ℝ B x
  have hA : HasFDerivAt B A x := (B.contMDiff.contDiff.differentiable (by simp) x).hasFDerivAt
  have hAbij : Function.Bijective A :=
    DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph
      B.toPartialDiffeomorph (mem_univ x)
  let R : E →L[ℝ] E := (innerSL ℝ x).smulRight (B x) +
    A.comp (ContinuousLinearMap.id ℝ E - (innerSL ℝ x).smulRight x)
  have hR : HasFDerivAt (fun y => ‖y‖ • B (‖y‖⁻¹ • y)) R x :=
    hasFDerivAt_radial_extension hA hx
  have hd : HasFDerivAt (fun y => (1 - t) • B y + t • (‖y‖ • B (‖y‖⁻¹ • y)))
      ((1 - t) • A + t • R) x := by
    convert! (hA.const_smul (1 - t)).add (hR.const_smul t) using 1
  rw [hd.fderiv]
  obtain ⟨a, ha, hnormal⟩ := hA.exists_pos_inner_eq_mul_inner_of_mapsTo_closedBall
    hAbij.surjective zero_lt_one zero_lt_one (by simpa using hx) (by simpa using hBx) hB
  simp only [sub_zero] at hnormal
  have hRapply (v : E) : R v = ⟪x, v⟫ • B x + A (v - ⟪x, v⟫ • x) := rfl
  have hRnormal (v : E) : ⟪B x, R v⟫ = ⟪x, v⟫ := by
    rw [hRapply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
      hBx, hnormal, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hx]
    ring
  exact A.toLinearMap.injective_convex_combination_of_eqOn_ker R.toLinearMap
    (innerSL ℝ x).toLinearMap (innerSL ℝ (B x)).toLinearMap hAbij.injective
    (fun v hv => by
      change A v = R v
      change ⟪x, v⟫ = 0 at hv
      rw [hRapply, hv, zero_smul, zero_smul, sub_zero, zero_add])
    ha zero_lt_one (by ext v; exact hnormal v) (by ext v; simpa using hRnormal v) ht


theorem exists_contDiff_compact_isotopy_eqOn_radial_interpolation
    [FiniteDimensional ℝ E] (B : E ≃ₘ[ℝ] E)
    (hB : B '' closedBall 0 1 = closedBall 0 1) :
    ∃ V : Set E, IsOpen V ∧ sphere 0 1 ⊆ V ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ V,
          Φ t (B x) = (1 - t) • B x + t • (‖x‖ • B (‖x‖⁻¹ • x))) ∧
        ∃ S : Set E, IsCompact S ∧ ∀ t : ℝ,
          EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  classical
  by_cases hne : (sphere (0 : E) 1).Nonempty
  · have hBsphere : B '' sphere 0 1 = sphere 0 1 := by
      change B.toHomeomorph '' sphere 0 1 = sphere 0 1
      have hB' : B.toHomeomorph '' closedBall 0 1 = closedBall 0 1 := hB
      rw [← frontier_closedBall (0 : E) one_ne_zero, B.toHomeomorph.image_frontier, hB']
    have hBx (x : E) (hx : x ∈ sphere 0 1) : ‖B x‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (hBsphere.subset ⟨x, hx, rfl⟩)
    let F : ℝ × E → E := fun z => (1 - z.1) • B z.2 +
      z.1 • (‖z.2‖ • B (‖z.2‖⁻¹ • z.2))
    let U : Set (ℝ × E) := {z | z.2 ≠ 0}
    have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
    have hF : ContDiffOn ℝ ∞ F U := by
      have hn : ContDiffOn ℝ ∞ (fun z : ℝ × E => ‖z.2‖) U :=
        contDiff_snd.contDiffOn.norm ℝ (fun _ hz => hz)
      have hni := hn.inv (fun z hz => norm_ne_zero_iff.mpr hz)
      exact ((contDiff_const.sub contDiff_fst).contDiffOn.smul
        (B.contMDiff.contDiff.comp contDiff_snd).contDiffOn).add
          (contDiff_fst.contDiffOn.smul (hn.smul
            (B.contMDiff.contDiff.comp_contDiffOn (hni.smul contDiff_snd.contDiffOn))))
    let G : ℝ × E → ℝ × E := fun z => (z.1, F z)
    let K : Set (ℝ × E) := Icc (0 : ℝ) 1 ×ˢ sphere (0 : E) 1
    have hK : IsCompact K := isCompact_Icc.prod (isCompact_sphere 0 1)
    have hGcore (z : ℝ × E) (hz : z ∈ K) : G z = (z.1, B z.2) := by
      have hnorm := mem_sphere_zero_iff_norm.mp hz.2
      change (z.1, (1 - z.1) • B z.2 + z.1 • (‖z.2‖ • B (‖z.2‖⁻¹ • z.2))) = _
      rw [hnorm, inv_one, one_smul, one_smul, ← add_smul, sub_add_cancel, one_smul]
    have hGi : InjOn G K := by
      intro z hz w hw h
      rw [hGcore z hz, hGcore w hw] at h
      exact Prod.ext (Prod.mk.inj h).1 (B.injective (Prod.mk.inj h).2)
    have hGloc : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) ∞ G K := by
      intro z
      apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_prod_of_injective_fderiv
        hU hF
      · change z.val.2 ≠ 0
        exact norm_ne_zero_iff.mp ((mem_sphere_zero_iff_norm.mp z.property.2).trans_ne one_ne_zero)
      · exact B.injective_fderiv_radial_interpolation
          (fun x hx => hB.subset ⟨x, hx, rfl⟩)
          (mem_sphere_zero_iff_norm.mp z.property.2) (hBx z.val.2 z.property.2) z.property.1
    obtain ⟨φ, hφK, hφ⟩ :=
      DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
        hGloc hK ((nonempty_Icc.mpr zero_le_one).prod hne) hGi
    have hφfst : ∀ z ∈ φ.source, (φ z).1 = z.1 := by
      intro z _
      rw [hφ]
    obtain ⟨V, hV, hSV, _, Φ, hΦ, hΦinv, hΦ0, htrack, S, hS, _, hfix⟩ :=
      φ.exists_contDiff_compact_isotopy_eqOn_fibers hφfst (isCompact_sphere 0 1) hφK
        isOpen_univ (by simp)
    refine ⟨V, hV, hSV, Φ, hΦ, hΦinv, hΦ0, ?_, S, hS, hfix⟩
    intro t ht x hx
    have h := htrack t ht x hx
    change Φ t (φ.toFun (0, x)).2 = (φ.toFun (t, x)).2 at h
    rw [hφ] at h
    simpa only [G, F, sub_zero, one_smul, zero_smul, add_zero] using h
  · refine ⟨∅, isOpen_empty, (fun x hx => False.elim (hne ⟨x, hx⟩)),
      fun _ => Diffeomorph.refl 𝓘(ℝ, E) E ∞,
      contDiff_snd, contDiff_snd, rfl, ?_, ∅, isCompact_empty, ?_⟩
    · intro t ht x hx
      exact hx.elim
    · intro t
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

private theorem exists_contDiff_isotopy_radial_collar_unit
    [FiniteDimensional ℝ E] (B : E ≃ₘ[ℝ] E)
    (hB : B '' closedBall 0 1 = closedBall 0 1) :
    ∃ C : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => C z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (C z.1).symm z.2) ∧
      C 0 = B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, C t '' closedBall 0 1 = closedBall 0 1 ∧
        EqOn (C t) B (sphere 0 1)) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ x ∈ sphere (0 : E) 1,
        ∀ s ∈ Icc (1 - δ) (1 + δ), C 1 (s • x) = s • B x := by
  obtain ⟨V, hV, hSV, Φ, hΦ, hΦinv, hΦ0, htrack, _, _, _⟩ :=
    B.exists_contDiff_compact_isotopy_eqOn_radial_interpolation hB
  have hBsphere : B '' sphere 0 1 = sphere 0 1 := by
    change B.toHomeomorph '' sphere 0 1 = sphere 0 1
    have hB' : B.toHomeomorph '' closedBall 0 1 = closedBall 0 1 := hB
    rw [← frontier_closedBall (0 : E) one_ne_zero, B.toHomeomorph.image_frontier, hB']
  have hfix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (y : E) (hy : y ∈ sphere 0 1) : Φ t y = y := by
    obtain ⟨x, hx, rfl⟩ := hBsphere.symm.subset hy
    have hxnorm := mem_sphere_zero_iff_norm.mp hx
    have h := htrack t ht x (hSV hx)
    simpa only [hxnorm, inv_one, one_smul, ← add_smul, sub_add_cancel] using h
  have hΦball (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Φ t '' closedBall 0 1 = closedBall 0 1 := by
    have hlevel (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
        (Φ u).toHomeomorph '' {x : E | ‖x‖ = 1} = {x : E | ‖x‖ = 1} := by
      have hfix' : EqOn (Φ u).toHomeomorph id {x : E | ‖x‖ = 1} :=
        fun x hx => hfix u hu x (mem_sphere_zero_iff_norm.mpr hx)
      rw [hfix'.image_eq]
      exact image_id _
    change (Φ t).toHomeomorph '' closedBall 0 1 = closedBall 0 1
    simpa only [closedBall, dist_zero_right] using
      Homeomorph.image_sublevel_eq_of_image_level_eq (fun u => (Φ u).toHomeomorph)
        continuous_norm (fun x => (hΦ.continuous.comp
          (continuous_id.prodMk continuous_const)).continuousOn)
        (by rw [hΦ0]; rfl) hlevel t ht
  obtain ⟨ε, hε, hεV⟩ := (isCompact_sphere (0 : E) 1).exists_cthickening_subset_open hV hSV
  let δ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  refine ⟨fun t => B.trans (Φ t),
    hΦ.comp (contDiff_fst.prodMk (B.contMDiff.contDiff.comp contDiff_snd)),
    B.symm.contMDiff.contDiff.comp hΦinv, ?_, ?_, δ, hδ, min_le_right _ _, ?_⟩
  · change B.trans (Φ 0) = B
    rw [hΦ0]
    ext x
    rfl
  · intro t ht
    refine ⟨?_, ?_⟩
    · change (fun x => Φ t (B x)) '' closedBall 0 1 = closedBall 0 1
      rw [← image_image, hB, hΦball t ht]
    · intro x hx
      exact hfix t ht (B x) (hBsphere.subset ⟨x, hx, rfl⟩)
  · intro x hx s hs
    have hspos : 0 < s := by have := min_le_right ε (1 / 2 : ℝ); dsimp [δ] at hs; linarith [hs.1]
    have hxnorm := mem_sphere_zero_iff_norm.mp hx
    have hsV : s • x ∈ V := by
      apply hεV
      apply mem_cthickening_of_dist_le (s • x) x ε (sphere (0 : E) 1) hx
      rw [dist_eq_norm, show s • x - x = (s - 1) • x by rw [sub_smul, one_smul],
        norm_smul, Real.norm_eq_abs, hxnorm, mul_one]
      exact abs_le.mpr ⟨by have := min_le_left ε (1 / 2 : ℝ); dsimp [δ] at hs; linarith [hs.1],
        by have := min_le_left ε (1 / 2 : ℝ); dsimp [δ] at hs; linarith [hs.2]⟩
    have hn : ‖s • x‖ = s := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hxnorm, mul_one]
    have heq := htrack 1 ⟨zero_le_one, le_rfl⟩ (s • x) hsV
    change Φ 1 (B (s • x)) = _
    simpa only [sub_self, zero_smul, one_smul, zero_add, hn, smul_smul,
      inv_mul_cancel₀ hspos.ne', one_mul] using heq

theorem exists_contDiff_isotopy_radial_collar_of_image_closedBall_eq
    [FiniteDimensional ℝ E] (B : E ≃ₘ[ℝ] E) (c : E) {r : ℝ} (hr : 0 < r)
    (hB : B '' closedBall c r = closedBall c r) :
    ∃ C : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => C z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (C z.1).symm z.2) ∧
      C 0 = B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, C t '' closedBall c r = closedBall c r ∧
        EqOn (C t) B (sphere c r)) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ x ∈ sphere c r,
        ∀ s ∈ Icc (1 - δ) (1 + δ),
          C 1 (c + s • (x - c)) = c + s • (B x - c) ∧
          (C 1).symm (c + s • (x - c)) = c + s • (B.symm x - c) := by
  let S : E ≃ₘ[ℝ] E :=
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 r hr.ne')).toDiffeomorph |>.trans
      (DifferentialGeometry.Topology.translateDiffeomorph c)
  have hS (x : E) : S x = r • x + c := rfl
  have hSi (x : E) : S.symm x = r⁻¹ • (x - c) := by
    change r⁻¹ • (x + -c) = _
    rw [sub_eq_add_neg]
  have hSball : S '' closedBall 0 1 = closedBall c r := by
    change (fun x : E => r • x + c) '' closedBall 0 1 = _
    calc
      _ = (fun x : E => x + c) '' ((fun x : E => r • x) '' closedBall 0 1) := by
        rw [image_image]
      _ = closedBall c r := by
        rw [image_smul, smul_unitClosedBall_of_nonneg hr.le]
        simp
  have hSiball : S.symm '' closedBall c r = closedBall 0 1 := by
    rw [← hSball, image_image]
    simp
  let D := S.trans (B.trans S.symm)
  have hD : D '' closedBall 0 1 = closedBall 0 1 := by
    change (fun x => S.symm (B (S x))) '' closedBall 0 1 = _
    calc
      _ = S.symm '' (B '' (S '' closedBall 0 1)) := by rw [image_image, image_image]
      _ = closedBall 0 1 := by rw [hSball, hB, hSiball]
  obtain ⟨C₀, hC₀smooth, hC₀inv, hC₀zero, hC₀, δ, hδ, hδ₂, heq⟩ :=
    exists_contDiff_isotopy_radial_collar_unit D hD
  let C : ℝ → (E ≃ₘ[ℝ] E) := fun t => S.symm.trans ((C₀ t).trans S)
  have hCsmooth : ContDiff ℝ ∞ (fun z : ℝ × E => C z.1 z.2) :=
    S.contMDiff.contDiff.comp (hC₀smooth.comp
      (contDiff_fst.prodMk (S.symm.contMDiff.contDiff.comp contDiff_snd)))
  have hCinv : ContDiff ℝ ∞ (fun z : ℝ × E => (C z.1).symm z.2) :=
    S.contMDiff.contDiff.comp (hC₀inv.comp
      (contDiff_fst.prodMk (S.symm.contMDiff.contDiff.comp contDiff_snd)))
  have hCzero : C 0 = B := by
    ext x
    change S (C₀ 0 (S.symm x)) = B x
    rw [hC₀zero]
    change S (S.symm (B (S (S.symm x)))) = B x
    rw [S.apply_symm_apply, S.apply_symm_apply]
  have hunit (x : E) (hx : x ∈ sphere c r) : S.symm x ∈ sphere (0 : E) 1 := by
    have hxnorm : ‖x - c‖ = r := by simpa [dist_eq_norm] using hx
    rw [mem_sphere_zero_iff_norm, hSi, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), hxnorm, inv_mul_cancel₀ hr.ne']
  have hC (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      C t '' closedBall c r = closedBall c r ∧ EqOn (C t) B (sphere c r) := by
    refine ⟨?_, ?_⟩
    · change (fun x => S (C₀ t (S.symm x))) '' closedBall c r = _
      calc
        _ = S '' (C₀ t '' (S.symm '' closedBall c r)) := by rw [image_image, image_image]
        _ = closedBall c r := by rw [hSiball, (hC₀ t ht).1, hSball]
    · intro x hx
      change S (C₀ t (S.symm x)) = B x
      rw [(hC₀ t ht).2 (hunit x hx)]
      change S (S.symm (B (S (S.symm x)))) = B x
      rw [S.apply_symm_apply, S.apply_symm_apply]
  have hforward (x : E) (hx : x ∈ sphere c r) (s : ℝ)
      (hs : s ∈ Icc (1 - δ) (1 + δ)) :
      C 1 (c + s • (x - c)) = c + s • (B x - c) := by
    have hSiarg : S.symm (c + s • (x - c)) = s • S.symm x := by
      rw [hSi, hSi, add_sub_cancel_left, smul_comm]
    change S (C₀ 1 (S.symm (c + s • (x - c)))) = _
    rw [hSiarg, heq (S.symm x) (hunit x hx) s hs]
    change S (s • S.symm (B (S (S.symm x)))) = _
    rw [S.apply_symm_apply, hS, hSi, smul_comm r s, smul_smul, smul_smul, mul_assoc,
      mul_inv_cancel₀ hr.ne', mul_one, add_comm]
  have hBsphere : B '' sphere c r = sphere c r := by
    change B.toHomeomorph '' sphere c r = sphere c r
    have hB' : B.toHomeomorph '' closedBall c r = closedBall c r := hB
    rw [← frontier_closedBall c hr.ne', B.toHomeomorph.image_frontier, hB']
  refine ⟨C, hCsmooth, hCinv, hCzero, hC, δ, hδ, hδ₂, fun x hx s hs => ⟨hforward x hx s hs, ?_⟩⟩
  have hxi : B.symm x ∈ sphere c r := by
    obtain ⟨y, hy, hyx⟩ := hBsphere.symm.subset hx
    simpa only [← hyx, B.symm_apply_apply] using hy
  apply (C 1).injective
  change C 1 ((C 1).symm (c + s • (x - c))) = C 1 (c + s • (B.symm x - c))
  rw [(C 1).apply_symm_apply, hforward (B.symm x) hxi s hs, B.apply_symm_apply]

theorem exists_diffeomorph_radial_collar_of_image_closedBall_eq
    [FiniteDimensional ℝ E] (B : E ≃ₘ[ℝ] E) (c : E) {r : ℝ} (hr : 0 < r)
    (hB : B '' closedBall c r = closedBall c r) :
    ∃ C : E ≃ₘ[ℝ] E, C '' closedBall c r = closedBall c r ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ x ∈ sphere c r,
        ∀ s ∈ Icc (1 - δ) (1 + δ),
          C (c + s • (x - c)) = c + s • (B x - c) ∧
          C.symm (c + s • (x - c)) = c + s • (B.symm x - c) := by
  obtain ⟨C, _, _, _, hC, δ, hδ, hδ₂, heq⟩ :=
    B.exists_contDiff_isotopy_radial_collar_of_image_closedBall_eq c hr hB
  exact ⟨C 1, (hC 1 ⟨zero_le_one, le_rfl⟩).1, δ, hδ, hδ₂, heq⟩

end Diffeomorph
