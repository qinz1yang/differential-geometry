import DifferentialGeometry.Topology.Handle.SphereCapComplementIsotopy
import DifferentialGeometry.Topology.Manifold.SphereLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.SphereRadialChart
import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign
import DifferentialGeometry.Tensor.LinearAlgebra.BoundaryBlockDeterminant
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit

/-!
# Germs of the unit ball of `ℝ³`: sphere charts and the sign of the Jacobian

Chapter-14 assembly, item L1 (lane ASM-L1), group G2, second part. A germ `F` of a partial
diffeomorphism of `ℝ³` that maps the unit sphere to itself and the closed unit ball into itself
restricts to a sphere germ; this file provides

* `exists_partialDiffeomorph_sphereChartComp`: a disk chart `φ` of the sphere composed with `F` is
  again a disk chart (`ψ x = F (φ x)`); the same construction as the private lemma
  `PartialDiffeomorph.exists_partialDiffeomorph_sphere_chart_comp` of `BallPairExtension.lean`,
  stated publicly for the sphere of `ℝ³`;
* `det_stereoChart_comp_mul_pos`: if `F` has positive Jacobian, then any two disk charts `φ`, `ψ`
  related by `ψ = F ∘ φ` have the same orientation in every stereographic chart. Route: conjugate `F`
  by the radial stereographic chart `(r, y) ↦ r • c⁻¹ y` (`exists_smooth_radial_chart`); the conjugate
  preserves the level `r = 1` and the side `r ≤ 1`, so its differential is block triangular with a
  nonnegative normal entry (`det_pos_iff_horizontal_of_surjective`); the Jacobian of the radial chart
  has constant sign on its connected source (`det_fderiv_pos_iff_of_preconnected`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace DifferentialGeometry.Topology.Handle

local instance fact_finrank_three_ASML1S :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- A disk chart of the unit sphere of `ℝ³` composed with a sphere-preserving germ of `ℝ³`. -/
theorem exists_partialDiffeomorph_sphereChartComp
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3)) ∞)
    (φ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2))
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hboundary : MapsTo F (sphere 0 1 ∩ F.source) (sphere 0 1))
    (hne : (φ.source ∩ (fun x => (φ x : EuclideanSpace ℝ (Fin 3))) ⁻¹' F.source).Nonempty) :
    ∃ ψ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2))
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ψ.source = φ.source ∩ (fun x => (φ x : EuclideanSpace ℝ (Fin 3))) ⁻¹' F.source ∧
      ∀ x ∈ ψ.source, (ψ x : EuclideanSpace ℝ (Fin 3)) = F (φ x : EuclideanSpace ℝ (Fin 3)) := by
  let E := EuclideanSpace ℝ (Fin 2)
  let A := EuclideanSpace ℝ (Fin 3)
  let c : E → A := fun x => (φ x).val
  let U : Set E := φ.source ∩ c ⁻¹' F.source
  have hcoe := (isSmoothEmbedding_coe_sphere (E := A) (n := 2))
  have hc : ContDiffOn ℝ ∞ c φ.source :=
    (hcoe.contMDiff.comp_contMDiffOn φ.contMDiffOn).contDiffOn
  have hU : IsOpen U := hc.continuousOn.isOpen_inter_preimage φ.open_source F.open_source
  let f : E → A := F ∘ c
  have hf : ContDiffOn ℝ ∞ f U :=
    F.contMDiffOn.contDiffOn.comp (hc.mono inter_subset_left) (fun _ hx => hx.2)
  have hnorm (x : E) (hx : x ∈ U) : ‖f x‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (hboundary ⟨(φ x).property, hx.2⟩)
  have hcder (x : E) (hx : x ∈ U) : Function.Injective (fderiv ℝ c x) := by
    have hi : Function.Injective (mfderiv (𝓡 2) (𝓡 3) c x) := by
      change Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Subtype.val ∘ φ) x)
      rw [mfderiv_comp x (hcoe.contMDiff.mdifferentiableAt (by simp))
        ((φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds hx.1)).mdifferentiableAt (by simp))]
      exact ((hcoe.isImmersion.isImmersionAt (φ x)).mfderiv_injective (by simp)).comp
        ((φ.isLocalDiffeomorphAt _ _ _ hx.1).mfderivToContinuousLinearEquiv (by simp)).injective
    simp only [mfderiv_eq_fderiv, TangentSpace] at hi
    convert! hi using 1
  have hd (x : E) (hx : x ∈ U) : Function.Injective (fderiv ℝ f x) := by
    rw [show f = F ∘ c from rfl, fderiv_comp x
      ((F.contMDiffOn.contDiffOn.contDiffAt (F.open_source.mem_nhds hx.2)).differentiableAt
        (by simp))
      ((hc.contDiffAt (φ.open_source.mem_nhds hx.1)).differentiableAt (by simp))]
    exact (DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph F
      hx.2).injective.comp (hcder x hx)
  let g := DifferentialGeometry.Topology.Manifold.sphereDirection (φ 0) ∘ f
  have hg :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphOn_sphereDirection_comp_of_norm_eq_one
      (n := 2) (φ 0) hU hf hnorm hd (by simp [E])
  have heq (x : E) (hx : x ∈ U) : (g x : A) = f x := by
    change (DifferentialGeometry.Topology.Manifold.sphereDirection (φ 0) (f x) : A) = f x
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection (φ 0)
      (norm_ne_zero_iff.mp ((hnorm x hx).trans_ne one_ne_zero)), hnorm x hx, inv_one, one_smul]
  have hinj : InjOn g U := by
    intro x hx y hy hxy
    apply φ.injOn hx.1 hy.1
    apply Subtype.ext
    apply F.injOn hx.2 hy.2
    exact (heq x hx).symm.trans ((congrArg Subtype.val hxy).trans (heq y hy))
  obtain ⟨ψ, hψs, _, hψ⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hg hU hne hinj
  refine ⟨ψ, hψs, ?_⟩
  intro x hx
  change (ψ.toFun x).val = _
  rw [hψ]
  exact heq x (hψs ▸ hx)

/-- A one-sided maximum at the right end: if `f r ≤ f 1` for `r ≤ 1` near `1`, the derivative of
`f` at `1` is nonnegative. -/
theorem deriv_nonneg_of_le_on_left {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 1)
    (hmax : ∀ᶠ r in 𝓝 (1 : ℝ), r ≤ 1 → f r ≤ f 1) : 0 ≤ f' := by
  have hloc : IsLocalMaxOn f (Iic 1) 1 := by
    filter_upwards [nhdsWithin_le_nhds hmax, self_mem_nhdsWithin] with r hr hrI
    exact hr hrI
  have hcone : (-1 : ℝ) ∈ posTangentConeAt (Iic (1 : ℝ)) 1 := by
    apply mem_posTangentConeAt_of_segment_subset
    intro r hr
    have h := segment_subset_uIcc (1 : ℝ) (1 + -1) hr
    rw [Set.mem_uIcc] at h
    rw [mem_Iic]
    rcases h with h | h <;> linarith [h.1, h.2]
  have h := hloc.hasFDerivWithinAt_nonpos hf.hasFDerivAt.hasFDerivWithinAt hcone
  have h' : -f' ≤ 0 := by simpa using h
  linarith

/-- **Orientation of sphere germs.** Let `F` be a germ of `ℝ³` mapping the unit sphere to itself
and the closed unit ball into itself, with positive Jacobian at a sphere point `φ 0`. If two disk
charts satisfy `ψ = F ∘ φ` near `0`, they have the same orientation in the stereographic chart from
any point `p` missed by `φ 0` and `ψ 0`. -/
theorem det_stereoChart_comp_mul_pos (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3)) ∞)
    (hbd : MapsTo F (sphere 0 1 ∩ F.source) (sphere 0 1))
    (hside : MapsTo F (closedBall 0 1 ∩ F.source) (closedBall 0 1))
    (φ ψ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2))
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (h0φ : (0 : EuclideanSpace ℝ (Fin 2)) ∈ φ.source)
    (hφp : φ 0 ≠ p) (hψp : ψ 0 ≠ p) (hF : (φ 0 : EuclideanSpace ℝ (Fin 3)) ∈ F.source)
    (heq : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℝ (Fin 2)),
      (ψ x : EuclideanSpace ℝ (Fin 3)) = F (φ x : EuclideanSpace ℝ (Fin 3)))
    (hdet : 0 < (fderiv ℝ F (φ 0 : EuclideanSpace ℝ (Fin 3))).det) :
    0 < (fderiv ℝ (stereoChart p ∘ φ) 0).det * (fderiv ℝ (stereoChart p ∘ ψ) 0).det := by
  set c := stereoChart p with hc
  let E2 := EuclideanSpace ℝ (Fin 2)
  let E3 := EuclideanSpace ℝ (Fin 3)
  let P := ℝ × E2
  obtain ⟨Ξ, hΞs, hΞ, hΞt, hΞsymm⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_smooth_radial_chart (n := 2)
      c.toOpenPartialHomeomorph (stereoChart_target p) c.contMDiffOn_toFun c.contMDiffOn_invFun
  let ι : E3 ≃L[ℝ] P :=
    (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2).trans (ContinuousLinearEquiv.prodComm ℝ E2 ℝ)
  let X : PartialDiffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞ := Ξ.trans ι.toDiffeomorph.toPartialDiffeomorph
  let G' : PartialDiffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞ :=
    (ι.symm.toDiffeomorph.toPartialDiffeomorph.trans F).trans ι.toDiffeomorph.toPartialDiffeomorph
  have hX (q : P) : X q = ι (q.1 • (c.symm q.2 : E3)) := by
    change ι (Ξ q) = _
    rw [hΞ]
    rfl
  have hXsymm (z : P) : X.symm z = (‖ι.symm z‖,
      c (DifferentialGeometry.Topology.Manifold.sphereDirection (c.symm 0) (ι.symm z))) := by
    change Ξ.symm (ι.symm z) = _
    rw [hΞsymm]
    rfl
  have hG' (z : P) : G' z = ι (F (ι.symm z)) := rfl
  have hXsource : X.source = Ioi (0 : ℝ) ×ˢ univ := by
    change Ξ.source ∩ Ξ ⁻¹' univ = _
    rw [preimage_univ, inter_univ, hΞs]
  -- the base points
  have hφs : φ 0 ∈ c.source := by rw [hc, stereoChart_source]; exact hφp
  have hψs : ψ 0 ∈ c.source := by rw [hc, stereoChart_source]; exact hψp
  set y₀ : E2 := c (φ 0) with hy₀
  have hcy₀ : c.symm y₀ = φ 0 := c.toPartialEquiv.left_inv hφs
  let q₀ : P := (1, y₀)
  have hq₀ : q₀ ∈ X.source := by rw [hXsource]; exact ⟨by norm_num [q₀], mem_univ _⟩
  have hXq₀ : X q₀ = ι (φ 0 : E3) := by
    rw [hX]
    simp only [q₀, one_smul, hcy₀]
  have hψF : (ψ 0 : E3) = F (φ 0 : E3) := heq.self_of_nhds
  have hG'q : G' (X q₀) = ι (ψ 0 : E3) := by
    rw [hG', hXq₀, ContinuousLinearEquiv.symm_apply_apply, hψF]
  have hXq₀G : X q₀ ∈ G'.source := by
    refine ⟨⟨mem_univ _, ?_⟩, mem_univ _⟩
    change ι.symm (X q₀) ∈ F.source
    rw [hXq₀, ContinuousLinearEquiv.symm_apply_apply]
    exact hF
  have hψ0 : (ψ 0 : E3) ≠ 0 := ne_zero_of_mem_unit_sphere (ψ 0)
  have hdirψ : DifferentialGeometry.Topology.Manifold.sphereDirection (c.symm 0) (ψ 0 : E3) =
      ψ 0 := by
    apply Subtype.ext
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hψ0,
      norm_eq_of_mem_sphere (ψ 0), inv_one, one_smul]
  have hG'tgt : G' (X q₀) ∈ X.target := by
    refine ⟨mem_univ _, ?_⟩
    change ι.symm (G' (X q₀)) ∈ Ξ.target
    rw [hG'q, ContinuousLinearEquiv.symm_apply_apply, hΞt]
    refine ⟨hψ0, ?_⟩
    change DifferentialGeometry.Topology.Manifold.sphereDirection (c.symm 0) (ψ 0 : E3) ∈
      c.source
    rw [hdirψ]
    exact hψs
  set q₂ := X.symm (G' (X q₀)) with hq₂def
  have hq₂ : q₂ ∈ X.source := X.map_target hG'tgt
  have hXq₂ : X q₂ = G' (X q₀) := X.right_inv hG'tgt
  -- derivatives
  have hdiffX (q : P) (hq : q ∈ X.source) : HasFDerivAt X (fderiv ℝ X q) q :=
    ((X.contMDiffOn.contDiffOn.contDiffAt (X.open_source.mem_nhds hq)).differentiableAt
      (by simp)).hasFDerivAt
  have hdiffXs : HasFDerivAt X.symm (fderiv ℝ X.symm (G' (X q₀))) (G' (X q₀)) :=
    ((X.symm.contMDiffOn.contDiffOn.contDiffAt (X.open_target.mem_nhds hG'tgt)).differentiableAt
      (by simp)).hasFDerivAt
  have hdiffG : HasFDerivAt G' (fderiv ℝ G' (X q₀)) (X q₀) :=
    ((G'.contMDiffOn.contDiffOn.contDiffAt (G'.open_source.mem_nhds hXq₀G)).differentiableAt
      (by simp)).hasFDerivAt
  set A₁ := fderiv ℝ X q₀
  set A₂ := fderiv ℝ X q₂
  set B := fderiv ℝ X.symm (G' (X q₀))
  set D := fderiv ℝ G' (X q₀)
  set L : P →L[ℝ] P := B.comp (D.comp A₁) with hL
  let T : P → P := fun q => X.symm (G' (X q))
  have hT : HasFDerivAt T L q₀ := hdiffXs.comp q₀ (hdiffG.comp q₀ (hdiffX q₀ hq₀))
  -- `B` inverts `A₂`
  have hBA : B.comp A₂ = ContinuousLinearMap.id ℝ P := by
    have hcomp : HasFDerivAt (fun q => X.symm (X q)) (B.comp A₂) q₂ := by
      have h := hdiffXs
      rw [← hXq₂] at h
      exact h.comp q₂ (hdiffX q₂ hq₂)
    have hid : (fun q => X.symm (X q)) =ᶠ[𝓝 q₂] id := by
      filter_upwards [X.open_source.mem_nhds hq₂] with q hq
      exact X.left_inv hq
    exact hcomp.unique ((hasFDerivAt_id q₂).congr_of_eventuallyEq hid)
  have hdetBA : (B : P →ₗ[ℝ] P).det * (A₂ : P →ₗ[ℝ] P).det = 1 := by
    rw [← LinearMap.det_comp]
    change ((B.comp A₂ : P →L[ℝ] P) : P →ₗ[ℝ] P).det = 1
    rw [hBA]
    simp
  -- the Jacobian of `G'` is that of `F`
  have hdetD : (D : P →ₗ[ℝ] P).det = (fderiv ℝ F (φ 0 : E3)).det := by
    have hFd : HasFDerivAt F (fderiv ℝ F (φ 0 : E3)) (φ 0 : E3) :=
      ((F.contMDiffOn.contDiffOn.contDiffAt (F.open_source.mem_nhds hF)).differentiableAt
        (by simp)).hasFDerivAt
    have hcomp : HasFDerivAt (fun z : P => ι (F (ι.symm z)))
        ((ι : E3 →L[ℝ] P).comp ((fderiv ℝ F (φ 0 : E3)).comp (ι.symm : P →L[ℝ] E3))) (X q₀) := by
      have hFd' : HasFDerivAt F (fderiv ℝ F (φ 0 : E3)) (ι.symm (X q₀)) := by
        rw [hXq₀, ContinuousLinearEquiv.symm_apply_apply]
        exact hFd
      exact ι.hasFDerivAt.comp (X q₀) (hFd'.comp (X q₀) ι.symm.hasFDerivAt)
    have hDeq : D = (ι : E3 →L[ℝ] P).comp ((fderiv ℝ F (φ 0 : E3)).comp (ι.symm : P →L[ℝ] E3)) :=
      hdiffG.unique hcomp
    rw [hDeq]
    exact LinearMap.det_conj (fderiv ℝ F (φ 0 : E3) : E3 →ₗ[ℝ] E3) ι.toLinearEquiv
  -- constant sign of the radial chart's Jacobian
  have hconn : IsPreconnected X.source := by
    rw [hXsource]
    exact ((convex_Ioi (0 : ℝ)).prod convex_univ).isPreconnected
  have hsign := DifferentialGeometry.Analysis.det_fderiv_pos_iff_of_preconnected X hconn hq₀ hq₂
  have hA₁ne := DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph X hq₀
  have hA₂ne := DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph X hq₂
  have hdetL : 0 < (L : P →ₗ[ℝ] P).det := by
    have hLdet : (L : P →ₗ[ℝ] P).det =
        (B : P →ₗ[ℝ] P).det * ((D : P →ₗ[ℝ] P).det * (A₁ : P →ₗ[ℝ] P).det) := by
      rw [hL]
      change ((B : P →ₗ[ℝ] P) ∘ₗ ((D : P →ₗ[ℝ] P) ∘ₗ (A₁ : P →ₗ[ℝ] P))).det = _
      rw [LinearMap.det_comp, LinearMap.det_comp]
    rw [hLdet, hdetD]
    have hB : (B : P →ₗ[ℝ] P).det = ((A₂ : P →ₗ[ℝ] P).det)⁻¹ :=
      eq_inv_of_mul_eq_one_left hdetBA
    rw [hB]
    rcases lt_or_gt_of_ne hA₁ne with h1 | h1
    · have h2 : (A₂ : P →ₗ[ℝ] P).det < 0 := by
        by_contra h2
        have h2' : 0 < (A₂ : P →ₗ[ℝ] P).det := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hA₂ne)
        exact absurd (hsign.mpr h2') (not_lt.mpr h1.le)
      have := mul_pos hdet (mul_pos_of_neg_of_neg h1 (inv_lt_zero.mpr h2))
      nlinarith [this]
    · have h2 : 0 < (A₂ : P →ₗ[ℝ] P).det := hsign.mp h1
      have := mul_pos (inv_pos.mpr h2) (mul_pos hdet h1)
      linarith
  -- the formula of `T`
  have hTq (q : P) : T q = (‖F (q.1 • (c.symm q.2 : E3))‖,
      c (DifferentialGeometry.Topology.Manifold.sphereDirection (c.symm 0)
        (F (q.1 • (c.symm q.2 : E3))))) := by
    simp only [T, hXsymm, hG', hX, ContinuousLinearEquiv.symm_apply_apply]
  have hcs : Continuous (fun y : E2 => (c.symm y : E3)) := by
    have h : ContinuousOn c.symm c.target := c.contMDiffOn_invFun.continuousOn
    rw [hc, stereoChart_target] at h
    exact continuous_subtype_val.comp (continuousOn_univ.mp h)
  have hdir (z : E3) (hz : ‖z‖ = 1) :
      ((DifferentialGeometry.Topology.Manifold.sphereDirection (c.symm 0) z : _) : E3) = z := by
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection _
      (norm_ne_zero_iff.mp (hz.trans_ne one_ne_zero)), hz, inv_one, one_smul]
  -- the level `r = 1` is preserved near `y₀`
  have hnear : ∀ᶠ y in 𝓝 y₀, (c.symm y : E3) ∈ F.source :=
    hcs.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds (by rw [hcy₀]; exact hF))
  let Lr : E2 →L[ℝ] P := L.comp ((0 : E2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E2))
  have hTr : HasFDerivAt (fun y : E2 => T (1, y)) Lr y₀ := by
    have hin : HasFDerivAt (fun y : E2 => ((1 : ℝ), y))
        ((0 : E2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E2)) y₀ :=
      (hasFDerivAt_const (1 : ℝ) y₀).prodMk (hasFDerivAt_id y₀)
    exact hT.comp y₀ hin
  have hfst : (ContinuousLinearMap.fst ℝ ℝ E2).comp Lr = 0 := by
    have h1 : HasFDerivAt (fun y : E2 => (T (1, y)).1)
        ((ContinuousLinearMap.fst ℝ ℝ E2).comp Lr) y₀ := hasFDerivAt_fst.comp y₀ hTr
    have hconst : (fun y : E2 => (T (1, y)).1) =ᶠ[𝓝 y₀] fun _ => (1 : ℝ) := by
      filter_upwards [hnear] with y hy
      rw [hTq]
      change ‖F ((1 : ℝ) • (c.symm y : E3))‖ = 1
      rw [one_smul]
      exact mem_sphere_zero_iff_norm.mp (hbd ⟨(c.symm y).2, hy⟩)
    exact h1.unique ((hasFDerivAt_const (1 : ℝ) y₀).congr_of_eventuallyEq hconst)
  let A : E2 →L[ℝ] E2 := (ContinuousLinearMap.snd ℝ ℝ E2).comp Lr
  have hLA (v : E2) : L (0, v) = (0, A v) := by
    have h0 : Lr v = L (0, v) := by
      change L ((0 : E2 →L[ℝ] ℝ) v, v) = L (0, v)
      rfl
    refine Prod.ext ?_ rfl
    · change (L (0, v)).1 = 0
      have h := congrArg (fun M : E2 →L[ℝ] ℝ => M v) hfst
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        zero_apply] at h
      rw [← h0]
      exact h
  have hG : HasFDerivAt (fun y : E2 => (T (1, y)).2) A y₀ := hasFDerivAt_snd.comp y₀ hTr
  -- the normal entry is nonnegative
  have hn : 0 ≤ (L (1, 0)).1 := by
    let f : ℝ → ℝ := fun r => (T (r, y₀)).1
    have hfd : HasDerivAt f (L (1, 0)).1 1 := by
      have hin : HasFDerivAt (fun r : ℝ => (r, y₀))
          ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] E2)) 1 :=
        (hasFDerivAt_id (1 : ℝ)).prodMk (hasFDerivAt_const y₀ 1)
      have h := (hasFDerivAt_fst.comp (1 : ℝ) (hT.comp (1 : ℝ) hin)).hasDerivAt
      exact h
    have hf1 : f 1 = 1 := by
      change (T q₀).1 = 1
      rw [hTq]
      change ‖F ((1 : ℝ) • (c.symm y₀ : E3))‖ = 1
      rw [one_smul, hcy₀]
      exact mem_sphere_zero_iff_norm.mp (hbd ⟨(φ 0).2, hF⟩)
    have hcont : Continuous (fun r : ℝ => r • (φ 0 : E3)) := continuous_id.smul continuous_const
    have hev : ∀ᶠ r in 𝓝 (1 : ℝ), r • (φ 0 : E3) ∈ F.source :=
      hcont.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds (by rw [one_smul]; exact hF))
    have hpos : ∀ᶠ r in 𝓝 (1 : ℝ), 0 < r := lt_mem_nhds (by norm_num)
    refine deriv_nonneg_of_le_on_left hfd ?_
    filter_upwards [hev, hpos] with r hr hr0 hr1
    rw [hf1]
    change (T (r, y₀)).1 ≤ 1
    rw [hTq]
    change ‖F (r • (c.symm y₀ : E3))‖ ≤ 1
    rw [hcy₀]
    have hball : r • (φ 0 : E3) ∈ closedBall (0 : E3) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere (φ 0), mul_one,
        Real.norm_eq_abs, abs_of_pos hr0]
      exact hr1
    exact mem_closedBall_zero_iff.mp (hside ⟨hball, hr⟩)
  -- surjectivity of `L`
  have hLs : Function.Surjective L := by
    have hA₁b := DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph X hq₀
    have hDb := DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph G' hXq₀G
    have hBb := DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph X.symm
      hG'tgt
    exact hBb.2.comp (hDb.2.comp hA₁b.2)
  have hAdet : 0 < (A : E2 →ₗ[ℝ] E2).det :=
    (DifferentialGeometry.Analysis.det_pos_iff_horizontal_of_surjective (L : P →ₗ[ℝ] P)
      (A : E2 →ₗ[ℝ] E2) hLA hLs hn).mp hdetL
  -- the two disk charts
  have hφc : (0 : E2) ∈ (φ.trans c).source := ⟨h0φ, hφs⟩
  have hφd : HasFDerivAt (c ∘ φ) (fderiv ℝ (c ∘ φ) 0) 0 :=
    (((φ.trans c).contMDiffOn.contDiffOn.contDiffAt
      ((φ.trans c).open_source.mem_nhds hφc)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasFDerivAt ((fun y : E2 => (T (1, y)).2) ∘ (c ∘ φ))
      (A.comp (fderiv ℝ (c ∘ φ) 0)) 0 :=
    hG.comp (0 : E2) hφd
  have hψeq : (c ∘ ψ) =ᶠ[𝓝 (0 : E2)] ((fun y : E2 => (T (1, y)).2) ∘ (c ∘ φ)) := by
    have hopenφ : ∀ᶠ x in 𝓝 (0 : E2), x ∈ (φ.trans c).source :=
      (φ.trans c).open_source.mem_nhds hφc
    filter_upwards [hopenφ, heq] with x hx hxeq
    have hxs : φ x ∈ c.source := hx.2
    change c (ψ x) = (T (1, c (φ x))).2
    rw [hTq]
    change c (ψ x) = c (DifferentialGeometry.Topology.Manifold.sphereDirection (c.symm 0)
      (F ((1 : ℝ) • (c.symm (c (φ x)) : E3))))
    rw [one_smul, show (c.symm.toPartialEquiv : _ → _) = c.toPartialEquiv.symm from rfl,
      c.toPartialEquiv.left_inv hxs, ← hxeq]
    congr 1
    apply Subtype.ext
    exact (hdir (ψ x : E3) (norm_eq_of_mem_sphere (ψ x))).symm
  have hψd : fderiv ℝ (c ∘ ψ) 0 = A.comp (fderiv ℝ (c ∘ φ) 0) :=
    (hcomp.congr_of_eventuallyEq hψeq).fderiv
  have hφne := DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph
    (φ.trans c) hφc
  change 0 < ((fderiv ℝ (c ∘ φ) 0 : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2).det *
    ((fderiv ℝ (c ∘ ψ) 0 : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2).det
  rw [hψd]
  change 0 < ((fderiv ℝ (c ∘ φ) 0 : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2).det *
    ((A : E2 →ₗ[ℝ] E2) ∘ₗ ((fderiv ℝ (c ∘ φ) 0 : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2)).det
  rw [LinearMap.det_comp]
  have hφne' : ((fderiv ℝ (c ∘ φ) 0 : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2).det ≠ 0 := hφne
  have hsq := pow_pos (abs_pos.mpr hφne') 2
  rw [sq_abs] at hsq
  nlinarith [hAdet, hsq]

end DifferentialGeometry.Topology.Handle
