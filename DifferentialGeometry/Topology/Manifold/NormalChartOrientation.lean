import DifferentialGeometry.Topology.Manifold.SmoothNormalAtlas
import DifferentialGeometry.Tensor.LinearAlgebra.BoundaryBlockDeterminant
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import Mathlib.Analysis.Calculus.Deriv.Comp

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem det_fderiv_pos_of_hasNormalSideFlipAt
    (e : OpenPartialHomeomorph (E × ℝ) (E × ℝ)) {x : E}
    (hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) 1 e (x, 0))
    (hfix : (fun y : E => e (y, 0)) =ᶠ[nhds x] fun y => (y, 0))
    (hside : HasNormalSideFlipAt e x false) : 0 < (fderiv ℝ e (x, 0)).det := by
  let A := fderiv ℝ e (x, 0)
  have he : HasFDerivAt e A (x, 0) :=
    (hloc.mdifferentiableAt one_ne_zero).differentiableAt.hasFDerivAt
  have hzero : HasFDerivAt (fun y : E => (y, (0 : ℝ)))
      (ContinuousLinearMap.inl ℝ E ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const 0 x)
  have hlin := ((he.comp x hzero).congr_of_eventuallyEq hfix.symm).unique hzero
  have hA (v : E) : A (v, 0) = (v, 0) :=
    congrArg (fun B : E →L[ℝ] E × ℝ => B v) hlin
  have hne := normalDeriv_ne_zero_of_isLocalDiffeomorphAt_of_eventuallyEq_zeroSection
    (I := 𝓘(ℝ, E)) e (by
      rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]) hfix
  have hpos := normalDeriv_pos_of_hasNormalSideFlipAt_of_ne_zero e
    (congrArg Prod.snd hfix.eq_of_nhds) hside hne
  have hc : HasFDerivAt (fun t : ℝ => (x, t))
      (ContinuousLinearMap.inr ℝ E ℝ) 0 :=
    (hasFDerivAt_const x 0).prodMk (hasFDerivAt_id 0)
  have hd : HasDerivAt (fun t : ℝ => (e (x, t)).2) (A (0, 1)).2 0 :=
    he.snd.comp_hasDerivAt 0 hc.hasDerivAt
  have hn : 0 < (A (0, 1)).2 := by
    change 0 < deriv (fun t : ℝ => (e (x, t)).2) 0 at hpos
    rwa [hd.deriv] at hpos
  let L := ContinuousLinearEquiv.prodComm ℝ E ℝ
  let B : ℝ × E →L[ℝ] ℝ × E := L.toContinuousLinearMap.comp (A.comp L.symm.toContinuousLinearMap)
  have hB (v : E) : B (0, v) = (0, v) := by
    change L (A (v, 0)) = (0, v)
    rw [hA]
    rfl
  have hdet : B.det = A.det := LinearMap.det_conj A.toLinearMap L.toLinearEquiv
  have hb := DifferentialGeometry.Analysis.det_eq_normal_mul_of_horizontal
    B.toLinearMap (LinearMap.id : E →ₗ[ℝ] E) hB
  change B.det = (A (0, 1)).2 * LinearMap.det (LinearMap.id : E →ₗ[ℝ] E) at hb
  rw [LinearMap.det_id, mul_one, hdet] at hb
  exact hb.symm ▸ hn

end DifferentialGeometry.Topology.OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.Manifold

theorem det_fderiv_mul_pos_of_hasNormalSideFlipAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F ≃L[ℝ] E × ℝ)
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞)
    (h₀ : (0 : F) ∈ φ₀.source) (h₁ : (0 : F) ∈ φ₁.source)
    (heq : (fun x : E => φ₀ (L.symm (x, 0))) =ᶠ[nhds 0]
      fun x => φ₁ (L.symm (x, 0)))
    (hside : HasNormalSideFlipAt
      ((((L.symm.toDiffeomorph.toPartialDiffeomorph.trans φ₀).trans φ₁.symm).trans
        L.toDiffeomorph.toPartialDiffeomorph).toOpenPartialHomeomorph) 0 false) :
    0 < (fderiv ℝ φ₀ 0).det * (fderiv ℝ φ₁ 0).det := by
  have heq0 : φ₀ 0 = φ₁ 0 := by
    simpa only [Prod.mk_zero_zero, map_zero] using heq.eq_of_nhds
  let T := φ₀.trans φ₁.symm
  let ψ := ((L.symm.toDiffeomorph.toPartialDiffeomorph.trans φ₀).trans φ₁.symm).trans
    L.toDiffeomorph.toPartialDiffeomorph
  have hT0 : (0 : F) ∈ T.source := by
    refine ⟨h₀, ?_⟩
    change φ₀ 0 ∈ φ₁.target
    rw [heq0]
    exact φ₁.map_source h₁
  have hψ0 : (0 : E × ℝ) ∈ ψ.source := by
    refine ⟨⟨⟨Set.mem_univ _, ?_⟩, ?_⟩, Set.mem_univ _⟩
    · change L.symm 0 ∈ φ₀.source
      simpa only [map_zero] using h₀
    · change φ₀ (L.symm 0) ∈ φ₁.target
      simpa only [map_zero, heq0] using φ₁.map_source h₁
  have hfix : (fun x : E => ψ.toOpenPartialHomeomorph (x, 0)) =ᶠ[nhds 0]
      fun x => (x, 0) := by
    have hc : Continuous (fun x : E => L.symm (x, (0 : ℝ))) :=
      L.symm.continuous.comp (continuous_id.prodMk continuous_const)
    have hs : ∀ᶠ x in nhds (0 : E), L.symm (x, (0 : ℝ)) ∈ φ₁.source :=
      hc.continuousAt.eventually_mem (φ₁.open_source.mem_nhds
        (by simpa only [Prod.mk_zero_zero, map_zero] using h₁))
    filter_upwards [heq, hs] with x hx hxs
    change L (φ₁.symm (φ₀ (L.symm (x, 0)))) = (x, 0)
    rw [hx, PartialDiffeomorph.symm_apply_apply φ₁ hxs, L.apply_symm_apply]
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) 1
      ψ.toOpenPartialHomeomorph (0, 0) :=
    (DifferentialGeometry.PartialDiffeomorph.ofLE ψ (by simp : (1 : ℕ∞ω) ≤ ∞)).isLocalDiffeomorphAt
      _ _ _ hψ0
  have hψpos := OpenPartialHomeomorph.det_fderiv_pos_of_hasNormalSideFlipAt
    ψ.toOpenPartialHomeomorph hlocal hfix hside
  have hTdiff : HasFDerivAt T (fderiv ℝ T 0) 0 :=
    ((T.contMDiffOn_toFun.contDiffOn.contDiffAt
      (T.open_source.mem_nhds hT0)).differentiableAt (by simp)).hasFDerivAt
  have hTdiff' : HasFDerivAt T (fderiv ℝ T 0) (L.symm 0) := by simpa using hTdiff
  have hψdiff := L.hasFDerivAt.comp (0 : E × ℝ)
    (hTdiff'.comp 0 L.symm.hasFDerivAt)
  have hψderiv : fderiv ℝ ψ.toOpenPartialHomeomorph 0 =
      L.toContinuousLinearMap.comp ((fderiv ℝ T 0).comp L.symm.toContinuousLinearMap) :=
    hψdiff.fderiv
  rw [show ((0 : E), (0 : ℝ)) = (0 : E × ℝ) from rfl, hψderiv] at hψpos
  have hconj :
      (L.toContinuousLinearMap.comp ((fderiv ℝ T 0).comp L.symm.toContinuousLinearMap)).det =
        (fderiv ℝ T 0).det :=
    LinearMap.det_conj (fderiv ℝ T 0).toLinearMap L.toLinearEquiv
  rw [hconj] at hψpos
  have hφ₀ := (φ₀.contMDiffOn_toFun.contDiffOn.contDiffAt
    (φ₀.open_source.mem_nhds h₀)).differentiableAt (by simp)
  have hφ₁i := (φ₁.symm.contMDiffOn_toFun.contDiffOn.contDiffAt
    (φ₁.open_target.mem_nhds (φ₁.map_source h₁))).differentiableAt (by simp)
  have hchain : (fderiv ℝ T 0).det =
      (fderiv ℝ φ₁.symm (φ₁ 0)).det * (fderiv ℝ φ₀ 0).det := by
    have hder := fderiv_comp 0 (heq0.symm ▸ hφ₁i) hφ₀
    change fderiv ℝ T 0 = _ at hder
    rw [hder, heq0]
    exact LinearMap.det_comp _ _
  have hinv : (fderiv ℝ φ₁.symm (φ₁ 0)).det * (fderiv ℝ φ₁ 0).det = 1 := by
    have h := DifferentialGeometry.Analysis.fderiv_symm_comp_fderiv_of_partialDiffeomorph φ₁ h₁
    have hd := congrArg (fun A : F →L[ℝ] F => A.det) h
    change LinearMap.det ((fderiv ℝ φ₁.symm (φ₁ 0)).toLinearMap.comp
      (fderiv ℝ φ₁ 0).toLinearMap) = LinearMap.det (LinearMap.id : F →ₗ[ℝ] F) at hd
    simpa only [LinearMap.det_comp, LinearMap.det_id] using hd
  have hne : (fderiv ℝ φ₁ 0).det ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hinv
    exact zero_ne_one hinv
  have hpos := mul_pos hψpos (sq_pos_of_ne_zero hne)
  rw [hchain] at hpos
  have halg : ((fderiv ℝ φ₁.symm (φ₁ 0)).det * (fderiv ℝ φ₀ 0).det) *
      (fderiv ℝ φ₁ 0).det ^ 2 =
      ((fderiv ℝ φ₁.symm (φ₁ 0)).det * (fderiv ℝ φ₁ 0).det) *
        ((fderiv ℝ φ₀ 0).det * (fderiv ℝ φ₁ 0).det) := by ring
  rwa [halg, hinv, one_mul] at hpos

end DifferentialGeometry.Topology.Manifold
