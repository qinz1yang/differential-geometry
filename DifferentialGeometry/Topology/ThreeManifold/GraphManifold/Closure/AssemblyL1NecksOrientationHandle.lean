import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksOrientation
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Chapter-14 assembly, item L1, T1′: the orientation of the two necks of a handle (E4)

Lane ASM-L1d (sub-statement E4 of T1′, frozen in `build-logs/scratch/ASM-L1e/Targets.lean`).

* `contMDiff_handleModelVal`, `bijective_mfderiv_handleModelVal`: the inclusion `D² × [0, 1] → ℝ² × ℝ`.
* `exists_handleLift`: a map into `ℝ² × ℝ` landing near `q` in `D² × [0, 1]` lifts near `q` to a
  map into the handle model, smooth at `q`.
* `hasFDerivAt_neckProduct`, `det_neckProductDeriv`: the product form
  `(z, τ) ↦ (A (P (‖z‖²) • z), endCoord b (T τ))` on the core and its determinant
  `P 0 ^ 2 * det A * (± T')`.
* `EdgeHandle.neckPreservesAt_iff_of_product`: one neck in product form (moved from `0` to the
  interior point `(0, δ / 2)` along its source, then read through the handle).
* **E4** `neckPreservesAt_iff_det_mul_neg`: the hypotheses `hP₀1`, `hP₁1`, `hP₀mono`, `hP₁mono` of
  the frozen statement are not needed and are dropped; the frozen statement is kept verbatim as an
  `example`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsO_ASML1d : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothO_ASML1d : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The charts of the closed 2-cell indexed as `ClosedCell (1 + 1)`. -/
local instance diskChartsSuccO_ASML1d :
    ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-- The smooth structure of the closed 2-cell indexed as `ClosedCell (1 + 1)`. -/
local instance diskSmoothSuccO_ASML1d : IsManifold (𝓡∂ (1 + 1)) ∞ (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The inclusion of the handle model `D² × [0, 1]` into `ℝ² × ℝ` is smooth. -/
theorem contMDiff_handleModelVal :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      (Prod.map Subtype.val Subtype.val :
        ClosedCell 2 × Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) × ℝ) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (isSmoothEmbedding_closedCell_inclusion 1).contMDiff.prodMap
    (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞))

/-- The inclusion of the handle model `D² × [0, 1]` into `ℝ² × ℝ` has bijective differentials. -/
theorem bijective_mfderiv_handleModelVal (x : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      (Prod.map Subtype.val Subtype.val :
        ClosedCell 2 × Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) × ℝ) x) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have hi := (isSmoothEmbedding_closedCell_inclusion 1).prodMap
    (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
  exact bijective_mfderiv_of_isImmersionAt ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (Prod.map Subtype.val Subtype.val) x (hi.isImmersion.isImmersionAt x) (by simp)

/-- **Lift through the handle model.** A map into `ℝ² × ℝ`, smooth at `q` and landing near `q` in
`D² × [0, 1]`, lifts near `q` to a map into the handle model, smooth at `q`. -/
theorem exists_handleLift {Φ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ}
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hΦ : ContDiffAt ℝ ∞ Φ q)
    (hev : ∀ᶠ q' in 𝓝 q, ‖(Φ q').1‖ ≤ 1 ∧ (Φ q').2 ∈ Icc (0 : ℝ) 1) :
    ∃ Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → ClosedCell 2 × Icc (0 : ℝ) 1,
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡∂ 2).prod (𝓡∂ 1)) ∞ Ψ q ∧
      ∀ᶠ q' in 𝓝 q, Prod.map Subtype.val Subtype.val (Ψ q') = Φ q' := by
  classical
  let Ψ₁ : EuclideanSpace ℝ (Fin 2) × ℝ → ClosedCell 2 := fun q' =>
    if h : ‖(Φ q').1‖ ≤ 1 then ⟨(Φ q').1, h⟩ else ⟨0, by simp⟩
  let Ψ₂ : EuclideanSpace ℝ (Fin 2) × ℝ → Icc (0 : ℝ) 1 := fun q' =>
    Set.projIcc (0 : ℝ) 1 zero_le_one (Φ q').2
  have hev₁ : (Subtype.val ∘ Ψ₁) =ᶠ[𝓝 q] fun q' => (Φ q').1 := by
    filter_upwards [hev] with q' hq'
    simp only [Function.comp_apply, Ψ₁, hq'.1, dite_true]
  have hev₂ : (Subtype.val ∘ Ψ₂) =ᶠ[𝓝 q] fun q' => (Φ q').2 := by
    filter_upwards [hev] with q' hq'
    simp only [Function.comp_apply, Ψ₂, Set.projIcc_of_mem _ hq'.2]
  have hs₁ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 2) ∞ (fun q' => (Φ q').1) q :=
    (contDiff_fst.contDiffAt.comp q hΦ).contMDiffAt
  have hs₂ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ) ∞ (fun q' => (Φ q').2) q :=
    (contDiff_snd.contDiffAt.comp q hΦ).contMDiffAt
  refine ⟨fun q' => (Ψ₁ q', Ψ₂ q'), ContMDiffAt.prodMk ?_ ?_, ?_⟩
  · have himm := (isSmoothEmbedding_closedCell_inclusion 1).isImmersion.isImmersionAt (Ψ₁ q)
    refine (ContMDiffAt.iff_comp_isImmersionAt (f := Ψ₁) (x := q) himm).mpr
      ⟨?_, hs₁.congr_of_eventuallyEq hev₁⟩
    exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (hs₁.continuousAt.congr hev₁.symm)
  · have himm := (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)
      (n := ∞)).isImmersion.isImmersionAt (Ψ₂ q)
    refine (ContMDiffAt.iff_comp_isImmersionAt (f := Ψ₂) (x := q) himm).mpr
      ⟨?_, hs₂.congr_of_eventuallyEq hev₂⟩
    exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (hs₂.continuousAt.congr hev₂.symm)
  · filter_upwards [hev₁, hev₂] with q' h₁ h₂
    exact Prod.ext h₁ h₂

/-- The derivative of the product form `(z, τ) ↦ (A (P (‖z‖²) • z), endCoord b (T τ))` on the core
`z = 0`. -/
theorem hasFDerivAt_neckProduct (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {P T : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hT : ContDiff ℝ ∞ T) (b : Bool) (τ : ℝ) :
    HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) × ℝ =>
        (A (P (‖q.1‖ ^ 2) • q.1), endCoord b (T q.2)))
      ((P 0 • ((A.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 2) →L[ℝ]
          EuclideanSpace ℝ (Fin 2)).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ))).prod
        (((if b then -1 else 1) * deriv T τ) •
          ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ))
      ((0 : EuclideanSpace ℝ (Fin 2)), τ) := by
  have hPd : Differentiable ℝ P := hP.differentiable (by simp)
  have hTd : Differentiable ℝ T := hT.differentiable (by simp)
  have hc : DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => P (‖q.1‖ ^ 2))
      ((0 : EuclideanSpace ℝ (Fin 2)), τ) :=
    hPd.differentiableAt.comp _ ((((contDiff_norm_sq ℝ (n := 1)).differentiable
      (by simp)).differentiableAt).comp _ differentiableAt_fst)
  have h1 := hc.hasFDerivAt.smul
    (hasFDerivAt_fst (p := ((0 : EuclideanSpace ℝ (Fin 2)), τ)) (𝕜 := ℝ))
  have h2 := (A.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 2) →L[ℝ]
    EuclideanSpace ℝ (Fin 2)).hasFDerivAt.comp _ h1
  have h3 : HasDerivAt (fun t => endCoord b (T t)) ((if b then -1 else 1) * deriv T τ) τ := by
    cases b
    · simpa [endCoord] using (hTd τ).hasDerivAt
    · simpa [endCoord] using (hTd τ).hasDerivAt.const_sub (1 : ℝ)
  have h4 := h3.comp_hasFDerivAt ((0 : EuclideanSpace ℝ (Fin 2)), τ)
    (hasFDerivAt_snd (p := ((0 : EuclideanSpace ℝ (Fin 2)), τ)) (𝕜 := ℝ))
  refine (h2.prodMk h4).congr_fderiv ?_
  cases b <;> ext v <;> simp

/-- The determinant of the derivative of the product form. -/
theorem det_neckProductDeriv (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a c : ℝ) :
    LinearMap.det (((a • ((A.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 2) →L[ℝ]
          EuclideanSpace ℝ (Fin 2)).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ))).prod
        (c • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ) :
          (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)) :
          (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)) =
      a ^ 2 * LinearMap.det A.toLinearMap * c := by
  have h : (((a • ((A.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 2) →L[ℝ]
          EuclideanSpace ℝ (Fin 2)).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ))).prod
        (c • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ) :
          (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)) :
          (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)) =
      LinearMap.prodMap (a • A.toLinearMap) (c • LinearMap.id) := by
    apply LinearMap.ext
    intro v
    rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul, LinearMap.det_id,
    finrank_euclideanSpace_fin, Module.finrank_self]
  ring

/-- One neck in product form on its handle side: the neck preserves the orientation at its centre iff
the comparison of the orientation of `W` with the orientation of `ℝ² × ℝ` through the handle (at a
point `x` of the handle model) agrees with the sign of `± det A` (`+` at the end `false`, `-` at the
end `true`). -/
theorem EdgeHandle.neckPreservesAt_iff_of_product {W : CompactCarrier.{u}} (H : EdgeHandle W)
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ ≤ 2 * ε) (hN : N.source = neckDomain ε)
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (P T : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ P) (hT : ContDiff ℝ ∞ T) (hPpos : 0 < P 0) (hT0 : T 0 = 0)
    (hTd : ∀ s, 0 ≤ s → s ≤ δ → 0 < deriv T s) (hT1 : T δ < 1) (b : Bool)
    (hprod : ∀ (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      0 ≤ τ → τ < δ →
      (w : EuclideanSpace ℝ (Fin 2)) = A (P (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
      (t : ℝ) = endCoord b (T τ) → N ((z : EuclideanSpace ℝ (Fin 2)), τ) = H.map (w, t)) :
    ∃ x : ClosedCell 2 × Icc (0 : ℝ) 1, NeckPreservesAt N 0 ↔
      (Orientation.map (Fin 3)
        ((differentialEquivOfBijective ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map H.mfderiv_bijective
          x).symm.trans (differentialEquivOfBijective ((𝓡∂ 2).prod (𝓡∂ 1))
            𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (Prod.map Subtype.val Subtype.val)
            bijective_mfderiv_handleModelVal x)).toLinearEquiv
        (W.orientation.orientation (H.map x)) = neckSpaceOrientation ↔
        0 < (if b then -1 else 1) * LinearMap.det A.toLinearMap) := by
  have hε : 0 < ε := by linarith
  have hτs : 0 < δ / 2 := by positivity
  have hτsδ : δ / 2 < δ := by linarith
  -- `T` is increasing on `[0, δ]`
  have hTmono : StrictMonoOn T (Icc 0 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 δ) hT.continuous.continuousOn
    intro s hs
    rw [interior_Icc] at hs
    exact hTd s hs.1.le hs.2.le
  have hTrange : ∀ τ, 0 ≤ τ → τ < δ → 0 ≤ T τ ∧ T τ < 1 := by
    intro τ h0 h1
    refine ⟨?_, ?_⟩
    · rw [← hT0]
      exact hTmono.monotoneOn ⟨le_rfl, hδ.le⟩ ⟨h0, h1.le⟩ h0
    · exact (hTmono.monotoneOn ⟨h0, h1.le⟩ ⟨hδ.le, le_rfl⟩ h1.le).trans_lt hT1
  -- the product form and its lift through the handle model near `(0, δ / 2)`
  let Φ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ := fun q =>
    (A (P (‖q.1‖ ^ 2) • q.1), endCoord b (T q.2))
  have hΦ : ContDiff ℝ ∞ Φ := by
    have hA : ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 2) => A w) :=
      (A.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin 2)).contDiff
    have h1 : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => P (‖q.1‖ ^ 2) • q.1) :=
      (hP.comp ((contDiff_norm_sq ℝ).comp contDiff_fst)).smul contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => endCoord b (T q.2)) := by
      cases b
      · exact hT.comp contDiff_snd
      · exact contDiff_const.sub (hT.comp contDiff_snd)
    exact (hA.comp h1).prodMk h2
  let qs : EuclideanSpace ℝ (Fin 2) × ℝ := ((0 : EuclideanSpace ℝ (Fin 2)), δ / 2)
  have hev : ∀ᶠ q in 𝓝 qs, ‖q.1‖ < 1 ∧ 0 < q.2 ∧ q.2 < δ ∧ ‖(Φ q).1‖ < 1 := by
    have hc1 : ContinuousAt (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => ‖q.1‖) qs := by fun_prop
    have hc4 : ContinuousAt (fun q => ‖(Φ q).1‖) qs :=
      (continuous_norm.comp (continuous_fst.comp hΦ.continuous)).continuousAt
    refine (hc1.eventually_lt continuousAt_const ?_).and
      ((continuousAt_const.eventually_lt continuous_snd.continuousAt ?_).and
        ((continuous_snd.continuousAt.eventually_lt continuousAt_const ?_).and
          (hc4.eventually_lt continuousAt_const ?_)))
    · simp [qs]
    · exact hτs
    · exact hτsδ
    · simp [Φ, qs]
  have hev' : ∀ᶠ q in 𝓝 qs, ‖(Φ q).1‖ ≤ 1 ∧ (Φ q).2 ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hev] with q hq
    obtain ⟨-, h2, h3, h4⟩ := hq
    obtain ⟨hT0', hT1'⟩ := hTrange q.2 h2.le h3
    refine ⟨h4.le, ?_⟩
    cases b
    · exact ⟨hT0', hT1'.le⟩
    · exact ⟨by simp only [Φ, endCoord, ite_true]; linarith,
        by simp only [Φ, endCoord, ite_true]; linarith⟩
  obtain ⟨Ψ, hΨ, hΨev⟩ := exists_handleLift hΦ.contDiffAt hev'
  have hNev : (N : EuclideanSpace ℝ (Fin 2) × ℝ → W.Carrier) =ᶠ[𝓝 qs] H.map ∘ Ψ := by
    filter_upwards [hev, hΨev] with q hq hΨq
    obtain ⟨h1, h2, h3, -⟩ := hq
    have hq1 : ((Ψ q).1 : EuclideanSpace ℝ (Fin 2)) = (Φ q).1 := congrArg Prod.fst hΨq
    have hq2 : ((Ψ q).2 : ℝ) = (Φ q).2 := congrArg Prod.snd hΨq
    exact hprod ⟨q.1, h1.le⟩ q.2 (Ψ q).1 (Ψ q).2 h2.le h3 hq1 hq2
  -- the source contains the segment from `0` to `(0, δ / 2)`
  have hseg : ((fun t : ℝ => ((0 : EuclideanSpace ℝ (Fin 2)), t)) '' Icc 0 (δ / 2)) ⊆
      N.source := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rw [hN]
    refine ⟨?_, ?_⟩
    · simp only [norm_zero]
      linarith
    · simp only [abs_of_nonneg ht0]
      linarith
  have hqs : qs ∈ N.source := hseg ⟨δ / 2, ⟨hτs.le, le_rfl⟩, rfl⟩
  have hpres : NeckPreservesAt N 0 ↔ NeckPreservesAt N qs :=
    neckPreservesAt_iff_of_isPreconnected (isPreconnected_Icc.image _ (by fun_prop)) hseg
      ⟨0, ⟨le_rfl, hτs.le⟩, rfl⟩ ⟨δ / 2, ⟨hτs.le, le_rfl⟩, rfl⟩
  -- the derivative of the product form
  have hder := hasFDerivAt_neckProduct A hP hT b (δ / 2)
  have hD : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N qs =
      (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map (Ψ qs)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡∂ 2).prod (𝓡∂ 1)) Ψ qs) := by
    rw [hNev.mfderiv_eq]
    exact mfderiv_comp qs (H.smooth.mdifferentiableAt (by simp)) (hΨ.mdifferentiableAt (by simp))
  have hι : (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      (Prod.map Subtype.val Subtype.val) (Ψ qs)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡∂ 2).prod (𝓡∂ 1)) Ψ qs) =
      fderiv ℝ Φ qs := by
    rw [← mfderiv_comp qs (contMDiff_handleModelVal.mdifferentiableAt (by simp))
      (hΨ.mdifferentiableAt (by simp))]
    have hev'' : (Prod.map Subtype.val Subtype.val ∘ Ψ) =ᶠ[𝓝 qs] Φ := hΨev
    rw [mfderiv_eq_fderiv, hev''.fderiv_eq]
    rfl
  have hdet : LinearMap.det ((((neckDiffEquiv N hqs).trans
      ((differentialEquivOfBijective ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map H.mfderiv_bijective
          (Ψ qs)).symm.trans (differentialEquivOfBijective ((𝓡∂ 2).prod (𝓡∂ 1))
            𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (Prod.map Subtype.val Subtype.val)
            bijective_mfderiv_handleModelVal (Ψ qs))).toLinearEquiv) :
        (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)) :
        (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)) =
      P 0 ^ 2 * LinearMap.det A.toLinearMap * ((if b then -1 else 1) * deriv T (δ / 2)) := by
    rw [← det_neckProductDeriv A (P 0) ((if b then -1 else 1) * deriv T (δ / 2)), ← hder.fderiv]
    congr 1
    refine LinearMap.ext fun v => ?_
    have hsymm : ∀ w, (differentialEquivOfBijective ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map
        H.mfderiv_bijective (Ψ qs)).symm
          (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map (Ψ qs) w) = w := fun w =>
      (differentialEquivOfBijective ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map
        H.mfderiv_bijective (Ψ qs)).symm_apply_apply w
    change mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      (Prod.map Subtype.val Subtype.val) (Ψ qs)
        ((differentialEquivOfBijective ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map
          H.mfderiv_bijective (Ψ qs)).symm (neckDiffEquiv N hqs v)) = fderiv ℝ Φ qs v
    have hDv : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N qs v =
        mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map (Ψ qs)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡∂ 2).prod (𝓡∂ 1)) Ψ qs v) := by
      rw [hD]
      rfl
    have hιv : mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
        (Prod.map Subtype.val Subtype.val) (Ψ qs)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡∂ 2).prod (𝓡∂ 1)) Ψ qs v) =
        fderiv ℝ Φ qs v := by
      rw [← hι]
      rfl
    rw [neckDiffEquiv_apply, hDv, hsymm, hιv]
  refine ⟨Ψ qs, ?_⟩
  rw [hpres, neckPreservesAt_iff hqs, hNev.self_of_nhds]
  refine (orientationMap_eq_iff_det_pos finrank_neckSpace _).trans (iff_congr Iff.rfl ?_)
  rw [hdet]
  have hpos : 0 < P 0 ^ 2 * deriv T (δ / 2) := by
    have := hTd (δ / 2) hτs.le hτsδ.le
    positivity
  rw [show P 0 ^ 2 * LinearMap.det A.toLinearMap * ((if b then -1 else 1) * deriv T (δ / 2)) =
    (P 0 ^ 2 * deriv T (δ / 2)) * ((if b then -1 else 1) * LinearMap.det A.toLinearMap) by ring]
  exact mul_pos_iff_of_pos_left hpos

/-- **E4** (stronger form: the hypotheses `hP₀1`, `hP₁1`, `hP₀mono`, `hP₁mono` of the frozen
statement are not needed). Two necks of one handle `H`, the first at the end `false`, the second at
the end `true`, both in product form on their handle side, preserve the orientation alike iff
`det A₀ * det A₁ < 0`. -/
theorem neckPreservesAt_iff_det_mul_neg {W : CompactCarrier.{u}} (H : EdgeHandle W)
    (N₀ N₁ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    {ε₀ ε₁ δ : ℝ} (hδ : 0 < δ) (hδ₀ : δ ≤ 2 * ε₀) (hδ₁ : δ ≤ 2 * ε₁)
    (hN₀ : N₀.source = neckDomain ε₀) (hN₁ : N₁.source = neckDomain ε₁)
    (A₀ A₁ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (P₀ P₁ T₀ T₁ : ℝ → ℝ)
    (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁) (hT₀ : ContDiff ℝ ∞ T₀)
    (hT₁ : ContDiff ℝ ∞ T₁)
    (hP₀pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₀ s) (hP₁pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₁ s)
    (hT₀0 : T₀ 0 = 0) (hT₁0 : T₁ 0 = 0) (hT₀d : ∀ s, 0 ≤ s → s ≤ δ → 0 < deriv T₀ s)
    (hT₁d : ∀ s, 0 ≤ s → s ≤ δ → 0 < deriv T₁ s) (hT₀1 : T₀ δ < 1) (hT₁1 : T₁ δ < 1)
    (hprod₀ : ∀ (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      0 ≤ τ → τ < δ →
      (w : EuclideanSpace ℝ (Fin 2)) = A₀ (P₀ (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
      (t : ℝ) = endCoord false (T₀ τ) → N₀ ((z : EuclideanSpace ℝ (Fin 2)), τ) = H.map (w, t))
    (hprod₁ : ∀ (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      0 ≤ τ → τ < δ →
      (w : EuclideanSpace ℝ (Fin 2)) = A₁ (P₁ (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
      (t : ℝ) = endCoord true (T₁ τ) → N₁ ((z : EuclideanSpace ℝ (Fin 2)), τ) = H.map (w, t)) :
    (NeckPreservesAt N₀ 0 ↔ NeckPreservesAt N₁ 0) ↔
      LinearMap.det A₀.toLinearMap * LinearMap.det A₁.toLinearMap < 0 := by
  let _ : PreconnectedSpace (ClosedCell 2) := by
    have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} : Set _) := by
      simpa only [Metric.closedBall, dist_zero_right] using
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ))
    exact Subtype.preconnectedSpace hconv.isPreconnected
  let _ : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  obtain ⟨x₀, hx₀⟩ := H.neckPreservesAt_iff_of_product N₀ hδ hδ₀ hN₀ A₀ P₀ T₀ hP₀ hT₀
    (hP₀pos 0 le_rfl zero_le_one) hT₀0 hT₀d hT₀1 false hprod₀
  obtain ⟨x₁, hx₁⟩ := H.neckPreservesAt_iff_of_product N₁ hδ hδ₁ hN₁ A₁ P₁ T₁ hP₁ hT₁
    (hP₁pos 0 le_rfl zero_le_one) hT₁0 hT₁d hT₁1 true hprod₁
  rw [hx₀, hx₁, orientationMap_differentials_iff (hbf := H.mfderiv_bijective)
    (hbg := bijective_mfderiv_handleModelVal) (oY := W.orientation) (oV := neckSpaceOrientation)
    H.smooth contMDiff_handleModelVal x₀ x₁]
  have hne : ∀ F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
      LinearMap.det F.toLinearMap ≠ 0 := by
    intro F
    rcases det_linearIsometryEquiv_eq_one_or_neg_one F with h | h <;> rw [h] <;> norm_num
  rw [iff_iff_iff_pos_iff_mul_pos (by simpa using hne A₀) (by simpa using hne A₁)]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  constructor <;> intro h <;> nlinarith

/-- **E4**, the frozen statement verbatim. -/
example {W : CompactCarrier.{u}} (H : EdgeHandle W)
    (N₀ N₁ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    {ε₀ ε₁ δ : ℝ} (hδ : 0 < δ) (hδ₀ : δ ≤ 2 * ε₀) (hδ₁ : δ ≤ 2 * ε₁)
    (hN₀ : N₀.source = neckDomain ε₀) (hN₁ : N₁.source = neckDomain ε₁)
    (A₀ A₁ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (P₀ P₁ T₀ T₁ : ℝ → ℝ)
    (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁) (hT₀ : ContDiff ℝ ∞ T₀)
    (hT₁ : ContDiff ℝ ∞ T₁) (_hP₀1 : P₀ 1 = 1) (_hP₁1 : P₁ 1 = 1)
    (hP₀pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₀ s) (hP₁pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₁ s)
    (_hP₀mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₀ (r ^ 2)) r)
    (_hP₁mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₁ (r ^ 2)) r)
    (hT₀0 : T₀ 0 = 0) (hT₁0 : T₁ 0 = 0) (hT₀d : ∀ s, 0 ≤ s → s ≤ δ → 0 < deriv T₀ s)
    (hT₁d : ∀ s, 0 ≤ s → s ≤ δ → 0 < deriv T₁ s) (hT₀1 : T₀ δ < 1) (hT₁1 : T₁ δ < 1)
    (hprod₀ : ∀ (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      0 ≤ τ → τ < δ →
      (w : EuclideanSpace ℝ (Fin 2)) = A₀ (P₀ (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
      (t : ℝ) = endCoord false (T₀ τ) → N₀ ((z : EuclideanSpace ℝ (Fin 2)), τ) = H.map (w, t))
    (hprod₁ : ∀ (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      0 ≤ τ → τ < δ →
      (w : EuclideanSpace ℝ (Fin 2)) = A₁ (P₁ (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
      (t : ℝ) = endCoord true (T₁ τ) → N₁ ((z : EuclideanSpace ℝ (Fin 2)), τ) = H.map (w, t)) :
    (NeckPreservesAt N₀ 0 ↔ NeckPreservesAt N₁ 0) ↔
      LinearMap.det A₀.toLinearMap * LinearMap.det A₁.toLinearMap < 0 :=
  neckPreservesAt_iff_det_mul_neg H N₀ N₁ hδ hδ₀ hδ₁ hN₀ hN₁ A₀ A₁ P₀ P₁ T₀ T₁ hP₀ hP₁ hT₀ hT₁
    hP₀pos hP₁pos hT₀0 hT₁0 hT₀d hT₁d hT₀1 hT₁1 hprod₀ hprod₁

end GC.GraphManifold.Assembly
