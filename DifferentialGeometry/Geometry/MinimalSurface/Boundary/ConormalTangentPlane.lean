import DifferentialGeometry.Analysis.Calculus.Inverse.TwoMapCommonProjection
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskDivergence
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false
noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

private theorem conormal_mfderivWithin_congr {F G : ℂ → M} {S : Set ℂ}
    (heq : EqOn F G S) {z : ℂ} (hz : z ∈ S) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F S z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) G S z) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext w
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D w) hd

private theorem mfderiv_one_eq_of_real_trace {F₁ F₂ : ℂ → M} {x : ℝ}
    (hd₁ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (x : ℂ))
    (hd₂ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (x : ℂ))
    (htrace : (fun t : ℝ => F₁ (t : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => F₂ (t : ℂ))) :
    (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (x : ℂ)) 1 =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (x : ℂ)) 1 := by
  have hline : HasFDerivAt (fun t : ℝ => (t : ℂ)) Complex.ofRealCLM x :=
    Complex.ofRealCLM.hasFDerivAt
  have he := htrace.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
  have hc₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) x
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (x : ℂ)).comp Complex.ofRealCLM) :=
    HasMFDerivAt.comp (f := fun t : ℝ => (t : ℂ)) (g := F₁)
      x hd₁.hasMFDerivAt hline.hasMFDerivAt
  have hc₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) x
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (x : ℂ)).comp Complex.ofRealCLM) :=
    HasMFDerivAt.comp (f := fun t : ℝ => (t : ℂ)) (g := F₂)
      x hd₂.hasMFDerivAt hline.hasMFDerivAt
  have hv := congrArg (fun L : ℝ →L[ℝ] E => L 1) he
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) x) 1 =
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) x) 1 at hv
  have hv₁ := congrArg (fun L : ℝ →L[ℝ] E => L 1) hc₁.mfderiv
  have hv₂ := congrArg (fun L : ℝ →L[ℝ] E => L 1) hc₂.mfderiv
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) x) 1 =
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (x : ℂ)) (1 : ℂ) at hv₁
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) x) 1 =
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (x : ℂ)) (1 : ℂ) at hv₂
  exact hv₁.symm.trans (hv.trans hv₂)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

-- This is the range argument of TransverseConormal, without its transverse
-- contradiction: cancellation puts the entire second tangent plane in the first.
private theorem mfderivWithin_range_le_of_conormal_sum_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F₁ F₂ : ℂ → M} {S : Set ℂ} {z : ℂ}
    (hi₂ : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S z))
    (hsame : (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S z) 1 =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S z) 1)
    (hcancel : (show E from inwardConormalWithin g F₁ S z) +
      (show E from inwardConormalWithin g F₂ S z) = 0) :
    LinearMap.range (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S z).toLinearMap ≤
    LinearMap.range (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S z).toLinearMap := by
  let D₁ : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S z
  let D₂ : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S z
  let ν₁ : E := inwardConormalWithin g F₁ S z
  let ν₂ : E := inwardConormalWithin g F₂ S z
  have hT₂ : D₂ 1 ≠ 0 := by
    intro h
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (hi₂ (h.trans D₂.map_zero.symm))
  have hunit₂ := (inwardConormalWithin_geometry g (U := F₂) (S := S) (z := z) hi₂).1
  have hν₂ : ν₂ ≠ 0 := by
    intro h
    change (inwardConormalWithin g F₂ S z : E) = 0 at h
    rw [h, map_zero] at hunit₂
    exact zero_ne_one hunit₂
  let R : Submodule ℝ E := LinearMap.range D₁.toLinearMap
  have hR₁ (w : ℂ) : D₁ w ∈ R := ⟨w, rfl⟩
  have hν₁R : ν₁ ∈ R := by
    change (Real.sqrt (gramWithin g F₁ S z 1 1) * densityWithin g F₁ S z)⁻¹ •
      (gramWithin g F₁ S z 1 1 • D₁ Complex.I -
        gramWithin g F₁ S z 1 Complex.I • D₁ 1) ∈ R
    exact R.smul_mem _ (R.sub_mem (R.smul_mem _ (hR₁ Complex.I))
      (R.smul_mem _ (hR₁ 1)))
  have hν₂R : ν₂ ∈ R := by
    have hc : ν₁ + ν₂ ∈ R := hcancel.symm ▸ R.zero_mem
    have heq : ν₁ + ν₂ - ν₁ = ν₂ := add_sub_cancel_left ν₁ ν₂
    exact heq ▸ R.sub_mem hc hν₁R
  let a₂ : ℝ := gramWithin g F₂ S z 1 1
  let b₂ : ℝ := gramWithin g F₂ S z 1 Complex.I
  let c₂ : ℝ := (Real.sqrt a₂ * densityWithin g F₂ S z)⁻¹
  have ha₂ : 0 < a₂ := g.pos (F₂ z) (D₂ 1) hT₂
  have hform : ν₂ = c₂ • (a₂ • D₂ Complex.I - b₂ • D₂ 1) := rfl
  have hc₂ : c₂ ≠ 0 := by
    intro h
    have hz : c₂ • (a₂ • D₂ Complex.I - b₂ • D₂ 1 : E) = (0 : E) := by
      rw [h]
      exact zero_smul ℝ _
    exact hν₂ (hform.trans hz)
  have hT₂R : D₂ 1 ∈ R := hsame ▸ hR₁ 1
  have hN₂R : D₂ Complex.I ∈ R := by
    apply (R.smul_mem_iff ha₂.ne').mp
    rw [hform] at hν₂R
    have hdiff := (R.smul_mem_iff hc₂).mp hν₂R
    simpa only [sub_add_cancel] using R.add_mem hdiff (R.smul_mem b₂ hT₂R)
  rintro v ⟨w, rfl⟩
  change D₂ w ∈ R
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im w).symm
  rw [hw, map_add, map_smul, map_smul]
  exact R.add_mem (R.smul_mem _ (hT₂R)) (R.smul_mem _ hN₂R)

/-- Two regular one-sided sheets with the same seam tangent and cancelling
original-metric inward conormals have the same tangent plane. No transversality
or ambient dimension assumption is used. -/
theorem mfderivWithin_range_eq_of_conormal_sum_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F₁ F₂ : ℂ → M} {S : Set ℂ} {z : ℂ}
    (hi₁ : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S z))
    (hi₂ : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S z))
    (hsame : (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S z) 1 =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S z) 1)
    (hcancel : inwardConormalWithin g F₁ S z +
      tangentSpaceCast 𝓘(ℝ, E) (F₂ z) (F₁ z) (inwardConormalWithin g F₂ S z) = 0) :
    LinearMap.range (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S z).toLinearMap =
    LinearMap.range (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S z).toLinearMap := by
  change (show E from inwardConormalWithin g F₁ S z) +
    (show E from inwardConormalWithin g F₂ S z) = 0 at hcancel
  apply le_antisymm
  · exact mfderivWithin_range_le_of_conormal_sum_eq_zero g hi₁ hsame.symm
      ((add_comm (show E from inwardConormalWithin g F₂ S z)
        (show E from inwardConormalWithin g F₁ S z)).trans hcancel)
  · exact mfderivWithin_range_le_of_conormal_sum_eq_zero g hi₂ hsame hcancel

/-- Apply the actual one-sided conormal cancellation to smooth extensions of
both sheets. Equality on the one-sided source transports the derivatives;
equality along the real seam derives their common tangential derivative.
The output concerns the literal two extensions and supplies both rank and
plane equality for the common-projection inverse theorem. -/
theorem mfderiv_range_eq_of_trace_conormal_cancellation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {F₁ F₂ U₁ U₂ : ℂ → M} {S : Set ℂ} {x : ℝ}
    (hx : (x : ℂ) ∈ S) (huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) S (x : ℂ))
    (heq₁ : EqOn F₁ U₁ S) (heq₂ : EqOn F₂ U₂ S)
    (hd₁ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₁ (x : ℂ))
    (hd₂ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₂ (x : ℂ))
    (hi₁ : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S (x : ℂ)))
    (hi₂ : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S (x : ℂ)))
    (htrace : (fun t : ℝ => U₁ (t : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => U₂ (t : ℂ)))
    (hcancel : inwardConormalWithin g F₁ S (x : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) (F₂ (x : ℂ)) (F₁ (x : ℂ))
        (inwardConormalWithin g F₂ S (x : ℂ)) = 0) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₁ (x : ℂ)) ∧
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₂ (x : ℂ)) ∧
    LinearMap.range (show ℂ →L[ℝ] E from
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₁ (x : ℂ)).toLinearMap =
    LinearMap.range (show ℂ →L[ℝ] E from
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₂ (x : ℂ)).toLinearMap := by
  have hD₁ : (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S (x : ℂ)) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₁ (x : ℂ)) :=
    (conormal_mfderivWithin_congr heq₁ hx).trans (mfderivWithin_eq_mfderiv huniq hd₁)
  have hD₂ : (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S (x : ℂ)) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₂ (x : ℂ)) :=
    (conormal_mfderivWithin_congr heq₂ hx).trans (mfderivWithin_eq_mfderiv huniq hd₂)
  have hsame : (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S (x : ℂ)) 1 =
      (show ℂ →L[ℝ] E from
        mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S (x : ℂ)) 1 := by
    rw [hD₁, hD₂]
    exact mfderiv_one_eq_of_real_trace hd₁ hd₂ htrace
  have hrange := mfderivWithin_range_eq_of_conormal_sum_eq_zero g hi₁ hi₂ hsame hcancel
  have hpoint₁ (v : ℂ) := congrArg (fun L : ℂ →L[ℝ] E => L v) hD₁
  have hpoint₂ (v : ℂ) := congrArg (fun L : ℂ →L[ℝ] E => L v) hD₂
  refine ⟨?_, ?_, ?_⟩
  · intro v w hvw
    apply hi₁
    exact (hpoint₁ v).trans (hvw.trans (hpoint₁ w).symm)
  · intro v w hvw
    apply hi₂
    exact (hpoint₂ v).trans (hvw.trans (hpoint₂ w).symm)
  · have hR₁ := congrArg (fun L : ℂ →L[ℝ] E => LinearMap.range L.toLinearMap) hD₁
    have hR₂ := congrArg (fun L : ℂ →L[ℝ] E => LinearMap.range L.toLinearMap) hD₂
    exact hR₁.symm.trans (hrange.trans hR₂)

/-- The cancelling one-sided sheets have common graph germs for a prescribed
original-metric projection. Both graph maps remain their literal smooth
extensions. The common target is small enough for every interpolation segment
to remain in the original ambient chart. -/
theorem exists_chart_graph_germs_of_trace_conormal_cancellation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {F₁ F₂ U₁ U₂ : ℂ → M} {S s₁ s₂ : Set ℂ} {x : ℝ}
    (hx : (x : ℂ) ∈ S) (huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) S (x : ℂ))
    (heq₁ : EqOn F₁ U₁ S) (heq₂ : EqOn F₂ U₂ S)
    (hs₁ : IsOpen s₁) (hs₂ : IsOpen s₂) (hx₁ : (x : ℂ) ∈ s₁) (hx₂ : (x : ℂ) ∈ s₂)
    (hU₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₁ s₁)
    (hU₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₂ s₂)
    (hi₁ : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S (x : ℂ)))
    (hi₂ : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S (x : ℂ)))
    (htrace : (fun t : ℝ => U₁ (t : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => U₂ (t : ℂ)))
    (hcancel : inwardConormalWithin g F₁ S (x : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) (F₂ (x : ℂ)) (F₁ (x : ℂ))
        (inwardConormalWithin g F₂ S (x : ℂ)) = 0)
    (p : M) (hchart₁ : ∀ z ∈ s₁, U₁ z ∈ (chartAt E p).source)
    (hchart₂ : ∀ z ∈ s₂, U₂ z ∈ (chartAt E p).source)
    (P : E →L[ℝ] ℂ)
    (hP : (P.comp (fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (U₁ z))
      (x : ℂ))).IsInvertible) :
    let X₁ : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U₁ z)
    let X₂ : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U₂ z)
    ∃ (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
      (x : ℂ) ∈ e₁.source ∧ (x : ℂ) ∈ e₂.source ∧
      e₁.source ⊆ s₁ ∧ e₂.source ⊆ s₂ ∧
      (e₁ : ℂ → ℂ) = P ∘ X₁ ∧ (e₂ : ℂ → ℂ) = P ∘ X₂ ∧
      ContDiffOn ℝ ∞ e₁.symm e₁.target ∧
      ContDiffOn ℝ ∞ e₂.symm e₂.target ∧
      IsOpen O ∧ P (X₁ (x : ℂ)) ∈ O ∧ O ⊆ e₁.target ∩ e₂.target ∧
      ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
        (1 - t) • X₂ (e₂.symm y) + t • X₁ (e₁.symm y) ∈
          (extChartAt 𝓘(ℝ, E) p).target := by
  intro X₁ X₂
  have hd₁ := (hU₁.contMDiffAt (hs₁.mem_nhds hx₁)).mdifferentiableAt (by simp)
  have hd₂ := (hU₂.contMDiffAt (hs₂.mem_nhds hx₂)).mdifferentiableAt (by simp)
  obtain ⟨_, hiU₂, hrange⟩ := mfderiv_range_eq_of_trace_conormal_cancellation
    g hx huniq heq₁ heq₂ hd₁ hd₂ hi₁ hi₂ htrace hcancel
  have hvalue : U₁ (x : ℂ) = U₂ (x : ℂ) := htrace.eq_of_nhds
  have hX₁ : ContDiffOn ℝ ∞ X₁ s₁ := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart₁ z hz)).comp z (hU₁.contMDiffAt (hs₁.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hX₂ : ContDiffOn ℝ ∞ X₂ s₂ := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart₂ z hz)).comp z (hU₂.contMDiffAt (hs₂.mem_nhds hz))).contDiffAt).contDiffWithinAt
  let chartD (q : M) : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) q
  let D₁ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₁ (x : ℂ)
  let D₂ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U₂ (x : ℂ)
  have hDX₁ : fderiv ℝ X₁ (x : ℂ) = (chartD (U₁ (x : ℂ))).comp D₁ := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart₁ _ hx₁)
    exact mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp (x : ℂ) (hc.mdifferentiableAt (by simp)) hd₁)
  have hDX₂ : fderiv ℝ X₂ (x : ℂ) = (chartD (U₂ (x : ℂ))).comp D₂ := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart₂ _ hx₂)
    exact mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp (x : ℂ) (hc.mdifferentiableAt (by simp)) hd₂)
  have hC₂ : Function.Injective (chartD (U₂ (x : ℂ))) :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
      (show U₂ (x : ℂ) ∈ (extChartAt 𝓘(ℝ, E) p).source by
        simpa only [extChartAt_source] using hchart₂ _ hx₂)).injective
  have hiX₂ : Function.Injective (fderiv ℝ X₂ (x : ℂ)) := by
    rw [hDX₂]
    exact hC₂.comp hiU₂
  have hrangeX : LinearMap.range (fderiv ℝ X₂ (x : ℂ)).toLinearMap ≤
      LinearMap.range (fderiv ℝ X₁ (x : ℂ)).toLinearMap := by
    rintro v ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := hrange.ge (LinearMap.mem_range_self D₂.toLinearMap w)
    change D₁ t = D₂ w at ht
    refine ⟨t, ?_⟩
    rw [hDX₁, hDX₂]
    change chartD (U₁ (x : ℂ)) (D₁ t) = chartD (U₂ (x : ℂ)) (D₂ w)
    rw [ht, hvalue]
  have hXvalue : X₁ (x : ℂ) = X₂ (x : ℂ) :=
    congrArg (extChartAt 𝓘(ℝ, E) p) hvalue
  obtain ⟨e₁, e₂, hxe₁, hxe₂, he₁s, he₂s, he₁, he₂, hei₁, hei₂, htargets⟩ :=
    Analysis.exists_two_map_common_projection_inverse_germs hs₁ hs₂ hX₁ hX₂ P
      hx₁ hx₂ hXvalue hP hiX₂ hrangeX
  have hpoint : X₁ (x : ℂ) ∈ (extChartAt 𝓘(ℝ, E) p).target :=
    (extChartAt 𝓘(ℝ, E) p).map_source (by
      simpa only [extChartAt_source] using hchart₁ _ hx₁)
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p) (X₁ (x : ℂ)) hpoint
  let O : Set ℂ := (e₁.target ∩ e₂.target) ∩
    ((fun y => X₁ (e₁.symm y)) ⁻¹' Metric.ball (X₁ (x : ℂ)) ε ∩
      (fun y => X₂ (e₂.symm y)) ⁻¹' Metric.ball (X₁ (x : ℂ)) ε)
  have hXe₁ : ContDiffOn ℝ ∞ (fun y => X₁ (e₁.symm y)) e₁.target :=
    hX₁.comp hei₁ (fun y hy => he₁s (e₁.map_target hy))
  have hXe₂ : ContDiffOn ℝ ∞ (fun y => X₂ (e₂.symm y)) e₂.target :=
    hX₂.comp hei₂ (fun y hy => he₂s (e₂.map_target hy))
  have hOo : IsOpen O := by
    have ho₁ := hXe₁.continuousOn.isOpen_inter_preimage
      (t := Metric.ball (X₁ (x : ℂ)) ε) e₁.open_target Metric.isOpen_ball
    have ho₂ := hXe₂.continuousOn.isOpen_inter_preimage
      (t := Metric.ball (X₁ (x : ℂ)) ε) e₂.open_target Metric.isOpen_ball
    convert ho₁.inter ho₂ using 1
    ext y
    simp only [O, mem_inter_iff, mem_preimage]
    tauto
  have hinv₁ : e₁.symm (P (X₁ (x : ℂ))) = (x : ℂ) := by
    change e₁.symm ((P ∘ X₁) (x : ℂ)) = (x : ℂ)
    rw [← he₁]
    exact e₁.left_inv hxe₁
  have hinv₂ : e₂.symm (P (X₁ (x : ℂ))) = (x : ℂ) := by
    rw [hXvalue]
    change e₂.symm ((P ∘ X₂) (x : ℂ)) = (x : ℂ)
    rw [← he₂]
    exact e₂.left_inv hxe₂
  refine ⟨e₁, e₂, O, hxe₁, hxe₂, he₁s, he₂s, he₁, he₂, hei₁, hei₂,
    hOo, ?_, inter_subset_left, ?_⟩
  · refine ⟨htargets, ?_, ?_⟩
    · change X₁ (e₁.symm (P (X₁ (x : ℂ)))) ∈ Metric.ball (X₁ (x : ℂ)) ε
      rw [hinv₁]
      exact Metric.mem_ball_self hε
    · change X₂ (e₂.symm (P (X₁ (x : ℂ)))) ∈ Metric.ball (X₁ (x : ℂ)) ε
      rw [hinv₂, ← hXvalue]
      exact Metric.mem_ball_self hε
  · intro y hy t ht
    exact hεsub ((convex_ball (X₁ (x : ℂ)) ε) hy.2.2 hy.2.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring))

end DifferentialGeometry.Geometry
