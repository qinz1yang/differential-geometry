import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BranchSlitFold
import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.CircleStraightening
import DifferentialGeometry.Topology.Planar.RadialStraightening
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
noncomputable section

open Set Filter Metric Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

private theorem range_le_of_not_surjective_coprod
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D₁ D₂ : ℂ →L[ℝ] E) (hd3 : Module.finrank ℝ E = 3)
    (hD₁ : Function.Injective D₁)
    (hnot : ¬ Function.Surjective (D₁.coprod (-D₂))) :
    LinearMap.range D₂.toLinearMap ≤ LinearMap.range D₁.toLinearMap := by
  let S := LinearMap.range (D₁.coprod (-D₂)).toLinearMap
  have h₁S : LinearMap.range D₁.toLinearMap ≤ S := by
    rintro x ⟨z, rfl⟩
    exact ⟨(z, 0), by simp⟩
  have h₂S : LinearMap.range D₂.toLinearMap ≤ S := by
    rintro x ⟨z, rfl⟩
    exact ⟨(0, -z), by simp⟩
  have hSne : S ≠ ⊤ := fun h => hnot (LinearMap.range_eq_top.mp h)
  have hSdim : Module.finrank ℝ S < 3 := by
    simpa only [finrank_top, hd3] using
      Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hSne)
  have hDdim : Module.finrank ℝ (LinearMap.range D₁.toLinearMap) = 2 := by
    rw [LinearMap.finrank_range_of_inj hD₁,
      Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
  have hEq : LinearMap.range D₁.toLinearMap = S :=
    Submodule.eq_of_le_of_finrank_eq h₁S (by
      have := Submodule.finrank_mono h₁S
      omega)
  exact h₂S.trans hEq.ge

private theorem comp_eq_of_not_transverse_of_projection_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D₁ D₂ : ℂ →L[ℝ] E) (P : E →L[ℝ] ℂ)
    (R₁ R₂ : ℂ →L[ℝ] ℂ) (hd3 : Module.finrank ℝ E = 3)
    (hP : (P.comp D₁).IsInvertible)
    (hnot : ¬ Function.Surjective (D₁.coprod (-D₂)))
    (hproj : (P.comp D₁).comp R₁ = (P.comp D₂).comp R₂) :
    D₁.comp R₁ = D₂.comp R₂ := by
  have hD₁ : Function.Injective D₁ := by
    intro x y hxy
    exact hP.injective (congrArg P hxy)
  have hrange := range_le_of_not_surjective_coprod D₁ D₂ hd3 hD₁ hnot
  ext v
  obtain ⟨w, hw⟩ := hrange (LinearMap.mem_range_self D₂.toLinearMap (R₂ v))
  change D₁ w = D₂ (R₂ v) at hw
  have hweq : w = R₁ v := by
    apply hP.injective
    change P (D₁ w) = P (D₁ (R₁ v))
    rw [hw]
    exact (congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hproj).symm
  change D₁ (R₁ v) = D₂ (R₂ v)
  simpa only [hweq] using hw

/-- At a nontransverse collision, equal leading projections of the two literal
root restrictions force the derivative of their height difference to vanish.
Only the supplied projection differential is used for rank; no new graph
coordinate or replacement disk is selected. -/
theorem IsMorreyDisk.root_height_fderiv_eq_zero_of_not_transverse
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hd3 : Module.finrank ℝ E = 3) (p : M)
    (P : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ)
    (e : OpenPartialHomeomorph ℂ ℂ) (ζ w : ℂ)
    (hei₁ : DifferentiableAt ℝ (e.symm : ℂ → ℂ) w)
    (hei₂ : DifferentiableAt ℝ (e.symm : ℂ → ℂ) (ζ * w))
    (hx : e.symm w ∈ Metric.ball (0 : ℂ) 1)
    (hy : e.symm (ζ * w) ∈ Metric.ball (0 : ℂ) 1)
    (hsrc : diskExtension q (e.symm w) ∈ (chartAt E p).source)
    (hvalue : diskExtension q (e.symm w) = diskExtension q (e.symm (ζ * w))) :
    let U := diskExtension q
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => P (X z)
    (fderiv ℝ F (e.symm w)).IsInvertible →
    (∀ᶠ z in 𝓝 w, F (e.symm z) = F (e.symm (ζ * z))) →
    (¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm w)).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm (ζ * w)))))) →
      fderiv ℝ (fun z => height (X (e.symm z)) - height (X (e.symm (ζ * z)))) w = 0 := by
  intro U X F hreg hprojection hnot
  let x := e.symm w
  let y := e.symm (ζ * w)
  let C : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
    (extChartAt 𝓘(ℝ, E) p) (U x)
  let D₁ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x
  let D₂ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U y
  let R₁ := fderiv ℝ (e.symm : ℂ → ℂ) w
  let R₂ := fderiv ℝ (fun z : ℂ => e.symm (ζ * z)) w
  have hUx := hq.smoothInterior.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)
  have hUy := hq.smoothInterior.contMDiffAt (Metric.isOpen_ball.mem_nhds hy)
  have hvalue' : U x = U y := hvalue
  have hsrcy : U y ∈ (chartAt E p).source := by
    rw [← hvalue']
    exact hsrc
  have hcx := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hsrc
  have hcy := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hsrcy
  have hXx : DifferentiableAt ℝ X x :=
    ((hcx.comp x hUx).contDiffAt).differentiableAt (by simp)
  have hXy : DifferentiableAt ℝ X y :=
    ((hcy.comp y hUy).contDiffAt).differentiableAt (by simp)
  have hDXx : fderiv ℝ X x = C.comp D₁ :=
    mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp x (hcx.mdifferentiableAt (by simp))
        (hUx.mdifferentiableAt (by simp)))
  have hDXy : fderiv ℝ X y = C.comp D₂ := by
    have hh : fderiv ℝ X y =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U y)).comp D₂ :=
      mfderiv_eq_fderiv.symm.trans
        (mfderiv_comp y (hcy.mdifferentiableAt (by simp))
          (hUy.mdifferentiableAt (by simp)))
    rw [← hvalue'] at hh
    exact hh
  have hDFx : fderiv ℝ F x = (P.comp C).comp D₁ := by
    have hPF : HasFDerivAt F (P.comp (fderiv ℝ X x)) x :=
      P.hasFDerivAt.comp x hXx.hasFDerivAt
    calc
      fderiv ℝ F x = P.comp (fderiv ℝ X x) := hPF.fderiv
      _ = (P.comp C).comp D₁ := by rw [hDXx]; rfl
  have hi₂ : DifferentiableAt ℝ (fun z : ℂ => e.symm (ζ * z)) w :=
    hei₂.comp w ((differentiableAt_id : DifferentiableAt ℝ (id : ℂ → ℂ) w).const_mul ζ)
  have hroot₁ : HasFDerivAt (fun z => X (e.symm z)) ((C.comp D₁).comp R₁) w := by
    rw [← hDXx]
    exact hXx.hasFDerivAt.comp w hei₁.hasFDerivAt
  have hroot₂ : HasFDerivAt (fun z => X (e.symm (ζ * z))) ((C.comp D₂).comp R₂) w := by
    rw [← hDXy]
    exact hXy.hasFDerivAt.comp w hi₂.hasFDerivAt
  have hproj : ((P.comp C).comp D₁).comp R₁ = ((P.comp C).comp D₂).comp R₂ := by
    have h₁ : HasFDerivAt (fun z : ℂ => F (e.symm z))
        (((P.comp C).comp D₁).comp R₁) w :=
      P.hasFDerivAt.comp w hroot₁
    have h₂ : HasFDerivAt (fun z : ℂ => F (e.symm (ζ * z)))
        (((P.comp C).comp D₂).comp R₂) w :=
      P.hasFDerivAt.comp w hroot₂
    have hprojection' : (fun z : ℂ => F (e.symm z)) =ᶠ[𝓝 w]
        (fun z : ℂ => F (e.symm (ζ * z))) := hprojection
    exact h₁.fderiv.symm.trans (hprojection'.fderiv_eq.trans h₂.fderiv)
  have hPinv : ((P.comp C).comp D₁).IsInvertible := by
    rw [← hDFx]
    exact hreg
  have hsame := comp_eq_of_not_transverse_of_projection_eq
    D₁ D₂ (P.comp C) R₁ R₂ hd3 hPinv hnot hproj
  have h₁ := height.hasFDerivAt.comp w hroot₁
  have h₂ := height.hasFDerivAt.comp w hroot₂
  have hderivatives : height.comp ((C.comp D₁).comp R₁) =
      height.comp ((C.comp D₂).comp R₂) := by
    change height.comp (C.comp (D₁.comp R₁)) = height.comp (C.comp (D₂.comp R₂))
    rw [hsame]
  have hheight : HasFDerivAt
      (fun z : ℂ => height (X (e.symm z)) - height (X (e.symm (ζ * z))))
      (height.comp ((C.comp D₁).comp R₁) - height.comp ((C.comp D₂).comp R₂)) w :=
    h₁.sub h₂
  exact hheight.fderiv.trans (by rw [hderivatives, sub_self])


/-- The original disk cannot carry a regular radial zero arc of a nontrivial
deck-height difference. The radius-preserving slit map is constructed from
that literal arc, and its exact positive lip is used for the contradiction. -/
theorem IsMorreyDisk.not_regular_branched_height_zero_arc
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hd3 : Module.finrank ℝ E = 3)
    {Lq : ℝ≥0} (hqLip : ∀ z v, riemannianEDistOf g (q z) (q v) ≤
      (Lq : ℝ≥0∞) * edist z v)
    (p : M) (P : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ)
    (N : E) (lift : ℂ → E)
    (hsplit : ∀ v : E, v = lift (P v) + height v • N)
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (hea : e a = 0)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (heSource : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (hechart : ∀ z ∈ e.source, diskExtension q z ∈ (chartAt E p).source)
    (heForward : ContDiffOn ℝ ∞ (e : ℂ → ℂ) (e.source \ {a}))
    (heInverse : ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) (e.target \ {0}))
    (n : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζne : ζ ≠ 1) (hζpower : ζ ^ n = 1) :
    let U := diskExtension q
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => P (X z)
    (∀ z ∈ e.source, z ≠ a → (fderiv ℝ F z).IsInvertible) →
    (∀ w ∈ e.target, F (e.symm w) = F a + w ^ n / (n : ℂ)) →
    ∀ (α : ℝ → ℂ) (R : ℝ), 0 < R →
      Metric.closedBall (0 : ℂ) R ⊆ e.target →
      (∀ t ∈ Icc 0 R, ‖α t‖ = t) →
      (∃ L : ℝ≥0, LipschitzOnWith L α (Icc 0 R)) →
      ContDiffOn ℝ ∞ α (Ioo 0 R) →
      (∀ t ∈ Icc 0 R,
        height (X (e.symm (α t))) = height (X (e.symm (ζ * α t)))) →
      fderiv ℝ (fun z => height (X (e.symm z)) - height (X (e.symm (ζ * z))))
        (α (R / 16)) ≠ 0 → False := by
  intro U X F hreg hpower α R hR heBall hαnorm hαLip hαsmooth hαzero hαregular
  obtain ⟨h, hInv, Kc, _hformula, hh1, hhneg, hcircle, hhLip, hiLip⟩ :=
    Complex.exists_circle_straightening hζ hζne
  obtain ⟨L, hαLip⟩ := hαLip
  obtain ⟨S, hSsource, hStarget, _hSformula, _hSiformula, hSnorm,
    hSLipschitz, hSsmooth, hSismooth, _hSregular, haxis⟩ :=
    Planar.exists_radial_straightening hR hαnorm hαLip hαsmooth hh1 hhneg
      (fun z hz => ⟨(hcircle z hz).1, (hcircle z hz).2.1,
        (hcircle z hz).2.2.1, (hcircle z hz).2.2.2.1,
        (hcircle z hz).2.2.2.2.1, (hcircle z hz).2.2.2.2.2.1⟩) hhLip hiLip
  obtain ⟨K, J, hSLip, hSiLip⟩ := hSLipschitz
  have haxisPos (t : ℝ) (ht : t ∈ Icc 0 R) : S (t : ℂ) = α t :=
    (haxis t ht).1
  have haxisNeg (t : ℝ) (ht : t ∈ Icc 0 R) : S (-(t : ℂ)) = ζ * α t :=
    (haxis t ht).2
  have hαtarget (t : ℝ) (ht : t ∈ Icc 0 R) : α t ∈ e.target := by
    apply heBall
    simpa only [Metric.mem_closedBall, dist_zero_right, hαnorm t ht] using ht.2
  have hζαtarget (t : ℝ) (ht : t ∈ Icc 0 R) : ζ * α t ∈ e.target := by
    apply heBall
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_mul, hζ,
      one_mul, hαnorm t ht] using ht.2
  have hvalues (t : ℝ) (ht : t ∈ Icc 0 R) :
      U (e.symm (α t)) = U (e.symm (ζ * α t)) := by
    have hP : P (X (e.symm (α t))) = P (X (e.symm (ζ * α t))) := by
      change F (e.symm (α t)) = F (e.symm (ζ * α t))
      rw [hpower _ (hαtarget t ht), hpower _ (hζαtarget t ht),
        mul_pow, hζpower, one_mul]
    have hX : X (e.symm (α t)) = X (e.symm (ζ * α t)) := by
      calc
        X (e.symm (α t)) =
            lift (P (X (e.symm (α t)))) + height (X (e.symm (α t))) • N := hsplit _
        _ = lift (P (X (e.symm (ζ * α t)))) +
            height (X (e.symm (ζ * α t))) • N := by rw [hP, hαzero t ht]
        _ = X (e.symm (ζ * α t)) := (hsplit _).symm
    apply (extChartAt 𝓘(ℝ, E) p).injOn
    · simpa only [extChartAt_source] using hechart _ (e.map_target (hαtarget t ht))
    · simpa only [extChartAt_source] using hechart _ (e.map_target (hζαtarget t ht))
    · exact hX
  have hpair : ∀ t ∈ Icc (0 : ℝ) R,
      U (e.symm (S (t : ℂ))) = U (e.symm (S (-(t : ℂ)))) := by
    intro t ht
    rw [haxisPos t ht, haxisNeg t ht]
    exact hvalues t ht
  let r : ℝ := R / 16
  have hr : r ∈ Ioo 0 R := by dsimp [r]; constructor <;> linarith
  have hrclosed : r ∈ Icc 0 R := ⟨hr.1.le, hr.2.le⟩
  have hw : α r ∈ e.target := hαtarget r hrclosed
  have hζw : ζ * α r ∈ e.target := hζαtarget r hrclosed
  have hwne : α r ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hαnorm r hrclosed]
    exact hr.1.ne'
  have hζnezero : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζ]; exact one_ne_zero)
  have hζwne : ζ * α r ≠ 0 := mul_ne_zero hζnezero hwne
  have hoff {z : ℂ} (hz : z ∈ e.target) (hz0 : z ≠ 0) : e.symm z ≠ a := by
    intro hza
    have hh := e.right_inv hz
    rw [hza, hea] at hh
    exact hz0 hh.symm
  have hrank (z : ℂ) (hz : z ∈ e.target) (hz0 : z ≠ 0) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm z)) := by
    have hs := e.map_target hz
    have hU := hq.smoothInterior.contMDiffAt
      (Metric.isOpen_ball.mem_nhds (heSource hs))
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hechart _ hs)
    have hX : DifferentiableAt ℝ X (e.symm z) :=
      ((hc.comp _ hU).contDiffAt).differentiableAt (by simp)
    have hDX : fderiv ℝ X (e.symm z) =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U (e.symm z))).comp
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm z)) :=
      mfderiv_eq_fderiv.symm.trans
        (mfderiv_comp _ (hc.mdifferentiableAt (by simp)) (hU.mdifferentiableAt (by simp)))
    have hDF : fderiv ℝ F (e.symm z) = P.comp (fderiv ℝ X (e.symm z)) :=
      (P.hasFDerivAt.comp _ hX.hasFDerivAt).fderiv
    intro u v huv
    apply (hreg _ hs (hoff hz hz0)).injective
    rw [hDF, hDX]
    exact congrArg (fun y => P
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U (e.symm z)) y)) huv
  have hcr : (r : ℂ) = (R : ℂ) / (16 : ℂ) := by
    dsimp only [r]
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  have hSp : S ((R : ℂ) / (16 : ℂ)) = α r := by
    rw [← hcr]
    exact haxisPos r hrclosed
  have hSm : S (-((R : ℂ) / (16 : ℂ))) = ζ * α r := by
    rw [← hcr]
    exact haxisNeg r hrclosed
  have hp : e.symm (S ((R : ℂ) / (16 : ℂ))) = e.symm (α r) :=
    congrArg e.symm hSp
  have hm : e.symm (S (-((R : ℂ) / (16 : ℂ)))) = e.symm (ζ * α r) :=
    congrArg e.symm hSm
  have hrankp : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm (S ((R : ℂ) / (16 : ℂ))))) :=
    (congrArg (fun z : ℂ => Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) hp).mpr (hrank _ hw hwne)
  have hrankm : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm (S (-((R : ℂ) / (16 : ℂ)))))) :=
    (congrArg (fun z : ℂ => Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) hm).mpr (hrank _ hζw hζwne)
  have hnot := hq.not_transverse_of_actual_slit_straightening hd3 hqLip e S hR hea
    he hei heSource heBall heForward heInverse hSsource hStarget hSnorm
    hSLip hSiLip hSsmooth hSismooth hpair hrankp hrankm
  have hnot' : ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm (α r))).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U
          (e.symm (ζ * α r))))) := by
    have hnotU : ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U
          (e.symm (S ((R : ℂ) / (16 : ℂ))))).coprod
            (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U
              (e.symm (S (-((R : ℂ) / (16 : ℂ)))))))) := hnot
    rw [hp, hm] at hnotU
    exact hnotU
  have hei₁ : DifferentiableAt ℝ (e.symm : ℂ → ℂ) (α r) :=
    ((hei.contDiffAt (e.open_target.mem_nhds hw)).differentiableAt one_ne_zero)
  have hei₂ : DifferentiableAt ℝ (e.symm : ℂ → ℂ) (ζ * α r) :=
    ((hei.contDiffAt (e.open_target.mem_nhds hζw)).differentiableAt one_ne_zero)
  have hprojection : ∀ᶠ z in 𝓝 (α r), F (e.symm z) = F (e.symm (ζ * z)) := by
    have hrot : ContinuousAt (fun z : ℂ => ζ * z) (α r) :=
      continuousAt_const.mul continuousAt_id
    filter_upwards [e.open_target.mem_nhds hw,
      hrot (e.open_target.mem_nhds hζw)] with z hz hζz
    rw [hpower _ hz, hpower _ hζz, mul_pow, hζpower, one_mul]
  have hzero := hq.root_height_fderiv_eq_zero_of_not_transverse hd3 p P height e ζ (α r)
    hei₁ hei₂ (heSource (e.map_target hw)) (heSource (e.map_target hζw))
    (hechart _ (e.map_target hw)) (hvalues r hrclosed)
    (hreg _ (e.map_target hw) (hoff hw hwne)) hprojection hnot'
  exact hαregular hzero

end DifferentialGeometry.Geometry
