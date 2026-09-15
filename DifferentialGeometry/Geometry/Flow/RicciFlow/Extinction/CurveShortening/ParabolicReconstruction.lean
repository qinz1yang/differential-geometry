import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ChartEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicGaugeLocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.AlongCurve
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Retraction
import DifferentialGeometry.Topology.Manifold.OpenSubtypeModel
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype

noncomputable section
open Set Manifold Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem velocity_eq_parametric_acceleration_of_chart
    {g : ℝ → SmoothRiemannianMetric I M} {c : CurveMap M} {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (β : M) (x t : ℝ) (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t) (hchart : c.lift x t ∈ (extChartAt I β).source)
    (heq : HasDerivWithinAt (fun τ => extChartAt I β (c.lift x τ))
      (curveShorteningParametricChartRhs g β
        (t, extChartAt I β (c.lift x t), deriv (fun y => extChartAt I β (c.lift y t)) x,
          deriv (deriv (fun y => extChartAt I β (c.lift y t))) x)) J t) :
    c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  have htime := (c.time_slice_contMDiffWithinAt J hc x t ht).mdifferentiableWithinAt
    (by simp)
  have hsrc : c.lift x t ∈ (chartAt H β).source := by
    rwa [extChartAt_source] at hchart
  have hbridge := chartCoord_mfderivWithin_along_curve_eq_fderivWithin
    htime htime.continuousWithinAt hJ.uniqueMDiffWithinAt hsrc
  have hslice : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x :=
    ((c.space_slice_contMDiffWithinAt J hc x t ht).contMDiffAt
      (univ_mem : (univ : Set ℝ) ∈ 𝓝 x)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hrhs := trivToE_parametric_acceleration_eq_chart g c β x t hslice hchart
  have hvel : trivToE I β (c.lift x t) (c.velocity (I := I) J x t) =
      trivToE I β (c.lift x t) (c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t) := by
    rw [hrhs]
    exact hbridge.trans (heq.derivWithin hJ)
  have hb : c.lift x t ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
  have h := congrArg ((trivializationAt E (TangentSpace I) β).symmL ℝ (c.lift x t)) hvel
  simpa only [trivToE, (trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt hb] using h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set Manifold Function
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace K] {I' : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold I' ∞ N]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem speed_comp_of_inner_map
    {g : ℝ → SmoothRiemannianMetric I M} {g' : ℝ → SmoothRiemannianMetric I' N}
    {e : M → N} (he : ContMDiff I I' ∞ e)
    (hg : ∀ t p v w, (g' t).inner (e p) (mfderiv I I' e p v) (mfderiv I I' e p w) =
      (g t).inner p v w)
    {c : CurveMap M} {x t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x) :
    CurveMap.speed (I := I') (fun z τ => e (c z τ)) g' x t = c.speed g x t := by
  have hX : CurveMap.X (I := I') (fun z τ => e (c z τ)) x t =
      mfderiv I I' e (c.lift x t) (c.X (I := I) x t) := by
    exact mfderiv_comp_apply x (he.mdifferentiableAt (by simp)) hc 1
  simp only [CurveMap.speed, hX]
  exact congrArg Real.sqrt (hg t (c.lift x t) _ _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold I' ∞ N] in
theorem velocity_comp
    {e : M → N} (he : ContMDiff I I' ∞ e)
    {c : CurveMap M} {J : Set ℝ} {x t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) J t)
    (hJ : UniqueDiffWithinAt ℝ J t) :
    CurveMap.velocity (I := I') (fun z τ => e (c z τ)) J x t =
      mfderiv I I' e (c.lift x t) (c.velocity (I := I) J x t) := by
  have h := mfderiv_comp_mfderivWithin t (he.mdifferentiableAt (by simp)) hc
    hJ.uniqueMDiffWithinAt
  exact congrArg (fun L => L (1 : ℝ)) h

theorem Dx_X_comp_of_vanishingSecondFundamentalForm
    {g : ℝ → SmoothRiemannianMetric I M} {g' : ℝ → SmoothRiemannianMetric I' N}
    {e : M → N}
    (hII : ∀ t, hasVanishingSecondFundamentalFormAlongCurves (g t) (g' t) e)
    {c : CurveMap M} {t : ℝ} (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t))
    (x : ℝ) :
    CurveMap.Dx (I := I') (fun z τ => e (c z τ)) g' (CurveMap.X (I := I') (fun z τ => e (c z τ))) x t =
      mfderiv I I' e (c.lift x t) (c.Dx g c.X x t) := by
  exact (hII t).covariantAcceleration_comp (fun y => c.lift y t) x hc

theorem velocity_eq_parametric_acceleration_of_comp
    {g : ℝ → SmoothRiemannianMetric I M} {g' : ℝ → SmoothRiemannianMetric I' N}
    {e : M → N} (he : ContMDiff I I' ∞ e)
    (hg : ∀ t p v w, (g' t).inner (e p) (mfderiv I I' e p v) (mfderiv I I' e p w) =
      (g t).inner p v w)
    (hII : ∀ t, hasVanishingSecondFundamentalFormAlongCurves (g t) (g' t) e)
    {c : CurveMap M} {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    {x t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (heq : CurveMap.velocity (I := I') (fun z τ => e (c z τ)) J x t =
      CurveMap.speed (I := I') (fun z τ => e (c z τ)) g' x t ^ (-2 : ℤ) •
        CurveMap.Dx (I := I') (fun z τ => e (c z τ)) g'
          (CurveMap.X (I := I') (fun z τ => e (c z τ))) x t) :
    c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have htime := (c.time_slice_contMDiffWithinAt J hc x t ht).mdifferentiableWithinAt
    (by simp)
  have hinj : Function.Injective (mfderiv I I' e (c.lift x t)) := by
    intro v w hv
    by_contra hne
    have hpos := (g t).pos (c.lift x t) (v - w) (sub_ne_zero.mpr hne)
    have hz : mfderiv I I' e (c.lift x t) (v - w) = 0 := by
      rw [map_sub, hv, sub_self]
    rw [← hg t (c.lift x t) (v - w) (v - w), hz] at hpos
    simp only [map_zero, lt_self_iff_false] at hpos
  apply hinj
  rw [map_smul, ← Dx_X_comp_of_vanishingSecondFundamentalForm hII hs x,
    ← speed_comp_of_inner_map he hg (hs.mdifferentiableAt (by simp)),
    ← velocity_comp he htime hJ]
  exact heq

theorem velocity_eq_parametric_acceleration_of_eqOn
    {g : ℝ → SmoothRiemannianMetric I M} {c d : CurveMap M} {J : Set ℝ}
    (heq : ∀ z t, t ∈ J → c z t = d z t) {x t : ℝ} (ht : t ∈ J)
    (hd : d.velocity (I := I) J x t = d.speed g x t ^ (-2 : ℤ) • d.Dx g d.X x t) :
    c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  have htime : c.velocity (I := I) J x t = d.velocity (I := I) J x t := by
    unfold CurveMap.velocity
    have h := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := I)
      (f₁ := c.lift x) (f := d.lift x) (fun y hy => heq (x : AddCircle (1 : ℝ)) y hy) ht
    exact congrArg (fun L : ℝ →L[ℝ] E => L 1) h
  have hspace : (fun y => c.lift y t) = (fun y => d.lift y t) :=
    funext (fun y => heq _ t ht)
  have hX : ∀ y, c.X (I := I) y t = d.X (I := I) y t := by
    intro y
    unfold CurveMap.X
    rw [hspace]
    rfl
  have hs : c.speed g x t = d.speed g x t := by
    unfold CurveMap.speed
    rw [hX, show c.lift x t = d.lift x t from heq _ t ht]
  have ha : c.Dx g c.X x t = d.Dx g d.X x t := by
    unfold CurveMap.Dx
    rw [hspace]
    simp only [hX]
    rfl
  rw [htime, hs, ha]
  exact hd

theorem exists_parabolic_curve_of_retraction
    {g : ℝ → SmoothRiemannianMetric I M} {g' : ℝ → SmoothRiemannianMetric I' N}
    {e : M → N} (he : ContMDiff I I' ∞ e)
    {r : N → M} (hr : ContMDiff I' I ∞ r) (hleft : LeftInverse r e)
    (hg : ∀ t p v w, (g' t).inner (e p) (mfderiv I I' e p v) (mfderiv I I' e p w) =
      (g t).inner p v w)
    (hII : ∀ t, hasVanishingSecondFundamentalFormAlongCurves (g t) (g' t) e)
    {d : CurveMap N} {J : Set ℝ} (hd : d.SmoothOn (I := I') J)
    (hJ : UniqueDiffOn ℝ J) (hrange : ∀ z t, t ∈ J → d z t ∈ range e)
    (hpde : ∀ x t, t ∈ J → d.velocity (I := I') J x t =
      d.speed g' x t ^ (-2 : ℤ) • d.Dx g' d.X x t) :
    ∃ c : CurveMap M, c.SmoothOn (I := I) J ∧
      (∀ z t, t ∈ J → e (c z t) = d z t) ∧
      ∀ x t, t ∈ J → c.velocity (I := I) J x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  let c : CurveMap M := fun z t => r (d z t)
  have hc : c.SmoothOn (I := I) J := hr.comp_contMDiffOn hd
  have hagree : ∀ z t, t ∈ J → e (c z t) = d z t := by
    intro z t ht
    obtain ⟨p, hp⟩ := hrange z t ht
    change e (r (d z t)) = d z t
    rw [← hp, hleft p]
  refine ⟨c, hc, hagree, ?_⟩
  intro x t ht
  apply velocity_eq_parametric_acceleration_of_comp he hg hII hc ht (hJ t ht)
  exact velocity_eq_parametric_acceleration_of_eqOn hagree ht (hpde x t ht)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set Manifold Function
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_parabolic_curve_of_retractionMetric
    (g : ℝ → SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p)
    {d : CurveMap U} {J : Set ℝ} (hd : d.SmoothOn (I := 𝓘(ℝ, F)) J)
    (hJ : UniqueDiffOn ℝ J) (hrange : ∀ z t, t ∈ J → (d z t : F) ∈ range e)
    (hpde : ∀ x t, t ∈ J → d.velocity (I := 𝓘(ℝ, F)) J x t =
      d.speed (fun t => retractionMetric (g t) he hr) x t ^ (-2 : ℤ) •
        d.Dx (fun t => retractionMetric (g t) he hr) d.X x t) :
    ∃ c : CurveMap M, c.SmoothOn (I := I) J ∧
      (∀ z t, t ∈ J → e (c z t) = (d z t : F)) ∧
      ∀ x t, t ∈ J → c.velocity (I := I) J x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  let j : M → U := fun p => ⟨e p, hEU (mem_range_self p)⟩
  have hj : ContMDiff I 𝓘(ℝ, F) ∞ j := (ContMDiff.subtypeVal_comp_iff U j).mp he
  have hr' : ContMDiff 𝓘(ℝ, F) I ∞ (fun p : U => r p) :=
    hr.comp_contMDiff contMDiff_subtype_val (fun x => x.2)
  have hmetric : ∀ t p v w,
      (retractionMetric (g t) he hr).inner (j p)
        (mfderiv I 𝓘(ℝ, F) j p v) (mfderiv I 𝓘(ℝ, F) j p w) = (g t).inner p v w := by
    intro t p v w
    rw [← mfderiv_subtypeVal_comp j p]
    exact retractionMetric_inner_map (g t) he hr hEU hleft p v w
  have hrange' : ∀ z t, t ∈ J → d z t ∈ range j := by
    intro z t ht
    obtain ⟨p, hp⟩ := hrange z t ht
    exact ⟨p, Subtype.ext hp⟩
  obtain ⟨c, hc, hce, hp⟩ := exists_parabolic_curve_of_retraction hj hr' hleft hmetric
    (fun t => hasVanishingSecondFundamentalFormAlongCurves_retractionMetric (g t) he hr hEU hleft)
    hd hJ hrange' hpde
  exact ⟨c, hc, fun z t ht => congrArg Subtype.val (hce z t ht), hp⟩

theorem exists_parabolic_curve_of_classical_retraction_equation
    (g : ℝ → SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (u : CurveMap F) {J : Set ℝ} (hu : u.SmoothOn (I := 𝓘(ℝ, F)) J)
    (hJ : UniqueDiffOn ℝ J) (hrange : ∀ z t, t ∈ J → u z t ∈ range e)
    (hpde : ∀ x t, t ∈ J → HasDerivWithinAt (u.lift x)
      (curveShorteningParametricChartRhs (fun t => retractionMetric (g t) he hr) β
        (t, u.lift x t, deriv (fun y => u.lift y t) x,
          deriv (deriv (fun y => u.lift y t)) x)) J t) :
    ∃ c : CurveMap M, c.SmoothOn (I := I) J ∧
      (∀ z t, t ∈ J → e (c z t) = u z t) ∧
      ∀ x t, t ∈ J → c.velocity (I := I) J x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  classical
  let d : CurveMap U := fun z t => if ht : t ∈ J then ⟨u z t, hEU (hrange z t ht)⟩ else β
  have hdu : ∀ z t, t ∈ J → (d z t : F) = u z t := by
    intro z t ht
    simp only [d, dif_pos ht]
  have hd : d.SmoothOn (I := 𝓘(ℝ, F)) J := by
    apply (DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff U
      (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ J)).mp
    exact hu.congr (fun p hp => hdu _ _ hp.2)
  have hdeq : ∀ x t, t ∈ J → d.velocity (I := 𝓘(ℝ, F)) J x t =
      d.speed (fun t => retractionMetric (g t) he hr) x t ^ (-2 : ℤ) •
        d.Dx (fun t => retractionMetric (g t) he hr) d.X x t := by
    intro x t ht
    apply velocity_eq_parametric_acceleration_of_chart hd β x t ht (hJ t ht)
      (by rw [DifferentialGeometry.extChartAt_opens_source]; trivial)
    have hspace : (fun y => extChartAt 𝓘(ℝ, F) β (d.lift y t)) =
        (fun y => u.lift y t) := by
      funext y
      rw [DifferentialGeometry.extChartAt_opens_apply]
      exact hdu _ _ ht
    rw [hspace, show extChartAt 𝓘(ℝ, F) β (d.lift x t) = u.lift x t from congrFun hspace x]
    apply (hpde x t ht).congr
    · intro τ hτ
      rw [DifferentialGeometry.extChartAt_opens_apply]
      exact hdu _ _ hτ
    · rw [DifferentialGeometry.extChartAt_opens_apply]
      exact hdu _ _ ht
  obtain ⟨c, hc, hce, hcpde⟩ := exists_parabolic_curve_of_retractionMetric g he hr hEU hleft
    hd hJ (fun z t ht => by rw [hdu _ _ ht]; exact hrange z t ht) hdeq
  exact ⟨c, hc, fun z t ht => (hce z t ht).trans (hdu z t ht), hcpde⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} {a b : ℝ}

theorem curveShorteningParabolicGaugeLocalExistence_of_classical_retraction_equation
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (h : ∀ t₀ ∈ Ico a b, ∀ c₀ : SmoothImmersion (I := I) (M := M),
      ∃ τ : ℝ, 0 < τ ∧ t₀ + τ ≤ b ∧ ∃ u : CurveMap F,
        u.SmoothOn (I := 𝓘(ℝ, F)) (Icc t₀ (t₀ + τ)) ∧
        (∀ z, u z t₀ = e (c₀.map z)) ∧
        (∀ z t, t ∈ Icc t₀ (t₀ + τ) → u z t ∈ range e) ∧
        ∀ x t, t ∈ Icc t₀ (t₀ + τ) → HasDerivWithinAt (u.lift x)
          (curveShorteningParametricChartRhs
            (fun t => retractionMetric (B.family.metric t) he hr) β
            (t, u.lift x t, deriv (fun y => u.lift y t) x,
              deriv (deriv (fun y => u.lift y t)) x)) (Icc t₀ (t₀ + τ)) t) :
    curveShorteningParabolicGaugeLocalExistence (I := I) (M := M) B := by
  apply curveShorteningParabolicGaugeLocalExistence_of_parabolic_equation B
  intro t₀ ht₀ c₀
  obtain ⟨τ, hτ, hτb, u, hu, hinit, hrange, hpde⟩ := h t₀ ht₀ c₀
  obtain ⟨c, hc, hcu, hcpde⟩ := CurveMap.exists_parabolic_curve_of_classical_retraction_equation
    B.family.metric he hr hEU hleft β u hu
      (uniqueDiffOn_Icc (by linarith : t₀ < t₀ + τ)) hrange hpde
  refine ⟨τ, hτ, hτb, c, hc, ?_, hcpde⟩
  intro z
  apply (show Function.LeftInverse r e from hleft).injective
  exact (hcu z t₀ ⟨le_rfl, by linarith⟩).trans (hinit z)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
