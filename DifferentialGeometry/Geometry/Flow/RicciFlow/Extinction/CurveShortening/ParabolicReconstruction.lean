import DifferentialGeometry.Analysis.Parabolic.Euclidean.InvariantSubmanifold
import DifferentialGeometry.Geometry.Metric.Family.Retraction
import DifferentialGeometry.Analysis.Parabolic.Euclidean.PeriodicPersistence
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ChartEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicGaugeLocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.AlongCurve
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
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


theorem velocity_eq_parametric_acceleration_of_chart_of_contMDiffAt
    {g : ℝ → SmoothRiemannianMetric I M} {c : CurveMap M} {J : Set ℝ}
    (β : M) (x t : ℝ)
    (htime : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) J t)
    (hslice : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x)
    (hJ : UniqueDiffWithinAt ℝ J t) (hchart : c.lift x t ∈ (extChartAt I β).source)
    (heq : HasDerivWithinAt (fun τ => extChartAt I β (c.lift x τ))
      (curveShorteningParametricChartRhs g β
        (t, extChartAt I β (c.lift x t), deriv (fun y => extChartAt I β (c.lift y t)) x,
          deriv (deriv (fun y => extChartAt I β (c.lift y t))) x)) J t) :
    c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  have hsrc : c.lift x t ∈ (chartAt H β).source := by
    rwa [extChartAt_source] at hchart
  have hbridge := chartCoord_mfderivWithin_along_curve_eq_fderivWithin
    htime htime.continuousWithinAt hJ.uniqueMDiffWithinAt hsrc
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


theorem velocity_eq_parametric_acceleration_of_comp_of_contMDiffAt [I.Boundaryless]
    {g : ℝ → SmoothRiemannianMetric I M} {g' : ℝ → SmoothRiemannianMetric I' N}
    {e : M → N} (he : ContMDiff I I' ∞ e)
    (hg : ∀ t p v w, (g' t).inner (e p) (mfderiv I I' e p v) (mfderiv I I' e p w) =
      (g t).inner p v w)
    (hII : ∀ t, hasVanishingSecondFundamentalFormAlongCurves (g t) (g' t) e)
    {c : CurveMap M} {J : Set ℝ} {x t : ℝ}
    (htime : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) J t)
    (hs : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x) (hJ : UniqueDiffWithinAt ℝ J t)
    (heq : CurveMap.velocity (I := I') (fun z τ => e (c z τ)) J x t =
      CurveMap.speed (I := I') (fun z τ => e (c z τ)) g' x t ^ (-2 : ℤ) •
        CurveMap.Dx (I := I') (fun z τ => e (c z τ)) g'
          (CurveMap.X (I := I') (fun z τ => e (c z τ))) x t) :
    c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  have hinj : Function.Injective (mfderiv I I' e (c.lift x t)) := by
    intro v w hv
    by_contra hne
    have hpos := (g t).pos (c.lift x t) (v - w) (sub_ne_zero.mpr hne)
    have hz : mfderiv I I' e (c.lift x t) (v - w) = 0 := by
      rw [map_sub, hv, sub_self]
    rw [← hg t (c.lift x t) (v - w) (v - w), hz] at hpos
    simp only [map_zero, lt_self_iff_false] at hpos
  have hacc : CurveMap.Dx (I := I') (fun z τ => e (c z τ)) g'
      (CurveMap.X (I := I') (fun z τ => e (c z τ))) x t =
      mfderiv I I' e (c.lift x t) (c.Dx g c.X x t) :=
    (hII t).covariantAcceleration_comp_of_contMDiffAt he (fun y => c.lift y t) x hs
  apply hinj
  rw [map_smul, ← hacc,
    ← speed_comp_of_inner_map he hg (hs.mdifferentiableAt (by norm_num)),
    ← velocity_comp he htime hJ]
  exact heq




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

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Parabolic

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem periodic_mem_range_of_retraction_equation
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (hg : MetricFamilySmoothOn D g)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {O : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r O)
    (hEO : range e ⊆ O) (hleft : ∀ p, r (e p) = p) (β : O)
    {u : ℝ → ℝ → F} {T : ℝ} (hT : 0 < T)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc 0 T))
    (hinit : ∀ x, u x 0 ∈ range e)
    (hx : ∀ x t, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun y => u y t) x)
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (Icc 0 1 ×ˢ Icc 0 T))
    (hjet : ∀ x t, t ∈ Icc 0 T →
      (t, u x t, deriv (fun y => u y t) x) ∈
        curveShorteningChartFirstJetDomain D (fun t => retractionMetric (g t) he hr) β)
    (hprojected : ∀ x t, t ∈ Icc 0 T →
      (t, e (r (u x t)), fderiv ℝ (fun y => e (r y)) (u x t)
        (deriv (fun y => u y t) x)) ∈
        curveShorteningChartFirstJetDomain D (fun t => retractionMetric (g t) he hr) β)
    (hpde : ∀ x t, t ∈ Ioo 0 T → HasDerivAt (u x)
      (curveShorteningParametricChartRhs (fun t => retractionMetric (g t) he hr) β
        (t, u x t, deriv (fun y => u y t) x,
          deriv (deriv (fun y => u y t)) x)) t) :
    ∀ x t, t ∈ Icc 0 T → u x t ∈ range e := by
  let G := fun t => retractionMetric (g t) he hr
  let j : M → O := fun p => ⟨e p, hEO (mem_range_self p)⟩
  let U := curveShorteningChartFirstJetDomain D G β
  let a := curveShorteningChartDiffusionCoefficient G β
  have hG : MetricFamilySmoothOn D G := metricFamilySmoothOn_retractionMetric g hg he hr
  have hj : ContMDiff I 𝓘(ℝ, F) ∞ j := (ContMDiff.subtypeVal_comp_iff O j).mp he
  have hgeo : ∀ t ∈ D.regular, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) j :=
    fun t _ => hasVanishingSecondFundamentalFormAlongCurves_retractionMetric (g t) he hr hEO hleft
  have hU : IsOpen U := isOpen_curveShorteningChartFirstJetDomain hG β
  have ha : ContDiffOn ℝ 1 a U :=
    (contDiffOn_curveShorteningChartDiffusionCoefficient hG β).of_le (by norm_num)
  have hUJO : U ⊆ D.regular ×ˢ (O : Set F) ×ˢ univ := by
    intro q hq
    refine ⟨hq.1, ?_, mem_univ _⟩
    simpa only [DifferentialGeometry.extChartAt_opens_target, O.isOpen.interior_eq] using hq.2.1
  let K := (fun p : ℝ × ℝ => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)) ''
    (univ ×ˢ Icc 0 T)
  have hK : IsCompact K := isCompact_image_firstJet_of_periodic hper hcont hDu
  have hKU : K ⊆ U := by
    rintro q ⟨⟨x, t⟩, hxt, rfl⟩
    exact hjet x t hxt.2
  obtain ⟨δ, hδ, hδa⟩ := hK.exists_forall_le' (ha.continuousOn.mono hKU)
    (fun q hq => curveShorteningChartDiffusionCoefficient_pos G β (hKU hq))
  apply periodic_mem_range_of_christoffel_parabolic_equation_on_open_set_of_continuous_deriv
    g G β hG hj hgeo (fun p => hleft p) hU Subset.rfl O.isOpen Subset.rfl
    (hr.of_le (by decide : (3 : ℕ∞ω) ≤ ∞)) ha hUJO hT hδ hper hcont hinit hx (fun x t ht => (hpde x t ht).differentiableAt) hDu hjet hprojected
  · intro x t ht'
    exact hδa _ ⟨(x, t), ⟨mem_univ _, ht'⟩, rfl⟩
  · intro x t ht'
    rw [(hpde x t ht').deriv]
    change a _ • _ + a _ • _ - a _ • _ = a _ • _
    abel

private theorem exists_pos_periodic_mem_range_of_retraction_equation
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (hg : MetricFamilySmoothOn D g)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {O : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r O)
    (hEO : range e ⊆ O) (hleft : ∀ p, r (e p) = p) (β : O)
    {u : ℝ → ℝ → F} {T : ℝ} (hT : 0 < T)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc 0 T))
    (hinit : ∀ x, u x 0 ∈ range e)
    (hx : ∀ x t, t ∈ Icc 0 T → ContDiffAt ℝ 2 (fun y => u y t) x)
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (Icc 0 1 ×ˢ Icc 0 T))
    (hjet : ∀ x,
      (0, u x 0, deriv (fun y => u y 0) x) ∈
        curveShorteningChartFirstJetDomain D (fun t => retractionMetric (g t) he hr) β)
    (hpde : ∀ x t, t ∈ Icc 0 T → HasDerivWithinAt (u x)
      (curveShorteningParametricChartRhs (fun t => retractionMetric (g t) he hr) β
        (t, u x t, deriv (fun y => u y t) x,
          deriv (deriv (fun y => u y t)) x)) (Icc 0 T) t) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ T ∧ ∀ x t, t ∈ Icc 0 ε → u x t ∈ range e := by
  let G := fun t => retractionMetric (g t) he hr
  let U := curveShorteningChartFirstJetDomain D G β
  have hG : MetricFamilySmoothOn D G := metricFamilySmoothOn_retractionMetric g hg he hr
  have hU : IsOpen U := isOpen_curveShorteningChartFirstJetDomain hG β
  have hP : ContDiffOn ℝ 1 (fun y => e (r y)) O :=
    (he.comp_contMDiffOn hr).contDiffOn.of_le (by norm_num)
  have hUV : ∀ q ∈ U, q.2.1 ∈ (O : Set F) := by
    intro q hq
    simpa only [DifferentialGeometry.extChartAt_opens_target, O.isOpen.interior_eq] using hq.2.1
  have hfix : ∀ x, e (r (u x 0)) = u x 0 := by
    intro x
    obtain ⟨p, hp⟩ := hinit x
    rw [← hp, hleft]
  obtain ⟨ε, hε, hεT, hK, hKsub⟩ := exists_isCompact_firstJet_image_subset_of_initial_curve_fixed
    hT hper hcont hDu hU O.isOpen hP hUV
    (fun x _ => hjet x) hfix
    (fun x _ => (hx x 0 ⟨le_rfl, hT.le⟩).differentiableAt (by norm_num))
  simp only [sub_zero, zero_add] at hεT hK hKsub
  have hsub : Icc (0 : ℝ) ε ⊆ Icc 0 T := Icc_subset_Icc le_rfl hεT
  refine ⟨ε, hε, hεT, ?_⟩
  apply periodic_mem_range_of_retraction_equation g hg he hr hEO hleft β hε hper
    (hcont.mono (prod_mono Subset.rfl hsub)) hinit
    (fun x t ht => hx x t (hsub ⟨ht.1.le, ht.2.le⟩))
    (hDu.mono (prod_mono Subset.rfl hsub))
    (fun x t ht => (hKsub ⟨(x, t), ⟨mem_univ _, ht⟩, rfl⟩).1)
  · intro x t ht
    exact (hKsub ⟨(x, t), ⟨mem_univ _, ht⟩, rfl⟩).2
  · intro x t ht
    have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht.1, ht.2.trans_le hεT⟩
    exact (hpde x t ⟨htT.1.le, htT.2.le⟩).hasDerivAt (Icc_mem_nhds htT.1 htT.2)

theorem CurveMap.exists_parabolic_curve_on_short_interval_of_classical_retraction_equation
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (hg : MetricFamilySmoothOn D g)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {O : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r O)
    (hEO : range e ⊆ O) (hleft : ∀ p, r (e p) = p) (β : O)
    (u : CurveMap F) {T : ℝ} (hT : 0 < T)
    (hu : u.SmoothOn (I := 𝓘(ℝ, F)) (Icc 0 T))
    (hinit : ∀ z, u z 0 ∈ range e)
    (hjet : ∀ x,
      (0, u.lift x 0, deriv (fun y => u.lift y 0) x) ∈
        curveShorteningChartFirstJetDomain D (fun t => retractionMetric (g t) he hr) β)
    (hpde : ∀ x t, t ∈ Icc 0 T → HasDerivWithinAt (u.lift x)
      (curveShorteningParametricChartRhs (fun t => retractionMetric (g t) he hr) β
        (t, u.lift x t, deriv (fun y => u.lift y t) x,
          deriv (deriv (fun y => u.lift y t)) x)) (Icc 0 T) t) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ T ∧ ∃ c : CurveMap M,
      c.SmoothOn (I := I) (Icc 0 ε) ∧
      (∀ z t, t ∈ Icc 0 ε → e (c z t) = u z t) ∧
      ∀ x t, t ∈ Icc 0 ε → c.velocity (I := I) (Icc 0 ε) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry u.lift) (univ ×ˢ Icc 0 T) :=
    hu.contDiffOn
  have hcont : ContinuousOn (Function.uncurry u.lift) (Icc 0 1 ×ˢ Icc 0 T) :=
    hsmooth.continuousOn.mono (prod_mono (subset_univ _) Subset.rfl)
  have hx : ∀ x t, t ∈ Icc 0 T → ContDiffAt ℝ 2 (fun y => u.lift y t) x := by
    intro x t ht
    have hs : ContDiff ℝ ∞ (fun y => u.lift y t) := contDiffOn_univ.mp
      (hsmooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun _ hy => ⟨hy, ht⟩))
    exact hs.contDiffAt.of_le (by decide)
  have hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u.lift y p.2) p.1)
      (Icc 0 1 ×ˢ Icc 0 T) :=
    (DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ
      (uniqueDiffOn_Icc hT) hsmooth).continuousOn.mono
        (prod_mono (subset_univ _) Subset.rfl)
  have hper : ∀ x t, u.lift (x + 1) t = u.lift x t := by
    intro x t
    simp only [CurveMap.lift, AddCircle.coe_add_period]
  obtain ⟨ε, hε, hεT, hrange⟩ := exists_pos_periodic_mem_range_of_retraction_equation
    g hg he hr hEO hleft β hT hper hcont
    (fun x => hinit (x : AddCircle (1 : ℝ))) hx hDu hjet hpde
  have hsub : Icc (0 : ℝ) ε ⊆ Icc 0 T := Icc_subset_Icc le_rfl hεT
  have hur : u.SmoothOn (I := 𝓘(ℝ, F)) (Icc 0 ε) :=
    hu.mono (prod_mono Subset.rfl hsub)
  refine ⟨ε, hε, hεT, ?_⟩
  apply CurveMap.exists_parabolic_curve_of_classical_retraction_equation
    g he hr hEO hleft β u hur (uniqueDiffOn_Icc hε)
  · intro z t ht
    induction z using QuotientAddGroup.induction_on with
    | H x => exact hrange x t ht
  · intro x t ht
    exact (hpde x t (hsub ht)).mono hsub

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

noncomputable section

open Set Manifold
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Parabolic

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem periodic_mem_range_of_retraction_equation_of_firstJet_mem
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {O : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r O)
    (hG : MetricFamilySmoothOn D (fun t => retractionMetric (g t) he hr))
    (hEO : range e ⊆ O) (hleft : ∀ p, r (e p) = p) (β : O)
    {u : ℝ → ℝ → F} {T : ℝ} (hT : 0 < T)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc 0 T))
    (hinit : ∀ x, u x 0 ∈ range e)
    (hx : ∀ x t, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun y => u y t) x)
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (Icc 0 1 ×ˢ Icc 0 T))
    (hjet : ∀ x t, t ∈ Icc 0 T →
      (t, u x t, deriv (fun y => u y t) x) ∈
        curveShorteningChartFirstJetDomain D (fun t => retractionMetric (g t) he hr) β)
    (hpde : ∀ x t, t ∈ Ioo 0 T → HasDerivAt (u x)
      (curveShorteningParametricChartRhs (fun t => retractionMetric (g t) he hr) β
        (t, u x t, deriv (fun y => u y t) x,
          deriv (deriv (fun y => u y t)) x)) t) :
    ∀ x t, t ∈ Icc 0 T → u x t ∈ range e := by
  let G := fun t => retractionMetric (g t) he hr
  let j : M → O := fun p => ⟨e p, hEO (mem_range_self p)⟩
  let U := curveShorteningChartFirstJetDomain D G β
  let a := curveShorteningChartDiffusionCoefficient G β
  have hj : ContMDiff I 𝓘(ℝ, F) ∞ j := (ContMDiff.subtypeVal_comp_iff O j).mp he
  have hgeo : ∀ t ∈ D.regular, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) j :=
    fun t _ => hasVanishingSecondFundamentalFormAlongCurves_retractionMetric (g t) he hr hEO hleft
  have ha : ContinuousOn a U := (contDiffOn_curveShorteningChartDiffusionCoefficient hG β).continuousOn
  let K := (fun p : ℝ × ℝ => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)) ''
    (univ ×ˢ Icc 0 T)
  have hK : IsCompact K := isCompact_image_firstJet_of_periodic hper hcont hDu
  have hKU : K ⊆ U := by
    rintro q ⟨⟨x, t⟩, hxt, rfl⟩
    exact hjet x t hxt.2
  obtain ⟨δ, hδ, hδa⟩ := hK.exists_forall_le' (ha.mono hKU)
    (fun q hq => curveShorteningChartDiffusionCoefficient_pos G β (hKU hq))
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (ha.mono hKU)
  let A₀ : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  apply periodic_mem_range_of_scaled_christoffel_equation g G β hG hj hgeo
    (fun p => hleft p) D.regular_isOpen Subset.rfl O.isOpen Subset.rfl
    (hr.of_le (by decide : (3 : ℕ∞ω) ≤ ∞)) hEO A₀ hT hδ hper hcont hinit hx
    (fun x t ht => (hpde x t ht).differentiableAt) hDu
  · intro t ht
    exact (hjet 0 t ht).1
  · intro x t ht
    simpa only [DifferentialGeometry.extChartAt_opens_target, O.isOpen.interior_eq] using
      (hjet x t ht).2.1
  · intro x t ht
    exact hδa _ ⟨(x, t), ⟨mem_univ _, ht.1.le, ht.2.le⟩, rfl⟩
  · intro x t ht
    calc
      _ ≤ |a (t, u x t, deriv (fun y => u y t) x)| := le_abs_self _
      _ = ‖a (t, u x t, deriv (fun y => u y t) x)‖ := (Real.norm_eq_abs _).symm
      _ ≤ A := hA _ ⟨(x, t), ⟨mem_univ _, ht.1.le, ht.2.le⟩, rfl⟩
      _ ≤ A₀ := le_max_left _ _
  · intro x t ht
    rw [(hpde x t ht).deriv]
    change a _ • _ + a _ • _ = a _ • (_ + _)
    exact (smul_add _ _ _).symm


theorem CurveMap.exists_parabolic_curve_of_classical_retraction_equation_of_firstJet_mem
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (hg : MetricFamilySmoothOn D g)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {O : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r O)
    (hEO : range e ⊆ O) (hleft : ∀ p, r (e p) = p) (β : O)
    (u : CurveMap F) {T : ℝ} (hT : 0 < T)
    (hu : u.SmoothOn (I := 𝓘(ℝ, F)) (Icc 0 T))
    (hinit : ∀ z, u z 0 ∈ range e)
    (hjet : ∀ x t, t ∈ Icc 0 T →
      (t, u.lift x t, deriv (fun y => u.lift y t) x) ∈
        curveShorteningChartFirstJetDomain D (fun t => retractionMetric (g t) he hr) β)
    (hpde : ∀ x t, t ∈ Icc 0 T → HasDerivWithinAt (u.lift x)
      (curveShorteningParametricChartRhs (fun t => retractionMetric (g t) he hr) β
        (t, u.lift x t, deriv (fun y => u.lift y t) x,
          deriv (deriv (fun y => u.lift y t)) x)) (Icc 0 T) t) :
    ∃ c : CurveMap M,
      c.SmoothOn (I := I) (Icc 0 T) ∧
      (∀ z t, t ∈ Icc 0 T → e (c z t) = u z t) ∧
      ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry u.lift) (univ ×ˢ Icc 0 T) :=
    hu.contDiffOn
  have hcont : ContinuousOn (Function.uncurry u.lift) (Icc 0 1 ×ˢ Icc 0 T) :=
    hsmooth.continuousOn.mono (prod_mono (subset_univ _) Subset.rfl)
  have hx : ∀ x t, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun y => u.lift y t) x := by
    intro x t ht
    have hs : ContDiff ℝ ∞ (fun y => u.lift y t) := contDiffOn_univ.mp
      (hsmooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun _ hy => ⟨hy, ht.1.le, ht.2.le⟩))
    exact hs.contDiffAt.of_le (by decide)
  have hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u.lift y p.2) p.1)
      (Icc 0 1 ×ˢ Icc 0 T) :=
    (DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ
      (uniqueDiffOn_Icc hT) hsmooth).continuousOn.mono
        (prod_mono (subset_univ _) Subset.rfl)
  have hper : ∀ x t, u.lift (x + 1) t = u.lift x t := by
    intro x t
    simp only [CurveMap.lift, AddCircle.coe_add_period]
  have hG := metricFamilySmoothOn_retractionMetric g hg he hr
  have hrange := periodic_mem_range_of_retraction_equation_of_firstJet_mem
    g he hr hG hEO hleft β hT hper hcont (fun x => hinit (x : AddCircle (1 : ℝ)))
    hx hDu hjet (fun x t ht =>
      (hpde x t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  apply CurveMap.exists_parabolic_curve_of_classical_retraction_equation
    g he hr hEO hleft β u hu (uniqueDiffOn_Icc hT)
  · intro z t ht
    induction z using QuotientAddGroup.induction_on with
    | H x => exact hrange x t ht
  · exact hpde

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
