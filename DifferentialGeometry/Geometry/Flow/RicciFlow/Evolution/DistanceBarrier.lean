import DifferentialGeometry.Geometry.Comparison.DistanceCalabi
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.Variation.SpeedDerivative
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.MetricTimeCompare
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.ScalarWeak

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Calabi upper supports for evolving Riemannian distance

This module owns the genuinely analytic geometry in the complete-noncompact
Shi route.  Its endpoint constructs a smooth spacetime upper support for the
positively rescaled Riemannian distance at one selected positive-time point.
The support is local; no global smoothness across the cut locus is asserted.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
  [SigmaCompactSpace M] [T2Space M]

/-- The time derivative of the length of a fixed regular path under Ricci flow.

Only the metric evolves: the path and its velocity are held fixed.  The
Ricci-flow equation differentiates the squared speed, the square-root chain
rule differentiates the speed, and compactness of the parameter interval
justifies differentiation under the interval integral. -/
theorem pathLength_timeDeriv_of_ricciFlow
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b t : Real}
    (hab : a ≤ b)
    (ht : t ∈ D.regular)
    (γ : Real → M)
    (hγ : ContMDiff 𝓘(Real, Real) I 1 γ)
    (hvel : ∀ u ∈ Set.Icc a b,
      mfderiv 𝓘(Real, Real) I γ u (1 : Real) ≠ 0) :
    HasDerivAt
      (fun s =>
        Variation.arcLength (I := I) (S.base.metric s) γ a b)
      (∫ u in a..b,
        -ricciTensor (I := I) (S.base.metric t) (γ u)
            (mfderiv 𝓘(Real, Real) I γ u (1 : Real))
            (mfderiv 𝓘(Real, Real) I γ u (1 : Real)) /
          Real.sqrt ((S.base.metric t).inner (γ u)
            (mfderiv 𝓘(Real, Real) I γ u (1 : Real))
            (mfderiv 𝓘(Real, Real) I γ u (1 : Real))))
      t := by
  classical
  let v : (u : Real) → TangentSpace I (γ u) :=
    fun u => mfderiv 𝓘(Real, Real) I γ u (1 : Real)
  let G : Real → Real → Real :=
    fun s u => (S.base.metric s).inner (γ u) (v u) (v u)
  let Ric : Real → Real → Real :=
    fun s u => ricciTensor (I := I) (S.base.metric s) (γ u) (v u) (v u)
  let F : Real → Real → Real := fun s u => Real.sqrt (G s u)
  let F' : Real → Real → Real :=
    fun s u => ((-2 : Real) * Ric s u) / (2 * Real.sqrt (G s u))
  obtain ⟨α, β, htIoo, hwin⟩ := D.exists_Icc_regular ht
  have hαβ : α ≤ β := (htIoo.1.trans htIoo.2).le
  let Kset : Set (Real × Real) := Set.Icc α β ×ˢ Set.Icc a b
  have hvLift : Continuous (fun u : Real =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) (γ u) (v u)) := by
    have h :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M)
        (γ := γ) (by norm_num) hγ
    simpa only [v, tangentMap] using h
  have hGcontOn :
      ContinuousOn (fun p : Real × Real => G p.1 p.2) Kset := by
    rw [continuousOn_iff_continuous_restrict]
    have htime : Continuous (fun q : ↥Kset => ((q : Real × Real).1)) :=
      continuous_fst.comp continuous_subtype_val
    have hparam : Continuous (fun q : ↥Kset => ((q : Real × Real).2)) :=
      continuous_snd.comp continuous_subtype_val
    have hbase : Continuous (fun q : ↥Kset => γ ((q : Real × Real).2)) :=
      hγ.continuous.comp hparam
    have hvec : ∀ _i : Fin 2, Continuous (fun q : ↥Kset =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y)
          (γ ((q : Real × Real).2)) (v ((q : Real × Real).2))) :=
      fun _i => hvLift.comp hparam
    have heval :=
      hS.smoothMetric.metricTensor_cont.eval_continuous
        (P := ↥Kset)
        (τ := fun q => ((q : Real × Real).1))
        (b := fun q => γ ((q : Real × Real).2))
        htime
        (fun q => D.regular_subset (hwin q.2.1))
        hbase
        (v := fun _i q => v ((q : Real × Real).2))
        hvec
    refine heval.congr (fun q => ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    rfl
  have hRicAtContOn :
      ContinuousOn
        (fun p : Real × Real =>
          S.ricciAt p.1 (γ p.2) (vec2 (I := I) (v p.2) (v p.2)))
        Kset := by
    rw [continuousOn_iff_continuous_restrict]
    have htime : Continuous (fun q : ↥Kset => ((q : Real × Real).1)) :=
      continuous_fst.comp continuous_subtype_val
    have hparam : Continuous (fun q : ↥Kset => ((q : Real × Real).2)) :=
      continuous_snd.comp continuous_subtype_val
    have hbase : Continuous (fun q : ↥Kset => γ ((q : Real × Real).2)) :=
      hγ.continuous.comp hparam
    have hvec : ∀ _i : Fin 2, Continuous (fun q : ↥Kset =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y)
          (γ ((q : Real × Real).2)) (v ((q : Real × Real).2))) :=
      fun _i => hvLift.comp hparam
    have heval :=
      hS.ricciCont.eval_continuous
        (P := ↥Kset)
        (τ := fun q => ((q : Real × Real).1))
        (b := fun q => γ ((q : Real × Real).2))
        htime
        (fun q => D.regular_subset (hwin q.2.1))
        hbase
        (v := fun _i q => v ((q : Real × Real).2))
        hvec
    refine heval.congr (fun q => ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    change
      metricRicciAt (I := I) (S.base.metric ((q : Real × Real).1))
          (γ ((q : Real × Real).2))
          (fun _i : Fin 2 => v ((q : Real × Real).2)) =
        metricRicciAt (I := I) (S.base.metric ((q : Real × Real).1))
          (γ ((q : Real × Real).2))
          (vec2 (I := I) (v ((q : Real × Real).2))
            (v ((q : Real × Real).2)))
    congr 1
    funext i
    fin_cases i <;> rfl
  have hRicContOn :
      ContinuousOn (fun p : Real × Real => Ric p.1 p.2) Kset := by
    refine hRicAtContOn.congr (fun p hp => ?_)
    simpa only [Ric, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      (metricRicciAt_apply_eq_ricciTensor
        (I := I) (S.base.metric p.1) (γ p.2) (v p.2) (v p.2)).symm
  have hFcontOn :
      ContinuousOn (fun p : Real × Real => F p.1 p.2) Kset :=
    Real.continuous_sqrt.comp_continuousOn hGcontOn
  have hF'contOn :
      ContinuousOn (fun p : Real × Real => F' p.1 p.2) Kset := by
    apply ContinuousOn.div
      (continuousOn_const.mul hRicContOn)
      (continuousOn_const.mul
        (Real.continuous_sqrt.comp_continuousOn hGcontOn))
    intro p hp
    have hvne : v p.2 ≠ 0 := hvel p.2 hp.2
    have hpos : 0 < G p.1 p.2 :=
      (S.base.metric p.1).pos (γ p.2) (v p.2) hvne
    exact ne_of_gt (mul_pos two_pos (Real.sqrt_pos.2 hpos))
  have hFslice : ∀ s ∈ Set.Icc α β,
      ContinuousOn (F s) (Set.Icc a b) := by
    intro s hs
    have hcomp := hFcontOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hs, hu⟩)
    simpa only [Prod.fst, Prod.snd] using hcomp
  have hF'slice : ∀ s ∈ Set.Icc α β,
      ContinuousOn (F' s) (Set.Icc a b) := by
    intro s hs
    have hcomp := hF'contOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hs, hu⟩)
    simpa only [Prod.fst, Prod.snd] using hcomp
  have hpoint : ∀ s ∈ Set.Ioo α β, ∀ u ∈ Set.Icc a b,
      HasDerivAt (fun r => F r u) (F' s u) s := by
    intro s hs u hu
    have hsreg : s ∈ D.regular :=
      hwin ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hmetric := metricDerivAt
      (I := I) S hS ⟨s, hsreg⟩ (γ u) (v u) (v u)
    have hbridge :
        S.ricciAt s (γ u) (vec2 (I := I) (v u) (v u)) = Ric s u := by
      exact metricRicciAt_apply_eq_ricciTensor
        (I := I) (S.base.metric s) (γ u) (v u) (v u)
    rw [hbridge] at hmetric
    have hGne : G s u ≠ 0 := ne_of_gt
      ((S.base.metric s).pos (γ u) (v u) (hvel u hu))
    simpa only [F, F', G] using hmetric.sqrt hGne
  have hKcompact : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hKcompact.exists_bound_of_continuousOn hF'contOn
  have hkey :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := a) (b := b)
      (F := F) (F' := F') (x₀ := t)
      (bound := fun _ => C) (s := Set.Ioo α β)
      (Ioo_mem_nhds htIoo.1 htIoo.2)
      (Filter.eventually_of_mem (Ioo_mem_nhds htIoo.1 htIoo.2)
        (fun s hs => by
          rw [Set.uIoc_of_le hab]
          exact
            ((hFslice s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).mono
              Set.Ioc_subset_Icc_self).aestronglyMeasurable
              measurableSet_Ioc))
      (by
        have hcontFt : ContinuousOn (F t) (Set.Icc a b) :=
          hFslice t ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩
        exact hcontFt.intervalIntegrable_of_Icc hab)
      (by
        rw [Set.uIoc_of_le hab]
        exact
          ((hF'slice t ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩).mono
            Set.Ioc_subset_Icc_self).aestronglyMeasurable
            measurableSet_Ioc)
      (by
        apply Filter.Eventually.of_forall
        intro u hu s hs
        rw [Set.uIoc_of_le hab] at hu
        exact hC (s, u)
          ⟨⟨le_of_lt hs.1, le_of_lt hs.2⟩,
            ⟨le_of_lt hu.1, hu.2⟩⟩)
      (_root_.intervalIntegrable_const)
      (by
        apply Filter.Eventually.of_forall
        intro u hu s hs
        rw [Set.uIoc_of_le hab] at hu
        exact hpoint s hs u ⟨le_of_lt hu.1, hu.2⟩)
  have hderiv :
      (∫ u in a..b, F' t u) =
        ∫ u in a..b,
          -Ric t u / Real.sqrt (G t u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hden : Real.sqrt (G t u) ≠ 0 := ne_of_gt
      (Real.sqrt_pos.2
        ((S.base.metric t).pos (γ u) (v u) (hvel u hu)))
    dsimp only [F']
    field_simp
  rw [← hderiv]
  simpa only [Variation.arcLength, F, G, Ric, v] using hkey.2

/-- A quadratic Ricci bound gives the expected lower bound for the time
derivative of the length of a fixed regular path. -/
theorem pathLength_deriv_ge
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b t A : Real}
    (hab : a ≤ b)
    (ht : t ∈ D.regular)
    (γ : Real → M)
    (hγ : ContMDiff 𝓘(Real, Real) I 1 γ)
    (hvel : ∀ u ∈ Set.Icc a b,
      mfderiv 𝓘(Real, Real) I γ u (1 : Real) ≠ 0)
    (hRic : ∀ u ∈ Set.Icc a b,
      |ricciTensor (I := I) (S.base.metric t) (γ u)
          (mfderiv 𝓘(Real, Real) I γ u (1 : Real))
          (mfderiv 𝓘(Real, Real) I γ u (1 : Real))| ≤
        A * (S.base.metric t).inner (γ u)
          (mfderiv 𝓘(Real, Real) I γ u (1 : Real))
          (mfderiv 𝓘(Real, Real) I γ u (1 : Real))) :
    -A * Variation.arcLength (I := I) (S.base.metric t) γ a b ≤
      deriv
        (fun s => Variation.arcLength (I := I) (S.base.metric s) γ a b)
        t := by
  classical
  let v : (u : Real) → TangentSpace I (γ u) :=
    fun u => mfderiv 𝓘(Real, Real) I γ u (1 : Real)
  let G : Real → Real :=
    fun u => (S.base.metric t).inner (γ u) (v u) (v u)
  let Ric : Real → Real :=
    fun u => ricciTensor (I := I) (S.base.metric t) (γ u) (v u) (v u)
  let Q : Real → Real := fun u => -Ric u / Real.sqrt (G u)
  have hvLift : Continuous (fun u : Real =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) (γ u) (v u)) := by
    have h :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (γ := γ) (by norm_num) hγ
    simpa only [v, tangentMap] using h
  have hGcont : ContinuousOn G (Set.Icc a b) := by
    rw [continuousOn_iff_continuous_restrict]
    have hbase : Continuous (fun u : ↥(Set.Icc a b) => γ (u : Real)) :=
      hγ.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Set.Icc a b) =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y)
          (γ (u : Real)) (v (u : Real))) :=
      fun _i => hvLift.comp continuous_subtype_val
    have heval :=
      hS.smoothMetric.metricTensor_cont.eval_continuous
        (P := ↥(Set.Icc a b))
        (τ := fun _u => t)
        (b := fun u => γ (u : Real))
        continuous_const
        (fun _u => D.regular_subset ht)
        hbase
        (v := fun _i u => v (u : Real))
        hvec
    refine heval.congr (fun u => ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    rfl
  have hRicAtCont :
      ContinuousOn
        (fun u =>
          S.ricciAt t (γ u) (vec2 (I := I) (v u) (v u)))
        (Set.Icc a b) := by
    rw [continuousOn_iff_continuous_restrict]
    have hbase : Continuous (fun u : ↥(Set.Icc a b) => γ (u : Real)) :=
      hγ.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Set.Icc a b) =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y)
          (γ (u : Real)) (v (u : Real))) :=
      fun _i => hvLift.comp continuous_subtype_val
    have heval :=
      hS.ricciCont.eval_continuous
        (P := ↥(Set.Icc a b))
        (τ := fun _u => t)
        (b := fun u => γ (u : Real))
        continuous_const
        (fun _u => D.regular_subset ht)
        hbase
        (v := fun _i u => v (u : Real))
        hvec
    refine heval.congr (fun u => ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    change
      metricRicciAt (I := I) (S.base.metric t) (γ (u : Real))
          (fun _i : Fin 2 => v (u : Real)) =
        metricRicciAt (I := I) (S.base.metric t) (γ (u : Real))
          (vec2 (I := I) (v (u : Real)) (v (u : Real)))
    congr 1
    funext i
    fin_cases i <;> rfl
  have hRicCont : ContinuousOn Ric (Set.Icc a b) := by
    refine hRicAtCont.congr (fun u hu => ?_)
    simpa only [Ric, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      (metricRicciAt_apply_eq_ricciTensor
        (I := I) (S.base.metric t) (γ u) (v u) (v u)).symm
  have hspeedCont : ContinuousOn (fun u => Real.sqrt (G u)) (Set.Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn hGcont
  have hQcont : ContinuousOn Q (Set.Icc a b) := by
    change ContinuousOn (fun u => -Ric u / Real.sqrt (G u)) (Set.Icc a b)
    apply ContinuousOn.div hRicCont.neg hspeedCont
    intro u hu
    exact ne_of_gt (Real.sqrt_pos.2
      ((S.base.metric t).pos (γ u) (v u) (hvel u hu)))
  have hleftInt :
      IntervalIntegrable (fun u => -A * Real.sqrt (G u))
        MeasureTheory.volume a b :=
    (continuousOn_const.mul hspeedCont).intervalIntegrable_of_Icc hab
  have hrightInt :
      IntervalIntegrable Q MeasureTheory.volume a b :=
    hQcont.intervalIntegrable_of_Icc hab
  have hpoint : ∀ u ∈ Set.Icc a b,
      -A * Real.sqrt (G u) ≤ Q u := by
    intro u hu
    have hGpos : 0 < G u :=
      (S.base.metric t).pos (γ u) (v u) (hvel u hu)
    have hRicLe : Ric u ≤ A * G u :=
      (le_abs_self (Ric u)).trans (by simpa only [Ric, G, v] using hRic u hu)
    dsimp only [Q]
    rw [le_div_iff₀ (Real.sqrt_pos.2 hGpos)]
    rw [mul_assoc, Real.mul_self_sqrt (le_of_lt hGpos)]
    linarith
  have hmono :
      (∫ u in a..b, -A * Real.sqrt (G u)) ≤
        ∫ u in a..b, Q u :=
    intervalIntegral.integral_mono_on hab hleftInt hrightInt hpoint
  have hderiv :=
    pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS hab ht γ hγ hvel
  rw [hderiv.deriv, Variation.arcLength,
    ← intervalIntegral.integral_const_mul]
  simpa only [Q, Ric, G, v] using hmono

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- An intrinsic geodesic with positive launch speed has nonzero velocity at
every parameter time. -/
private theorem intrGeo_vel_ne
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (v : TangentSpace I p)
    (hv : 0 < g.inner p v v) (u : Real) :
    mfderiv 𝓘(Real, Real) I
        (intrinsicGeodesic (I := I) g hEnorm p v) u (1 : Real) ≠ 0 := by
  intro hzero
  have hspeed :=
    intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v u
  have hinner0 :
      g.inner (intrinsicGeodesic (I := I) g hEnorm p v u)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm p v) u (1 : Real))
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm p v) u (1 : Real)) = 0 := by
    have h := congrArg
      (fun w : TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p v u) =>
        g.inner (intrinsicGeodesic (I := I) g hEnorm p v u) w w)
      hzero
    simpa only [map_zero] using h
  exact hv.ne' (hspeed.symm.trans hinner0)

/-- The checked fields of one scaled evolving-distance support. -/
private structure ScaledDistSupport
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (O : M) (T t : Real) (x : M) (d Λ r : Real) where
  rho : Real → M → Real
  eq_at : rho t x = Real.exp (Λ * t) * r
  upper_nhds :
    ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      Real.exp (Λ * p.1) *
          (riemannianEDistOf (I := I)
            (S.base.metric p.1) O p.2).toReal ≤
        rho p.1 p.2
  time_diff :
    DifferentiableWithinAt Real
      (fun s => rho s x) (Set.Icc 0 T) t
  space_diff_nhds :
    ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (rho t) y
  grad_diff :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (S.base.metric t) (rho t) y) x
  grad_sq :
    (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (rho t) x)
        (gradientFun (I := I) (S.base.metric t) (rho t) x) ≤
      Real.exp (2 * Λ * t)
  par_lower :
    -Real.exp (Λ * t) *
        (2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ)) ≤
      parabolicOperatorWithDrift
        (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y)) rho t x

/-- Choose the dimension-normalized transverse Ricci comparison coefficient. -/
private theorem exists_calabi_coeff
    (g : SmoothRiemannianMetric I M)
    {Λ : Real}
    (hΛ : 0 ≤ Λ)
    (hricQuad : ∀ y : M, ∀ v : TangentSpace I y,
      |ricciTensor (I := I) g y v v| ≤
        Λ * g.inner y v v) :
    let dNat : Nat := Module.finrank Real E
    let d : Real := (dNat : Real)
    let nNat : Nat := dNat - 1
    let n : Real := (nNat : Real)
    ∃ q : Real,
      0 ≤ q ∧
      Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) g (-(n * q ^ 2)) ∧
      n * q = Real.sqrt ((d - 1) * Λ) := by
  dsimp only
  let dNat : Nat := Module.finrank Real E
  let d : Real := (dNat : Real)
  let nNat : Nat := dNat - 1
  let n : Real := (nNat : Real)
  have hdNat_pos : 0 < dNat := by
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  have hdNat_one : 1 ≤ dNat := hdNat_pos
  have hdn : d - 1 = n := by
    dsimp only [d, n, nNat]
    rw [Nat.cast_sub hdNat_one]
    norm_num
  let q : Real :=
    if nNat = 0 then 0 else Real.sqrt (Λ / n)
  have hq : 0 ≤ q := by
    dsimp only [q]
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  have hRicLower :
      Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) g (-(n * q ^ 2)) := by
    by_cases hn0 : nNat = 0
    · have hd1 : dNat = 1 := by omega
      simpa only [q, hn0, if_pos, zero_pow, zero_mul, mul_zero, neg_zero,
        n, nNat, hd1, Nat.cast_zero] using
        (Geometry.Riemannian.BonnetMyers.ricciLower_dim1
          (I := I) g hd1)
    · have hnNat_pos : 0 < nNat := Nat.pos_of_ne_zero hn0
      have hn : 0 < n := by
        dsimp only [n]
        exact_mod_cast hnNat_pos
      have hq_sq : q ^ 2 = Λ / n := by
        dsimp only [q]
        rw [if_neg hn0, Real.sq_sqrt (div_nonneg hΛ hn.le)]
      intro y v
      have habs := hricQuad y v
      have hneg :
          -(Λ * g.inner y v v) ≤
            ricciTensor (I := I) g y v v :=
        neg_le_of_abs_le habs
      rw [hq_sq]
      have hcoeff : n * (Λ / n) = Λ := by
        field_simp
      rw [hcoeff]
      simpa only [neg_mul] using hneg
  have hnq :
      n * q = Real.sqrt ((d - 1) * Λ) := by
    by_cases hn0 : nNat = 0
    · simp only [q, hn0, if_pos, n, Nat.cast_zero, zero_mul, mul_zero,
        hdn, Real.sqrt_zero]
    · rw [hdn]
      have hnNat_pos : 0 < nNat := Nat.pos_of_ne_zero hn0
      have hn : 0 < n := by
        dsimp only [n]
        exact_mod_cast hnNat_pos
      have hq_def : q = Real.sqrt (Λ / n) := by
        simp only [q, hn0, if_false]
      have hq_nonneg : 0 ≤ q := hq
      have hq_sq : q ^ 2 = Λ / n := by
        rw [hq_def, Real.sq_sqrt (div_nonneg hΛ hn.le)]
      have hright_sq :
          (Real.sqrt (n * Λ)) ^ 2 = n * Λ :=
        Real.sq_sqrt (mul_nonneg hn.le hΛ)
      have hleft_nonneg : 0 ≤ n * q := mul_nonneg hn.le hq_nonneg
      have hright_nonneg :
          0 ≤ Real.sqrt (n * Λ) := Real.sqrt_nonneg _
      have hscale : n * q ^ 2 = Λ := by
        rw [hq_sq]
        field_simp
      have hleft_sq : (n * q) ^ 2 = n * Λ := by
        nlinarith
      nlinarith
  exact ⟨q, hq, hRicLower, hnq⟩

/-- Convert the scalar curvature bound into the uniform quadratic Ricci bound. -/
private theorem ricci_quad_of_curv
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {T K : Real}
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 * Real.sqrt K
    0 ≤ Λ ∧
    (∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v) := by
  dsimp only
  let dNat : Nat := Module.finrank Real E
  let d : Real := (dNat : Real)
  let Λ : Real := d ^ 2 * Real.sqrt K
  have hsqrtK : 0 ≤ Real.sqrt K := by
    rcases hK.eq_or_lt with hK0 | hKpos
    · rw [← hK0]
      norm_num
    · exact (Real.sqrt_pos.2 hKpos).le
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ, d]
    exact mul_nonneg (sq_nonneg _) hsqrtK
  have hcurv0 : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric s) y 4
        (S.base.rm04 s y) ≤ K := by
    intro s hs y
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hcurv s hs y
  have hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v := by
    intro s hs y v
    simpa only [Λ, d, dNat] using
      (ricci_quad_sol (I := I) S y v (hcurv0 s hs y))
  exact ⟨hΛ, hricQuad⟩

/-- The unscaled fixed-time Calabi data and broken-path time estimate used
before multiplying by the exponential Ricci-flow weight. -/
private structure CalabiFlowCore
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (O : M) (T t : Real) (x : M) (Λ r n q : Real) where
  rho0 : M → Real
  support : Real → M → Real
  support_t : support t = rho0
  rho0_x : rho0 x = r
  upper_nhds :
    ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      (riemannianEDistOf (I := I)
        (S.base.metric p.1) O p.2).toReal ≤
        support p.1 p.2
  time_diff :
    DifferentiableAt Real (fun s => support s x) t
  time_lower :
    -Λ * support t x ≤ deriv (fun s => support s x) t
  space_diff_nhds :
    ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) rho0 y
  grad_diff :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (S.base.metric t) rho0 y) x
  grad_sq :
    (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) rho0 x)
        (gradientFun (I := I) (S.base.metric t) rho0 x) = 1
  lap_upper :
    laplacian
        (I := I) (LeviCivita (I := I) (S.base.metric t))
        (S.base.metric t) rho0 x ≤
      2 * n / r + n * q

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Construct the unscaled Calabi support and its broken-path time estimate. -/
private theorem calabi_core_of_sol
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E
      (fun y : M => TangentSpace I y)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T Λ t r n q : Real}
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite : Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal))
    (hOx : O ≠ x)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal
          (Real.sqrt ((S.base.metric t).inner y w w)))
    (hq : 0 ≤ q)
    (hRicLower :
      Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) (S.base.metric t) (-(n * q ^ 2)))
    (hr : r = (Manifold.riemannianEDist I O x).toReal)
    (hn :
      n = ((Module.finrank Real E - 1 : Nat) : Real)) :
    Nonempty (CalabiFlowCore (I := I) S O T t x Λ r n q) := by
  classical
  have hRicLower' :
      Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) (S.base.metric t)
          (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)) := by
    simpa only [← hn] using hRicLower
  obtain ⟨tail, _, hrho0_x, _, hrho0_ev,
      hgrad0, hgrad0_norm, hlap0⟩ :=
    exists_calabiData
      (I := I) (S.base.metric t) hEnorm q hq hRicLower' hOx hfinite
  let rho0 : M → Real := fun y =>
    tail.left +
      branchRadius (I := I) (S.base.metric t) tail.branch y
  have hleft_fin :
      Manifold.riemannianEDist I O tail.p ≠ (⊤ : ENNReal) := by
    rw [tail.left_edist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨vLeft, hvLeft_exp, hvLeft_norm⟩ :=
    minExp_of_ne_top
      (I := I) (S.base.metric t) hEnorm O tail.p hleft_fin
  have hvLeft_norm' :
      Real.sqrt ((S.base.metric t).inner O vLeft vLeft) =
        tail.left := by
    rw [hvLeft_norm, tail.left_edist,
      ENNReal.toReal_ofReal tail.left_nonneg]
  have hvLeft_pos :
      0 < (S.base.metric t).inner O vLeft vLeft := by
    apply Real.sqrt_pos.mp
    rw [hvLeft_norm']
    exact tail.left_pos
  let γ : Real → M :=
    intrinsicGeodesic (I := I) (S.base.metric t) hEnorm O vLeft
  let δ : M → Real → M := fun y =>
    intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.p
      (show TangentSpace I tail.p from tail.branch.inv y)
  let L₁ : Real → Real := fun s =>
    Geometry.Riemannian.Variation.arcLength
      (I := I) (S.base.metric s) γ 0 1
  let L₂ : Real → M → Real := fun s y =>
    Geometry.Riemannian.Variation.arcLength
      (I := I) (S.base.metric s) (δ y) 0 1
  let vSupport : Real → M → Real := fun s y => L₁ s + L₂ s y
  have hγ_smooth : ContMDiff 𝓘(Real, Real) I 1 γ := by
    exact contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn
        (I := I) (S.base.metric t) hEnorm O vLeft)
  have hδ_smooth : ∀ y : M, ContMDiff 𝓘(Real, Real) I 1 (δ y) := by
    intro y
    exact contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn
        (I := I) (S.base.metric t) hEnorm tail.p
          (show TangentSpace I tail.p from tail.branch.inv y))
  have hγ_zero : γ 0 = O := by
    exact intrinsicGeodesic_zero
      (I := I) (S.base.metric t) hEnorm O vLeft
  have hγ_one : γ 1 = tail.p := by
    simpa only [γ, expMapIntrinsic_def] using hvLeft_exp
  have hδ_zero : ∀ y : M, δ y 0 = tail.p := by
    intro y
    exact intrinsicGeodesic_zero
      (I := I) (S.base.metric t) hEnorm tail.p
        (show TangentSpace I tail.p from tail.branch.inv y)
  have hδ_one : ∀ y ∈ tail.branch.dom, δ y 1 = y := by
    intro y hy
    simpa only [δ, expMapIntrinsic_def] using
      tail.branch.right_inv hy
  have hL₁_t : L₁ t = tail.left := by
    rw [show L₁ t =
        Geometry.Riemannian.Variation.arcLength
          (I := I) (S.base.metric t)
          (intrinsicGeodesic
            (I := I) (S.base.metric t) hEnorm O vLeft) 0 1 by
      rfl]
    rw [arcLength_radial, sub_zero, one_mul, hvLeft_norm']
  have hL₂_t : ∀ y : M,
      L₂ t y =
        branchRadius (I := I) (S.base.metric t) tail.branch y := by
    intro y
    rw [show L₂ t y =
        Geometry.Riemannian.Variation.arcLength
          (I := I) (S.base.metric t)
          (intrinsicGeodesic
            (I := I) (S.base.metric t) hEnorm tail.p
              (show TangentSpace I tail.p from tail.branch.inv y)) 0 1 by
      rfl]
    rw [arcLength_radial, sub_zero, one_mul]
    rfl
  have hvSupport_t : ∀ y : M, vSupport t y = rho0 y := by
    intro y
    rw [show vSupport t y = L₁ t + L₂ t y by rfl,
      hL₁_t, hL₂_t]
  have htarget_ev :
      ∀ᶠ p : Real × M in 𝓝 (t, x), p.2 ∈ tail.branch.dom := by
    exact continuousAt_snd.preimage_mem_nhds
      (tail.branch.hom.open_target.mem_nhds tail.target_mem)
  have hupper :
      ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        (riemannianEDistOf
          (I := I) (S.base.metric p.1) O p.2).toReal ≤
          vSupport p.1 p.2 := by
    filter_upwards [htarget_ev.filter_mono inf_le_left] with p hp
    have hdist :
        riemannianEDistOf (I := I) (S.base.metric p.1) O p.2 ≤
          ENNReal.ofReal (L₁ p.1) + ENNReal.ofReal (L₂ p.1 p.2) := by
      calc
        riemannianEDistOf (I := I) (S.base.metric p.1) O p.2 =
            riemannianEDistOf (I := I) (S.base.metric p.1)
              (γ 0) (δ p.2 1) := by rw [hγ_zero, hδ_one p.2 hp]
        _ ≤ ENNReal.ofReal (L₁ p.1) +
              ENNReal.ofReal (L₂ p.1 p.2) := by
          exact edistOf_le_two_arcs
            (I := I) (S.base.metric p.1)
              (a := 0) (b := 1) (c := 0) (d := 1)
              zero_le_one zero_le_one
              (hγ_smooth.contMDiffOn)
              ((hδ_smooth p.2).contMDiffOn)
              (hγ_one.trans (hδ_zero p.2).symm)
    have hL₁_nonneg : 0 ≤ L₁ p.1 := by
      dsimp only [L₁]
      unfold Geometry.Riemannian.Variation.arcLength
      exact intervalIntegral.integral_nonneg zero_le_one
        (fun u _ => Real.sqrt_nonneg _)
    have hL₂_nonneg : 0 ≤ L₂ p.1 p.2 := by
      dsimp only [L₂]
      unfold Geometry.Riemannian.Variation.arcLength
      exact intervalIntegral.integral_nonneg zero_le_one
        (fun u _ => Real.sqrt_nonneg _)
    have hreal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hdist
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hL₁_nonneg,
      ENNReal.toReal_ofReal hL₂_nonneg] at hreal
    exact hreal
  have htreg : t ∈ D.regular :=
    hreg ⟨htpos, ht.2⟩
  have hγ_vel : ∀ u ∈ Set.Icc (0 : Real) 1,
      mfderiv 𝓘(Real, Real) I γ u (1 : Real) ≠ 0 := by
    intro u _hu
    simpa only [γ] using
      intrGeo_vel_ne
        (I := I) (S.base.metric t) hEnorm O vLeft hvLeft_pos u
  have hinv_x : tail.branch.inv x = (tail.u : E) := by
    have hleft := tail.branch.left_inv tail.source_mem
    rw [tail.exp_eq] at hleft
    exact hleft
  have hu_pos :
      0 < (S.base.metric t).inner tail.p tail.u tail.u := by
    apply Real.sqrt_pos.mp
    rw [tail.u_norm]
    exact tail.ell_pos
  have hinv_pos :
      0 < (S.base.metric t).inner tail.p
        (show TangentSpace I tail.p from tail.branch.inv x)
        (show TangentSpace I tail.p from tail.branch.inv x) := by
    simpa only [hinv_x] using hu_pos
  have hδx_vel : ∀ u ∈ Set.Icc (0 : Real) 1,
      mfderiv 𝓘(Real, Real) I (δ x) u (1 : Real) ≠ 0 := by
    intro u _hu
    simpa only [δ] using
      intrGeo_vel_ne
        (I := I) (S.base.metric t) hEnorm tail.p
          (show TangentSpace I tail.p from tail.branch.inv x)
          hinv_pos u
  have hL₁_deriv :=
    pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS zero_le_one htreg γ hγ_smooth hγ_vel
  have hL₂_deriv :=
    pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS zero_le_one htreg (δ x) (hδ_smooth x) hδx_vel
  have hL₁_diff : DifferentiableAt Real L₁ t := by
    simpa only [L₁] using hL₁_deriv.differentiableAt
  have hL₂_diff : DifferentiableAt Real (fun s => L₂ s x) t := by
    simpa only [L₂] using hL₂_deriv.differentiableAt
  have hL₁_lower :
      -Λ * L₁ t ≤ deriv L₁ t := by
    simpa only [L₁] using
      pathLength_deriv_ge
        (I := I) S hS (A := Λ) zero_le_one htreg γ hγ_smooth hγ_vel
          (fun u _hu => hricQuad t ht (γ u)
            (mfderiv 𝓘(Real, Real) I γ u (1 : Real)))
  have hL₂_lower :
      -Λ * L₂ t x ≤ deriv (fun s => L₂ s x) t := by
    simpa only [L₂] using
      pathLength_deriv_ge
        (I := I) S hS (A := Λ) zero_le_one htreg (δ x)
          (hδ_smooth x) hδx_vel
          (fun u _hu => hricQuad t ht (δ x u)
            (mfderiv 𝓘(Real, Real) I (δ x) u (1 : Real)))
  have hv_diffAt :
      DifferentiableAt Real (fun s => vSupport s x) t := by
    change DifferentiableAt Real (fun s => L₁ s + L₂ s x) t
    exact hL₁_diff.add hL₂_diff
  have hv_lower :
      -Λ * vSupport t x ≤ deriv (fun s => vSupport s x) t := by
    change -Λ * (L₁ t + L₂ t x) ≤
      deriv (fun s => L₁ s + L₂ s x) t
    have hderiv_add :
        deriv (fun s => L₁ s + L₂ s x) t =
          deriv L₁ t + deriv (fun s => L₂ s x) t := by
      simpa only [Pi.add_apply] using deriv_add hL₁_diff hL₂_diff
    rw [hderiv_add]
    linarith
  have hrho0_ev' :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) rho0 y := by
    simpa only [rho0] using hrho0_ev
  have hgrad0' :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) (S.base.metric t) rho0 y) x := by
    simpa only [rho0] using hgrad0
  have hgrad0_norm' :
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) rho0 x)
          (gradientFun (I := I) (S.base.metric t) rho0 x) = 1 := by
    simpa only [rho0] using hgrad0_norm
  have hlap0' :
      laplacian
          (I := I) (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) rho0 x ≤
        2 * n / r + n * q := by
    rw [hr, hn]
    simpa only [rho0] using hlap0
  refine ⟨{
    rho0 := rho0
    support := vSupport
    support_t := ?_
    rho0_x := ?_
    upper_nhds := hupper
    time_diff := hv_diffAt
    time_lower := hv_lower
    space_diff_nhds := hrho0_ev'
    grad_diff := hgrad0'
    grad_sq := hgrad0_norm'
    lap_upper := hlap0'
  }⟩
  · funext y
    exact hvSupport_t y
  · exact hrho0_x.trans hr.symm

/-- Multiply the unscaled Calabi core by the exponential Ricci-flow weight. -/
private theorem CalabiFlowCore.scale
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {O x : M} {T t d Λ r n q : Real}
    (C : CalabiFlowCore (I := I) S O T t x Λ r n q)
    (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T)
    (hcoef :
      2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ) =
        2 * n / r + n * q) :
    Nonempty (ScaledDistSupport (I := I) S O T t x d Λ r) := by
  let rho : Real → M → Real := fun s y =>
    Real.exp (Λ * s) * C.support s y
  have hrho_t : ∀ y : M,
      rho t y = Real.exp (Λ * t) * C.rho0 y := by
    intro y
    rw [show rho t y = Real.exp (Λ * t) * C.support t y by rfl,
      C.support_t]
  have hrho_tx : rho t x = Real.exp (Λ * t) * r := by
    rw [hrho_t, C.rho0_x]
  have hupper :
      ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        Real.exp (Λ * p.1) *
            (riemannianEDistOf
              (I := I) (S.base.metric p.1) O p.2).toReal ≤
          rho p.1 p.2 := by
    filter_upwards [C.upper_nhds] with p hp
    exact mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
  have hrho_t_fun :
      rho t = Real.exp (Λ * t) • C.rho0 := by
    funext y
    simpa only [Pi.smul_apply, smul_eq_mul] using hrho_t y
  have hrho_space :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) (rho t) y := by
    rw [hrho_t_fun]
    filter_upwards [C.space_diff_nhds] with y hy
    exact hy.const_smul _
  have hgrad_ev :
      (fun y : M =>
        gradientFun (I := I) (S.base.metric t) (rho t) y) =ᶠ[𝓝 x]
        (fun y : M =>
          Real.exp (Λ * t) •
            gradientFun (I := I) (S.base.metric t) C.rho0 y) := by
    filter_upwards [C.space_diff_nhds] with y hy
    rw [hrho_t_fun]
    exact
      gradientFun_const_smul
        (I := I) (S.base.metric t) (Real.exp (Λ * t)) hy
  have hgrad_scaled :
      MDiffAt
        (T% fun y : M =>
          Real.exp (Λ * t) •
            gradientFun (I := I) (S.base.metric t) C.rho0 y) x := by
    simpa only [Pi.smul_apply] using
      C.grad_diff.smul_const_section (a := Real.exp (Λ * t))
  have hgrad_total :
      (T% fun y : M =>
        gradientFun (I := I) (S.base.metric t) (rho t) y) =ᶠ[𝓝 x]
        (T% fun y : M =>
          Real.exp (Λ * t) •
            gradientFun (I := I) (S.base.metric t) C.rho0 y) := by
    filter_upwards [hgrad_ev] with y hy
    change TotalSpace.mk' E y _ = TotalSpace.mk' E y _
    rw [hy]
  have hrho_grad :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) (S.base.metric t) (rho t) y) x :=
    hgrad_scaled.congr_of_eventuallyEq hgrad_total
  have hgrad_x :
      gradientFun (I := I) (S.base.metric t) (rho t) x =
        Real.exp (Λ * t) •
          gradientFun (I := I) (S.base.metric t) C.rho0 x :=
    hgrad_ev.self_of_nhds
  have hexp_sq :
      Real.exp (Λ * t) ^ 2 = Real.exp (2 * Λ * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hrho_grad_norm :
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) (rho t) x)
          (gradientFun (I := I) (S.base.metric t) (rho t) x) ≤
        Real.exp (2 * Λ * t) := by
    rw [hgrad_x, gInner_smul_self (I := I) (S.base.metric t) x,
      C.grad_sq, mul_one, hexp_sq]
  have huniq :=
    uniqueDiffOn_Icc hT t ht
  have hv_time :
      DifferentiableWithinAt Real
        (fun s => C.support s x) (Set.Icc 0 T) t :=
    C.time_diff.differentiableWithinAt
  have hcancel :
      0 ≤
        derivWithin (fun s => C.support s x) (Set.Icc 0 T) t +
          Λ * C.support t x := by
    rw [C.time_diff.derivWithin huniq]
    linarith [C.time_lower]
  have hlin :
      HasDerivAt (fun s : Real => Λ * s) Λ t := by
    simpa using (hasDerivAt_id t).const_mul Λ
  have hexp :
      HasDerivAt (fun s : Real => Real.exp (Λ * s))
        (Real.exp (Λ * t) * Λ) t :=
    hlin.exp
  have hrho_time :
      DifferentiableWithinAt Real
        (fun s => rho s x) (Set.Icc 0 T) t := by
    change DifferentiableWithinAt Real
      (fun s => Real.exp (Λ * s) * C.support s x) _ t
    exact hexp.differentiableAt.differentiableWithinAt.mul hv_time
  have hrho_deriv :
      derivWithin (fun s => rho s x) (Set.Icc 0 T) t =
        Real.exp (Λ * t) *
          (derivWithin (fun s => C.support s x) (Set.Icc 0 T) t +
            Λ * C.support t x) := by
    change derivWithin
      (fun s => Real.exp (Λ * s) * C.support s x) _ t = _
    rw [derivWithin_fun_mul
      hexp.differentiableAt.differentiableWithinAt hv_time,
      hexp.differentiableAt.derivWithin huniq, hexp.deriv]
    ring
  have hlap_rho :
      laplacianAt (I := I) (flowG (I := I) S) t (rho t) x =
        Real.exp (Λ * t) *
          laplacian
            (I := I) (LeviCivita (I := I) (S.base.metric t))
            (S.base.metric t) C.rho0 x := by
    rw [hrho_t_fun, laplacianAt_eq]
    simpa only [flowG, SolutionFamily.connection, LeviCivita] using
      (laplacian_smul_at
        (I := I) (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) (Real.exp (Λ * t))
          C.space_diff_nhds C.grad_diff)
  have hpar :
      -Real.exp (Λ * t) * (2 * n / r + n * q) ≤
        parabolicOperatorWithDrift
          (I := I) (flowG (I := I) S) T
          (fun _ y => (0 : TangentSpace I y)) rho t x := by
    rw [parabolicOperatorWithDrift_eq,
      heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt,
      hrho_deriv, hlap_rho]
    have htime_mul :=
      mul_nonneg (Real.exp_pos (Λ * t)).le hcancel
    have hlap_mul :=
      mul_le_mul_of_nonneg_left C.lap_upper (Real.exp_pos (Λ * t)).le
    linarith
  refine ⟨{
    rho := rho
    eq_at := hrho_tx
    upper_nhds := hupper
    time_diff := hrho_time
    space_diff_nhds := hrho_space
    grad_diff := hrho_grad
    grad_sq := hrho_grad_norm
    par_lower := ?_
  }⟩
  rw [hcoef]
  exact hpar

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Assemble the fixed-time Calabi core and apply the exponential time weight
once the Ricci quadratic bound and time-slice completeness are available. -/
private theorem scaled_of_quad
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T t Λ : Real}
    (hT : 0 < T)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hΛ : 0 ≤ Λ)
    (hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v)
    (hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    let d : Real := Module.finrank Real E
    let r : Real :=
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    Nonempty (ScaledDistSupport (I := I) S O T t x d Λ r) := by
  classical
  dsimp only
  let dNat : Nat := Module.finrank Real E
  let d : Real := (dNat : Real)
  let nNat : Nat := dNat - 1
  let n : Real := (nNat : Real)
  let r : Real :=
    (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
  have hdNat_pos : 0 < dNat := by
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  have hdNat_one : 1 ≤ dNat := hdNat_pos
  have hdn : d - 1 = n := by
    dsimp only [d, n, nNat]
    rw [Nat.cast_sub hdNat_one]
    norm_num
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨(S.base.metric t).toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun y : M => TangentSpace I y) :=
    ⟨⟨(S.base.metric t).inner,
      (S.base.metric t).contMDiff.continuous,
      by intro y v w; rfl⟩⟩
  letI : PseudoEMetricSpace M :=
    PseudoEMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := hcomplete_t.complete
  have hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal
          (Real.sqrt ((S.base.metric t).inner y w w)) := by
    intro y w
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    congr 2
  have hfinite' :
      Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    simpa only [riemannianEDistOf] using hfinite
  obtain ⟨q, hq, hRicLower, hnq⟩ :=
    exists_calabi_coeff
      (I := I) (S.base.metric t) hΛ (hricQuad t ht)
  have hr : r = (Manifold.riemannianEDist I O x).toReal := by
    simp only [r, riemannianEDistOf]
  have hnDim :
      n = ((Module.finrank Real E - 1 : Nat) : Real) := by
    rfl
  obtain ⟨core⟩ :=
    calabi_core_of_sol
      (I := I) S hS O hreg hricQuad ht htpos x hfinite' hOx
        hEnorm hq hRicLower hr hnDim
  have hcoef :
      2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ) =
        2 * n / r + n * q := by
    calc
      2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ) =
          2 * n / r + Real.sqrt ((d - 1) * Λ) := by rw [hdn]
      _ = 2 * n / r + n * q := by rw [hnq]
  exact core.scale hT ht hcoef

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Construct the bundled scaled-distance support used by the public
upper-support theorem. -/
private theorem scaledDist_support
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T K t : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 * Real.sqrt K
    let r : Real :=
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    Nonempty (ScaledDistSupport (I := I) S O T t x d Λ r) := by
  classical
  dsimp only
  obtain ⟨hΛ, hricQuad⟩ :=
    ricci_quad_of_curv (I := I) S hK hcurv
  have hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t) :=
    complete_of_ricBound
      (I := I) (D := D) (a := 0) (b := T)
        (K := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
        (s := t) S hS hslab hreg hΛ hricQuad hcomplete ht
  exact scaled_of_quad
    (I := I) (D := D) (T := T) (t := t)
      (Λ := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
      S hS O hT hreg hΛ hricQuad hcomplete_t ht htpos x hfinite hOx

/-- A positively rescaled evolving distance admits a quantitative smooth
Calabi upper support at every positive-time point of finite nonzero distance.

This is the unique new geometric-analysis frontier in the Route B-prime
complete-Shi producer.  The proof joins a point-pair minimizing geodesic, a
fixed-first Calabi tail, fixed-metric Laplacian comparison, and the Ricci-flow
variation of the length of the selected broken path. -/
theorem scaledDist_calabiUpperSupport_of_sol
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T K t : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 * Real.sqrt K
    let r : Real :=
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    ∃ ρ : Real → M → Real,
      ρ t x = Real.exp (Λ * t) * r ∧
      (∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        Real.exp (Λ * p.1) *
            (riemannianEDistOf (I := I)
              (S.base.metric p.1) O p.2).toReal ≤
          ρ p.1 p.2) ∧
      DifferentiableWithinAt Real
        (fun s => ρ s x) (Set.Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) (ρ t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M =>
          gradientFun (I := I) (S.base.metric t) (ρ t) y) x ∧
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) (ρ t) x)
          (gradientFun (I := I) (S.base.metric t) (ρ t) x) ≤
        Real.exp (2 * Λ * t) ∧
      -Real.exp (Λ * t) *
          (2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ)) ≤
        parabolicOperatorWithDrift
          (I := I) (flowG (I := I) S) T
          (fun _ y => (0 : TangentSpace I y)) ρ t x := by
  dsimp only
  obtain ⟨h⟩ :=
    scaledDist_support
      (I := I) S hS O hT hslab hreg hcomplete hK hcurv
        ht htpos x hfinite hOx
  exact
    ⟨h.rho, h.eq_at, h.upper_nhds, h.time_diff, h.space_diff_nhds,
      h.grad_diff, h.grad_sq, h.par_lower⟩

end DifferentialGeometry.PDE.RicciFlow

end
