import DifferentialGeometry.Geometry.Comparison.Variation.Curve.SpeedDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
  (RealTimeInterval metricRicciAt ricciTensor vec2)
open scoped Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

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
    rw [continuousOn_iff_continuous_domRestrict]
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
    rw [continuousOn_iff_continuous_domRestrict]
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
    with_unfolding_all exact hcomp
  have hF'slice : ∀ s ∈ Set.Icc α β,
      ContinuousOn (F' s) (Set.Icc a b) := by
    intro s hs
    have hcomp := hF'contOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hs, hu⟩)
    with_unfolding_all exact hcomp
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
    with_unfolding_all exact hmetric.sqrt hGne
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

theorem pathLength_deriv_ge_of_ricci_le
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
      ricciTensor (I := I) (S.base.metric t) (γ u)
          (mfderiv 𝓘(Real, Real) I γ u (1 : Real))
          (mfderiv 𝓘(Real, Real) I γ u (1 : Real)) ≤
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
    rw [continuousOn_iff_continuous_domRestrict]
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
    rw [continuousOn_iff_continuous_domRestrict]
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
      by simpa only [Ric, G, v] using hRic u hu
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
  exact pathLength_deriv_ge_of_ricci_le S hS hab ht γ hγ hvel
    (fun u hu => (le_abs_self _).trans (hRic u hu))

end DifferentialGeometry.PDE.RicciFlow
