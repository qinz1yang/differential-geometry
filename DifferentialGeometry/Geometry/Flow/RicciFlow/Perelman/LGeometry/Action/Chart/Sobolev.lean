import DifferentialGeometry.Geometry.Operator.Family.Gram.Sobolev
import DifferentialGeometry.Geometry.Metric.ChartLipschitz
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

noncomputable section

open Bundle Filter Function MeasureTheory Set
open scoped Manifold ContDiff Interval Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem exists_timeH1_extChartAt_of_intervalIntegrable_lRegularizedLagrangian
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T A B : ℝ) (hAB : A ≤ B) (alpha : ℝ → M) (p : M)
    (hAC : let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace;
      AbsolutelyContinuousOnInterval alpha A B)
    (hsrc : MapsTo alpha (Icc A B) (chartAt H p).source)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume A B)
    (hreg : ∀ s ∈ Icc A B, T - s ^ 2 ∈ D.regular) :
    ∃ u : timeH1 E (B - A),
      EqOn u.toFun (fun r ↦ extChartAt I p (alpha (A + r))) (Icc 0 (B - A)) ∧
        u.deriv =ᵐ[timeMeasure (B - A)]
          deriv (fun r ↦ extChartAt I p (alpha (A + r))) := by
  let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
  let L : ℝ := B - A
  let beta : ℝ → M := fun r ↦ alpha (A + r)
  let tau : ℝ → ℝ := fun r ↦ T - (A + r) ^ 2
  have hL : 0 ≤ L := sub_nonneg.mpr hAB
  have hαc : ContinuousOn alpha (uIcc A B) :=
    (uniformContinuousOn_of_absolutelyContinuousOnInterval hAC).continuousOn
  have hmaps : MapsTo (fun r : ℝ ↦ A + r) (Icc 0 L) (Icc A B) := by
    intro r hr
    exact ⟨le_add_of_nonneg_right hr.1, by dsimp only [L] at hr; linarith [hr.2]⟩
  have hfAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ beta) 0 L := by
    let cg : ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      (S.base.metric T).toContinuousRiemannianMetric
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
    let _ : IsRiemannianManifold I M := ⟨fun _ _ ↦ rfl⟩
    have hshiftAC : AbsolutelyContinuousOnInterval beta 0 L :=
      hAC.comp_monotone_lipschitzOn (isometry_add_left A).lipschitz.lipschitzOnWith
        (by intro x _ y _ hxy; linarith)
        (by simpa only [uIcc_of_le hL, uIcc_of_le hAB] using hmaps)
    obtain ⟨C, hchart⟩ :=
      Geometry.Riemannian.exists_lipschitzOnWith_extChartAt_of_isCompact (I := I) p
        (isCompact_Icc.image_of_continuousOn (hαc.mono Icc_subset_uIcc))
        (by simpa only [extChartAt_source] using mapsTo_iff_image_subset.mp hsrc)
    exact hchart.comp_absolutelyContinuousOnInterval hshiftAC (fun r hr ↦
      ⟨A + r, hmaps (by simpa only [uIcc_of_le hL] using hr), rfl⟩)
  have hsrcShift : MapsTo beta (uIcc 0 L) (chartAt H p).source := by
    simpa only [uIcc_of_le hL, beta, Function.comp_def] using hsrc.comp hmaps
  have hchart : MapsTo ((extChartAt I p) ∘ beta) (Icc 0 L)
      (interior (extChartAt I p).target) := by
    intro r hr
    rw [(isOpen_extChartAt_target (I := I) p).interior_eq]
    exact (extChartAt I p).map_source (by
      simpa only [extChartAt_source] using hsrcShift (Icc_subset_uIcc hr))
  have hmdiff : ∀ᵐ r ∂timeMeasure L,
      MDifferentiableAt 𝓘(ℝ, ℝ) I alpha (A + r) := by
    have hshift := hfAC.ae_mdifferentiableAt_of_extChartAt p hsrcShift
    rw [uIcc_of_le hL] at hshift
    filter_upwards [hshift] with r hr
    have hsub : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun s : ℝ ↦ s - A) (A + r) :=
      mdifferentiableAt_iff_differentiableAt.mpr
        ((hasDerivAt_id (A + r)).sub_const A).differentiableAt
    have hcomp := MDifferentiableAt.comp_of_eq (x := A + r) (f := fun s : ℝ ↦ s - A)
      hr hsub (show A + r - A = r by ring)
    apply hcomp.congr_of_eventuallyEq
    filter_upwards with s
    simp only [Function.comp_apply, beta]
    congr 1
    ring
  have hcarrier : ∀ s ∈ uIcc A B, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [uIcc_of_le hAB] using hs))
  have hEnergy : IntervalIntegrable
      (fun s ↦ (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) volume A B := by
    convert (hLag.sub (lScalar_int S hSc T A B alpha hcarrier hαc)).const_mul 2 using 1
    funext s
    dsimp only [lRegularizedLagrangian]
    ring
  have hEnergyShift : IntervalIntegrable
      (fun r ↦ (S.base.metric (tau r)).inner (beta r)
        (lVelocity (I := I) alpha (A + r)) (lVelocity (I := I) alpha (A + r)))
        volume 0 L := by
    simpa only [L, sub_self] using
      (IntervalIntegrable.comp_add_left_iff (a := A) (b := B) (c := A)).2 hEnergy
  have hInt : Integrable (fun r ↦ (S.family.metric (tau r)).inner (beta r)
      ((mfderiv 𝓘(ℝ, ℝ) I beta r : ℝ →L[ℝ] _) (1 : ℝ))
      ((mfderiv 𝓘(ℝ, ℝ) I beta r : ℝ →L[ℝ] _) (1 : ℝ))) (timeMeasure L) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL] at hEnergyShift
    apply hEnergyShift.congr
    filter_upwards [hmdiff] with r hr
    have hadd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ A + s) r :=
      mdifferentiableAt_iff_differentiableAt.mpr
        ((hasDerivAt_id r).const_add A).differentiableAt
    have hd : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ A + s) r) (1 : ℝ) = 1 := by
      rw [mfderiv_eq_fderiv]
      exact ((hasDerivAt_id r).const_add A).deriv
    have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (I'' := I) r hr hadd (1 : ℝ)
    rw [hd] at hcomp
    change (S.family.metric (tau r)).inner (beta r)
      ((mfderiv 𝓘(ℝ, ℝ) I alpha (A + r)) (1 : ℝ))
      ((mfderiv 𝓘(ℝ, ℝ) I alpha (A + r)) (1 : ℝ)) = _
    rw [show (mfderiv 𝓘(ℝ, ℝ) I beta r) (1 : ℝ) =
      (mfderiv 𝓘(ℝ, ℝ) I alpha (A + r)) (1 : ℝ) from hcomp]
  exact MetricConnectionFamilyOn.exists_timeH1_extChartAt S.family hMet p beta tau hfAC hsrcShift
    hchart (continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2))
    (fun r hr ↦ hreg _ (hmaps hr)) hInt

end DifferentialGeometry.PDE.RicciFlow.Perelman
