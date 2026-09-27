import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredScalarBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelCoveringBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBoundedCurvatureFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Bundle
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

section Bookkeeping

theorem parabolicTime_mem_backwardCarrier {Hd s B u : ℝ} (hB : 0 < B)
    (hs0 : s ≤ 0)
    (hlo : -(B * (2 * Hd + s)) ≤ u) (hhi : u ≤ 0) :
    DifferentialGeometry.PDE.RicciFlow.parabolicTime s B u ∈ Set.Icc (-(2 * Hd)) 0 := by
  constructor
  · have h1 : -(2 * Hd + s) ≤ u / B := by
      rw [le_div_iff₀ hB]
      nlinarith [hlo]
    dsimp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime]
    linarith
  · have h1 : u / B ≤ 0 := div_nonpos_of_nonpos_of_nonneg hhi hB.le
    dsimp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime]
    linarith

theorem parabolicTime_mem_backwardRegular {Hd s B u : ℝ} (hB : 0 < B)
    (hs0 : s ≤ 0) (hlo : -(B * (2 * Hd + s)) < u) (hhi : u < 0) :
    DifferentialGeometry.PDE.RicciFlow.parabolicTime s B u ∈ Set.Ioo (-(2 * Hd)) 0 := by
  constructor
  · have h1 : -(2 * Hd + s) < u / B := by
      rw [lt_div_iff₀ hB]
      nlinarith [hlo]
    dsimp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime]
    linarith
  · have h1 : u / B < 0 := div_neg_of_neg_of_pos hhi hB
    dsimp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime]
    linarith

theorem sqrt_mul_renormalizedScale {B scale sigma : ℝ} (hB : 0 ≤ B) :
    Real.sqrt (B * scale) * sigma = Real.sqrt B * (Real.sqrt scale * sigma) := by
  rw [Real.sqrt_mul hB]
  ring

end Bookkeeping

section Crossing

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_scalar_eq_of_metricDistance_le {M : Type u}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [PreconnectedSpace M]
    {D : RealTimeInterval}
    {S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I3) (M := M) D}
    {s : ℝ} {z y : M} {A B D₀ : ℝ}
    (hA : S.scalar s z ≤ A) (hAB : A < B) (hBy : B ≤ S.scalar s y)
    (hD₀ : 0 ≤ D₀) (hd : metricDistance (S.base.metric s) z y ≤ D₀) :
    ∃ w : M, S.scalar s w = B ∧
      metricDistance (S.base.metric s) z w ≤ D₀ + 1 ∧
      metricDistance (S.base.metric s) w y ≤ D₀ + 1 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) :=
    ⟨(S.base.metric s).toRiemannianMetric⟩
  have hgfin : DifferentialGeometry.riemannianEDistOf (I := I3) (S.base.metric s) z y ≠ ⊤ :=
    DifferentialGeometry.riemannianEDistOf_ne_top (I := I3) (S.base.metric s) z y
  have hball : y ∈ riemannianClosedBallOf (I := I3) (S.base.metric s) z D₀ :=
    (ENNReal.le_ofReal_iff_toReal_le hgfin hD₀).mpr hd
  obtain ⟨gam, hsm, hg0, hg1, hlen⟩ :=
    exists_path_lintegral_speed_lt_of_mem_closedBall (I := I3) (S.base.metric s) hD₀
      one_pos hball
  have hcont : ContinuousOn (fun u : ℝ => S.scalar s (gam u)) (Set.Icc 0 1) :=
    (((DifferentialGeometry.PDE.RicciFlow.scalarSmoothOfSolution (I := I3) S s).continuous).comp
      hsm.continuous).continuousOn
  have hmem : B ∈ Set.Icc ((fun u : ℝ => S.scalar s (gam u)) 0)
      ((fun u : ℝ => S.scalar s (gam u)) 1) := by
    constructor
    · change S.scalar s (gam 0) ≤ B
      rw [hg0]
      exact le_of_lt (lt_of_le_of_lt hA hAB)
    · change B ≤ S.scalar s (gam 1)
      rw [hg1]
      exact hBy
  obtain ⟨u₀, hu₀, hval⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
  have hval' : S.scalar s (gam u₀) = B := hval
  have hpl : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      metricDistance (S.base.metric s) (gam a) (gam b) ≤ D₀ + 1 := by
    intro a b ha hab hb1
    have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ha hb1
    have hmono : (∫⁻ tau in Set.Icc a b, ENNReal.ofReal (Real.sqrt
          ((S.base.metric s).inner (gam tau)
            (mfderiv 𝓘(ℝ, ℝ) I3 gam tau
              (DifferentialGeometry.Analysis.Calculus.realTangentOne tau))
            (mfderiv 𝓘(ℝ, ℝ) I3 gam tau
              (DifferentialGeometry.Analysis.Calculus.realTangentOne tau))))) ≤
        ∫⁻ tau in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt
          ((S.base.metric s).inner (gam tau)
            (mfderiv 𝓘(ℝ, ℝ) I3 gam tau
              (DifferentialGeometry.Analysis.Calculus.realTangentOne tau))
            (mfderiv 𝓘(ℝ, ℝ) I3 gam tau
              (DifferentialGeometry.Analysis.Calculus.realTangentOne tau)))) :=
      MeasureTheory.lintegral_mono_set hsub
    have hlenab : (∫⁻ tau in Set.Icc a b, ENNReal.ofReal (Real.sqrt
          ((S.base.metric s).inner (gam tau)
            (mfderiv 𝓘(ℝ, ℝ) I3 gam tau
              (DifferentialGeometry.Analysis.Calculus.realTangentOne tau))
            (mfderiv 𝓘(ℝ, ℝ) I3 gam tau
              (DifferentialGeometry.Analysis.Calculus.realTangentOne tau))))) <
        ENNReal.ofReal (D₀ + 1) := lt_of_le_of_lt hmono hlen
    have hpl : Manifold.pathELength I3 gam a b ≤ ENNReal.ofReal (D₀ + 1) := by
      rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
      refine le_trans (le_of_eq ?_) hlenab.le
      refine MeasureTheory.lintegral_congr fun tau => ?_
      rw [← ofReal_norm, norm_eq_sqrt_real_inner]
      congr 2
    have hed : DifferentialGeometry.riemannianEDistOf (I := I3) (S.base.metric s) (gam a)
        (gam b) ≤ Manifold.pathELength I3 gam a b := by
      exact Manifold.riemannianEDist_le_pathELength (I := I3) (γ := gam) (a := a) (b := b)
        (hsm.contMDiffOn.mono (Set.subset_univ _)) rfl rfl hab
    have := ENNReal.toReal_mono (show (ENNReal.ofReal (D₀ + 1)) ≠ ⊤ by simp)
      (le_trans hed hpl)
    simpa only [metricDistance,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ D₀ + 1)] using this
  refine ⟨gam u₀, hval', ?_, ?_⟩
  · have := hpl 0 u₀ le_rfl hu₀.1 hu₀.2
    simpa only [hg0] using this
  · simpa only [hg1] using hpl u₀ 1 hu₀.1 hu₀.2 le_rfl

end Crossing

section Renormalization

def RecenteredAnchorEscapeData (eps kappa sigma : ℝ) (Phi : ℝ → ℝ) (A D : ℝ)
    (X : ℕ → NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ n : ℕ, ∃ i : ℕ, n ≤ i ∧ n ≤ (X n).depth i ∧ n ≤ (X n).scale i ∧
    ∃ s : ℝ, s ∈ Set.Icc (-((X n).depth i / 2)) 0 ∧
      ∃ z w y : ((X n).term i).M,
        ((X n).term i).S.scalar s z ≤ A ∧
        ((X n).term i).S.scalar s w = max (A + 1) 3 ∧
        (n : ℝ) + 1 ≤ ((X n).term i).S.scalar s y ∧
        metricDistance (((X n).term i).S.base.metric s) z w ≤ D ∧
        metricDistance (((X n).term i).S.base.metric s) w y ≤ D

def RecenteredAnchorEscape (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∀ eps A D : ℝ, 0 < eps → 0 < A → 0 ≤ D →
    ∀ X : ℕ → NormalizedSequence.{u} eps kappa sigma Phi,
      RecenteredAnchorEscapeData eps kappa sigma Phi A D X →
        ∃ X' : NormalizedSequence.{u} eps kappa sigma Phi, ¬ BoundedAtDistance X'

end Renormalization

section Producer

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem recenteredAnchorEscape {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    RecenteredAnchorEscape.{u} kappa sigma Phi := by
  intro eps A D heps hA hD X hX
  classical
  let B : ℝ := max (A + 1) 3
  have hB3 : 3 ≤ B := le_max_right _ _
  have hBpos : 0 < B := by linarith
  have hAle : A < B := by
    have h1 : A + 1 ≤ B := le_max_left _ _
    linarith
  choose i hi hdep hsca s hs z w y hz hw hy hzw hwy using hX
  have hdepth_pos : ∀ n, 0 < (X n).depth (i n) := fun n => (X n).depth_pos (i n)
  have hdepth_buf : ∀ n, eps⁻¹ ≤ (X n).depth (i n) := fun n => (X n).depth_buffer (i n)
  have hslow : ∀ n, -((X n).depth (i n) / 2) ≤ s n := fun n => (hs n).1
  have hs0 : ∀ n, s n ≤ 0 := fun n => (hs n).2
  have hmem : ∀ n, s n ∈ ((X n).interval (i n)).carrier := fun n => by
    rw [(X n).carrier_eq (i n)]
    exact ⟨by linarith [hdepth_pos n, hslow n], hs0 n⟩
  let depthFn : ℕ → ℝ := fun n => max eps⁻¹ (n : ℝ)
  have depthFn_pos : ∀ n, 0 < depthFn n := fun n =>
    lt_of_lt_of_le (inv_pos.mpr heps) (le_max_left _ _)
  have depthFn_ge : ∀ n, eps⁻¹ ≤ depthFn n := fun n => le_max_left _ _
  have depthFn_le : ∀ n, depthFn n ≤ B * ((X n).depth (i n) + s n) := by
    intro n
    have hd := hdepth_pos n
    have hb := hdepth_buf n
    have hge : (X n).depth (i n) / 2 ≤ (X n).depth (i n) + s n := by linarith [hslow n]
    have hstep1 : eps⁻¹ ≤ B * ((X n).depth (i n) + s n) := by
      have h2 : eps⁻¹ / 2 ≤ (X n).depth (i n) + s n := by linarith
      have h3 : 3 * (eps⁻¹ / 2) ≤ B * ((X n).depth (i n) + s n) := by nlinarith
      have h4 : eps⁻¹ ≤ 3 * (eps⁻¹ / 2) := by linarith [inv_pos.mpr heps]
      linarith
    have hstep2 : (n : ℝ) ≤ B * ((X n).depth (i n) + s n) := by nlinarith [hdep n, hge]
    exact max_le hstep1 hstep2
  let Dfun : ℕ → RealTimeInterval := fun n =>
    RealTimeInterval.closed (-(2 * depthFn n)) 0 (by have := depthFn_pos n; linarith)
  have hcarSub : ∀ n, (Dfun n).carrier ⊆
      (DifferentialGeometry.PDE.RicciFlow.parabolicInterval ((X n).interval (i n)) (s n) B
        (hmem n)).carrier := by
    intro n u hu
    have h2 : u ∈ Set.Icc (-(2 * depthFn n)) 0 := hu
    have hle : -(B * (2 * (X n).depth (i n) + s n)) ≤ u := by
      have h1 : 2 * depthFn n ≤ B * (2 * (X n).depth (i n) + s n) := by
        nlinarith [depthFn_le n, hs0 n, hBpos]
      linarith [h2.1]
    rw [DifferentialGeometry.PDE.RicciFlow.parabolicInterval_carrier,
      (X n).carrier_eq (i n)]
    exact parabolicTime_mem_backwardCarrier hBpos (hs0 n) hle h2.2
  have hregSub : ∀ n, (Dfun n).regular ⊆
      (DifferentialGeometry.PDE.RicciFlow.parabolicInterval ((X n).interval (i n)) (s n) B
        (hmem n)).regular := by
    intro n u hu
    have h2 : u ∈ Set.Ioo (-(2 * depthFn n)) 0 := hu
    have hle : -(B * (2 * (X n).depth (i n) + s n)) < u := by
      have h1 : 2 * depthFn n ≤ B * (2 * (X n).depth (i n) + s n) := by
        nlinarith [depthFn_le n, hs0 n, hBpos]
      linarith [h2.1]
    rw [DifferentialGeometry.PDE.RicciFlow.parabolicInterval_regular,
      (X n).regular_eq (i n)]
    exact parabolicTime_mem_backwardRegular hBpos (hs0 n) hle h2.2
  have depthFn_tendsto : Filter.Tendsto depthFn Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => le_max_right _ _) tendsto_natCast_atTop_atTop
  have scaleFn_pos : ∀ n, 0 < B * (X n).scale (i n) := fun n =>
    mul_pos hBpos ((X n).scale_pos (i n))
  have scaleFn_tendsto : Filter.Tendsto (fun n => B * (X n).scale (i n))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    nlinarith [hsca n, hB3]
  let termFn : ∀ n, PointedFlowData.{u, 0, 0} I3 (Dfun n) := fun n => {
    M := ((X n).term (i n)).M
    topology := ((X n).term (i n)).topology
    charted := ((X n).term (i n)).charted
    smooth := ((X n).term (i n)).smooth
    sigmaCompact := ((X n).term (i n)).sigmaCompact
    t2 := ((X n).term (i n)).t2
    t2TangentBundle := ((X n).term (i n)).t2TangentBundle
    basepoint := w n
    S := (DifferentialGeometry.PDE.RicciFlow.parabolicSolution ((X n).term (i n)).S (s n) B
      hBpos (hmem n)).timeRestrict (Dfun n)
    isSolution := isSolutionOn_timeRestrict
      (DifferentialGeometry.PDE.RicciFlow.parabolicSolution_isSolutionOn
        (((X n).term (i n)).S) ((X n).term (i n)).isSolution (s n) B hBpos (hmem n))
      (hcarSub n) (hregSub n) }
  let X' : NormalizedSequence.{u} eps kappa sigma Phi := {
    interval := Dfun
    term := termFn
    depth := depthFn
    scale := fun n => B * (X n).scale (i n)
    depth_pos := depthFn_pos
    depth_buffer := depthFn_ge
    scale_pos := scaleFn_pos
    depth_tendsto := depthFn_tendsto
    scale_tendsto := scaleFn_tendsto
    carrier_eq := fun n => rfl
    regular_eq := fun n => rfl
    connected := fun n => (X n).connected (i n)
    orientation := fun n => (X n).orientation (i n)
    complete := fun n t ht => by
      have htpar : DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B t ∈
          ((X n).interval (i n)).carrier := hcarSub n ht
      have hcomp := MetricComplete.complete_of_lower
        (((X n).term (i n)).atTime (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B t))
        ((X n).complete (i n) (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B t) htpar)
        (scaleMetric B hBpos (((X n).term (i n)).atTime
          (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B t)).metric)
        B hBpos (fun x v => le_of_eq (by simp))
      exact hcomp
    source_bound := fun n => by
      obtain ⟨C, hC⟩ := (X n).source_bound (i n)
      refine ⟨(B⁻¹) ^ 2 * C, fun t ht x => ?_⟩
      have hpr := DifferentialGeometry.PDE.RicciFlow.parabolicRmNormSq ((X n).term (i n)).S
        (s n) B hBpos (hmem n) t x
      have hb := hC (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B t) (hcarSub n ht) x
      have hnn : (0 : ℝ) ≤ (B⁻¹) ^ 2 := by positivity
      exact le_trans (le_of_eq hpr) (mul_le_mul_of_nonneg_left hb hnn)
    base_one := fun n => by
      change (DifferentialGeometry.PDE.RicciFlow.parabolicSolution ((X n).term (i n)).S (s n) B
        hBpos (hmem n)).scalar 0 (w n) = 1
      rw [DifferentialGeometry.PDE.RicciFlow.parabolicSolution_scalar]
      simp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime_zero, hw n]
      exact inv_mul_cancel₀ hBpos.ne'
    noncollapse := fun n => by
      have hpara := parabolicallyKappaNoncollapsedBelowScale_parabolicSolution
        (((X n).term (i n)).S) (s n) B hBpos (hmem n) _
        (Real.sqrt ((X n).scale (i n)) * sigma) ((X n).noncollapse (i n))
      have hres := parabolicallyKappaNoncollapsedBelowScale_timeRestrict (S := _) (D' := Dfun n)
        (hcarSub n) hpara
      rw [← sqrt_mul_renormalizedScale hBpos.le] at hres
      exact hres
    pinching := fun n u hu x => by
      have hpara := DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_paraSolution
        (((X n).term (i n)).S) hBpos (hmem n) ((X n).pinching (i n))
      have hres := hpara u (hcarSub n hu) x
      rwa [rescalePinchingFunction_rescale] at hres
    higher_good := fun n u hu x hx => by
      have hx' : 2 ≤ (DifferentialGeometry.PDE.RicciFlow.parabolicSolution ((X n).term (i n)).S
          (s n) B hBpos (hmem n)).scalar u x := hx
      have hyQ : 2 * B ≤ ((X n).term (i n)).S.scalar
          (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B u) x := by
        have hsc : 2 ≤ (DifferentialGeometry.PDE.RicciFlow.parabolicSolution ((X n).term (i n)).S
            (s n) B hBpos (hmem n)).scalar u x := hx'
        rw [DifferentialGeometry.PDE.RicciFlow.parabolicSolution_scalar] at hsc
        have hmul := mul_le_mul_of_nonneg_right hsc hBpos.le
        have heq : (B⁻¹ * ((X n).term (i n)).S.scalar
            (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B u) x) * B =
            ((X n).term (i n)).S.scalar
              (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B u) x := by
          field_simp
        rwa [heq] at hmul
      have hyB : 2 ≤ ((X n).term (i n)).S.scalar
          (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B u) x := by linarith
      have hwin : DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B u ∈
          Set.Icc (-((X n).depth (i n))) 0 := by
        have hle : -(B * ((X n).depth (i n) + s n)) ≤ u := by
          have h1 := depthFn_le n
          linarith [hu.1]
        refine ⟨?_, ?_⟩
        · have h1 : -((X n).depth (i n) + s n) ≤ u / B := by
            rw [le_div_iff₀ hBpos]
            nlinarith [hle]
          dsimp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime]
          linarith
        · have h1 : u / B ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu.2 hBpos.le
          dsimp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime]
          linarith [h1, hs0 n]
      have hsrc := (X n).higher_good (i n)
        (DifferentialGeometry.PDE.RicciFlow.parabolicTime (s n) B u) hwin x hyB
      have hres := (orientedWitness_paraSolution_iff (((X n).term (i n)).S)
        ((X n).orientation (i n)) hBpos (hmem n) u x eps kappa).mpr hsrc
      refine orientedWitness_timeRestrict (Dfun n) (S := _) ?_ ?_ hres
      · exact ⟨by have := depthFn_pos n; linarith [hu.1], hu.2⟩
      · intro v hv
        have hsmall : (eps * 2)⁻¹ ≤ depthFn n := by
          have h1 : (eps * 2)⁻¹ ≤ eps⁻¹ := by
            rw [inv_le_inv₀ (by positivity) heps]
            linarith
          linarith [depthFn_ge n]
        have h2 : (eps * (DifferentialGeometry.PDE.RicciFlow.parabolicSolution
            ((X n).term (i n)).S (s n) B hBpos (hmem n)).scalar u x)⁻¹ ≤ depthFn n := by
          have h3 : eps * 2 ≤ eps * (DifferentialGeometry.PDE.RicciFlow.parabolicSolution
              ((X n).term (i n)).S (s n) B hBpos (hmem n)).scalar u x :=
            mul_le_mul_of_nonneg_left hx' heps.le
          have h4 : (eps * (DifferentialGeometry.PDE.RicciFlow.parabolicSolution
              ((X n).term (i n)).S (s n) B hBpos (hmem n)).scalar u x)⁻¹ ≤ (eps * 2)⁻¹ := by
            have hpos : (0 : ℝ) < eps * (DifferentialGeometry.PDE.RicciFlow.parabolicSolution
                ((X n).term (i n)).S (s n) B hBpos (hmem n)).scalar u x :=
              mul_pos heps (lt_of_lt_of_le (by norm_num) hx')
            rw [inv_le_inv₀ hpos (mul_pos heps (by norm_num))]
            exact h3
          exact le_trans h4 hsmall
        exact ⟨by linarith [hv.1, h2, hu.1], by linarith [hv.2, hu.2]⟩ }
  refine ⟨X', ?_⟩
  intro hbd
  obtain ⟨C, hC⟩ := hbd (Real.sqrt B * D + 1) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt (B * (C + 1) + 1)
  have hdist : metricDistance ((termFn n).S.base.metric 0) (termFn n).basepoint (y n) ≤
      Real.sqrt B * D + 1 := by
    change metricDistance ((DifferentialGeometry.PDE.RicciFlow.parabolicSolution
      ((X n).term (i n)).S (s n) B hBpos (hmem n)).base.metric 0) (w n) (y n) ≤
        Real.sqrt B * D + 1
    rw [DifferentialGeometry.PDE.RicciFlow.parabolicSolution_metric]
    simp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime_zero]
    rw [metricDistance_scaleMetric]
    nlinarith [Real.sqrt_nonneg B, hwy n]
  have hscal : C < (termFn n).S.scalar 0 (y n) := by
    change C < (DifferentialGeometry.PDE.RicciFlow.parabolicSolution ((X n).term (i n)).S
      (s n) B hBpos (hmem n)).scalar 0 (y n)
    rw [DifferentialGeometry.PDE.RicciFlow.parabolicSolution_scalar]
    simp only [DifferentialGeometry.PDE.RicciFlow.parabolicTime_zero]
    have h1 : B⁻¹ * ((n : ℝ) + 1) ≤ B⁻¹ * ((X n).term (i n)).S.scalar (s n) (y n) :=
      mul_le_mul_of_nonneg_left (hy n) (inv_nonneg.mpr hBpos.le)
    have h2 : C + 1 ≤ B⁻¹ * ((n : ℝ) + 1) := by
      rw [le_inv_mul_iff₀ hBpos]
      nlinarith
    linarith
  exact absurd (hC n (y n) hdist) (not_le.mpr hscal)

end Producer

section Reduction

theorem recenteredScalarBoundBeyondRadius_of_boundedAtDistanceShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hshell : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi 1 := by
  obtain ⟨eS, heS, hshell⟩ := hshell
  refine ⟨min eS 1, lt_min heS one_pos, fun eps heps hle A D hA hD _hrad => ?_⟩
  have hleS : eps ≤ eS := le_trans hle (min_le_left _ _)
  have hAB : A < max (A + 1) 3 := by
    have h1 : A + 1 ≤ max (A + 1) 3 := le_max_left _ _
    linarith
  by_contra hno
  push Not at hno
  have hdata : ∀ n : ℕ, ∃ (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ)
      (s : ℝ) (z y : (X.term i).M),
      n ≤ i ∧ n ≤ X.depth i ∧ n ≤ X.scale i ∧
      s ∈ Set.Icc (-(X.depth i / 2)) 0 ∧
      (X.term i).S.scalar s z ≤ A ∧
      metricDistance ((X.term i).S.base.metric s) z y ≤ D ∧
      max ((n : ℝ) + 1) (max (A + 1) 3) < (X.term i).S.scalar s y := by
    intro n
    obtain ⟨X, hX⟩ := hno (max ((n : ℝ) + 1) (max (A + 1) 3))
    have hev : ∀ᶠ i in Filter.atTop,
        n ≤ i ∧ n ≤ X.depth i ∧ n ≤ X.scale i := by
      filter_upwards [Filter.eventually_ge_atTop (n : ℕ),
        X.depth_tendsto.eventually_ge_atTop (n : ℝ),
        X.scale_tendsto.eventually_ge_atTop (n : ℝ)] with i h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨i, hi, h1, h2, h3⟩ := (hX.and_eventually hev).exists
    obtain ⟨s, hsmem, z, y, hz, hd, hcs⟩ := hi
    exact ⟨X, i, s, z, y, h1, h2, h3, hsmem, hz, hd, hcs⟩
  choose Xf iF sF zF yF hge_i hge_d hge_c hsmem hz hd hycs using hdata
  have hesc := recenteredAnchorEscape (kappa := kappa) (sigma := sigma) (Phi := Phi)
    eps A (D + 1) heps hA (by linarith) Xf ?_
  · obtain ⟨X', hX'⟩ := hesc
    exact hX' (hshell eps heps hleS X')
  · intro n
    have : PreconnectedSpace ((Xf n).term (iF n)).M :=
      ((Xf n).connected (iF n)).toPreconnectedSpace
    obtain ⟨w, hw, hzw, hwy⟩ := exists_scalar_eq_of_metricDistance_le
      (S := ((Xf n).term (iF n)).S) (s := sF n) (A := A) (B := max (A + 1) 3) (D₀ := D)
      (hz n) hAB (le_of_lt (lt_of_le_of_lt (le_max_right _ _) (hycs n))) hD (hd n)
    exact ⟨iF n, hge_i n, hge_d n, hge_c n, sF n, hsmem n, zF n, w, yF n,
      hz n, hw,
      le_of_lt (lt_of_le_of_lt (le_max_left ((n : ℝ) + 1) (max (A + 1) 3)) (hycs n)),
      hzw, hwy⟩

end Reduction

section ConeExclusion

theorem recenteredScalarBoundBeyondRadius_of_coneExclusion
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hesc : CurvatureEscapeRealization.{u} kappa sigma Phi)
    (hconstruction : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps →
      eps ≤ epsStar → ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        Nonempty (FiniteControlledRadius X) → Nonempty (RealizedFiniteHorn X.toFlowSequence))
    (hcone : FiniteHornConeLimitProducer.{u} kappa sigma Phi) :
    RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi 1 :=
  recenteredScalarBoundBeyondRadius_of_boundedAtDistanceShell
    (boundedAtDistance_of_curvatureEscapeRealization_of_finiteHornConstruction_of_coneLimitProducer
      hesc hconstruction hcone)

theorem recentered_source_bound_of_boundedAtDistanceShell
    {kappa sigma c : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) (hc : 0 < c)
    (hlocal : TerminalLocalPropagationBound.{u} kappa c)
    (hshell : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    RecenteredSourceBound.{u} kappa sigma Phi :=
  recentered_source_bound_of_canonical_beyondRadius hsigma hPhi hc hlocal
    (recenteredScalarBoundBeyondRadius_of_boundedAtDistanceShell hshell)

end ConeExclusion

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
