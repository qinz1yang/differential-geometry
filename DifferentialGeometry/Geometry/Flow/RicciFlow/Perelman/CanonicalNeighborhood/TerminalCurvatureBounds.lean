import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarCompactControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAmbientMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarBallProducer

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_eventually_curvature_bound_of_terminal_scalar_le {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, ∃ delta K : ℝ, 0 < delta ∧ 0 < K ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
            ∀ y : (X.term i).M, (X.term i).S.scalar 0 y ≤ A →
              Set.Icc (-delta) 0 ⊆ (X.interval i).carrier ∧
              ∀ t ∈ Set.Icc (-delta) 0,
                curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ K := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ := local_propagation_of_modelBound hmod
  refine ⟨epsStar, hepsStar, fun eps heps hle sigma hsigma Phi hPhi A => ?_⟩
  let B : ℝ := 1 + max A (6 * Phi 0)
  have hPhi0 : 0 < Phi 0 := hPhi.pos 0
  have hB : 0 < B := by
    dsimp [B]
    linarith [le_max_right A (6 * Phi 0)]
  refine ⟨c / B, (C * (B + 1)) ^ 2, div_pos hc hB, by positivity, fun X => ?_⟩
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.scale_tendsto.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    X.pinching_error_eventually hPhi (L0 := B) (eta := 1) one_pos]
    with i hcyl hscale hpinch
  intro y hy
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hlow : -6 * Phi 0 ≤ (X.term i).S.scalar 0 y := by
    have h := neg_six_mul_phi_zero_le_scalar (hPhi.rescale (X.scale_pos i))
      (X.pinching i) (by simp [ThreeSpace]) hzero y
    have hres : rescalePinchingFunction (X.scale i) Phi 0 = (X.scale i)⁻¹ * Phi 0 := by
      simp only [rescalePinchingFunction, mul_zero]
    rw [hres] at h
    have hinv : (X.scale i)⁻¹ * Phi 0 ≤ Phi 0 := by
      have h1 : (X.scale i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hscale
      nlinarith
    linarith
  let L : ℝ := 1 + |(X.term i).S.scalar 0 y|
  have hL1 : 1 ≤ L := by
    dsimp [L]
    linarith [abs_nonneg ((X.term i).S.scalar 0 y)]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hLB : L ≤ B := by
    have habs : |(X.term i).S.scalar 0 y| ≤ max A (6 * Phi 0) :=
      abs_le.mpr ⟨by linarith [le_max_right A (6 * Phi 0)],
        hy.trans (le_max_left A (6 * Phi 0))⟩
    dsimp [L, B]
    linarith
  have htime : c / B ≤ c / L := div_le_div_of_nonneg_left hc.le hL hLB
  have hs : (0 : ℝ) ∈ Set.Icc (-(X.depth i / 2)) 0 :=
    ⟨by linarith [X.depth_pos i], le_rfl⟩
  obtain ⟨hcarrier, hcurv⟩ := hcyl 0 hs y
  have hsub : Set.Icc (-(c / B)) 0 ⊆ Set.Icc (0 - c / L) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  refine ⟨hsub.trans hcarrier, fun t ht => ?_⟩
  have hmem : (y, t) ∈ frozenBackwardCylinder (X.term i).S y 0 c c L := by
    refine ⟨?_, hsub ht⟩
    change riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0) y y ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have herror : (Phi (4 * X.scale i * L) + Phi 0) / X.scale i < 1 :=
    hpinch L ⟨hL1, hLB⟩
  have hbound := (hcurv y t hmem).2.2
  have hrm : Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S t y) ≤ C * (B + 1) := by
    refine hbound.trans ?_
    apply mul_le_mul_of_nonneg_left _ hC.le
    change L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i ≤ B + 1
    linarith
  have hsquare := (Real.sqrt_le_iff.mp hrm).2
  exact hsquare

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_eventually_curvature_bound_of_terminal_metric_scalar_le
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, ∃ delta B : ℝ, 0 < delta ∧ 0 < B ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ (L : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ), StrictMono f →
              ∀ (F : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
                (C : MetricConvergenceData F),
                (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i) →
                  ∀ K : Set L.M, IsCompact K →
                    (∀ x ∈ K, metricScalarAt L.metric x ≤ A) → ∀ᶠ i in atTop,
                      K ⊆ (F.partialDiffeomorph i).source ∧
                      Icc (-delta) 0 ⊆ (X.interval (f i)).carrier ∧
                      Ioo (-delta) 0 ⊆ (X.interval (f i)).regular ∧
                      ∀ t ∈ Icc (-delta) 0, ∀ x ∈ K,
                        curvDerivNormSq (I := I3) 0 ((X.term (f i)).S.base.metric t)
                          (F.partialDiffeomorph i x) ≤ B := by
  obtain ⟨epsStar, hepsStar, hprop⟩ :=
    exists_eventually_curvature_bound_of_terminal_scalar_le hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi A
  obtain ⟨delta, B, hdelta, hB, hcurv⟩ :=
    hprop eps heps hle sigma hsigma Phi hPhi (A + 1)
  refine ⟨delta, B, hdelta, hB, ?_⟩
  intro X L f hf F C hcanonical K hK hlimit
  obtain ⟨N, hN⟩ := KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical K hK 1 one_pos
  have hcurvSubseq := hf.tendsto_atTop.eventually (hcurv X)
  have hdepth := (X.depth_tendsto.comp hf.tendsto_atTop).eventually
    (eventually_ge_atTop delta)
  filter_upwards [eventually_ge_atTop N, hcurvSubseq, hdepth] with i hi hci hdi
  change delta ≤ X.depth (f i) at hdi
  refine ⟨(hN i hi).1, ?_, ?_, ?_⟩
  · intro t ht
    rw [X.carrier_eq (f i)]
    exact ⟨by linarith [ht.1], ht.2⟩
  · intro t ht
    rw [X.regular_eq (f i)]
    exact ⟨by linarith [ht.1], ht.2⟩
  · intro t ht x hx
    have herr := (abs_lt.mp ((hN i hi).2 x hx)).2
    have hscalarSource : (X.term (f i)).S.scalar 0 (F.partialDiffeomorph i x) ≤ A + 1 := by
      change metricScalarAt ((X.term (f i)).S.base.metric 0) (F.partialDiffeomorph i x) ≤ _
      have hlim := hlimit x hx
      change metricScalarAt ((X.term (f i)).S.base.metric 0) (F.partialDiffeomorph i x) -
        metricScalarAt L.metric x < 1 at herr
      linarith
    exact (hci (F.partialDiffeomorph i x) hscalarSource).2 t ht


theorem exists_terminal_slab_curvature_bound
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
          ∃ delta B : ℝ, 0 < delta ∧ 0 < B ∧ delta ≤ 2 * modelDepth eps ∧
            ∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in atTop,
              K ⊆ (L.maps.partialDiffeomorph i).source ∧
              Icc (-delta) 0 ⊆ (X.interval (L.subseq i)).carrier ∧
              Ioo (-delta) 0 ⊆ (X.interval (L.subseq i)).regular ∧
              ∀ t ∈ Icc (-delta) 0, ∀ x ∈ K,
                PointedFlowData.rmNormSq (X.term (L.subseq i)) t
                  (L.maps.partialDiffeomorph i x) ≤ B := by
  obtain ⟨epsStar, hepsStar, hbound⟩ :=
    exists_eventually_curvature_bound_of_terminal_metric_scalar_le hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X L
  obtain ⟨A, hA⟩ := L.scalar_bound
  obtain ⟨delta, B, hdelta, hB, hcurv⟩ := hbound eps heps hle sigma hsigma Phi hPhi A
  have hdepth : 0 < 2 * modelDepth eps := by
    apply mul_pos (by norm_num)
    exact inv_pos.mpr heps
  refine ⟨min delta (2 * modelDepth eps), B, lt_min hdelta hdepth, hB,
    min_le_right _ _, ?_⟩
  intro K hK
  filter_upwards [hcurv X L.space L.subseq L.strictMono L.maps L.converges
    L.canonical_domains K hK (fun x _ => hA x)] with i hi
  have hsub : Icc (-min delta (2 * modelDepth eps)) 0 ⊆ Icc (-delta) 0 :=
    Icc_subset_Icc (neg_le_neg (min_le_left _ _)) le_rfl
  refine ⟨hi.1, hsub.trans hi.2.1,
    (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) le_rfl).trans hi.2.2.1, ?_⟩
  intro t ht x hx
  exact (rmNormSq_eq_curvDerivNormSq X (L.subseq i) t
    (L.maps.partialDiffeomorph i x)).le.trans (hi.2.2.2 t (hsub ht) x hx)

theorem exists_eventually_curvature_bound_on_compact_of_terminal_metric_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ (L : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ), StrictMono f →
            ∀ (F : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
              (C : MetricConvergenceData F),
              (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i) →
                ∀ K : Set L.M, IsCompact K →
                  ∃ delta B : ℝ, 0 < delta ∧ 0 < B ∧ ∀ᶠ i in atTop,
                    K ⊆ (F.partialDiffeomorph i).source ∧
                    Icc (-delta) 0 ⊆ (X.interval (f i)).carrier ∧
                    Ioo (-delta) 0 ⊆ (X.interval (f i)).regular ∧
                    ∀ t ∈ Icc (-delta) 0, ∀ x ∈ K,
                      curvDerivNormSq (I := I3) 0 ((X.term (f i)).S.base.metric t)
                        (F.partialDiffeomorph i x) ≤ B := by
  obtain ⟨epsStar, hepsStar, hbound⟩ :=
    exists_eventually_curvature_bound_of_terminal_metric_scalar_le hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X L f hf F C hcanonical K hK
  obtain ⟨A, hA⟩ := (hK.image (metricScalar_smooth L.metric).continuous).bddAbove
  obtain ⟨delta, B, hdelta, hB, hcurv⟩ := hbound eps heps hle sigma hsigma Phi hPhi A
  exact ⟨delta, B, hdelta, hB,
    hcurv X L f hf F C hcanonical K hK (fun x hx => hA ⟨x, hx, rfl⟩)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem eventually_pointed_metric_uniformly_equivalent_on_compact_of_curvature_bound
    {X : FlowSequence.{u}} {L : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) L f)
    (C : MetricConvergenceData F)
    (hreference : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    {K : Set L.M} (hK : IsCompact K) {width : ℝ} (hw : 0 < width) {Bcurv : ℝ}
    (hcurv : ∀ᶠ i in atTop,
      Icc (-width) 0 ⊆ (X.interval (f i)).carrier ∧
      Ioo (-width) 0 ⊆ (X.interval (f i)).regular ∧
      ∀ t ∈ Icc (-width) 0, ∀ x ∈ K,
        PointedFlowData.rmNormSq (X.term (f i)) t (F.partialDiffeomorph i x) ≤ Bcurv) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ i in atTop,
      K ⊆ (F.partialDiffeomorph i).source ∧
      ∀ t ∈ Icc (-width) 0, ∀ x ∈ K, ∀ v : TangentSpace I3 x,
        B⁻¹ * L.metric.inner x v v ≤
          ((X.term (f i)).S.base.metric t).inner (F.partialDiffeomorph i x)
            (mfderiv I3 I3 (F.partialDiffeomorph i) x v)
            (mfderiv I3 I3 (F.partialDiffeomorph i) x v) ∧
        ((X.term (f i)).S.base.metric t).inner (F.partialDiffeomorph i x)
            (mfderiv I3 I3 (F.partialDiffeomorph i) x v)
            (mfderiv I3 I3 (F.partialDiffeomorph i) x v) ≤
          B * L.metric.inner x v v := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let A : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt Bcurv
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let Bt : ℝ := Real.exp (2 * A * width)
  have hBt : 1 ≤ Bt := Real.one_le_exp (by positivity)
  have hBt0 : 0 ≤ Bt := zero_le_one.trans hBt
  obtain ⟨N, hN⟩ := KappaSolutions.exists_pointed_full_ambient_quadratic_control
    C hreference K hK (1 / 2) (by norm_num)
  refine ⟨2 * Bt, by linarith, ?_⟩
  filter_upwards [hcurv, eventually_ge_atTop N] with i hi hiN
  obtain ⟨hcarrier, hregular, hbound⟩ := hi
  obtain ⟨hsource, hinit⟩ := hN i hiN
  refine ⟨hsource, ?_⟩
  let U : Set (X.term (f i)).M := F.partialDiffeomorph i '' K
  have hquad := twoTensorQuadBound_of_solutions (I := I3)
    (fun _ => (X.term (f i)).S) U (-width) 0 Bcurv
    (fun _ t ht y hy => by
      obtain ⟨x, hx, rfl⟩ := hy
      exact hbound t ht x hx)
  have hEq := metric_uniform_equivalent_on_closed_interval_of_solution
    (X.term (f i)).S (X.term (f i)).isSolution
    (show -width < 0 by linarith) hcarrier hregular
    (show (0 : ℝ) ∈ Icc (-width) 0 from ⟨by linarith, le_rfl⟩)
    hA (fun t ht y hy v => hquad.2 0 t ht y hy v)
  intro t ht x hx v
  have hfactor : metricEquivalenceFactor 1 A t 0 ≤ Bt := by
    simp only [metricEquivalenceFactor, one_mul, sub_zero]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨ht.1, ht.2.trans hw.le⟩)
      (mul_nonneg (by norm_num) hA)
  have htime := (metricUniformEquivalentOn_of_le (hEq 0 t ht) hfactor).2
    (F.partialDiffeomorph i x) (Set.mem_image_of_mem _ hx)
    (mfderiv I3 I3 (F.partialDiffeomorph i) x v)
  have hstartAbs :
      |((X.term (f i)).S.base.metric 0).inner (F.partialDiffeomorph i x)
          (mfderiv I3 I3 (F.partialDiffeomorph i) x v)
          (mfderiv I3 I3 (F.partialDiffeomorph i) x v) - L.metric.inner x v v| ≤
        (1 / 2 : ℝ) * L.metric.inner x v v := hinit x hx v
  have hstart := abs_le.mp hstartAbs
  have hnn : 0 ≤ L.metric.inner x v v :=
    DifferentialGeometry.metric_inner_self_nonneg L.metric x v
  constructor
  · calc
      _ = Bt⁻¹ * ((1 - (1 / 2 : ℝ)) * L.metric.inner x v v) := by
        rw [mul_inv_rev]
        ring
      _ ≤ Bt⁻¹ * (((X.term (f i)).S.base.metric 0).inner (F.partialDiffeomorph i x)
          (mfderiv I3 I3 (F.partialDiffeomorph i) x v)
          (mfderiv I3 I3 (F.partialDiffeomorph i) x v)) :=
        mul_le_mul_of_nonneg_left (by linarith [hstart.1]) (inv_nonneg.mpr hBt0)
      _ ≤ _ := htime.1
  · calc
      _ ≤ Bt * (((X.term (f i)).S.base.metric 0).inner (F.partialDiffeomorph i x)
          (mfderiv I3 I3 (F.partialDiffeomorph i) x v)
          (mfderiv I3 I3 (F.partialDiffeomorph i) x v)) := htime.2
      _ ≤ Bt * ((1 + (1 / 2 : ℝ)) * L.metric.inner x v v) :=
        mul_le_mul_of_nonneg_left (by linarith [hstart.2]) hBt0
      _ ≤ _ := by nlinarith [mul_nonneg hBt0 hnn]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem source_curvature_jets_uniform_on_closed_ball_of_compact_curvature_bound
    {X : FlowSequence.{u}} (P : MetricCompactLimit (X.atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    {width depthBound : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (p : P.limit.M) {radius : ℝ} (hradius : 0 ≤ radius) {C₀ : ℝ}
    (hslab : ∀ᶠ i in atTop,
      Icc (-depthBound) 0 ⊆ (X.interval (P.subseq i)).carrier ∧
      Ioo (-depthBound) 0 ⊆ (X.interval (P.subseq i)).regular ∧
      ∀ t ∈ Icc (-depthBound) 0,
        ∀ x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p (radius + 1),
          PointedFlowData.rmNormSq (X.term (P.subseq i)) t (P.maps.partialDiffeomorph i x) ≤ C₀) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ᶠ i in atTop,
      ∀ m : ℕ, ∀ t ∈ Icc (-width) 0,
      ∀ x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p radius,
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) (X.term (P.subseq i)).S
          m t (P.maps.partialDiffeomorph i x)) ≤ C m := by
  let width' := (width + depthBound) / 2
  have hww' : width < width' := by dsimp only [width']; linarith
  have hw'd : width' < depthBound := by dsimp only [width']; linarith
  have hw' : 0 < width' := hw.trans hww'
  let tau := (width' - width) / 2
  have htau : 0 < tau := by dsimp only [tau]; linarith
  have hcomplete : RiemannianMetricComplete (I := I3) P.limit.metric :=
    ⟨MetricComplete.complete (I := I3) P.limit P.limit_complete⟩
  let K := riemannianClosedBallOf (I := I3) P.limit.metric p (radius + 1)
  have hK : IsCompact K := hcomplete.closedEBall_isCompact p (radius + 1)
  have href : ∀ i, (P.convergence.metrics.domain i).referenceMetric =
      (P.convergence.metrics.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    rfl
  have hwindow : ∀ᶠ i in atTop,
      Icc (-width') 0 ⊆ (X.interval (P.subseq i)).carrier ∧
      Ioo (-width') 0 ⊆ (X.interval (P.subseq i)).regular ∧
      ∀ t ∈ Icc (-width') 0, ∀ x ∈ K,
        PointedFlowData.rmNormSq (X.term (P.subseq i)) t (P.maps.partialDiffeomorph i x) ≤ C₀ :=
    hslab.mono fun i hi =>
      ⟨(Icc_subset_Icc (by linarith) le_rfl).trans hi.1,
        (Ioo_subset_Ioo (by linarith) le_rfl).trans hi.2.1,
        fun t ht x hx => hi.2.2 t ⟨by linarith [ht.1], ht.2⟩ x hx⟩
  obtain ⟨B, hB, heq⟩ :=
    eventually_pointed_metric_uniformly_equivalent_on_compact_of_curvature_bound
      P.maps P.convergence.metrics href hK hw' hwindow
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let Kc := Real.sqrt (max C₀ 0) + 1
  have hKc : 0 < Kc := by dsimp only [Kc]; positivity
  have hCK : C₀ ≤ Kc ^ 2 := by
    have hs := Real.sq_sqrt (le_max_right C₀ 0)
    have hn := Real.sqrt_nonneg (max C₀ 0)
    dsimp only [Kc]
    nlinarith [le_max_left C₀ 0]
  let r := 1 / (2 * B)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrB : r < 1 / B := by
    dsimp only [r]
    exact div_lt_div_of_pos_left zero_lt_one hBp (by linarith)
  let R := r * Real.sqrt Kc
  have hR : 0 < R := mul_pos hr (Real.sqrt_pos.mpr hKc)
  have hrad : R / Real.sqrt Kc = r := by
    dsimp only [R]
    exact mul_div_cancel_right₀ r (Real.sqrt_pos.mpr hKc).ne'
  let C : ℕ → ℝ := fun m => max 0
    (shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (Kc * tau) R *
      Kc / Real.sqrt tau ^ m)
  refine ⟨C, fun m => le_max_left _ _, ?_⟩
  filter_upwards [heq, hwindow] with i hi hwindowi
  obtain ⟨hcarrier, hregular, hcurv⟩ := hwindowi
  have hsource : K ⊆ (P.maps.partialDiffeomorph i).source := hi.1
  have hsub (x : P.limit.M)
      (hx : x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p radius) :
      riemannianClosedBallOf (I := I3) P.limit.metric x 1 ⊆ K := by
    intro y hy
    calc
      riemannianEDistOf (I := I3) P.limit.metric p y ≤
          riemannianEDistOf (I := I3) P.limit.metric p x +
            riemannianEDistOf (I := I3) P.limit.metric x y :=
        riemannianEDistOf_triangle P.limit.metric p x y
      _ ≤ ENNReal.ofReal radius + ENNReal.ofReal 1 := add_le_add hx hy
      _ = ENNReal.ofReal (radius + 1) := (ENNReal.ofReal_add hradius zero_le_one).symm
  have hcpt (s : ℝ) (hs : s ∈ Set.Icc (-width') 0)
      (x : P.limit.M) (hx : x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p radius) :
      IsCompact (riemannianClosedBallOf (I := I3)
        ((X.term (P.subseq i)).S.base.metric s) (P.maps.map i x) r) ∧
      riemannianClosedBallOf (I := I3) ((X.term (P.subseq i)).S.base.metric s)
        (P.maps.map i x) r ⊆ (P.maps.partialDiffeomorph i) '' K := by
    have hball := hcomplete.closedEBall_isCompact x 1
    have hsmall := hsub x hx
    have himage : IsCompact ((P.maps.partialDiffeomorph i) ''
        riemannianClosedBallOf (I := I3) P.limit.metric x 1) :=
      hball.image_of_continuousOn
        ((P.maps.partialDiffeomorph i).contMDiffOn_toFun.continuousOn.mono (hsmall.trans hsource))
    have hcap := closedBall_subset_image_of_metric_lower P.limit.metric
      ((X.term (P.subseq i)).S.base.metric s) (P.maps.partialDiffeomorph i) x
      zero_lt_one hBp hrB hball (hsmall.trans hsource) (fun y hy v => by
        have hh := (hi.2 s hs y (hsmall hy) v).1
        have hmul := mul_le_mul_of_nonneg_left hh hBp.le
        rw [← mul_assoc, mul_inv_cancel₀ hBp.ne', one_mul] at hmul
        have hnn : 0 ≤ ((X.term (P.subseq i)).S.base.metric s).inner
            (P.maps.map i y) (mfderiv I3 I3 (P.maps.map i) y v)
            (mfderiv I3 I3 (P.maps.map i) y v) := by
          let g := (X.term (P.subseq i)).S.base.metric s
          let z : (X.term (P.subseq i)).M := P.maps.map i y
          let w : TangentSpace I3 z := mfderiv I3 I3 (P.maps.map i) y v
          change 0 ≤ g.inner z w w
          by_cases hw : w = 0
          · rw [hw]
            simp only [map_zero, le_refl]
          · exact (g.pos z w hw).le
        exact hmul.trans (mul_le_mul_of_nonneg_right (by nlinarith : B ≤ B ^ 2) hnn))
    refine ⟨himage.of_isClosed_subset ?_ hcap, hcap.trans (Set.image_mono hsmall)⟩
    exact isClosed_le
      (continuous_riemannianEDist ((X.term (P.subseq i)).S.base.metric s) (P.maps.map i x))
      continuous_const
  have hbound (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ico (-width) 0)
      (x : P.limit.M) (hx : x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p radius) :
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) (X.term (P.subseq i)).S
        m t (P.maps.map i x)) ≤ C m := by
    have hstart : t - tau ∈ Set.Icc (-width') 0 := by
      dsimp only [tau]
      constructor <;> linarith [ht.1, ht.2]
    have hshi := shi_bound_on_sliding_regular_window
      (X.term (P.subseq i)).S (X.term (P.subseq i)).isSolution
      (show -width' < 0 by linarith) htau hKc hR
      hcarrier
      hregular
      (show t ∈ Set.Ioo (-width' + tau) 0 from
        ⟨by dsimp only [tau]; linarith [ht.1], ht.2⟩) (P.maps.map i x)
      (by simpa only [hrad, riemannianClosedBallOf] using (hcpt _ hstart x hx).1)
      (by
        intro s hs y hy
        have hy' : y ∈ riemannianClosedBallOf (I := I3)
            ((X.term (P.subseq i)).S.base.metric (t - tau)) (P.maps.map i x) r := by
          simpa only [hrad, riemannianClosedBallOf, Set.mem_ofPred_eq] using hy
        obtain ⟨y, hyK, rfl⟩ := (hcpt _ hstart x hx).2 hy'
        have hh := (hcurv s ⟨hstart.1.trans hs.1, hs.2.trans ht.2.le⟩ y hyK).trans hCK
        simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
          PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04] using hh)
      m (P.maps.map i x) (by erw [riemannianEDistOf_self]; exact bot_le)
    exact hshi.trans (le_max_right _ _)
  intro m t ht x hx
  by_cases ht0 : t = 0
  · subst t
    have hc := solution_nablaKRm04NormSqIntrinsic_continuousWithinAt_terminal
      (X.term (P.subseq i)).S (X.term (P.subseq i)).isSolution
      (show -width' < 0 by linarith) hcarrier
      hregular m (P.maps.map i x)
    apply le_of_tendsto ((hc.mono Set.Iio_subset_Iic_self).sqrt)
    filter_upwards [Ioo_mem_nhdsLT (show -width < (0 : ℝ) by linarith)] with s hs
    exact hbound m s ⟨hs.1.le, hs.2⟩ x hx
  · exact hbound m t ⟨ht.1, lt_of_le_of_ne ht.2 ht0⟩ x hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_eventually_curvature_jets_on_closed_ball_of_terminal_metric_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
              ∀ p : P.limit.M, ∀ radius : ℝ, 0 ≤ radius →
                ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
                  ∀ᶠ i in atTop,
                    Icc (-delta) 0 ⊆ (X.interval (P.subseq i)).carrier ∧
                    Ioo (-delta) 0 ⊆ (X.interval (P.subseq i)).regular ∧
                    ∀ m : ℕ, ∀ t ∈ Icc (-delta) 0,
                      ∀ x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p radius,
                        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3)
                          (X.term (P.subseq i)).S m t (P.maps.partialDiffeomorph i x)) ≤ C m := by
  obtain ⟨epsStar, hepsStar, hcompact⟩ :=
    exists_eventually_curvature_bound_on_compact_of_terminal_metric_convergence hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius
  have hcomplete : RiemannianMetricComplete (I := I3) P.limit.metric :=
    ⟨MetricComplete.complete (I := I3) P.limit P.limit_complete⟩
  let K := riemannianClosedBallOf (I := I3) P.limit.metric p (radius + 1)
  have hK : IsCompact K := hcomplete.closedEBall_isCompact p (radius + 1)
  obtain ⟨depthBound, B, hdepth, _hB, hbound⟩ := hcompact eps heps hle sigma hsigma
    Phi hPhi X P.limit P.subseq P.strictMono P.maps P.convergence.metrics hcanonical K hK
  have hslab : ∀ᶠ i in atTop,
      Icc (-depthBound) 0 ⊆ (X.interval (P.subseq i)).carrier ∧
      Ioo (-depthBound) 0 ⊆ (X.interval (P.subseq i)).regular ∧
      ∀ t ∈ Icc (-depthBound) 0, ∀ x ∈ K,
        PointedFlowData.rmNormSq (X.term (P.subseq i)) t (P.maps.partialDiffeomorph i x) ≤ B := by
    filter_upwards [hbound] with i hi
    refine ⟨hi.2.1, hi.2.2.1, ?_⟩
    intro t ht x hx
    exact (rmNormSq_eq_curvDerivNormSq X (P.subseq i) t
      (P.maps.partialDiffeomorph i x)).le.trans (hi.2.2.2 t ht x hx)
  obtain ⟨C, hC, hjets⟩ :=
    source_curvature_jets_uniform_on_closed_ball_of_compact_curvature_bound
      P hcanonical (width := depthBound / 2) (half_pos hdepth) (half_lt_self hdepth)
      p hradius hslab
  refine ⟨depthBound / 2, half_pos hdepth, C, hC, ?_⟩
  filter_upwards [hslab, hjets] with i hi hji
  exact ⟨(Icc_subset_Icc (by linarith) le_rfl).trans hi.1,
    (Ioo_subset_Ioo (by linarith) le_rfl).trans hi.2.1, hji⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
