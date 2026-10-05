import DifferentialGeometry.Geometry.Collapse.SmallRadial
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.JointZeroPacketAssembled
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02UniformWitnesses
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause
/-!
The finite joint zero packet is produced on the same small model of each actual source.
Its diffeomorphisms remain explicit for returning all source maps to the original carrier.
-/
set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Manifold
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.MetricSmoothing DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry Set Filter Bundle
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped Manifold ContDiff ENNReal Topology
universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓡 3
namespace DifferentialGeometry.Geometry.Collapse
def smallThreeModel (M : Type u) [i1 : MetricSpace M] [i2 : ChartedSpace E3 M]
    [i3 : IsManifold I3 ∞ M] [i4 : SigmaCompactSpace M] : SmallManifoldModel (I := I3) M := by
  let _sourceSecondCountable := ChartedSpace.secondCountable_of_sigmaCompact E3 M
  exact smallManifoldModel
theorem lfr49_finite_joint_zero_packet_smallSources
    (K : ℕ) (hK : 10 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [cX : ∀ i, ChartedSpace E3 (X i)]
    [sX : ∀ i, IsManifold I3 ∞ (X i)] [scX : ∀ i, SigmaCompactSpace (X i)]
    [hXc : ∀ i, CompleteSpace (X i)]
    [connX : ∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤
      riemannianVolumeMeasure I3 (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {δ ε e T : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ R : ℝ, T ≤ R ∧ ∃ hR : 0 < R,
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
      letI _limitMetric := mN
      letI _limitCharts := cN
      ∃ (_modelSmooth : IsManifold I3 ∞ N)
        (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : N → Type _))
        (q : N),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI _limitBundle : RiemannianBundle (fun x : N => TangentSpace I3 x) :=
           ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold I3 N) ∧
        (∀ (x : N) (v w : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x v w) ∧
        PointedGHConverges (fun j => p (k j)) q ∧
        ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
          (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
            Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
        ∃ (Ns : Type) (_modelTopology : TopologicalSpace Ns) (_modelCharts : ChartedSpace E3 Ns)
          (_modelSmooth : IsManifold I3 ∞ Ns) (_modelHomeomorph : Ns ≃ₜ N),
        ∀ᶠ j in atTop,
          Nonempty (@KleinerLottApprox (X (k j)) C
            ((mX (k j)).rescale R⁻¹ (inv_pos.mpr hR)) mC (p (k j)) o δ) ∧
          (letI _sourceRescaled := (mX (k j)).rescale R⁻¹ (inv_pos.mpr hR)
          let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (g (k j))
          ∃ F : X (k j) → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
            (∃ O : Set (X (k j)), IsOpen O ∧
              {x : X (k j) | 1 / 10 ≤ dist x (p (k j)) ∧ dist x (p (k j)) ≤ 10} ⊆ O ∧
              ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O) ∧
            (∀ x, |F x - Metric.infDist x {p (k j)}| < e) ∧
            (∀ x, x ∉ {x : X (k j) | 1 / 20 < dist x (p (k j)) ∧ dist x (p (k j)) < 20} →
              F x = Metric.infDist x {p (k j)}) ∧
            (∀ x y, |(F x - Metric.infDist x {p (k j)}) - (F y - Metric.infDist y {p (k j)})| ≤
              ε * dist x y) ∧
            (∀ x, 0 ≤ F x) ∧ F (p (k j)) = 0 ∧
            (∀ q' ∈ {x : X (k j) | 1 / 10 ≤ dist x (p (k j)) ∧ dist x (p (k j)) ≤ 10},
              1 - ε ≤ Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ∧
                Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ≤ 1 + ε) ∧
            (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x (p (k j)) ∧
              dist x (p (k j)) < 2 + e) ∧
            F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆
              {x : X (k j) | 1 / 10 ≤ dist x (p (k j)) ∧ dist x (p (k j)) ≤ 10} ∧
            (∃ O' : Set (X (k j)), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
              ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q' ∈ O', gradFun gR F q' ≠ 0) ∧
            ∃ L' : ℝ, 0 ≤ L' ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L') ∧
              ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
              (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
              (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
              tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
                {x : X (k j) | 1 / 5 - e < dist x (p (k j)) ∧ dist x (p (k j)) < 9 / 10 + e} ∧
              ∀ q', Real.sqrt (gR.inner q'
                (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')
                (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')) ≤ L' * (1 + ε)) ∧
          ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X (k j)) Ns ∞,
            Ψ.source = Metric.ball (p (k j)) (ρ' * R) ∧ Ψ.target = univ := by
  let S := fun i => smallThreeModel (X i)
  let Y := fun i => (S i).Carrier
  let mY := fun i => (S i).metricSpace
  let smallMetrics := mY
  let smallCharts := fun i => (S i).charts
  let smallSmooth := fun i => (S i).smooth
  let smallSigma : ∀ i, SigmaCompactSpace (Y i) := fun i => smallModelSigmaCompact (S i)
  let smallComplete : ∀ i, CompleteSpace (Y i) :=
    fun i => (S i).isometryEquiv.completeSpace
  let smallConnected : ∀ i, ConnectedSpace (Y i) :=
    fun i => (S i).diffeo.toHomeomorph.connectedSpace_iff.mpr inferInstance
  let gY := fun i => (S i).metric (g i)
  let pY := fun i => (S i).diffeo.symm (p i)
  have hm : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b) :=
    fun i => (S i).metric_aligned (g i) (hmetric i)
  have hvY : ∀ᶠ i in atTop, ENNReal.ofReal v ≤ ballVolume (gY i) (pY i) r := by
    filter_upwards [hvol] with i hi
    rw [smallModel_ballVolume, Diffeomorph.apply_symm_apply]
    exact hi
  have hcY : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (gY i) (pY i) R, curvDerivNorm k (gY i) y ≤ A R := by
    intro R hR
    filter_upwards [hcurv R hR] with i hi
    intro k hk y hy
    rw [smallModel_curvDerivNorm]
    apply hi k hk ((S i).diffeo y)
    rw [smallModel_ball_preimage] at hy
    simpa only [mem_preimage, pY, Diffeomorph.apply_symm_apply] using hy
  have hsY : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (gY i) (pY i) (L i),
      SectionalBoundedBelowAt (gY i) y (-η i) := by
    filter_upwards [hsec] with i hi
    intro y hy
    apply sectionalBoundedBelowAt_pullbackMetricCross (g i) (S i).diffeo y
    apply hi ((S i).diffeo y)
    rw [smallModel_ball_preimage] at hy
    simpa only [mem_preimage, pY, Diffeomorph.apply_symm_apply] using hy
  obtain ⟨k, hk, R, hTR, hR, N, mN, cN, sN, G, q, hproper, hconnected, hriem,
    hsecN, hGH, C, mC, o, hcone, hlim, Ns, tNs, cNs, sNs, hhome, hpackets⟩ :=
    lfr49_finite_joint_zero_packet K hK hr hv A gY hm pY hvY hcY hη hL hsY
      hδ hδ1 hε hε1 he he1
  let limitMetric := mN
  let limitCharts := cN
  let limitSmooth := sN
  let coneMetric := mC
  let modelTopology := tNs
  let modelCharts := cNs
  let modelSmooth := sNs
  have hGHOriginal : PointedGHConverges (fun j => p (k j)) q :=
    hGH.comap_source_isometry (fun j => (S (k j)).isometryEquiv.symm) (fun j => rfl)
  refine ⟨k, hk, R, hTR, hR, N, mN, cN, sN, G, q, hproper, hconnected, hriem,
    hsecN, hGHOriginal, C, mC, o, hcone, hlim, Ns, tNs, cNs, sNs, hhome, ?_⟩
  filter_upwards [hpackets] with j hj
  rcases hj with ⟨happrox, hradial, hcharts⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases happrox with ⟨approx⟩
    have transported := smallModel_backCone (mM := mX (k j)) (S (k j))
      (pY (k j)) R⁻¹ (inv_pos.mpr hR) approx
    simpa only [pY, Diffeomorph.apply_symm_apply] using Nonempty.intro transported
  · rcases hradial with ⟨F, hF⟩
    refine ⟨smallModel_backFunction (mM := mX (k j)) (S (k j)) F, ?_⟩
    have ht := smallModel_radial_spec_back (mM := mX (k j)) (S (k j)) (g (k j))
      R hR (pY (k j)) F ε e (1 / 10) 10 le_rfl le_rfl hF
    simpa only [pY, Diffeomorph.apply_symm_apply, mem_ofPred_eq] using ht
  · intro level hlevel
    obtain ⟨chart, hsource, htarget⟩ := hcharts level hlevel
    refine ⟨smallModel_backPartial (mM := mX (k j)) (S (k j)) chart, ?_, ?_⟩
    · have ht := smallModel_backPartial_ball_source (mM := mX (k j)) (S (k j))
        chart (pY (k j)) (level * R) hsource
      simpa only [pY, Diffeomorph.apply_symm_apply] using ht
    · rw [smallModel_backPartial_target, htarget]
def smallCompactThreeModel (M : Type u) [i5 : MetricSpace M] [i6 : ChartedSpace E3 M]
    [i7 : IsManifold I3 ∞ M] [i8 : CompactSpace M] : SmallManifoldModel (I := I3) M := by
  let _sourceSecondCountable := ChartedSpace.secondCountable_of_sigmaCompact E3 M
  exact smallManifoldModel
theorem lpa02_uniform_joint_zero_witnesses_smallSources
    {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [cX : ∀ i, ChartedSpace E3 (X i)]
    [sX : ∀ i, IsManifold I3 ∞ (X i)] [cptX : ∀ i, CompactSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    {ε δ' e T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ' : 0 < δ') (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop, ∀ (p : X i) (r : ℝ) (hr : 0 < r),
      r ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
      ∃ s ∈ Icc T V, ∃ hs : 0 < s,
      ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
        letI _limitMetric := mN
        letI _limitCharts := cN
        ∃ (_limitSmooth : IsManifold I3 ∞ N)
          (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : N → Type _))
          (q : N),
          ProperSpace N ∧ ConnectedSpace N ∧
          (letI _limitBundle : RiemannianBundle (fun x : N => TangentSpace I3 x) :=
           ⟨G.toRiemannianMetric⟩
           IsRiemannianManifold I3 N) ∧
          (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
          fourPointComparison 0 (univ : Set N) ∧
          (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
            f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            ProperSpace C ∧
            (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
              Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
          ∃ (Ns : Type) (_modelTopology : TopologicalSpace Ns) (_modelCharts : ChartedSpace E3 Ns)
            (_modelSmooth : IsManifold I3 ∞ Ns) (_modelHomeomorph : Ns ≃ₜ N),
            (∀ y ∈ Metric.ball p (400 * (s * r)),
              SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2))) ∧
            Nonempty (@KleinerLottApprox (X i) C
              ((mX i).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))) mC p o δ) ∧
            (letI _sourceRescaled := (mX i).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))
            let gR := scaleMetric ((s * r)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (mul_pos hs hr)) 2) (g i)
            ∃ F : X i → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
              (∃ O : Set (X i), IsOpen O ∧ {x : X i | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O) ∧
              (∀ x, |F x - Metric.infDist x {p}| < e) ∧
              (∀ x, x ∉ {x : X i | 1 / 20 < dist x p ∧ dist x p < 20} →
                F x = Metric.infDist x {p}) ∧
              (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
                ε * dist x y) ∧
              (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
              (∀ q' ∈ {x : X i | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
                1 - ε ≤ Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ∧
                  Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ≤ 1 + ε) ∧
              (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
              F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : X i | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
              (∃ O' : Set (X i), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q' ∈ O', gradFun gR F q' ≠ 0) ∧
              ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
                ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
                (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
                (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
                tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
                  {x : X i | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
                ∀ q', Real.sqrt (gR.inner q'
                  (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')
                  (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')) ≤ L * (1 + ε)) ∧
            ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X i) Ns ∞,
              Ψ.source = Metric.ball p (ρ' * (s * r)) ∧ Ψ.target = univ := by
  let S := fun i => smallCompactThreeModel (X i)
  let Y := fun i => (S i).Carrier
  let mY := fun i => (S i).metricSpace
  let smallMetrics := mY
  let smallCharts := fun i => (S i).charts
  let smallSmooth := fun i => (S i).smooth
  let smallCompact : ∀ i, CompactSpace (Y i) :=
    fun i => (S i).diffeo.toHomeomorph.symm.compactSpace
  let gY := fun i => (S i).metric (g i)
  have hm : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b) :=
    fun i => (S i).metric_aligned (g i) (hmetric i)
  have hs : ∀ i (p : Y i),
      ENNReal.ofReal (α i * firstVolumeScale (gY i) p (α i)⁻¹) ≤
        curvatureRadius (gY i) p := by
    intro i p
    rw [smallModel_firstVolumeScale, smallModel_curvatureRadius]
    exact hstand i ((S i).diffeo p)
  have hd : ∀ i (p : Y i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (gY i) p (C * firstVolumeScale (gY i) p v),
        curvatureDerivativeNorm (gY i) k y ≤
          A C v * (firstVolumeScale (gY i) p v ^ (k + 2))⁻¹ := by
    intro i p v hv hvc hav C hC hCa k hk y hy
    rw [smallModel_curvatureDerivativeNorm, smallModel_firstVolumeScale]
    apply hder i ((S i).diffeo p) v hv hvc hav C hC hCa k hk ((S i).diffeo y)
    rw [smallModel_ball_preimage, smallModel_firstVolumeScale] at hy
    exact hy
  obtain ⟨V, hTV, δ, hδ, hδδ', hpackets⟩ :=
    lpa02_uniform_joint_zero_witnesses (T := T) gY hm hα hs K hK A hA hd hΛ hw hwc
      hε hε1 hδ' he he1
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  filter_upwards [hpackets] with i hi
  intro p r hr hbound
  have hboundY : r ≤ 2 * firstVolumeScale (gY i) ((S i).diffeo.symm p)
      (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
    rw [smallModel_firstVolumeScale, Diffeomorph.apply_symm_apply]
    exact hbound
  obtain ⟨scale, hscale, hscalePos, N, mN, cN, sN, G, q, hproper, hconnected,
    hriem, hsec, hfour, hsegments, C, mC, o, hcone, hproperC, hlim,
    Ns, tNs, cNs, sNs, hhome, hcurvature, happrox, hradial, hcharts⟩ :=
    hi ((S i).diffeo.symm p) r hr hboundY
  let limitMetric := mN
  let limitCharts := cN
  let limitSmooth := sN
  let coneMetric := mC
  let modelTopology := tNs
  let modelCharts := cNs
  let modelSmooth := sNs
  refine ⟨scale, hscale, hscalePos, N, mN, cN, sN, G, q, hproper, hconnected,
    hriem, hsec, hfour, hsegments, C, mC, o, hcone, hproperC, hlim,
    Ns, tNs, cNs, sNs, hhome, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hyS : (S i).diffeo.symm y ∈ Metric.ball ((S i).diffeo.symm p)
        (400 * (scale * r)) := by
      have hd := (S i).isometryEquiv.symm.dist_eq y p
      change dist ((S i).diffeo.symm y) ((S i).diffeo.symm p) = dist y p at hd
      simpa only [Metric.mem_ball, hd] using hy
    have hb := hcurvature ((S i).diffeo.symm y) hyS
    have hmetricBack :
        Diffeomorph.pullbackMetricCross (gY i) (S i).diffeo.symm = g i := by
      dsimp only [gY]
      rw [SmallManifoldModel.metric, Diffeomorph.pullbackMetricCross_trans,
        Diffeomorph.symm_trans_self, Diffeomorph.pullbackMetricCross_refl]
    simpa only [hmetricBack] using
      sectionalBoundedBelowAt_pullbackMetricCross (gY i) (S i).diffeo.symm y hb
  · rcases happrox with ⟨approx⟩
    have transported := smallModel_backCone (mM := mX i) (S i)
      ((S i).diffeo.symm p) (scale * r)⁻¹ (inv_pos.mpr (mul_pos hscalePos hr)) approx
    simpa only [Diffeomorph.apply_symm_apply] using Nonempty.intro transported
  · rcases hradial with ⟨F, hF⟩
    refine ⟨smallModel_backFunction (mM := mX i) (S i) F, ?_⟩
    have ht := smallModel_radial_spec_back (mM := mX i) (S i) (g i)
      (scale * r) (mul_pos hscalePos hr) ((S i).diffeo.symm p) F ε e
      (3 / 40) 11 (by norm_num) (by norm_num) hF
    simpa only [Diffeomorph.apply_symm_apply, mem_ofPred_eq] using ht
  · intro level hlevel
    obtain ⟨chart, hsource, htarget⟩ := hcharts level hlevel
    refine ⟨smallModel_backPartial (mM := mX i) (S i) chart, ?_, ?_⟩
    · rw [smallModel_backPartial_source, hsource]
      ext x
      simp only [mem_image, Metric.mem_ball]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have ht := (S i).isometryEquiv.dist_eq y ((S i).diffeo.symm p)
        change dist ((S i).diffeo y) ((S i).diffeo ((S i).diffeo.symm p)) =
          dist y ((S i).diffeo.symm p) at ht
        rw [(S i).diffeo.apply_symm_apply] at ht
        rwa [ht]
      · intro hx
        refine ⟨(S i).diffeo.symm x, ?_, (S i).diffeo.apply_symm_apply x⟩
        have ht := (S i).isometryEquiv.symm.dist_eq x p
        exact ht.le.trans_lt hx
    · rw [smallModel_backPartial_target, htarget]
theorem lpa05_selected_sublevel_types_withCarrier_smallSources
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
    ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
    ∀ (X : ℕ → Type u) [_mX : ∀ i, MetricSpace (X i)] [_cX : ∀ i, ChartedSpace E3 (X i)]
      [_sX : ∀ i, IsManifold I3 ∞ (X i)] [_cptX : ∀ i, CompactSpace (X i)]
      (g : ∀ i, SmoothRiemannianMetric I3 (X i))
      (_hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
      (α : ℕ → ℝ), Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
    ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ → ℝ),
      (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
      (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
        ∀ C, 0 < C → C < α i → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
          curvatureDerivativeNorm (g i) k y ≤
            A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
    ∀ oX : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3,
    ∀ (Λ w : ℝ), 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
    ∃ S : ∀ i, SmallManifoldModel (I := I3) (X i),
    let Y := fun i => (S i).Carrier
    let mY := fun i => (S i).metricSpace
    letI _smallMetrics := mY
    letI _smallCharts := fun i => (S i).charts
    letI _smallSmooth := fun i => (S i).smooth
    ∃ oY : ∀ i, ManifoldOrientation I3 (Y i) 3,
      (∀ i, (S i).diffeo.symm.preservesOrientation (oX i) (oY i)) ∧
    let gY := fun i => (S i).metric (g i)
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
      ∀ (ρ : X i → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
      let ρY := ρ ∘ (S i).diffeo
      let hρY := fun p => hρ ((S i).diffeo p)
      ∃ (N C : Y i → Type) (_modelMetrics : ∀ b, MetricSpace (N b))
        (_modelCharts : ∀ b, ChartedSpace E3 (N b))
       
        (_modelSmooth : ∀ b, IsManifold I3 ∞ (N b))
        (_coneMetrics : ∀ b, MetricSpace (C b)) (o : ∀ b, C b),
        ∃ Z : ZeroModelFamily I3 (Y i) (gY i) ρY hρY β N C o δ ε e T V,
          (∀ c (hc : c ∈ Z.centres), ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
            CompactModelSublevel (oY i) (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
            PointSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
            CircleSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
            ProjectiveSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
            KleinSoulCoreSublevel (N (Z.zero c hc).model)
              {x | (Z.zero c hc).radial x ≤ ρ'}) ∧
          ∀ c (hc : c ∈ Z.centres) level,
            Nonempty ({x : Y i // (Z.zero c hc).radial x ≤ level} ≃ₜ
              {x : X i // smallModel_backFunction (mM := _mX i) (S i)
                (Z.zero c hc).radial x ≤ level}) := by
  classical
  obtain ⟨ε, δ', Λ', hε, hε1, hδ', hΛ', hrow⟩ :=
    lpa05_selected_sublevel_types_withCarrier hβ hβone hβζ hζone
  refine ⟨ε, δ', Λ', hε, hε1, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 X mX cX sX cptX g hmetric α hα hstand K hK A hA hder
    oX Λ w hΛ hw hwc
  let S := fun i => smallCompactThreeModel (X i)
  let Y := fun i => (S i).Carrier
  let mY := fun i => (S i).metricSpace
  let smallMetrics := mY
  let smallCharts := fun i => (S i).charts
  let smallSmooth := fun i => (S i).smooth
  let smallCompact : ∀ i, CompactSpace (Y i) :=
    fun i => (S i).diffeo.toHomeomorph.symm.compactSpace
  let oY := fun i => Classical.choose ((S i).exists_orientation (oX i))
  have hO : ∀ i, (S i).diffeo.symm.preservesOrientation (oX i) (oY i) :=
    fun i => Classical.choose_spec ((S i).exists_orientation (oX i))
  refine ⟨S, oY, hO, ?_⟩
  let gY := fun i => (S i).metric (g i)
  have hm : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b) :=
    fun i => (S i).metric_aligned (g i) (hmetric i)
  have hs : ∀ i (p : Y i),
      ENNReal.ofReal (α i * firstVolumeScale (gY i) p (α i)⁻¹) ≤
        curvatureRadius (gY i) p := by
    intro i p
    rw [smallModel_firstVolumeScale, smallModel_curvatureRadius]
    exact hstand i ((S i).diffeo p)
  have hd : ∀ i (p : Y i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (gY i) p (C * firstVolumeScale (gY i) p v),
        curvatureDerivativeNorm (gY i) k y ≤
          A C v * (firstVolumeScale (gY i) p v ^ (k + 2))⁻¹ := by
    intro i p v hv hvc hav C hC hCa k hk y hy
    rw [smallModel_curvatureDerivativeNorm, smallModel_firstVolumeScale]
    apply hder i ((S i).diffeo p) v hv hvc hav C hC hCa k hk ((S i).diffeo y)
    rw [smallModel_ball_preimage, smallModel_firstVolumeScale] at hy
    exact hy
  obtain ⟨V, hTV, δ, hδ, hδδ', hmodels⟩ :=
    hrow T hT hTΛ e he he1 Y gY hm α hα hs K hK A hA hd oY Λ w hΛ hw hwc
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  filter_upwards [hmodels] with i hi
  intro ρ hρ hcont hbound
  have hboundY : ∀ p, (ρ ∘ (S i).diffeo) p ≤
      2 * firstVolumeScale (gY i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
    intro p
    rw [smallModel_firstVolumeScale]
    exact hbound ((S i).diffeo p)
  obtain ⟨N, C, mN, cN, sN, mC, o, Z, htypes⟩ :=
    hi (ρ ∘ (S i).diffeo) (fun p => hρ ((S i).diffeo p))
      (hcont.comp (S i).diffeo.continuous) hboundY
  let modelMetrics := mN
  let modelCharts := cN
  let modelSmooth := sN
  let coneMetrics := mC
  refine ⟨N, C, mN, cN, sN, mC, o, Z, htypes, ?_⟩
  intro c hc level
  exact ⟨smallModel_sublevel_homeomorph (mM := mX i) (S i)
    (Z.zero c hc).radial level⟩
end DifferentialGeometry.Geometry.Collapse
