import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

structure BlowupLimit (S : SolutionOn (I := I3) (M := M) D)
    (o : TangentOrientationSection M) (kappa : ℝ) (x : ℕ → M) (t : ℕ → ℝ) where
  model : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval
  ancient : IsAncientKappaSolution kappa model
  normalized : PointedFlowScalarAtBase model 1
  orientation : TangentOrientationSection model.M
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  scale_pos : ∀ i, 0 < S.scalar (t (subseq i)) (x (subseq i))
  map : ℕ → PartialDiffeomorph I3 I3 model.M M ∞
  exhaustion : ExhaustsByOpen (fun i => (map i).source)
  base_mem : ∀ i, model.basepoint ∈ (map i).source
  base_eq : ∀ i, map i model.basepoint = x (subseq i)
  oriented : ∀ i y, y ∈ (map i).source →
    ∃ hf : Function.Bijective (mfderiv I3 I3 (map i) y),
      PreservesTangentOrientationAt orientation o (map i) y hf
  capture : ∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
    riemannianBallOf (I := I3)
      (rescaledMetric S (t (subseq i)) (S.scalar (t (subseq i)) (x (subseq i)))
        (scale_pos i) 0) (x (subseq i)) r ⊆ (map i) '' (map i).source
  convergence : ∀ K : Set model.M, IsCompact K → ∀ A : ℝ, 0 < A →
    ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
      Set.Icc (t (subseq i) - A / S.scalar (t (subseq i)) (x (subseq i))) (t (subseq i)) ⊆
        D.carrier ∧ K ⊆ (map i).source ∧
      Nonempty (MetricComparisonOn (fun s => model.S.base.metric s)
        (rescaledMetric S (t (subseq i)) (S.scalar (t (subseq i)) (x (subseq i))) (scale_pos i))
        (map i) K (Set.Icc (-A) 0) order eta)

noncomputable def blowupLimitOfSlabCompactness
    {T theta : ℝ} (hT : 0 < T) (htheta : 0 < theta)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    {kappa : ℝ} (x : ℕ → M) (t : ℕ → ℝ)
    (htpos : ∀ i, 0 < t i) (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T)
    (httheta : ∀ i, theta ≤ t i)
    (hscalar : Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hanc : IsAncientKappaSolution (I := I3) kappa L)
    (hnorm : PointedFlowScalarAtBase (I := I3) L 1)
    (hori : TangentOrientationSection L.M)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (F : PointedRiemannianConvergenceMaps (I := I3)
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0)
      (L.atTime (I := I3) 0) phi)
    (hcompact : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A →
      ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
        K ⊆ (F.partialDiffeomorph i).source ∧
        Nonempty (MetricComparisonOn (fun s => L.S.base.metric s)
          (fun s =>
            ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term (phi i)).S.base.metric s)
          (F.partialDiffeomorph i) K (Set.Icc (-A) 0) order eta))
    (hcap : ∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
      riemannianBallOf (I := I3)
          (rescaledMetric S (t (phi i)) (S.scalar (t (phi i)) (x (phi i)))
            (hpos (phi i)) 0) (x (phi i)) r ⊆
        (fun a => F.partialDiffeomorph i a) '' (F.partialDiffeomorph i).source)
    (hor : ∀ i y, y ∈ (F.partialDiffeomorph i).source →
      ∃ hf : Function.Bijective (mfderiv I3 I3 (F.partialDiffeomorph i) y),
        PreservesTangentOrientationAt hori o (F.partialDiffeomorph i) y hf) :
    BlowupLimit S o kappa x t := by
  exact { model := L
          ancient := hanc
          normalized := hnorm
          orientation := hori
          subseq := phi
          strictMono := hphi
          scale_pos := fun i => hpos (phi i)
          map := fun i => F.partialDiffeomorph i
          exhaustion := F.source_exhausts
          base_mem := fun i => F.base_mem i
          base_eq := fun i => F.basepoint_map i
          oriented := fun i y hy => hor i y hy
          capture := by
            intro r hr
            exact hcap r hr
          convergence := by
            intro K hK A hA order eta heta
            have hdeep : ∀ᶠ i in Filter.atTop,
                A ≤ S.scalar (t (phi i)) (x (phi i)) * t (phi i) := by
              have htend : Filter.Tendsto (fun i => S.scalar (t (phi i)) (x (phi i)))
                  Filter.atTop Filter.atTop := hscalar.comp hphi.tendsto_atTop
              filter_upwards [htend.eventually_ge_atTop (A / theta)] with i hi
              have h1 : A / theta ≤ S.scalar (t (phi i)) (x (phi i)) := hi
              have h2 : A ≤ S.scalar (t (phi i)) (x (phi i)) * theta :=
                (div_le_iff₀ htheta).mp h1
              have h3 : theta ≤ t (phi i) := httheta (phi i)
              have h4 : 0 < S.scalar (t (phi i)) (x (phi i)) := hpos (phi i)
              nlinarith [h2, h3, h4]
            filter_upwards [hcompact K hK A hA order eta heta, hdeep] with i hi hAd
            refine ⟨?_, hi.1, hi.2⟩
            intro s hs
            have hQ : 0 < S.scalar (t (phi i)) (x (phi i)) := hpos (phi i)
            have hle : A / S.scalar (t (phi i)) (x (phi i)) ≤ t (phi i) := by
              rw [div_le_iff₀ hQ]
              linarith [hAd]
            exact ⟨by linarith [hs.1, hle], lt_of_le_of_lt hs.2 (htmem (phi i)).2⟩ }

theorem metricScalar_le_one_of_canonical_metric_convergence
    (X : PointedRiemannianSeq.{u, 0, 0} (I := I3))
    (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
    {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (I := I3) X L phi)
    (hphi : StrictMono phi)
    (hconv : ∀ K : Set L.M, IsCompact K → metricSourceConvergesOn (I := I3) F
      (CanonicalMetricCompactness.canonicalSourceData (I := I3) F) K 2)
    (hsource : ∀ᶠ k in Filter.atTop, ∀ y : (X.obj k).M,
      metricScalarAt (I := I3) (X.obj k).metric y ≤ 1) :
    ∀ y : L.M, metricScalarAt (I := I3) L.metric y ≤ 1 := by
  intro y
  have hlim :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_canonical_metric_convergence
      (I := I3) (Phi := F) hconv y
  have hev : ∀ᶠ k in Filter.atTop,
      metricScalarAt (I := I3) (X.obj (phi k)).metric (F.map k y) ≤ 1 := by
    filter_upwards [hphi.tendsto_atTop.eventually hsource] with k hk
    exact hk (F.map k y)
  exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds hev

theorem maximal_point_singularity_model_of_slab_compactness
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (hgap : ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
        (htmem0 : ∀ i, t i ∈ Set.Ico (0 : ℝ) T)
        (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
      (∀ i, theta ≤ t i) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
      ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ)
        (F : PointedRiemannianConvergenceMaps (I := I3)
          ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime 0)
          (L.atTime (I := I3) 0) phi),
        StrictMono phi ∧ IsAncientKappaSolution (I := I3) kappa L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        (∀ t' : ℝ, t' ≤ 0 →
          ∃ Ft : PointedRiemannianConvergenceMaps (I := I3)
            ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime t')
            (L.atTime (I := I3) t') phi,
            ∀ K : Set L.M, IsCompact K → metricSourceConvergesOn (I := I3) Ft
              (CanonicalMetricCompactness.canonicalSourceData (I := I3) Ft) K 2) ∧
        (∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A →
          ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
            K ⊆ (F.partialDiffeomorph i).source ∧
            Nonempty (MetricComparisonOn (fun s => L.S.base.metric s)
              (fun s =>
                ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).term
                  (phi i)).S.base.metric s)
              (F.partialDiffeomorph i) K (Set.Icc (-A) 0) order eta)) ∧
        (∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
          riemannianBallOf (I := I3)
              (rescaledMetric S (t (phi i)) (S.scalar (t (phi i)) (x (phi i)))
                (hpos (phi i)) 0) (x (phi i)) r ⊆
            (fun a => F.partialDiffeomorph i a) '' (F.partialDiffeomorph i).source) ∧
        (∃ ori : TangentOrientationSection L.M, ∀ i y,
          y ∈ (F.partialDiffeomorph i).source →
          ∃ hf : Function.Bijective (mfderiv I3 I3 (F.partialDiffeomorph i) y),
            PreservesTangentOrientationAt ori o (F.partialDiffeomorph i) y hf)) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        (∀ i, 0 < S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 := by
  obtain ⟨kappa, hkpos, hmain⟩ := hgap
  refine ⟨kappa, hkpos, fun theta htheta x t htmem hmax hpos hscalar => ?_⟩
  have htthe : ∀ i, theta ≤ t i := fun i => (htmem i).1
  have htpos : ∀ i, 0 < t i := fun i => lt_of_lt_of_le htheta (htthe i)
  have htmem0 : ∀ i, t i ∈ Set.Ico (0 : ℝ) T :=
    fun i => ⟨le_trans htheta.le (htthe i), (htmem i).2⟩
  obtain ⟨L, phi, F, hphi, hanc, hnorm, hconvT, hcmp, hcap, ori, hor⟩ :=
    hmain theta htheta x t htpos htmem0 hpos htthe hscalar
  have hsource : ∀ (k : ℕ) (s : ℝ), s ∈ Set.Icc (-(t k * S.scalar (t k) (x k))) 0 →
      ∀ y : ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).term k).M,
        ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).term k).S.scalar s y ≤ 1 := by
    intro k s hs y
    have hQ : 0 < S.scalar (t k) (x k) := hpos k
    have htime : parabolicTime (t k) (S.scalar (t k) (x k)) s ∈ Set.Icc 0 (t k) := by
      refine ⟨?_, ?_⟩
      · have h1 : -(t k * S.scalar (t k) (x k)) ≤ s := hs.1
        have h2 : -t k ≤ s / S.scalar (t k) (x k) := by
          rw [le_div_iff₀ hQ]
          nlinarith [h1]
        simp only [parabolicTime]
        linarith
      · have h1 : s ≤ 0 := hs.2
        have h2 : s / S.scalar (t k) (x k) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg h1 hQ.le
        simp only [parabolicTime]
        linarith
    change metricScalarAt (I := I3)
      (scaleMetric (I := I3) (S.scalar (t k) (x k)) (hpos k)
        (S.base.metric (parabolicTime (t k) (S.scalar (t k) (x k)) s))) y ≤ 1
    have hscale := DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric
      (I := I3) (M := M) (S.scalar (t k) (x k)) (hpos k)
      (S.base.metric (parabolicTime (t k) (S.scalar (t k) (x k)) s)) y
    rw [hscale]
    refine (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hQ.le)).trans_eq (inv_mul_cancel₀ hQ.ne')
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family_metric] using
      hmax k (parabolicTime (t k) (S.scalar (t k) (x k)) s) htime y
  have hlim : PointedFlowScalarBounded (I := I3) L 1 := by
    intro t' ht' y
    refine ⟨?_, ?_⟩
    · have ht0 : t' ≤ 0 := by simpa only [hanc.carrier_eq, Set.mem_Iic] using ht'
      exact DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_nonneg
        (I := I3) L hanc ht0 y
    · have ht0 : t' ≤ 0 := by simpa only [hanc.carrier_eq, Set.mem_Iic] using ht'
      obtain ⟨Ft, hFt⟩ := hconvT t' ht0
      refine metricScalar_le_one_of_canonical_metric_convergence
        ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime t')
        (L.atTime (I := I3) t') Ft hphi hFt ?_ y
      have hdeep' : ∀ᶠ k in Filter.atTop,
          -(t k * S.scalar (t k) (x k)) ≤ t' := by
        have htend : Filter.Tendsto (fun k => S.scalar (t k) (x k))
            Filter.atTop Filter.atTop := hscalar
        filter_upwards [htend.eventually_ge_atTop (-t' / theta)] with k hk
        have h1 : -t' / theta ≤ S.scalar (t k) (x k) := hk
        have h2 : -t' ≤ S.scalar (t k) (x k) * theta :=
          (div_le_iff₀ htheta).mp h1
        have h3 : theta ≤ t k := htthe k
        have h4 : 0 < S.scalar (t k) (x k) := hpos k
        nlinarith [h2, h3, h4]
      filter_upwards [hdeep'] with k hk
      intro z
      simpa only [FlowSequence.atTime, PointedFlowData.atTime, highCurvatureFlowSequence,
        SolutionOn.family_metric, SolutionOn.scalar, SolutionFamily.scalar] using
        hsource k t' ⟨hk, ht0⟩ z
  refine ⟨blowupLimitOfSlabCompactness hT htheta S hS o
    x t htpos htmem0 htthe hscalar hpos L hanc hnorm ori phi hphi F hcmp hcap hor, ?_⟩
  unfold blowupLimitOfSlabCompactness
  exact hlim

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
