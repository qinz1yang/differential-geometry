import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureBlowupFrontierReduction

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem tendsto_add_const_atTop_nat (N : ℕ) :
    Filter.Tendsto (fun n : ℕ => n + N) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun x hx => ?_⟩)
  exact le_trans (Nat.le_add_right b N) (Nat.add_le_add_right hx N)

theorem highCurvatureFlowSequence_scalar_le_one_of_pastMaximum {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (k : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (-(t k * S.scalar (t k) (x k))) 0) :
    ∀ y : ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term k).M,
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term k).S.scalar s y ≤ 1 := by
  intro y
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

def MaximalPointSlabCompactnessAtPastMaximum {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) : Prop :=
  ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
    ∀ (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
      (htmem0 : ∀ i, t i ∈ Set.Ico (0 : ℝ) T)
      (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
      (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y : M,
        S.scalar s y ≤ S.scalar (t i) (x i)) →
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
            PreservesTangentOrientationAt ori o (F.partialDiffeomorph i) y hf)

theorem maximalPointSlabCompactnessAtPastMaximum_of_maximalPointSlabCompactness {T : ℝ}
    (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactness.{u} hT S hS o) :
    MaximalPointSlabCompactnessAtPastMaximum.{u} hT S hS o := by
  obtain ⟨kappa, hkpos, hmain⟩ := h
  refine ⟨kappa, hkpos, fun theta htheta x t htpos htmem0 hpos _hmax => ?_⟩
  exact hmain theta htheta x t htpos htmem0 hpos

theorem maximal_point_singularity_model_of_atPastMaximum
    [CompactSpace M] [ConnectedSpace M] [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactnessAtPastMaximum.{u} hT S hS o) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 := by
  obtain ⟨kappa, hkpos, hmain⟩ := h
  refine ⟨kappa, hkpos, fun theta htheta x t htmem hmax hscalar => ?_⟩
  have hev : ∀ᶠ i in Filter.atTop, 0 < S.scalar (t i) (x i) :=
    hscalar.eventually (Filter.eventually_gt_atTop (0 : ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hposN : ∀ i : ℕ, 0 < S.scalar (t (i + N)) (x (i + N)) :=
    fun i => hN (i + N) (Nat.le_add_left N i)
  have hscalarN : Filter.Tendsto (fun i => S.scalar (t (i + N)) (x (i + N)))
      Filter.atTop Filter.atTop := hscalar.comp (tendsto_add_const_atTop_nat N)
  have htposN : ∀ i : ℕ, 0 < t (i + N) := fun i => htheta.trans_le (htmem (i + N)).1
  have htmem0N : ∀ i : ℕ, t (i + N) ∈ Set.Ico (0 : ℝ) T :=
    fun i => ⟨le_trans htheta.le (htmem (i + N)).1, (htmem (i + N)).2⟩
  have hmaxN : ∀ i s, s ∈ Set.Icc 0 (t (i + N)) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t (i + N)) (x (i + N)) := fun i => hmax (i + N)
  obtain ⟨L, phi, F, hphi, hanc, hbase, hconvT, hcmp, hcap, ori, hor⟩ :=
    hmain theta htheta (fun i => x (i + N)) (fun i => t (i + N)) htposN htmem0N hposN hmaxN
  have hsource := highCurvatureFlowSequence_scalar_le_one_of_pastMaximum hT S hS
    (fun i => x (i + N)) (fun i => t (i + N)) htmem0N htposN hposN hmaxN
  have hlim : PointedFlowScalarBounded (I := I3) L 1 := by
    intro t' ht' y
    refine ⟨?_, ?_⟩
    · have ht0 : t' ≤ 0 := by simpa only [hanc.carrier_eq, Set.mem_Iic] using ht'
      exact DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_nonneg
        (I := I3) L hanc ht0 y
    · have ht0 : t' ≤ 0 := by simpa only [hanc.carrier_eq, Set.mem_Iic] using ht'
      obtain ⟨Ft, hFt⟩ := hconvT t' ht0
      refine metricScalar_le_one_of_canonical_metric_convergence
        ((highCurvatureFlowSequence hT S hS (fun i => x (i + N)) (fun i => t (i + N))
          htmem0N htposN hposN).atTime t')
        (L.atTime (I := I3) t') Ft hphi hFt ?_ y
      have hdeep' : ∀ᶠ k in Filter.atTop,
          -(t (k + N) * S.scalar (t (k + N)) (x (k + N))) ≤ t' := by
        have htend : Filter.Tendsto (fun k => S.scalar (t (k + N)) (x (k + N)))
            Filter.atTop Filter.atTop := hscalarN
        filter_upwards [htend.eventually_ge_atTop (-t' / theta)] with k hk
        have h1 : -t' / theta ≤ S.scalar (t (k + N)) (x (k + N)) := hk
        have h2 : -t' ≤ S.scalar (t (k + N)) (x (k + N)) * theta :=
          (div_le_iff₀ htheta).mp h1
        have h3 : theta ≤ t (k + N) := (htmem (k + N)).1
        have h4 : 0 < S.scalar (t (k + N)) (x (k + N)) := hposN k
        nlinarith [h2, h3, h4]
      filter_upwards [hdeep'] with k hk
      intro z
      simpa only [FlowSequence.atTime, PointedFlowData.atTime, highCurvatureFlowSequence,
        SolutionOn.family_metric, SolutionOn.scalar, SolutionFamily.scalar] using
        hsource k t' ⟨hk, ht0⟩ z
  let L' : BlowupLimit S o kappa (fun i => x (i + N)) (fun i => t (i + N)) :=
    blowupLimit_of_slab_compactness hT htheta S hS o (fun i => x (i + N)) (fun i => t (i + N))
      htposN htmem0N (fun i => (htmem (i + N)).1) hscalarN hposN
      L hanc hbase ori phi hphi F hcmp hcap hor
  let L'' : BlowupLimit S o kappa x t :=
    { model := L'.model
      ancient := L'.ancient
      normalized := L'.normalized
      orientation := L'.orientation
      subseq := fun i => L'.subseq i + N
      strictMono := fun _ _ hab => Nat.add_lt_add_right (L'.strictMono hab) N
      scale_pos := fun i => L'.scale_pos i
      map := L'.map
      exhaustion := L'.exhaustion
      base_mem := L'.base_mem
      base_eq := L'.base_eq
      oriented := L'.oriented
      capture := L'.capture
      convergence := L'.convergence }
  exact ⟨L'', hlim⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_pastMaximumSequence {T : ℝ} (hT : 0 < T) {theta t0 : ℝ}
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (htheta : 0 < theta) (htheta0 : theta ≤ t0) (ht0T : t0 < T) (x0 : M)
    (hpos0 : 0 < S.scalar t0 x0)
    (hmax0 : ∀ s, s ∈ Set.Icc 0 t0 → ∀ y : M, S.scalar s y ≤ S.scalar t0 x0) :
    ∃ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, 0 < t i) ∧ (∀ i, t i ∈ Set.Ico (0 : ℝ) T) ∧
      (∀ i, 0 < S.scalar (t i) (x i)) ∧
      (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y : M, S.scalar s y ≤ S.scalar (t i) (x i)) :=
  ⟨fun _ => x0, fun _ => t0, fun _ => lt_of_lt_of_le htheta htheta0,
    fun _ => ⟨le_trans htheta.le htheta0, ht0T⟩, fun _ => hpos0,
    fun _ s hs y => hmax0 s hs y⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
