import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalClassificationNormalization

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
  {D : RealTimeInterval}

private theorem tendsto_add_const_atTop_nat (N : ℕ) :
    Filter.Tendsto (fun n : ℕ => n + N) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun x hx => ?_⟩)
  exact le_trans (Nat.le_add_right b N) (Nat.add_le_add_right hx N)

def MaximalPointSlabCompactness {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) : Prop :=
  ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
    ∀ (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
      (htmem0 : ∀ i, t i ∈ Set.Ico (0 : ℝ) T)
      (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
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

theorem maximal_point_singularity_model_of_maximalPointSlabCompactness
    [CompactSpace M] [ConnectedSpace M] [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactness.{u} hT S hS o) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 := by
  obtain ⟨kappa, hkpos, hmain⟩ := h
  obtain ⟨kappa', hkpos', hmain'⟩ :=
    maximal_point_singularity_model_of_slab_compactness hT S hS o ⟨kappa, hkpos, hmain⟩
  refine ⟨kappa', hkpos', fun theta htheta x t htmem hmax hscalar => ?_⟩
  have hev : ∀ᶠ i in Filter.atTop, 0 < S.scalar (t i) (x i) :=
    hscalar.eventually (Filter.eventually_gt_atTop (0 : ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hposN : ∀ i : ℕ, 0 < S.scalar (t (i + N)) (x (i + N)) :=
    fun i => hN (i + N) (Nat.le_add_left N i)
  have hscalarN : Filter.Tendsto (fun i => S.scalar (t (i + N)) (x (i + N)))
      Filter.atTop Filter.atTop := hscalar.comp (tendsto_add_const_atTop_nat N)
  obtain ⟨L', hL'⟩ := hmain' theta htheta (fun i => x (i + N)) (fun i => t (i + N))
    (fun i => htmem (i + N)) (fun i => hmax (i + N)) hposN hscalarN
  exact ⟨{ model := L'.model
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
           convergence := L'.convergence }, hL'⟩

theorem arbitrary_high_curvature_blowup_of_maximalPointSlabCompactness
    [CompactSpace M] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactness.{u} hT S hS o) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Set.Ico 0 T) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        Nonempty (BlowupLimit S o kappa x t) := by
  obtain ⟨kappa, hkpos, hmain⟩ := h
  refine ⟨kappa, hkpos, fun x t htmem hscalar => ?_⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hT2 : 0 < T / 2 := by linarith
  have hsub : Set.Icc 0 (T / 2) ⊆ (RealTimeInterval.closedOpen 0 T hT).carrier := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 (by linarith)⟩
  obtain ⟨C, _hCnn, hC⟩ :=
    exists_curvature_bound_on_carrier_interval_of_isSolutionOn (I := I3) (M := M) S hS hsub
  let Msc : ℝ := (3 : ℝ) ^ 2 * Real.sqrt C
  have hbound : ∀ s ∈ Set.Icc 0 (T / 2), ∀ y : M, S.scalar s y ≤ Msc := by
    intro s hs y
    have h1 := scalar_abs_le_rm (I := I3) (M := M) (S.base.metric s) y
    have h2 : normSq0S (I := I3) (S.base.metric s) y 4
        (metricRm04At (I := I3) (S.base.metric s) y) ≤ C := by
      have h := hC s hs y
      simpa only [SolutionOn.family_metric] using h
    have h3 : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
    rw [h3, hdim] at h1
    refine le_trans (le_abs_self _) (le_trans h1 ?_)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (by positivity)
  have hevbig : ∀ᶠ i in Filter.atTop, Msc < S.scalar (t i) (x i) :=
    hscalar.eventually (Filter.eventually_gt_atTop Msc)
  have hevtbig : ∀ᶠ i in Filter.atTop, T / 2 < t i := by
    filter_upwards [hevbig] with i hi
    by_contra hcon
    have hle : t i ≤ T / 2 := not_lt.mp hcon
    have hb := hbound (t i) ⟨(htmem i).1, hle⟩ (x i)
    linarith
  have hevpos : ∀ᶠ i in Filter.atTop, 0 < S.scalar (t i) (x i) :=
    hscalar.eventually (Filter.eventually_gt_atTop (0 : ℝ))
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 hevtbig
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 hevpos
  set N : ℕ := max N1 N2 with hNdef
  have hN1le : N1 ≤ N := le_max_left N1 N2
  have hN2le : N2 ≤ N := le_max_right N1 N2
  have htposN : ∀ i : ℕ, 0 < t (i + N) :=
    fun i => hT2.trans (hN1 (i + N) (le_trans hN1le (Nat.le_add_left N i)))
  have hposN : ∀ i : ℕ, 0 < S.scalar (t (i + N)) (x (i + N)) :=
    fun i => hN2 (i + N) (le_trans hN2le (Nat.le_add_left N i))
  have hscalarN : Filter.Tendsto (fun i => S.scalar (t (i + N)) (x (i + N)))
      Filter.atTop Filter.atTop := hscalar.comp (tendsto_add_const_atTop_nat N)
  obtain ⟨L, phi, F, hphi, hanc, hnorm, _hconvT, hcmp, hcap, ori, hor⟩ :=
    hmain (T / 2) hT2 (fun i => x (i + N)) (fun i => t (i + N)) htposN
      (fun i => htmem (i + N)) hposN
  let L' : BlowupLimit S o kappa (fun i => x (i + N)) (fun i => t (i + N)) :=
    blowupLimit_of_slab_compactness hT hT2 S hS o (fun i => x (i + N)) (fun i => t (i + N))
      htposN (fun i => htmem (i + N))
      (fun i => (hN1 (i + N) (le_trans hN1le (Nat.le_add_left N i))).le) hscalarN hposN
      L hanc hnorm ori phi hphi F hcmp hcap hor
  exact ⟨{ model := L'.model
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
           convergence := L'.convergence }⟩

theorem buffered_canonical_pullback_of_windowedCanonicalPullback
    (h : windowedCanonicalPullback.{u}) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
            (o : TangentOrientationSection M) (x : M) (t : ℝ),
            OrientedWitness S o delta kappa x t → Nonempty (CanonicalWitness S eps C1 C2 x t) :=
  buffered_canonical_pullback_of_classification.{u}
    (kappaUniformCanonicalClassification_of_windowedCanonicalPullback.{u} h)

omit [T2Space M] [SigmaCompactSpace M] in
theorem isEmpty_windowedModelWitness_of_one_le {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (x : M) (t : ℝ) {eps kappa : ℝ} (h : 1 ≤ eps) :
    IsEmpty (WindowedModelWitness eps kappa S x t) :=
  ⟨fun W => absurd W.eps_lt_one (not_lt.mpr h)⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem isEmpty_orientedWitness_of_one_le {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (o : TangentOrientationSection M) (x : M) (t : ℝ)
    {eps kappa : ℝ} (h : 1 ≤ eps) :
    IsEmpty (OrientedWitness S o eps kappa x t) :=
  ⟨fun hw => by
    obtain ⟨W, _, _⟩ := hw
    exact absurd W.eps_lt_one (not_lt.mpr h)⟩

theorem isEmpty_canonicalWitness_of_one_le {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (x : M) (t : ℝ) {eps C1 C2 : ℝ} (h : 1 ≤ eps) :
    IsEmpty (CanonicalWitness S eps C1 C2 x t) :=
  ⟨fun W => absurd W.eps_lt_one (not_lt.mpr h)⟩

theorem isEmpty_canonicalWitness_of_nonpos {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (x : M) (t : ℝ) {eps C1 C2 : ℝ} (h : eps ≤ 0) :
    IsEmpty (CanonicalWitness S eps C1 C2 x t) :=
  ⟨fun W => absurd W.eps_pos (not_lt.mpr h)⟩

theorem not_pointedFlowScalarBounded_of_scalarAtBase_lt
    {P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval} {r c : ℝ}
    (hbase : PointedFlowScalarAtBase (I := I3) P r) (hc : c < r) :
    ¬ PointedFlowScalarBounded (I := I3) P c := by
  intro h
  have h0 : (0 : ℝ) ∈ ancientTimeInterval.carrier := by simp
  have hle : P.S.scalar 0 P.basepoint ≤ c := (h 0 h0 P.basepoint).2
  have heq : P.S.scalar 0 P.basepoint = r := hbase
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
