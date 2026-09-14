import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MaximalPointSlabReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalPullbackReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelsReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureDerivativeEstimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.JetLocalBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelExistenceClean

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
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

theorem maximal_point_singularity_model_of_slabCompactnessAtPastMaximum
    [CompactSpace M] [ConnectedSpace M] [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactnessAtPastMaximum.{u} hT S hS o) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 :=
  maximal_point_singularity_model_of_atPastMaximum hT S hS o h

theorem blowupAtHighCurvatureFrontier_of_maximalPointSlabCompactness
    [CompactSpace M] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactness.{u} hT S hS o) :
    BlowupAtHighCurvatureFrontier.{u} hT S o := by
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
  have hevtbig : ∀ᶠ i in Filter.atTop, T / 2 < t i := by
    filter_upwards [hscalar.eventually (Filter.eventually_gt_atTop Msc)] with i hi
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

theorem blowupLimitModelFrontier_of_slabCompactnessAtPastMaximum
    [CompactSpace M] [ConnectedSpace M] [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactnessAtPastMaximum.{u} hT S hS o) :
    BlowupLimitModelFrontier.{u} hT S hS o :=
  maximal_point_singularity_model_of_slabCompactnessAtPastMaximum hT S hS o h

theorem high_curvature_derivatives_of_windowedWitnessJetTransfer_and_universalMixedJetBound
    {a b : ℕ} {C eta : ℝ} (hC : 0 < C) (heta : 0 < eta)
    (hmodel : HighCurvatureModelWitnessExistence.{u})
    (htransfer : WindowedWitnessJetTransfer.{u} a b eta)
    (hU : DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.UniversalMixedJetBound.{u}
      a b C) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta :=
  exists_jetLocalBound_of_modelWitnessExistence_and_transfer hC heta hmodel htransfer
    (ancientModelMixedBound_of_universalMixedJetBound a b hU)

theorem high_curvature_derivatives_of_scalar_nonpositive (a b : ℕ)
    (hneg : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
      (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, S.scalar t x ≤ 0) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta :=
  ⟨1, 1, one_pos, one_pos, jetLocalBound_of_scalar_nonpositive a b hneg⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
