import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNonroundBufferedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalKappaGap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmReduction

section
set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (D : RealTimeInterval) (P : PointedFlowData.{u, 0, 0} I3 D)
        (delta t : ℝ) (W : WindowedModelWitness delta kappa P.S P.basepoint t),
        delta ≤ delta0 → Ioo (t - (delta * P.S.scalar t P.basepoint)⁻¹) t ⊆ D.regular →
        (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
        ∃ B : BufferedCanonical P.S alpha C H P.basepoint t,
          B.witness.capTubeHasNeckChart alpha := by
  classical
  by_contra hnone
  have hbad (n : ℕ) : ∃ (kappa : ℝ) (D : RealTimeInterval) (P : PointedFlowData.{u, 0, 0} I3 D)
      (delta t : ℝ) (W : WindowedModelWitness delta kappa P.S P.basepoint t),
      delta ≤ 1 / ((n : ℝ) + 2) ∧ Ioo (t - (delta * P.S.scalar t P.basepoint)⁻¹) t ⊆ D.regular ∧
      (¬ IsShrinkingSphericalSpaceFormFlow W.model) ∧ Nonempty (TangentOrientationSection W.model.M) ∧
      ¬ ∃ B : BufferedCanonical P.S alpha ((n : ℝ) + 1) H P.basepoint t,
        B.witness.capTubeHasNeckChart alpha := by
    by_contra hn
    push Not at hn
    apply hnone
    refine ⟨(n : ℝ) + 1, 1 / ((n : ℝ) + 2), by linarith [Nat.cast_nonneg (α := ℝ) n], by positivity, ?_, ?_⟩
    · apply (div_lt_one (by positivity : 0 < (n : ℝ) + 2)).mpr
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro kappa D P delta t W hd hreg hnc o
      exact hn kappa D P delta t W hd hreg hnc ⟨o⟩
  choose kappa D P delta t W hdelta hregular hnotround horient hfail using hbad
  let W0 (i : ℕ) : WindowedModelWitness (delta i) universalKappaConstant (P i).S (P i).basepoint (t i) :=
    { W i with model_ancient := ((ancientKappaThree_universal_kappa_gap (W i).model (W i).model_ancient (by simp [ThreeSpace])).resolve_left (hnotround i)) }
  have hzero : Tendsto delta atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
    exact squeeze_zero (fun i => (W i).eps_pos.le) hdelta hbound
  let models := fun i => (W0 i).model
  obtain ⟨L, phi, hphi, Phi, hL, hLbase, _hKL, _hconv, hcmp⟩ :=
    exists_ancientKappa_fixed_kappa_compactness models (fun i => (W0 i).model_ancient)
      (fun i => (W0 i).model_scalar_base)
  let F : PointedRiemannianConvergenceMaps ⟨fun i => (W0 i).model.atTime 0⟩ (L.atTime 0) phi :=
    Phi.atTime (X := ancientPointedFlowSeq models) (L := L) 0
  have hcmp' : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W0 (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta) :=
    fun K hK A hA order eta heta => hcmp (-A) 0 (by linarith) le_rfl K hK order eta heta
  obtain ⟨C, _hC, hbuffer⟩ := exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models
    (fun i => (P i).isSolution) W0 hzero hregular L hphi.tendsto_atTop F hcmp' hL hLbase hnotround
    (fun i => Classical.choice (horient i)) ha hasmall H
  have hlarge : ∀ᶠ i in atTop, C < (phi i : ℝ) + 1 :=
    ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).comp hphi.tendsto_atTop).eventually_gt_atTop C
  obtain ⟨i, hi, hCi⟩ := (hbuffer.and hlarge).exists
  obtain ⟨B, hB⟩ := hi
  apply hfail (phi i)
  refine ⟨B.enlargeConstants hCi, ?_⟩
  change (B.witness.enlargeConstants hCi.le hCi.le).capTubeHasNeckChart alpha
  exact hB.enlarge_constants hCi.le hCi.le

theorem exists_universal_nonround_windowed_buffer_constant
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (D : RealTimeInterval) (P : PointedFlowData.{u, 0, 0} I3 D)
        (delta t : ℝ) (W : WindowedModelWitness delta kappa P.S P.basepoint t),
        delta ≤ delta0 → Ioo (t - (delta * P.S.scalar t P.basepoint)⁻¹) t ⊆ D.regular →
        (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
        Nonempty (BufferedCanonical P.S alpha C H P.basepoint t) := by
  obtain ⟨C, delta0, hC, hd, hd1, hmain⟩ :=
    exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts.{u} ha hasmall H
  refine ⟨C, delta0, hC, hd, hd1, ?_⟩
  intro kappa D P delta t W hdelta hreg hnc orient
  obtain ⟨B, _⟩ := hmain kappa D P delta t W hdelta hreg hnc orient
  exact ⟨B⟩

theorem exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness delta kappa S x t),
          delta ≤ delta0 → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
          ∃ B : BufferedCanonical S alpha C H x t, B.witness.capTubeHasNeckChart alpha := by
  obtain ⟨C, delta0, hC, hd, hd1, hmain⟩ := exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts.{u} ha hasmall H
  refine ⟨C, delta0, hC, hd, hd1, ?_⟩
  intro kappa M _ _ _ _ _ D S hS delta x t W hdelta hreg hnc orient
  let P : PointedFlowData.{u, 0, 0} I3 D := { M := M, basepoint := x, S := S, isSolution := hS }
  exact hmain kappa D P delta t W hdelta hreg hnc orient

theorem exists_universal_nonround_windowed_bufferedCanonical
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness delta kappa S x t),
          delta ≤ delta0 → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
          Nonempty (BufferedCanonical S alpha C H x t) := by
  obtain ⟨C, delta0, hC, hd, hd1, hmain⟩ :=
    exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts.{u} ha hasmall H
  refine ⟨C, delta0, hC, hd, hd1, ?_⟩
  intro kappa M _ _ _ _ _ D S hS delta x t W hdelta hreg hnc orient
  obtain ⟨B, _⟩ := hmain kappa M D S hS delta x t W hdelta hreg hnc orient
  exact ⟨B⟩

theorem exists_universal_nonround_windowed_canonicalWitness
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ,
      ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
          IsSolutionOn S → ∀ (x : M) (t : ℝ) (W : WindowedModelWitness delta kappa S x t),
          Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          (¬ IsShrinkingSphericalSpaceFormFlow W.model) → TangentOrientationSection W.model.M →
          Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  obtain ⟨C, delta, hC, hd, hd1, hmain⟩ := exists_universal_nonround_windowed_bufferedCanonical.{u} heps hsmall 1
  refine ⟨C, C, hC, hC, fun kappa => ⟨delta, hd, hd1, ?_⟩⟩
  intro M _ _ _ _ _ D S hS x t W hreg hnc orient
  obtain ⟨B⟩ := hmain kappa M D S hS delta x t W le_rfl hreg hnc orient
  exact ⟨B.canonicalWitnessMono B.tolerance_lt.le hsmall⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
