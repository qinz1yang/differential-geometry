import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Topology
import DifferentialGeometry.Topology.Manifold.PartitionOfUnity.Coordinates
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.ActiveConfiguration
import DifferentialGeometry.Topology.Manifold.Gluing.PartitionOfUnity
import Mathlib.Geometry.Manifold.LocalDiffeomorph

section

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))



theorem IntrinsicBallChart.exists_chart_active_configuration_sub_const [Fintype ι]
    (hJsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) (Metric.ball (0 : E) (ρ / 2))) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      ∀ (K : Set D.toGlueData.glued)
        (mu : SmoothPartitionOfUnity ι (modelWithCornersSelf ℝ E) D.toGlueData.glued K),
        mu.IsSubordinate (fun i => Set.range (D.toGlueData.ι i)) →
        (∀ i : ι, ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
          (fun z : U => D.toGlueData.ι i z)) →
        ∀ (j : ι) (a : E),
          let weights := mu.coordinateWeights U (fun z : U => D.toGlueData.ι j z)
          ∃ xi : ℕ → E → ι → E,
            (∀ k, ContDiffOn ℝ ∞ (fun z => (weights z, xi k z)) U) ∧
            CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
              (fun k z => (weights z, xi k z)) (fun z => (weights z, fun _ => z - a)) ∧
            (∀ z : U, ∀ i, 0 ≤ weights z i) ∧
            (∀ z : U, D.toGlueData.ι j z ∈ K → ∑ i, weights z i = 1) ∧
            (∀ z : U, ∀ i, weights z i ≠ 0 →
              ∃ h : near j i = true, J ⟨(j, i), h⟩ z ∈ U) ∧
            ∀ᶠ k in atTop, ∀ z : U, ∀ i (h : near j i = true), weights z i ≠ 0 →
              xi k z i = -a + (c j k).hom.symm ((c i k).hom (J ⟨(j, i), h⟩ z)) := by
  intro D U C K mu hsub hinc j a weights
  have hsymm : ∀ i l, near i l = true → near l i = true := by
    intro i l hil
    exact (EMetric.eq_swap_of_eventually_edist_lt_or_ge x near hclass i l).symm.trans hil
  let nc : ∀ i k, NormalBallChart (I := I) (x i k) := fun i k =>
    (c i k).toNormalBallChart (g k) (hEnorm k) (x i k) hρ
  have hweights : ContDiffOn ℝ ∞ weights (Metric.ball (0 : E) (ρ / 8)) :=
    mu.contDiffOn_coordinateWeights U (fun z : U => D.toGlueData.ι j z) (hinc j)
  have hactive : ∀ z ∈ Metric.ball (0 : E) (ρ / 8), ∀ i, weights z i ≠ 0 →
      ∃ h : near j i = true, J ⟨(j, i), h⟩ z ∈ Metric.ball (0 : E) (ρ / 8) := by
    intro z hz i hmi
    have hmi' : mu i (D.toGlueData.ι j ⟨z, hz⟩) ≠ 0 := by
      have hh := hmi
      change mu.coordinateWeights U (fun z : U => D.toGlueData.ι j z) (⟨z, hz⟩ : U) i ≠ 0 at hh
      rw [SmoothPartitionOfUnity.coordinateWeights_apply] at hh
      exact hh
    have hm := hsub i (subset_closure hmi')
    change (⟨z, hz⟩ : U) ∈ D.toGlueData.ι j ⁻¹' Set.range (D.toGlueData.ι i) at hm
    rw [D.preimage_range i j] at hm
    obtain ⟨w, hw⟩ := hm
    have hp : ∃ h : near j i = true, J ⟨(j, i), h⟩ (w.val : E) ∈ Metric.ball (0 : E) (ρ / 8) :=
      w.property
    have hwval : (w.val : E) = z := congrArg (fun u : U => (u : E)) hw
    simpa only [hwval] using hp
  have hreverseC : ∀ i (h : near j i = true), ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ ((nc i k).transition (nc j k)) (Metric.ball (0 : E) (ρ / 2)) := by
    intro i h
    filter_upwards [hclass i j] with k hk
    apply (nc i k).transition_smooth (nc j k)
    apply (c i k).overlap_on_ball_of_edist_add_le
      (g k) (hEnorm k) (x i k) (x j k) (c j k) hρ hρ (by linarith)
    calc
      edist (x i k) (x j k) + ENNReal.ofReal (ρ / 2) ≤
          ENNReal.ofReal (ρ / 4) + ENNReal.ofReal (ρ / 2) :=
        add_le_add (hk.1 (hsymm j i h)).le le_rfl
      _ = ENNReal.ofReal (ρ / 4 + ρ / 2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (by linarith)
  have hinverse : ∀ i (h : near j i = true) z, z ∈ Metric.ball (0 : E) (ρ / 8) →
      J ⟨(i, j), hsymm j i h⟩ (J ⟨(j, i), h⟩ z) = z := by
    intro i h z hz
    have hi := IntrinsicBallChart.transition_limit_inverse_on_ball_of_lt g hEnorm
      (x j) (x i) hρ (c j) (c i) (s := ρ / 8) (by positivity) (by linarith)
      (hconv ⟨(j, i), h⟩) (hconv ⟨(i, j), hsymm j i h⟩)
      (hcont ⟨(j, i), h⟩) (hcont ⟨(i, j), hsymm j i h⟩)
      ((hclass j i).mono fun _ hk => hk.1 h)
    exact hi.1 hz
  obtain ⟨xi, hxiC, hxi, hxiEq⟩ :=
    CheegerGromovCompactness.exists_translated_active_configuration_of_near a j ρ hρ near
      (fun i h => J ⟨(j, i), h⟩) (fun i h => J ⟨(i, j), hsymm j i h⟩)
      (fun i _ k => (nc i k).transition (nc j k)) weights hweights
      (fun i h => hJsmooth ⟨(j, i), h⟩) (fun i h => hJsmooth ⟨(i, j), hsymm j i h⟩)
      (fun i h => hconv ⟨(i, j), hsymm j i h⟩) hreverseC hinverse hactive
  refine ⟨xi, hxiC, hxi, ?_, ?_, ?_, ?_⟩
  · exact fun z i => mu.coordinateWeights_nonneg U (fun z : U => D.toGlueData.ι j z) z i
  · exact fun z hz => mu.sum_coordinateWeights_eq_one U (fun z : U => D.toGlueData.ι j z) z hz
  · exact fun z i hi => hactive z z.property i hi
  · filter_upwards [hxiEq] with k hk z i h hi
    exact hk z z.property i h hi

theorem IntrinsicBallChart.exists_partition_chart_active_configurations [Fintype ι]
    (hJsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) (Metric.ball (0 : E) (ρ / 2)))
    (i₀ : ι) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued →
      (∀ i : ι, ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∀ K : Set D.toGlueData.glued, IsClosed K →
        letI := Classical.decEq ι
        ∃ mu : SmoothPartitionOfUnity ι (modelWithCornersSelf ℝ E) D.toGlueData.glued K,
          mu.IsSubordinate (fun i => Set.range (D.toGlueData.ι i)) ∧
          (∃ W : Set D.toGlueData.glued, IsOpen W ∧
            D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩ ∈ W ∧
            ∀ p ∈ W, ∀ i, mu i p = if i = i₀ then 1 else 0) ∧
          ∀ (j : ι) (a : E),
            let weights := mu.coordinateWeights U (fun z : U => D.toGlueData.ι j z)
            ∃ xi : ℕ → E → ι → E,
              (∀ k, ContDiffOn ℝ ∞ (fun z => (weights z, xi k z)) U) ∧
              CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
                (fun k z => (weights z, xi k z)) (fun z => (weights z, fun _ => z - a)) ∧
              (∀ z : U, ∀ i, 0 ≤ weights z i) ∧
              (∀ z : U, D.toGlueData.ι j z ∈ K → ∑ i, weights z i = 1) ∧
              (∀ z : U, ∀ i, weights z i ≠ 0 →
                ∃ h : near j i = true, J ⟨(j, i), h⟩ z ∈ U) ∧
              ∀ᶠ k in atTop, ∀ z : U, ∀ i (h : near j i = true), weights z i ≠ 0 →
                xi k z i = -a + (c j k).hom.symm ((c i k).hom (J ⟨(j, i), h⟩ z)) := by
  intro D U C hman hinc K hK
  let := hman
  let : T2Space D.toGlueData.glued :=
    IntrinsicBallChart.bufferedTransitionGlueData_t2Space g hEnorm x hρ c near hclass J hcont hconv
  let : Finite D.J := by change Finite ι; infer_instance
  let (i : D.J) : SigmaCompactSpace (D.U i) := by
    change SigmaCompactSpace U
    let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
    exact sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨mu, hsub, W, hW, hbase, hone⟩ :=
    D.exists_smoothPartitionOfUnity_chartRange_eq_single_near
      (I := modelWithCornersSelf ℝ E) hK i₀
      (⟨0, Metric.mem_ball_self (by positivity)⟩ : U)
  refine ⟨mu, hsub, ⟨W, hW, hbase, hone⟩, ?_⟩
  intro j a
  exact IntrinsicBallChart.exists_chart_active_configuration_sub_const
    g hEnorm x hρ c near hclass J hcont hconv hJsmooth C K mu hsub hinc j a

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
