import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.BoundaryIdentity
import DifferentialGeometry.Topology.MetricSpace.TruncatedDistance
import DifferentialGeometry.Geometry.Measure.Energy.ScalarComposition
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Analysis.Calculus.DiskTraceApproximation
import Mathlib.Topology.TietzeExtension

section

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [MetricSpace X]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem diskTrace_eq_of_intrinsic_energy_bounded_ae_limit
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ι : X → M) (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    (u : ℕ → C(closedDisk, M)) (q : C(closedDisk, X)) (η : C(loopCircle, X))
    (hLip : ∀ n, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (L : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (ι (diskExtension q z))))
    (hboundary : ∀ θ : loopCircle,
      Tendsto (fun n => u n (diskBoundary θ)) atTop (𝓝 (ι (η θ))))
    {B : ℝ} (henergy : ∀ n, riemannianDiskEnergy g (u n) ≤ B) :
    diskTrace q = η := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hedist (a b : M) : edist a b = riemannianEDistOf g a b := rfl
  ext θ₀
  let a : X := q (diskBoundary θ₀)
  let P : M → ℝ := fun z => (min (edist z (ι a)) 1).toReal
  have hP : LipschitzWith 1 P := EMetric.lipschitzWith_truncated_edist _
  have hPX (x : X) : P (ι x) = min (dist x a) 1 := by
    change (min (edist (ι x) (ι a)) 1).toReal = _
    rw [hedist, ← hι, ENNReal.toReal_min (edist_ne_top _ _) (by simp),
      ENNReal.toReal_one, ← dist_edist]
  let qP : C(closedDisk, ℝ) := ⟨fun z => min (dist (q z) a) 1, by fun_prop⟩
  let ηP : C(loopCircle, ℝ) := ⟨fun θ => min (dist (η θ) a) 1, by fun_prop⟩
  let b : loopCircle → ℂ := fun θ => (diskBoundary θ : ℂ)
  have hb : Continuous b := continuous_subtype_val.comp diskBoundary.continuous
  have hbinj : Function.Injective b := by
    intro x y hxy
    apply AddCircle.injective_toCircle one_ne_zero
    exact Subtype.ext hxy
  obtain ⟨ηbar, hηbar⟩ := ηP.exists_extension' (hb.isClosedEmbedding hbinj)
  choose L hL using hLip
  let f : ℕ → ℂ → ℝ := fun n => P ∘ diskExtension (u n)
  have hf (n : ℕ) : LipschitzWith (L n) (f n) := by
    intro z w
    have h := hP (diskExtension (u n) z) (diskExtension (u n) w)
    simp only [ENNReal.coe_one, one_mul, hedist] at h
    exact h.trans (diskExtension_riemannian_lipschitz g (hL n) z w)
  have haef : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => f n z) atTop (𝓝 (diskExtension qP z)) := by
    filter_upwards [hae] with z hz
    have h := hP.continuous.continuousAt.tendsto.comp hz
    have heq : P (ι (diskExtension q z)) = diskExtension qP z := hPX _
    rwa [heq] at h
  have hboundaryf (z : ℂ) (hz : ‖z‖ = 1) :
      Tendsto (fun n => f n z) atTop (𝓝 (ηbar z)) := by
    obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one hz
    have h := hP.continuous.continuousAt.tendsto.comp (hboundary θ)
    have heq : ηbar (diskBoundary θ) = P (ι (η θ)) := by
      have hh := congrFun hηbar θ
      change ηbar (b θ) = ηP θ at hh
      exact hh.trans (hPX _).symm
    rw [← hθ, heq]
    simpa only [f, Function.comp_apply, diskExtension_coe] using! h
  have hEf (n : ℕ) : (∫ z in closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ 2 * B := by
    have hh := integral_norm_fderiv_sq_le_mul_disk_energy g (u n) (K := 1) (hL n)
      (f := f n) (fun z w => by
        simpa only [hedist, f, Function.comp_apply] using
          hP (diskExtension (u n) z) (diskExtension (u n) w))
    norm_num only [NNReal.coe_one, one_pow, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (henergy n) (by norm_num))
  have hidentity := Analysis.disk_boundary_eq_of_lipschitz_sequence_energy_bound
    f qP ηbar L hf haef hboundaryf ηbar.continuous.continuousOn hEf
  have hp : (diskBoundary θ₀ : ℂ) ∈ sphere (0 : ℂ) 1 := by
    simpa only [mem_sphere, dist_zero_right] using diskBoundary_norm_coe θ₀
  have hh := hidentity (diskBoundary θ₀) hp
  have hbval : ηbar (diskBoundary θ₀) = ηP θ₀ := congrFun hηbar θ₀
  have hz : min (dist (η θ₀) a) 1 = 0 := by
    rw [hbval] at hh
    change min (dist (q (diskBoundary θ₀)) a) 1 = min (dist (η θ₀) a) 1 at hh
    simpa only [a, dist_self, min_eq_left zero_le_one] using hh.symm
  change a = η θ₀
  apply dist_eq_zero.mp
  rw [dist_comm]
  by_contra hn
  have hd : 0 < dist (η θ₀) a := lt_of_le_of_ne dist_nonneg (Ne.symm hn)
  have hm := lt_min hd zero_lt_one
  rw [hz] at hm
  exact (lt_irrefl (0 : ℝ)) hm

end DifferentialGeometry.Geometry

end

end
