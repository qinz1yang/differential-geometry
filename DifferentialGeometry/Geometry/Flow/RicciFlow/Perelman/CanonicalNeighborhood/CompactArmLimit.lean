import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactMetricSegment
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
noncomputable section
open Filter Set BoundedContinuousFunction
open scoped Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {X : Type*} [MetricSpace X]

theorem exists_uniform_limit_of_compact_metric_segments
    {K : Set X} (hK : IsCompact K) {length : ℕ → ℝ} {r : ℝ}
    (hlength : ∀ n, 0 ≤ length n) (hlengthT : Tendsto length atTop (𝓝 r))
    (c : ℕ → Icc (0 : ℝ) 1 → X)
    (hmem : ∀ n s, c n s ∈ K)
    (hdist : ∀ n s t, dist (c n s) (c n t) = length n * dist s t)
    {p q : X}
    (hp : Tendsto (fun n => c n ⟨0, by norm_num⟩) atTop (𝓝 p))
    (hq : Tendsto (fun n => c n ⟨1, by norm_num⟩) atTop (𝓝 q)) :
    ∃ (f : Icc (0 : ℝ) 1 → X) (phi : ℕ → ℕ),
      StrictMono phi ∧ Continuous f ∧ TendstoUniformly (fun n => c (phi n)) f atTop ∧
      f ⟨0, by norm_num⟩ = p ∧ f ⟨1, by norm_num⟩ = q ∧
      (∀ s, f s ∈ K) ∧ ∀ s t, dist (f s) (f t) = r * dist s t := by
  obtain ⟨B, hB⟩ := hlengthT.bddAbove_range
  have hBnonneg : 0 ≤ B := (hlength 0).trans (hB (mem_range_self 0))
  let L : ℝ≥0 := ⟨B, hBnonneg⟩
  have hLip (n : ℕ) : LipschitzWith L (c n) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [hdist n s t]
    exact mul_le_mul_of_nonneg_right (hB (mem_range_self n)) dist_nonneg
  let T := Icc (0 : ℝ) 1
  let F (n : ℕ) : T →ᵇ X :=
    BoundedContinuousFunction.mkOfCompact ⟨c n, (hLip n).continuous⟩
  let A := range F
  have hEA : Equicontinuous (fun f : A => ((f : T →ᵇ X) : T → X)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ L
    intro f
    obtain ⟨n, hn⟩ := f.property
    rw [← hn]
    exact hLip n
  have hAcpt : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli K hK A
    · intro f s hf
      obtain ⟨n, rfl⟩ := hf
      exact hmem n s
    · exact hEA
  obtain ⟨f, _hf, phi, hphi, hlim⟩ :=
    hAcpt.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have heval (s : T) : Tendsto (fun n => c (phi n) s) atTop (𝓝 (f s)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const s).continuous.tendsto f).comp hlim
  have huniform : TendstoUniformly (fun n => c (phi n)) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  have hzero : f ⟨0, by norm_num [T]⟩ = p :=
    tendsto_nhds_unique (heval ⟨0, by norm_num [T]⟩) (hp.comp hphi.tendsto_atTop)
  have hone : f ⟨1, by norm_num [T]⟩ = q :=
    tendsto_nhds_unique (heval ⟨1, by norm_num [T]⟩) (hq.comp hphi.tendsto_atTop)
  refine ⟨f, phi, hphi, f.continuous, huniform, hzero, hone, ?_, ?_⟩
  · intro s
    exact hK.isClosed.mem_of_tendsto (heval s)
      (Eventually.of_forall (fun n => hmem (phi n) s))
  · intro s t
    have hpair := (heval s).dist (heval t)
    have hscale := (hlengthT.comp hphi.tendsto_atTop).mul_const (dist s t)
    exact tendsto_nhds_unique hpair
      (hscale.congr (fun n => (hdist (phi n) s t).symm))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
