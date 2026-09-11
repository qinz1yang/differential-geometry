import DifferentialGeometry.Geometry.Comparison.Soul.SbrRightTangent
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_lipschitzOnWith_intrinsicFiber
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M) :
    ∃ K : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith K (fun v : E => expMapIntrinsic g hEnorm p
        (show TangentSpace I p from v)) (Metric.ball 0 r) := by
  let e : E → M := fun v => expMapIntrinsic g hEnorm p (show TangentSpace I p from v)
  have he : ContMDiff 𝓘(ℝ, E) I ∞ e := intrinsicFiber_smooth g hEnorm p
  have he0 : e 0 = p := expMapIntrinsic_zero g hEnorm p
  have hc : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I p) (e 0) := by
    rw [he0]
    exact contMDiffAt_extChartAt (I := I) (x := p)
  have hcoord : ContDiffAt ℝ 1 ((extChartAt I p) ∘ e) 0 :=
    contMDiffAt_iff_contDiffAt.mp (hc.comp 0 (he.of_le (by simp)).contMDiffAt)
  obtain ⟨K, S, hS, hK⟩ := hcoord.exists_lipschitzOnWith
  obtain ⟨C, _, U, hU, hC⟩ := exists_dist_le_extChartAt (I := I) p
  have hpre : e ⁻¹' U ∈ 𝓝 (0 : E) :=
    he.continuous.continuousAt.preimage_mem_nhds (he0.symm ▸ hU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hS hpre)
  refine ⟨C * K, r, hr, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro v hv w hw
  have hb := hK.dist_le_mul v (hball hv).1 w (hball hw).1
  rw [dist_eq_norm] at hb
  calc
    dist (e v) (e w) ≤ C * ‖extChartAt I p (e v) - extChartAt I p (e w)‖ :=
      hC _ (hball hv).2 _ (hball hw).2
    _ ≤ C * (K * dist v w) := mul_le_mul_of_nonneg_left hb C.coe_nonneg
    _ = (C * K : ℝ≥0) * dist v w := by rw [NNReal.coe_mul, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_intrinsicRightDerivative_exp_sequence
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (p : M) (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    {ι : Type*} {l : Filter ι} {h : ι → ℝ} {w : ι → E}
    (htime : Tendsto h l (𝓝[>] 0)) (hvec : Tendsto w l (𝓝 (v : E))) :
    Tendsto (fun i => (F (expMapIntrinsic g hEnorm p
      (show TangentSpace I p from h i • w i)) - F p) / h i)
      l (𝓝 (intrinsicRightDerivative g hEnorm F p v)) := by
  let e : E → M := fun z => expMapIntrinsic g hEnorm p (show TangentSpace I p from z)
  let vE : E := v
  change Tendsto w l (𝓝 vE) at hvec
  obtain ⟨K, r, hr, hK⟩ := exists_lipschitzOnWith_intrinsicFiber g hEnorm p
  have ht0 : Tendsto h l (𝓝 (0 : ℝ)) := htime.mono_right nhdsWithin_le_nhds
  have htpos : ∀ᶠ i in l, 0 < h i := htime.eventually self_mem_nhdsWithin
  have hmove : Tendsto (fun i => h i • w i) l (𝓝 (0 : E)) := by
    simpa only [zero_smul] using ht0.smul hvec
  have hfixed : Tendsto (fun i => h i • vE) l (𝓝 (0 : E)) := by
    simpa only [zero_smul] using ht0.smul (tendsto_const_nhds (x := vE))
  have hmoveBall := hmove.eventually (Metric.ball_mem_nhds (0 : E) hr)
  have hfixedBall := hfixed.eventually (Metric.ball_mem_nhds (0 : E) hr)
  have herr : Tendsto (fun i => (F (e (h i • w i)) - F (e (h i • vE))) / h i)
      l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hupper : Tendsto (fun i => ((L : ℝ) * K) * ‖w i - vE‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero, mul_zero] using
        (hvec.sub_const vE).norm.const_mul ((L : ℝ) * K)
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hupper
    filter_upwards [htpos, hmoveBall, hfixedBall] with i hi hwi hvi
    have hmetric := hK.dist_le_mul _ hwi _ hvi
    have hvalue := hF.dist_le_mul (e (h i • w i)) (e (h i • vE))
    rw [Real.dist_eq] at hvalue
    have hbound := hvalue.trans (mul_le_mul_of_nonneg_left hmetric L.coe_nonneg)
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hi] at hbound
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi]
    apply (div_le_iff₀ hi).2
    convert hbound using 1
    ring
  have hbase : Tendsto (fun i => (F (e (h i • vE)) - F p) / h i) l
      (𝓝 (intrinsicRightDerivative g hEnorm F p v)) := by
    have hexp (t : ℝ) : e (t • vE) = intrinsicGeodesic g hEnorm p v t := by
      change intrinsicGeodesic g hEnorm p (t • v) 1 = intrinsicGeodesic g hEnorm p v t
      exact intrinsicGeodesic_smul g hEnorm p v t
    have hlim := (tendsto_intrinsicRightDerivative g hEnorm F p v hconc).comp htime
    simpa only [hexp, Function.comp_def] using hlim
  have hsum := herr.add hbase
  simp only [zero_add] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun i => by dsimp only [e]; ring

end DifferentialGeometry.Geometry.Topology
