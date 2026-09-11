import DifferentialGeometry.Geometry.Measure.Area.RegularLeastArea
import DifferentialGeometry.Geometry.Metric.LoopDistanceContinuity








noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry Filter
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]



theorem continuous_regularLeastArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    Continuous[regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top)), inferInstance]
      (regularLeastArea g) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he₁
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  have hval : Continuous (fun γ : regularContractibleLoop E M => γ.val) := continuous_induced_dom
  have hjet : Continuous (fun γ : regularContractibleLoop E M => regularLoopJet e he₁ γ.val) :=
    continuous_induced_rng.mp hval
  have hΓ : Continuous (fun γ : regularContractibleLoop E M => γ.val.val) :=
    (continuous_regularLoop_inclusion e he₁ hemb).comp hval
  obtain ⟨Cr, hCr⟩ := exists_regular_loop_lipschitz_factor g e he hemb hi
  let B : regularContractibleLoop E M → ℝ := fun γ =>
    (Cr : ℝ) * ‖regularLoopDerivative e he₁ γ.val‖
  have hB : Continuous B := continuous_const.mul hjet.snd.norm
  have hlength (γ : regularContractibleLoop E M) :
      riemannianCurveLength g (fun t : ℝ => γ.val.val (t : loopCircle)) 0 1 ≤ B γ := by
    simpa only [B, NNReal.coe_mul, coe_nnnorm] using
      loop_arclength_le_of_riemannian_lipschitz g (hCr γ.val)
  obtain ⟨ρ, C, hρ, _, harea⟩ := exists_leastSpanningArea_annulus_bound g
  apply continuous_iff_continuousAt.mpr
  intro γ₀
  have hD := continuous_riemannianLoopDistance g hΓ (continuous_const (y := γ₀.val.val))
  have hDt : Tendsto (fun γ : regularContractibleLoop E M =>
      (riemannianLoopDistance g γ.val.val γ₀.val.val : ℝ)) (𝓝 γ₀) (𝓝 0) := by
    simpa only [ContinuousAt, riemannianLoopDistance_self, NNReal.coe_zero] using
      (hD.continuousAt (x := γ₀))
  have hBt : Tendsto (fun γ => (C : ℝ) * (riemannianLoopDistance g γ.val.val γ₀.val.val : ℝ) *
      (B γ + B γ₀)) (𝓝 γ₀) (𝓝 0) := by
    simpa only [mul_zero, zero_mul, Pi.add_apply] using!
      (tendsto_const_nhds.mul hDt).mul ((hB.continuousAt (x := γ₀)).add tendsto_const_nhds)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hBt
  filter_upwards [hDt.eventually_lt_const (by exact_mod_cast hρ : (0 : ℝ) < ρ)] with γ hnear
  have ha := harea (regularContractibleToLipschitz g γ) (regularContractibleToLipschitz g γ₀)
    (by exact_mod_cast hnear)
  rw [Real.dist_eq]
  apply ha.trans
  exact mul_le_mul_of_nonneg_left (add_le_add (hlength γ) (hlength γ₀))
    (mul_nonneg C.coe_nonneg (riemannianLoopDistance g γ.val.val γ₀.val.val).coe_nonneg)

end DifferentialGeometry.Geometry
