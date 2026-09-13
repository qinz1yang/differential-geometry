import DifferentialGeometry.Geometry.Measure.Area.RegularLeastArea
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaComponent
import DifferentialGeometry.Geometry.Metric.LoopDistanceContinuity








noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry Filter
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]



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
  apply continuous_iff_continuousAt.mpr
  intro γ₀
  set U : TopologicalSpace.Opens M := loopComponentOpen E γ₀.val.val with hUdef
  have hUclosed : IsClosed (U : Set M) := isClosed_loopComponent γ₀.val.val
  have hUconn : ConnectedSpace ↥U := loopComponentOpen_connectedSpace E γ₀.val.val
  have hUcomp : CompactSpace ↥U := loopComponentOpen_compactSpace E γ₀.val.val
  obtain ⟨ρ, C, hρ, hC, hann⟩ :=
    exists_leastSpanningArea_annulus_bound_of_image_subset (U := U) g hUclosed
  have hmem : ∀ θ : loopCircle, γ₀.val.val θ ∈ U := fun θ => loop_mem_component γ₀.val.val θ
  have hopen : IsOpen {f : C(loopCircle, M) | MapsTo f univ (U : Set M)} :=
    ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ U.isOpen
  have hnbhd : ∀ᶠ γ : regularContractibleLoop E M in 𝓝 γ₀,
      ∀ θ : loopCircle, γ.val.val θ ∈ U :=
    (hΓ.continuousAt.eventually (hopen.mem_nhds fun θ _ => hmem θ)).mono
      fun γ hγ θ => Set.mapsTo_univ_iff.mp hγ θ
  have hdt : Tendsto (fun γ : regularContractibleLoop E M =>
      (riemannianLoopDistance g γ.val.val γ₀.val.val : ℝ)) (𝓝 γ₀) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hε : 0 < (Real.toNNReal (δ / 2) : ℝ≥0∞) := by
      rw [ENNReal.coe_pos]
      exact Real.toNNReal_pos.mpr (by linarith)
    filter_upwards [hΓ.continuousAt.eventually
      (eventually_forall_riemannianEDist_lt g γ₀.val.val hε)] with γ hγ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0 : ℝ) ≤ _)]
    have hsup : (⨆ θ : loopCircle, riemannianEDistOf g (γ.val.val θ) (γ₀.val.val θ)) ≤
        (Real.toNNReal (δ / 2) : ℝ≥0∞) := iSup_le fun θ => (hγ θ).le
    have h1 : riemannianLoopDistance g γ.val.val γ₀.val.val ≤ Real.toNNReal (δ / 2) := by
      rw [riemannianLoopDistance]
      exact ENNReal.toNNReal_mono ENNReal.coe_ne_top hsup
    have h3 : (riemannianLoopDistance g γ.val.val γ₀.val.val : ℝ) ≤ δ / 2 :=
      (NNReal.coe_le_coe.mpr h1).trans_eq (Real.coe_toNNReal _ (by linarith))
    linarith
  have hsmallR : ∀ᶠ γ : regularContractibleLoop E M in 𝓝 γ₀,
      (riemannianLoopDistance g γ.val.val γ₀.val.val : ℝ) < (ρ : ℝ) :=
    hdt.eventually_lt_const (by exact_mod_cast hρ : (0 : ℝ) < (ρ : ℝ))
  have hsmall : ∀ᶠ γ : regularContractibleLoop E M in 𝓝 γ₀,
      riemannianLoopDistance g γ.val.val γ₀.val.val < ρ :=
    hsmallR.mono fun _ h => by exact_mod_cast h
  have hBt : Tendsto (fun γ : regularContractibleLoop E M =>
      (C : ℝ) * (riemannianLoopDistance g γ.val.val γ₀.val.val : ℝ) * (B γ + B γ₀))
      (𝓝 γ₀) (𝓝 0) := by
    simpa only [mul_zero, zero_mul, Pi.add_apply] using!
      (tendsto_const_nhds.mul hdt).mul
        ((hB.continuousAt (x := γ₀)).add tendsto_const_nhds)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hBt
  filter_upwards [hsmall, hnbhd] with γ hnear hsub
  let γU := lipschitzContractibleLoopInOpen g U hUclosed γ.val.val γ.property hsub
    (regularLoop_riemannian_lipschitz g γ.val).choose_spec
  let γ₀U := lipschitzContractibleLoopInOpen g U hUclosed γ₀.val.val γ₀.property hmem
    (regularLoop_riemannian_lipschitz g γ₀.val).choose_spec
  have hlift : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp γU.val.val = γ.val.val := by
    ext θ
    exact lipschitzContractibleLoopInOpen_coe g U hUclosed γ.val.val γ.property hsub
      (regularLoop_riemannian_lipschitz g γ.val).choose_spec θ
  have hlift₀ : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, M)).comp γ₀U.val.val = γ₀.val.val := by
    ext θ
    exact lipschitzContractibleLoopInOpen_coe g U hUclosed γ₀.val.val γ₀.property hmem
      (regularLoop_riemannian_lipschitz g γ₀.val).choose_spec θ
  have hnearU : riemannianLoopDistance (g.restrictOpen U) γU.val.val γ₀U.val.val < ρ := by
    rw [riemannianLoopDistance_restrictOpen g hUclosed, hlift, hlift₀]
    exact hnear
  have ha := hann (regularContractibleToLipschitz g γ) (regularContractibleToLipschitz g γ₀)
    hsub hmem hnearU
  rw [Real.dist_eq]
  refine ha.trans ?_
  exact mul_le_mul_of_nonneg_left (add_le_add (hlength γ) (hlength γ₀))
    (mul_nonneg C.coe_nonneg NNReal.zero_le_coe)


end DifferentialGeometry.Geometry
