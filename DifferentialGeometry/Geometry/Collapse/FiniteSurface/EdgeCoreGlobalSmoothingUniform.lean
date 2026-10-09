import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreBinding

/-!
# LFR24 with the global smoothing exported, uniform threshold (LFR28 row parameter order)

`finiteSurface_edge_model_core_global_uniform`: B6's `finiteSurface_edge_model_core_global`
(FiniteSurface/EdgeCoreGlobalSmoothing.lean) with its threshold made EXPLICIT and universal:
every `0 < δ ≤ ε² / 24000000` works, for every surface. B6's statement has `∃ δ₀ > 0` AFTER the
surface `(Z, k)`, which is too late for the LFR28 row (its `τ₀` precedes the limit and its carrier,
blueprint A:27223, "These choices precede `K ≥ 5`, ..."). The proof is B6's proof verbatim (B6's
file is frozen and untouched; its `δ₀` is this constant).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Function Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Surface
open DifferentialGeometry.Geometry.FiniteSoul

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

/-- **LFR24 with the global smoothing exported, uniform threshold `ε² / 24000000`.** The row `finiteSurface_edge_model_core`, and
moreover its LFR02 smoothing `F`: continuous, `|F - r| < μ` everywhere, smooth with the all-direction
gradient clause on an open `O_F ⊇ {3/4 ≤ r ≤ 9.1}`, and `h = edgeModelCore F`. -/
theorem finiteSurface_edge_model_core_global_uniform (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ (z₀ : Z) (q : Z → ℝ) (δ : ℝ), 0 < δ → δ ≤ ε ^ 2 / 24000000 → q z₀ = 0 →
      (∀ y ∈ closedBall z₀ 10, 0 ≤ q y) →
      (∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ) →
      (∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) →
      ∀ μ : ℝ, 0 < μ → μ < 1 / 100 →
      ∃ F : Z → ℝ, Continuous F ∧ (∀ x, |F x - dist x z₀| < μ) ∧
        (∃ OF : Set Z, IsOpen OF ∧ {x | 3 / 4 ≤ dist x z₀ ∧ dist x z₀ ≤ 91 / 10} ⊆ OF ∧
          ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ F OF ∧
          ∀ x ∈ OF, ∀ v ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x,
            ∀ w : TangentSpace (𝓡 2) x,
              |mvfderiv (𝓡 2) F x w + k.inner x v w| ≤ ε / 25 * Real.sqrt (k.inner x w w)) ∧
      ∃ h : Z → ℝ, h = edgeModelCore F ∧
        (∃ W : Set Z, IsOpen W ∧ closedBall z₀ 9 ⊆ W ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h W) ∧
        (∃ O : Set Z, IsOpen O ∧ closedBall z₀ (1 / 2) ⊆ O ∧ EqOn h 0 O) ∧
        (∀ x, dist x z₀ ≤ 1 → h x ∈ Icc (0 : ℝ) 2) ∧
        (∀ x, 21 / 10 ≤ dist x z₀ → dist x z₀ ≤ 9 → |h x - dist x z₀| < μ ∧
          ∀ v ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x, ∀ w : TangentSpace (𝓡 2) x,
            |mvfderiv (𝓡 2) h x w + k.inner x v w| ≤ ε / 25 * Real.sqrt (k.inner x w w)) ∧
        (∀ s ∈ Icc (3 : ℝ) 6,
          IsCompact {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
          closedBall z₀ (s - μ) ⊆ {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
          {x | dist x z₀ < 9 ∧ h x ≤ s} ⊆ ball z₀ (s + μ) ∧
          ∃ b : ClosedCell 2 → Z, Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧
            range b = {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
            range (b ∘ cellBoundaryInclusion 2) = {x | dist x z₀ < 9 ∧ h x = s}) ∧
        (∃ V : (x : Z) → TangentSpace (𝓡 2) x,
          ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 2) Z)) ∧
          (∀ x, k.inner x (V x) (V x) < 2 ^ 2) ∧
          (∃ O : Set Z, IsOpen O ∧
            (fun x => infDist x ({z₀} : Set Z)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4) ⊆ O ∧
            ∀ x ∈ O, ∀ u ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x,
              k.inner x (V x) u < -(3 / 4)) ∧
          ∀ x, 21 / 10 ≤ dist x z₀ → dist x z₀ ≤ 8 → 1 / 2 < mvfderiv (𝓡 2) h x (V x)) ∧
        (∀ x, dist x z₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0) ∧
        ∀ Δ : ℝ, 0 < Δ →
          {p : ℝ × Z | p.1 ∈ Ioo (-(6 * Δ)) (6 * Δ) ∧ dist p.2 z₀ < 9 ∧
              (p.1, Δ * h p.2) ∈ Icc (-(4 * Δ)) (4 * Δ) ×ˢ Iic (4 * Δ)} =
            Icc (-(4 * Δ)) (4 * Δ) ×ˢ {x | dist x z₀ < 9 ∧ h x ≤ 4} ∧
          Icc (-(4 * Δ)) (4 * Δ) ×ˢ {x | dist x z₀ < 9 ∧ h x ≤ 4} ⊆
            interior (Icc (-(9 / 2 * Δ)) (9 / 2 * Δ) ×ˢ {z | dist z z₀ ≤ 5}) := by
  have hε' : ε ≤ 1 := by linarith
  intro z₀ q δ hδ hδ₀ hq0 hqnn hdist hdense μ hμ hμ1
  have : NeZero (Module.finrank ℝ E2) := ⟨by simp⟩
  have : ProperSpace Z := Manifold.properSpace_of_isRiemannianManifold (𝓡 2)
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hdim : Module.finrank ℝ E2 = 2 := by simp
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hδ1 : δ ≤ 1 / 9600 := hδ₀.trans (by linarith)
  ---------------------------------------------------------------- LFR02 with `ε` and `μ`
  set U : Set Z := {x | 1 / 2 < dist x z₀ ∧ dist x z₀ < 37 / 4} with hU
  set C : Set Z := {x | 3 / 4 ≤ dist x z₀ ∧ dist x z₀ ≤ 91 / 10} with hC
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
  have hUY : U ⊆ ({z₀} : Set Z)ᶜ := fun x hx hxz => by
    rw [mem_singleton_iff] at hxz
    have := hx.1
    rw [hxz, dist_self] at this
    linarith
  have hCc : IsCompact C := (isCompact_closedBall z₀ (91 / 10)).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)) fun x hx => hx.2
  have hCU : C ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsqrt : 2 * Real.sqrt (600 * δ) ≤ min 1 ε / 100 := by
    have h1 : Real.sqrt (600 * δ) ≤ ε / 200 := by
      rw [show ε / 200 = Real.sqrt ((ε / 200) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [min_eq_right hε']
    linarith
  obtain ⟨F, OF, hOF, hCOF, hFs, hFr, -, -, hFlip, -, -, hgrad⟩ :=
    exists_localized_distance_smoothing_lfr02 k hr2 hnorm hε isClosed_singleton
      (singleton_nonempty z₀) hUo hUY (fun x hx v hv v' hv' => by
        have hx₁ : 1 / 2 ≤ dist z₀ x := by rw [dist_comm]; exact hx.1.le
        have hx₂ : dist z₀ x ≤ 37 / 4 := by rw [dist_comm]; exact hx.2.le
        exact (sqrt_inner_sub_lt_of_endpoint_band k hr2 hnorm hK hδ (by linarith) hq0 hqnn hdist
          hdense hx₁ hx₂ hv hv').trans_le hsqrt) hCc hCU (e := μ) hμ
  have hFc : Continuous F := hFlip.continuous
  have hμ' : μ ≤ 1 / 100 := hμ1.le
  have hFr2 : ∀ x, |F x - (fun x => dist x z₀) x| < μ := fun x => by
    have h := hFr x
    rwa [infDist_singleton] at h
  have hA : ∀ x, 3 / 4 ≤ (fun x => dist x z₀) x → (fun x => dist x z₀) x ≤ 9 → x ∈ OF :=
    fun x h1 h2 => hCOF ⟨h1, by linarith [h2]⟩
  ---------------------------------------------------------------- LFR23's field
  obtain ⟨V, hV, hVR, O, hO, hAO, hOout, -⟩ :=
    exists_endpoint_field k hr2 hnorm hK hδ hδ1 hq0 hqnn hdist hdense
  have hdFV : ∀ x, 21 / 10 ≤ (fun x => dist x z₀) x → (fun x => dist x z₀) x ≤ 8 →
      1 / 2 < mvfderiv (𝓡 2) F x (V x) := by
    intro x h1 h2
    have hxO : x ∈ O := hAO (show infDist x ({z₀} : Set Z) ∈ Icc (1 / 2 : ℝ) (37 / 4) by
      rw [infDist_singleton]; exact ⟨by linarith [h1], by linarith [h2]⟩)
    obtain ⟨v, hv⟩ := (k.finiteMinimizingDirectionsTo_nonempty_isCompact hr2 hnorm
      isClosed_singleton (singleton_nonempty z₀) x).1
    exact one_half_lt_mvfderiv_of_gradient k hε' (hgrad x (hA x (by linarith) (by linarith)) v hv
      (V x)) (hVR x) (hOout x hxO v hv)
  have hcpt7 : IsCompact {x : Z | (fun x => dist x z₀) x ≤ 7} := isCompact_closedBall z₀ 7
  refine ⟨F, hFc, hFr2, ⟨OF, hOF, fun x hx => hCOF ⟨hx.1, hx.2⟩, hFs, hgrad⟩, edgeModelCore F, rfl,
    ?_, edgeModelCore_eqOn_zero hFc hμ' hFr2,
    fun x hx => edgeModelCore_mem_Icc hμ' hFr2 hx, fun x h1 h2 => ⟨abs_edgeModelCore_sub_lt hμ' hFr2 h1,
      fun v hv w => by
        rw [mvfderiv_edgeModelCore_eq hFc hμ' hFr2 h1]
        exact hgrad x (hA x (by linarith) h2) v hv w⟩, fun s hs => ?_,
    ⟨V, hV, hVR, ⟨O, hO, hAO, hOout⟩, fun x h1 h2 => edgeModelCore_field hFc hμ' hFr2 V hdFV h1 h2⟩,
    fun x hx hx4 => mvfderiv_edgeModelCore_ne_zero hFc hμ' hFr2 V hdFV (s := 4)
      ⟨by norm_num, by norm_num⟩ hx hx4,
    fun Δ hΔ => edgeModelCore_product_enclosure hΔ (continuous_id.dist continuous_const) hμ' hFr2⟩
  · obtain ⟨W, hW, hW9, hWs⟩ := contMDiffOn_edgeModelCore hFc hOF hFs hA hμ' hFr2
    exact ⟨W, hW, hW9, hWs⟩
  · have hD : edgeCoreSublevel (fun x => dist x z₀) F s = {x | F x ≤ s} :=
      edgeCoreSublevel_eq hμ' hFr2 hs
    have hcpt : IsCompact (edgeCoreSublevel (fun x => dist x z₀) F s) := by
      rw [hD]
      refine (isCompact_closedBall z₀ 7).of_isClosed_subset (isClosed_le hFc continuous_const)
        fun x hx => ?_
      have h2 := abs_lt.1 (hFr2 x)
      change F x ≤ s at hx
      change dist x z₀ ≤ 7
      change -μ < F x - dist x z₀ ∧ F x - dist x z₀ < μ at h2
      linarith [h2.1, hs.2]
    obtain ⟨φ, hφ, hφr, hφb⟩ := exists_disk_sublevel_of_smoothing o k hr hnorm hK hδ hδ1 hq0 hqnn
      hdist hdense hFc hμ' hFr hOF hFs (fun x h1 h2 => hCOF ⟨h1, h2⟩) hε' hgrad hs
    obtain ⟨b, hb, hbr, hbb⟩ := edgeCoreSublevel_smooth_disk hdim hFc hOF hFs hA hμ' hFr2 hcpt7 V
      hV.contMDiffOn hdFV hs hφ.continuous hφ.injective (hφr.trans hD.symm) hφb
    refine ⟨hcpt, subset_edgeCoreSublevel hμ' hFr2 hs, edgeCoreSublevel_subset hμ' hFr2 hs, b, hb,
      hbr, ?_⟩
    rw [hbb]
    exact (edgeCoreLevel_eq hμ' hFr2 hs).symm

end DifferentialGeometry.Geometry.Collapse
