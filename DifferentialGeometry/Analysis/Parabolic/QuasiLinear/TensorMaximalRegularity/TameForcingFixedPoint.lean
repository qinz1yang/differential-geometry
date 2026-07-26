import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PartialForcingFixedPoint
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Tame forcing-space fixed points on a lower Sobolev ball

At the critical three-dimensional regularity the Ricci--DeTurck remainder is
not globally Lipschitz from the top Sobolev space to the forcing space.  Its
correct estimate has three arms: a small top-order arm, a lower-order arm, and
a tame arm in which the top norm of either endpoint multiplies the lower norm
of their difference.

This file supplies the abstract analytic bridges needed by that estimate.
First, a map on a dense core which is Lipschitz on every finite state-space
ball has a continuous dense extension, and the tame estimate both supplies
those local constants and passes to that extension.  Second, the three-arm
estimate contracts the Duhamel forcing map on a small forcing ball, even
though it does not give a global Lipschitz constant for the pointwise
nonlinearity.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

/-- A map on a dense subset which is Lipschitz on every ball about a fixed
ambient centre has a continuous dense extension.  Global Lipschitz control
is not required. -/
theorem dense_cont_on_balls
    {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    [CompleteSpace Y] {D : Set X} (hD : Dense D) (F : D → Y) (x₀ : X)
    (hball : ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ R}) :
    Continuous (Dense.extend hD F) := by
  apply hD.isDenseInducing_val.continuous_extend_of_cauchy
  intro x
  let l : Filter D := comap ((↑) : D → X) (𝓝 x)
  have hl : Cauchy l := by
    exact cauchy_nhds.comap'
      (le_of_eq isUniformEmbedding_subtype_val.isUniformInducing.comap_uniformity)
      (hD.comap_val_nhds_neBot x)
  let R : ℝ := dist x x₀ + 1
  let S : Set D := {d | dist (d : X) x₀ ≤ R}
  obtain ⟨K, hK⟩ := hball R
  have hxball : x ∈ Metric.ball x₀ R := by
    rw [Metric.mem_ball]
    dsimp only [R]
    linarith
  have hclosed : Metric.closedBall x₀ R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem hxball
  have hlS : l ≤ 𝓟 S := by
    rw [le_principal_iff]
    have hpre : ((↑) : D → X) ⁻¹' Metric.closedBall x₀ R ∈ l :=
      preimage_mem_comap hclosed
    simpa only [S, Metric.mem_closedBall, Set.mem_setOf_eq] using hpre
  exact hl.map_of_le hK.uniformContinuousOn hlS

/-- A three-arm tame estimate is Lipschitz on each top-size ball.  This is the
local input needed by `dense_cont_on_balls`; no global top-order bound is
asserted. -/
theorem tame_lip_balls
    {X V Y Z : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {D : Set X} (F : D → Y) (x₀ : X) (e : X → V)
    (he : Isometry e) (he₀ : e x₀ = 0) (J : V →L[ℝ] Z)
    (A B C R : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hR : 0 ≤ R)
    (htame : ∀ u v : D,
      ‖F u - F v‖ ≤
        A * R * ‖e (u : X) - e (v : X)‖ +
          B * ‖J (e (u : X) - e (v : X))‖ +
          C * (‖e (u : X)‖ + ‖e (v : X)‖) *
            ‖J (e (u : X) - e (v : X))‖) :
    ∀ r : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ r} := by
  intro r
  let q : ℝ := max r 0
  let K₀ : ℝ := A * R + B * ‖J‖ + 2 * C * q * ‖J‖
  have hq : 0 ≤ q := by dsimp only [q]; exact le_max_right _ _
  have hK₀ : 0 ≤ K₀ := by
    dsimp only [K₀]
    positivity
  refine ⟨Real.toNNReal K₀, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have heu : ‖e (u : X)‖ ≤ q := by
    calc
      ‖e (u : X)‖ = dist (e (u : X)) (e x₀) := by
        rw [he₀, dist_zero_right]
      _ = dist (u : X) x₀ := he.dist_eq _ _
      _ ≤ r := hu
      _ ≤ q := le_max_left _ _
  have hev : ‖e (v : X)‖ ≤ q := by
    calc
      ‖e (v : X)‖ = dist (e (v : X)) (e x₀) := by
        rw [he₀, dist_zero_right]
      _ = dist (v : X) x₀ := he.dist_eq _ _
      _ ≤ r := hv
      _ ≤ q := le_max_left _ _
  have hediff : ‖e (u : X) - e (v : X)‖ = dist (u : X) (v : X) := by
    rw [← dist_eq_norm]
    exact he.dist_eq _ _
  have hJdiff : ‖J (e (u : X) - e (v : X))‖ ≤
      ‖J‖ * dist (u : X) (v : X) := by
    calc
      ‖J (e (u : X) - e (v : X))‖ ≤
          ‖J‖ * ‖e (u : X) - e (v : X)‖ := J.le_opNorm _
      _ = ‖J‖ * dist (u : X) (v : X) := by rw [hediff]
  have hsum : ‖e (u : X)‖ + ‖e (v : X)‖ ≤ 2 * q := by
    linarith
  have hBterm : B * ‖J (e (u : X) - e (v : X))‖ ≤
      B * (‖J‖ * dist (u : X) (v : X)) :=
    mul_le_mul_of_nonneg_left hJdiff hB
  have hthird :
      C * (‖e (u : X)‖ + ‖e (v : X)‖) *
          ‖J (e (u : X) - e (v : X))‖ ≤
        C * (2 * q) * (‖J‖ * dist (u : X) (v : X)) := by
    calc
      C * (‖e (u : X)‖ + ‖e (v : X)‖) *
          ‖J (e (u : X) - e (v : X))‖ =
          C * ((‖e (u : X)‖ + ‖e (v : X)‖) *
            ‖J (e (u : X) - e (v : X))‖) := by ring
      _ ≤ C * ((2 * q) * (‖J‖ * dist (u : X) (v : X))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hsum hJdiff (norm_nonneg _) (by positivity)) hC
      _ = C * (2 * q) * (‖J‖ * dist (u : X) (v : X)) := by ring
  rw [dist_eq_norm]
  calc
    ‖F u - F v‖ ≤
        A * R * ‖e (u : X) - e (v : X)‖ +
          B * ‖J (e (u : X) - e (v : X))‖ +
          C * (‖e (u : X)‖ + ‖e (v : X)‖) *
            ‖J (e (u : X) - e (v : X))‖ := htame u v
    _ ≤ A * R * dist (u : X) (v : X) +
          B * (‖J‖ * dist (u : X) (v : X)) +
          C * (2 * q) * (‖J‖ * dist (u : X) (v : X)) := by
      rw [hediff]
      exact add_le_add (add_le_add le_rfl hBterm) hthird
    _ = K₀ * dist (u : X) (v : X) := by
      dsimp only [K₀]
      ring
    _ = (Real.toNNReal K₀ : ℝ) * dist u v := by
      rw [Real.coe_toNNReal _ hK₀, Subtype.dist_eq]

/-- A tame estimate on a dense core passes to its continuous dense extension.

The ambient state space need not be linear.  Its points are realized in a
normed space by `e`; this is the form needed for a lower-Sobolev state-ball
subtype. -/
theorem dense_tame_extend
    {X V Y Z : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {D : Set X} (hD : Dense D) (F : D → Y) (x₀ : X)
    (hball : ∀ r : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ r})
    (e : X → V) (he : Continuous e) (J : V →L[ℝ] Z)
    (A B C R : ℝ)
    (htame : ∀ u v : D,
      ‖F u - F v‖ ≤
        A * R * ‖e (u : X) - e (v : X)‖ +
          B * ‖J (e (u : X) - e (v : X))‖ +
          C * (‖e (u : X)‖ + ‖e (v : X)‖) *
            ‖J (e (u : X) - e (v : X))‖) :
    ∀ u v : X,
      ‖Dense.extend hD F u - Dense.extend hD F v‖ ≤
        A * R * ‖e u - e v‖ + B * ‖J (e u - e v)‖ +
          C * (‖e u‖ + ‖e v‖) * ‖J (e u - e v)‖ := by
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro d
    let r : ℝ := dist (d : X) x₀ + 1
    obtain ⟨K, hK⟩ := hball r
    have hdball : (d : X) ∈ Metric.ball x₀ r := by
      rw [Metric.mem_ball]
      dsimp only [r]
      linarith
    have hclosed : Metric.closedBall x₀ r ∈ 𝓝 (d : X) :=
      Metric.closedBall_mem_nhds_of_mem hdball
    have hpre : ((↑) : D → X) ⁻¹' Metric.closedBall x₀ r ∈ 𝓝 d :=
      continuousAt_subtype_val.preimage_mem_nhds hclosed
    have hd : d ∈ {x : D | dist (x : X) x₀ ≤ r} := by
      change dist (d : X) x₀ ≤ dist (d : X) x₀ + 1
      linarith
    apply (hK.continuousOn d hd).continuousAt
    simpa only [Metric.mem_closedBall, Set.mem_setOf_eq] using hpre
  have hext_cont : Continuous (Dense.extend hD F) :=
    dense_cont_on_balls hD F x₀ hball
  have hext_eq : ∀ d : D, Dense.extend hD F (d : X) = F d := by
    intro d
    exact hD.extend_eq hFcont d
  set lhs : X × X → ℝ := fun p =>
    ‖Dense.extend hD F p.1 - Dense.extend hD F p.2‖ with hlhs_def
  set rhs : X × X → ℝ := fun p =>
    A * R * ‖e p.1 - e p.2‖ + B * ‖J (e p.1 - e p.2)‖ +
      C * (‖e p.1‖ + ‖e p.2‖) * ‖J (e p.1 - e p.2)‖ with hrhs_def
  have hlhs_cont : Continuous lhs := by
    rw [hlhs_def]
    exact ((hext_cont.comp continuous_fst).sub
      (hext_cont.comp continuous_snd)).norm
  have hesub : Continuous (fun p : X × X => e p.1 - e p.2) :=
    (he.comp continuous_fst).sub (he.comp continuous_snd)
  have hJsub : Continuous (fun p : X × X => J (e p.1 - e p.2)) :=
    J.continuous.comp hesub
  have hrhs_cont : Continuous rhs := by
    rw [hrhs_def]
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · exact continuous_const.mul hesub.norm
    · exact continuous_const.mul hJsub.norm
    · exact (continuous_const.mul
        ((he.comp continuous_fst).norm.add
          (he.comp continuous_snd).norm)).mul hJsub.norm
  have hclosed : IsClosed {p | lhs p ≤ rhs p} :=
    isClosed_le hlhs_cont hrhs_cont
  have hsub : (D ×ˢ D) ⊆ {p | lhs p ≤ rhs p} := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    let ud : D := ⟨u, hu⟩
    let vd : D := ⟨v, hv⟩
    have hu_ext : Dense.extend hD F u = F ud := by
      change Dense.extend hD F (ud : X) = F ud
      exact hext_eq ud
    have hv_ext : Dense.extend hD F v = F vd := by
      change Dense.extend hD F (vd : X) = F vd
      exact hext_eq vd
    change lhs (u, v) ≤ rhs (u, v)
    change ‖Dense.extend hD F u - Dense.extend hD F v‖ ≤
      A * R * ‖e u - e v‖ + B * ‖J (e u - e v)‖ +
        C * (‖e u‖ + ‖e v‖) * ‖J (e u - e v)‖
    rw [hu_ext, hv_ext]
    simpa only [ud, vd, Subtype.coe_mk] using htame ud vd
  have huniv : {p | lhs p ≤ rhs p} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (hD.prod hD).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  intro u v
  have hmem : (u, v) ∈ {p | lhs p ≤ rhs p} := by
    rw [huniv]
    trivial
  rw [Set.mem_setOf_eq, hlhs_def, hrhs_def] at hmem
  exact hmem

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/- A four-term `L²` Minkowski estimate.  It is kept private because its public
consumer is the three-arm fixed-point theorem below. -/
private theorem l2_four
    {T : ℝ} {X Y Z W V : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : timeL2 X T) (p : timeL2 Y T) (q : timeL2 Z T)
    (r : timeL2 W T) (s : timeL2 V T) {A B C D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖h t‖ ≤ A * ‖p t‖ + B * ‖q t‖ + C * ‖r t‖ + D * ‖s t‖) :
    ‖h‖ ≤ A * ‖p‖ + B * ‖q‖ + C * ‖r‖ + D * ‖s‖ := by
  let Pf : ℝ → ℝ := fun t => ‖(p : ℝ → Y) t‖
  let Qf : ℝ → ℝ := fun t => ‖(q : ℝ → Z) t‖
  let Rf : ℝ → ℝ := fun t => ‖(r : ℝ → W) t‖
  let Sf : ℝ → ℝ := fun t => ‖(s : ℝ → V) t‖
  have hPm : AEStronglyMeasurable Pf (timeMeasure T) := (Lp.aestronglyMeasurable p).norm
  have hQm : AEStronglyMeasurable Qf (timeMeasure T) := (Lp.aestronglyMeasurable q).norm
  have hRm : AEStronglyMeasurable Rf (timeMeasure T) := (Lp.aestronglyMeasurable r).norm
  have hSm : AEStronglyMeasurable Sf (timeMeasure T) := (Lp.aestronglyMeasurable s).norm
  have hAPm : AEStronglyMeasurable (A • Pf) (timeMeasure T) := hPm.const_smul A
  have hBQm : AEStronglyMeasurable (B • Qf) (timeMeasure T) := hQm.const_smul B
  have hCRm : AEStronglyMeasurable (C • Rf) (timeMeasure T) := hRm.const_smul C
  have hDSm : AEStronglyMeasurable (D • Sf) (timeMeasure T) := hSm.const_smul D
  let major : ℝ → ℝ := A • Pf + B • Qf + C • Rf + D • Sf
  have hmono : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      eLpNorm major 2 (timeMeasure T) := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hbound] with t ht
    have happ : major t =
        A * ‖p t‖ + B * ‖q t‖ + C * ‖r t‖ + D * ‖s t‖ := by
      simp only [major, Pf, Qf, Rf, Sf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hnonneg : 0 ≤ major t := by
      rw [happ]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, happ]
    exact ht
  have htri₁ : eLpNorm major 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) +
        eLpNorm (D • Sf) 2 (timeMeasure T) := by
    exact eLpNorm_add_le ((hAPm.add hBQm).add hCRm) hDSm (by norm_num)
  have htri₂ : eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) +
        eLpNorm (C • Rf) 2 (timeMeasure T) := by
    exact eLpNorm_add_le (hAPm.add hBQm) hCRm (by norm_num)
  have htri₃ : eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf) 2 (timeMeasure T) +
        eLpNorm (B • Qf) 2 (timeMeasure T) :=
    eLpNorm_add_le hAPm hBQm (by norm_num)
  have hscaleP : eLpNorm (A • Pf) 2 (timeMeasure T) =
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA]
  have hscaleQ : eLpNorm (B • Qf) 2 (timeMeasure T) =
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hB]
  have hscaleR : eLpNorm (C • Rf) 2 (timeMeasure T) =
      ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hC]
  have hscaleS : eLpNorm (D • Sf) 2 (timeMeasure T) =
      ENNReal.ofReal D * eLpNorm (s : ℝ → V) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hD]
  have hfinal : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) +
        ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) +
        ENNReal.ofReal D * eLpNorm (s : ℝ → V) 2 (timeMeasure T) := by
    calc
      eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤ eLpNorm major 2 (timeMeasure T) := hmono
      _ ≤ eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) +
          eLpNorm (D • Sf) 2 (timeMeasure T) := htri₁
      _ ≤ (eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) +
            eLpNorm (C • Rf) 2 (timeMeasure T)) +
          eLpNorm (D • Sf) 2 (timeMeasure T) :=
        add_le_add htri₂ le_rfl
      _ ≤ ((eLpNorm (A • Pf) 2 (timeMeasure T) +
              eLpNorm (B • Qf) 2 (timeMeasure T)) +
            eLpNorm (C • Rf) 2 (timeMeasure T)) +
          eLpNorm (D • Sf) 2 (timeMeasure T) :=
        add_le_add (add_le_add htri₃ le_rfl) le_rfl
      _ = _ := by rw [hscaleP, hscaleQ, hscaleR, hscaleS]
  have hp_top : eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp p).2.ne
  have hq_top : eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp q).2.ne
  have hr_top : eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp r).2.ne
  have hs_top : eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp s).2.ne
  have hp_mul : ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top
  have hq_mul : ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top
  have hr_mul : ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr_top
  have hs_mul : ENNReal.ofReal D * eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs_top
  have hrhs_ne :
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) +
        ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) +
        ENNReal.ofReal D * eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩, hr_mul⟩, hs_mul⟩
  change (eLpNorm (h : ℝ → X) 2 (timeMeasure T)).toReal ≤
    A * (eLpNorm (p : ℝ → Y) 2 (timeMeasure T)).toReal +
      B * (eLpNorm (q : ℝ → Z) 2 (timeMeasure T)).toReal +
      C * (eLpNorm (r : ℝ → W) 2 (timeMeasure T)).toReal +
      D * (eLpNorm (s : ℝ → V) 2 (timeMeasure T)).toReal
  refine le_trans (ENNReal.toReal_mono hrhs_ne hfinal) ?_
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩, hr_mul⟩) hs_mul,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩) hr_mul,
    ENNReal.toReal_add hp_mul hq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hD]

/- A continuous state-set map satisfying the three-arm estimate sends every
top-order `L²` field which remains in the state set to an `L²` forcing field. -/
private theorem memLp_tame
    {T R : ℝ} {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : S → Y) (hN : Continuous N) (A B C : ℝ≥0)
    (htame : ∀ u v : S,
      ‖N u - N v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    MemLp (fun t => N (aeSetLift hzero f t)) 2 (timeMeasure T) := by
  let z : S := ⟨0, hzero⟩
  let K : ℝ := (A : ℝ) * R + (C : ℝ) * R
  let Q : ℝ := (B : ℝ) * R + ‖N z‖
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hlift := aeSetLift_aesm hzero f hf
  have hmeas : AEStronglyMeasurable
      (fun t => N (aeSetLift hzero f t)) (timeMeasure T) :=
    hN.comp_aestronglyMeasurable hlift
  let major : ℝ → ℝ := fun t => K * ‖f t‖ + Q
  have hmajor : MemLp major 2 (timeMeasure T) := by
    have hnorm : MemLp (fun t => ‖f t‖) 2 (timeMeasure T) := (Lp.memLp f).norm
    have hscaled : MemLp (K • fun t => ‖f t‖) 2 (timeMeasure T) := hnorm.const_smul K
    have hconst : MemLp (fun _ : ℝ => Q) 2 (timeMeasure T) := memLp_const Q
    have hadd := hscaled.add hconst
    simpa only [major, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hadd
  refine hmajor.of_le hmeas ?_
  filter_upwards [hf] with t ht
  let u : S := ⟨f t, ht⟩
  have huJ : ‖J (f t)‖ ≤ R := by
    simpa only [u] using hstate u
  have hdiff : ‖N u - N z‖ ≤ K * ‖f t‖ + (B : ℝ) * R := by
    have hraw := htame u z
    have hraw' : ‖N u - N z‖ ≤
        (A : ℝ) * R * ‖f t‖ + (B : ℝ) * ‖J (f t)‖ +
          (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := by
      simpa only [u, z, Subtype.coe_mk, sub_zero, map_zero, norm_zero, add_zero] using hraw
    calc
      ‖N u - N z‖ ≤
          (A : ℝ) * R * ‖f t‖ + (B : ℝ) * ‖J (f t)‖ +
            (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := hraw'
      _ ≤ (A : ℝ) * R * ‖f t‖ + (B : ℝ) * R +
            (C : ℝ) * ‖f t‖ * R := by
        gcongr
      _ = K * ‖f t‖ + (B : ℝ) * R := by
        dsimp only [K]
        ring
  have hn : ‖N u‖ ≤ major t := by
    calc
      ‖N u‖ = ‖(N u - N z) + N z‖ := by rw [sub_add_cancel]
      _ ≤ ‖N u - N z‖ + ‖N z‖ := norm_add_le _ _
      _ ≤ (K * ‖f t‖ + (B : ℝ) * R) + ‖N z‖ :=
        add_le_add hdiff le_rfl
      _ = major t := by
        dsimp only [major, Q]
        ring
  have hmajor0 : 0 ≤ major t := by
    dsimp only [major]
    exact add_nonneg (mul_nonneg hK (norm_nonneg _)) hQ
  change ‖N (aeSetLift hzero f t)‖ ≤ ‖major t‖
  have hu : aeSetLift hzero f t = u := by
    simp only [aeSetLift, dif_pos ht, u]
  rw [hu, Real.norm_eq_abs, abs_of_nonneg hmajor0]
  exact hn

/-- Quantitative forcing-space existence for a continuous nonlinearity on a
lower-order state ball satisfying the critical three-arm tame estimate.

The first smallness hypothesis controls the genuinely top-order arm.  The
second controls the high-size times lower-difference arm on the forcing ball.
The horizon controls only the fixed lower-order arm and the displacement of
the zero forcing. -/
theorem partial_sol_tame
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 < R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hcont : Continuous Nfun)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ‖Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR.le⟩‖ ≤ D)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16)
    (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
                ‖(u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖) :
    ∃ T₀ : ℝ,
      T₀ = min 1 (min (1 / (64 * ((B : ℝ) + 1) ^ 2))
        ((((R / 4) / (2 * (D + 1))) ^ 2))) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        let field := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce
        u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            field t ∈ lowerState (I := I) (M := M) g₀ a R) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => Nfun (aeSetLift
              (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le) field t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (a : ℝ) field + gforce ∧
          ‖gforce‖ ≤ R / 4 := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  have ha12 : (a : ℝ) + 1 ≤ (a : ℝ) + 2 := by linarith
  let J := tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    ha12
  let hz := zero_mem_lowerState (I := I) (M := M) g₀ a hR.le
  have hstateJ : ∀ u : lowerState (I := I) (M := M) g₀ a R, ‖J (u : _)‖ ≤ R := by
    intro u
    simpa only [lowerState, lowerBall, J] using u.property
  set ρ : ℝ := R / 4 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have h2ρR : 2 * ρ ≤ R := by rw [hρdef]; nlinarith [hR]
  set T₀ : ℝ := min 1 (min (1 / (64 * ((B : ℝ) + 1) ^ 2))
    ((ρ / (2 * (D + 1))) ^ 2)) with hT₀def
  have hD1 : 0 < D + 1 := by linarith
  have hT₀ : 0 < T₀ := by
    refine lt_min one_pos (lt_min (by positivity) ?_)
    positivity
  refine ⟨T₀, ?_, hT₀, ?_⟩
  · rw [hT₀def, hρdef]
  intro T hT hTT₀ hT1
  have hTlo : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2) :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hTstay : T ≤ (ρ / (2 * (D + 1))) ^ 2 :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have hsqrt1T : Real.sqrt (1 + T) ≤ 2 := by
    have hsq : Real.sqrt (1 + T) ≤ 1 + T := by
      calc
        Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
        _ = 1 + T := Real.sqrt_sq (by linarith)
    linarith
  set Λ : ℝ :=
      (A : ℝ) * R * (1 + T) + (B : ℝ) * (2 * Real.sqrt T) +
        2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T) with hΛdef
  have hΛnn : 0 ≤ Λ := by rw [hΛdef]; positivity
  have harm1 : (A : ℝ) * R * (1 + T) ≤ 1 / 8 := by
    have hARnn : 0 ≤ (A : ℝ) * R := mul_nonneg A.coe_nonneg hR.le
    calc
      (A : ℝ) * R * (1 + T) ≤ (A : ℝ) * R * 2 :=
        mul_le_mul_of_nonneg_left h1T hARnn
      _ ≤ (1 / 16 : ℝ) * 2 := mul_le_mul_of_nonneg_right hsmallA (by positivity)
      _ = 1 / 8 := by norm_num
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((B : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((B : ℝ) + 1)) =
      Real.sqrt ((1 / (8 * ((B : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hTlo ?_)
    rw [div_pow, one_pow, mul_pow]
    norm_num
  have harm2 : (B : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    calc
      (B : ℝ) * (2 * Real.sqrt T) = 2 * (B : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (B : ℝ) * (1 / (8 * ((B : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (B : ℝ) / ((B : ℝ) + 1) * (1 / 4) := by
        field_simp
        ring
      _ ≤ 1 / 4 := by
        have hfrac : (B : ℝ) / ((B : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [B.coe_nonneg]
        nlinarith [hfrac,
          div_nonneg B.coe_nonneg (by positivity : (0 : ℝ) ≤ (B : ℝ) + 1)]
  have harm3 :
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T) ≤ 1 / 8 := by
    calc
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T) ≤
          2 * (C : ℝ) * ρ * 2 * 2 := by
        gcongr
      _ = 2 * ((C : ℝ) * R) := by rw [hρdef]; ring
      _ ≤ 2 * (1 / 16 : ℝ) := mul_le_mul_of_nonneg_left hsmallC (by positivity)
      _ = 1 / 8 := by norm_num
  have hΛle : Λ ≤ 1 / 2 := by rw [hΛdef]; linarith
  have hΛlt : Λ < 1 := by linarith

  set z₀ : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T := 0 with hz₀
  set ρt := recenteredBallRetraction z₀ ρ with hρtdef
  have hρt_mem : ∀ F, ρt F ∈ Metric.closedBall z₀ ρ := fun F =>
    recenteredBallRetraction_mapsTo (X := _) hρ.le z₀ (Set.mem_univ F)
  have hρt_norm : ∀ F, ‖ρt F‖ ≤ ρ := by
    intro F
    have h := hρt_mem F
    rw [Metric.mem_closedBall, hz₀, dist_zero_right] at h
    exact h
  have hρt_lip : LipschitzWith 1 ρt :=
    recenteredBallRetraction_lipschitzWith hρ.le z₀
  set field : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T :=
    fun F => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F)
    with hfielddef
  have hstate : ∀ F, ∀ᵐ t ∂(timeMeasure T),
      field F t ∈ lowerState (I := I) (M := M) g₀ a R := by
    intro F
    exact field_mem_lower (I := I) (M := M) g₀ a hT hT1 h2ρR
      (ρt F) (hρt_norm F)
  let liftN : ∀ (f : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T),
      (∀ᵐ t ∂(timeMeasure T), f t ∈ lowerState (I := I) (M := M) g₀ a R) →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    fun f hf => (memLp_tame hz hR.le J hstateJ Nfun hcont A B C hsingle f hf).toLp
      (fun t => Nfun (aeSetLift hz f t))
  have liftN_coe : ∀ (f : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
      (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ lowerState (I := I) (M := M) g₀ a R),
      liftN f hf =ᵐ[timeMeasure T] fun t => Nfun (aeSetLift hz f t) := by
    intro f hf
    exact (memLp_tame hz hR.le J hstateJ Nfun hcont A B C hsingle f hf).coeFn_toLp
  set Ψ : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    fun F => liftN (field F) (hstate F) with hΨdef

  have hΨ_retr : ∀ F F', ‖Ψ F - Ψ F'‖ ≤ Λ * ‖ρt F - ρt F'‖ := by
    intro F F'
    have hfield_dist : ‖field F - field F'‖ ≤
        (1 + T) * ‖ρt F - ρt F'‖ := by
      exact maxRegDuhamelSolField_dist_le (I := I) (M := M) (h_compact := h_compact)
        (a := (a : ℝ)) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F) (ρt F')
    have hincl_dist :
        ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            ha12 (field F - field F')‖ ≤
          2 * Real.sqrt T * ‖ρt F - ρt F'‖ := by
      change
        ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            ha12
            (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F) -
              maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F'))‖ ≤
          2 * Real.sqrt T * ‖ρt F - ρt F'‖
      rw [map_sub,
        timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F),
        timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F')]
      exact maxRegDuhamelSolFieldHa1_dist_le (I := I) (M := M) (h_compact := h_compact)
        (a := (a : ℝ)) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F) (ρt F')
    have hfield_norm : ∀ G, ‖field G‖ ≤ (1 + T) * ρ := by
      intro G
      calc
        ‖field G‖ ≤ (1 + T) * ‖ρt G‖ := by
          simpa only [hfielddef] using
            norm_maxRegDuhamelSolField_zero_le (I := I) (M := M) (g₀ := g₀)
              hT hT1 (ρt G)
        _ ≤ (1 + T) * ρ :=
          mul_le_mul_of_nonneg_left (hρt_norm G) (by linarith)
    have hfield_sub : field F - field F' =
        maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (ρt F - ρt F') := by
      change
        maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F) -
            maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F') =
          maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            (ρt F - ρt F')
      have hsub := maxRegDuhamelSolField_sub (I := I) (M := M)
        (h_compact := h_compact) (a := (a : ℝ)) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F) (ρt F')
      have hdiffzero := maxRegDuhamelSolField_sub (I := I) (M := M)
        (h_compact := h_compact) (a := (a : ℝ)) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (ρt F - ρt F') 0
      rw [sub_zero,
        maxRegDuhamelSolField_zero_zero (I := I) (M := M) (g₀ := g₀) hT hT1,
        sub_zero] at hdiffzero
      exact hsub.trans hdiffzero.symm
    have hpoint : ∀ᵐ t ∂(timeMeasure T),
        ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          ha12
          (field F - field F')) t‖ ≤
            Real.sqrt (1 + T) * ‖ρt F - ρt F'‖ := by
      rw [hfield_sub]
      exact maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le
        (I := I) (M := M) (g₀ := g₀) hT hT1 (ρt F - ρt F')
    let S : ℝ := Real.sqrt (1 + T) * ‖ρt F - ρt F'‖
    have hS : 0 ≤ S := by dsimp only [S]; positivity
    have hΨF : Ψ F =ᵐ[timeMeasure T]
        fun t => Nfun (aeSetLift hz (field F) t) := by
      simpa only [hΨdef] using liftN_coe (field F) (hstate F)
    have hΨF' : Ψ F' =ᵐ[timeMeasure T]
        fun t => Nfun (aeSetLift hz (field F') t) := by
      simpa only [hΨdef] using liftN_coe (field F') (hstate F')
    have hΨsub := Lp.coeFn_sub (Ψ F) (Ψ F')
    have hfieldsub := Lp.coeFn_sub (field F) (field F')
    have hinclcoe :
        ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          ha12 (field F - field F'))
          =ᵐ[timeMeasure T]
        fun t => J ((field F - field F') t) := by
      simpa only [J] using
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          ha12).coeFn_compLpL
          (p := 2) (μ := timeMeasure T) (field F - field F')
    have hbound : ∀ᵐ t ∂(timeMeasure T),
        ‖(Ψ F - Ψ F') t‖ ≤
          (A : ℝ) * R * ‖(field F - field F') t‖ +
            (B : ℝ) *
              ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                ha12
                (field F - field F')) t‖ +
            ((C : ℝ) * S) * ‖field F t‖ +
            ((C : ℝ) * S) * ‖field F' t‖ := by
      filter_upwards [hΨsub, hΨF, hΨF', hfieldsub, hinclcoe, hpoint,
        hstate F, hstate F'] with t htΨ htF htF' htfsub htincl htpoint htstate htstate'
      rw [htΨ, Pi.sub_apply, htF, htF']
      simp only [aeSetLift, dif_pos htstate, dif_pos htstate']
      let u : lowerState (I := I) (M := M) g₀ a R := ⟨field F t, htstate⟩
      let u' : lowerState (I := I) (M := M) g₀ a R := ⟨field F' t, htstate'⟩
      have hraw := hsingle u u'
      have htfsub' : field F t - field F' t = (field F - field F') t := by
        calc
          field F t - field F' t = (⇑(field F) - ⇑(field F')) t := rfl
          _ = (field F - field F') t := htfsub.symm
      have htincl_sub :
          tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              ha12
              ((field F - field F') t) =
            (timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              ha12
              (field F - field F')) t := by
        change J ((field F - field F') t) =
          (timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            ha12
            (field F - field F')) t
        exact htincl.symm
      have hraw' : ‖Nfun u - Nfun u'‖ ≤
          (A : ℝ) * R * ‖(field F - field F') t‖ +
            (B : ℝ) *
              ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                ha12
                (field F - field F')) t‖ +
            (C : ℝ) * (‖field F t‖ + ‖field F' t‖) *
              ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                ha12
                (field F - field F')) t‖ := by
        simpa only [u, u', Subtype.coe_mk, htfsub', htincl_sub] using hraw
      have hthird :
          (C : ℝ) * (‖field F t‖ + ‖field F' t‖) *
              ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                ha12
                (field F - field F')) t‖ ≤
            ((C : ℝ) * S) * ‖field F t‖ +
              ((C : ℝ) * S) * ‖field F' t‖ := by
        calc
          (C : ℝ) * (‖field F t‖ + ‖field F' t‖) *
                ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  ha12
                  (field F - field F')) t‖ ≤
              (C : ℝ) * (‖field F t‖ + ‖field F' t‖) * S := by
            exact mul_le_mul_of_nonneg_left
              (by simpa only [S] using htpoint)
              (mul_nonneg C.coe_nonneg (by positivity))
          _ = ((C : ℝ) * S) * ‖field F t‖ +
                ((C : ℝ) * S) * ‖field F' t‖ := by ring
      calc
        ‖Nfun u - Nfun u'‖ ≤
            ((A : ℝ) * R * ‖(field F - field F') t‖ +
              (B : ℝ) *
                ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  ha12
                  (field F - field F')) t‖) +
              (C : ℝ) * (‖field F t‖ + ‖field F' t‖) *
                ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  ha12
                  (field F - field F')) t‖ := hraw'
        _ ≤ ((A : ℝ) * R * ‖(field F - field F') t‖ +
              (B : ℝ) *
                ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  ha12
                  (field F - field F')) t‖) +
              (((C : ℝ) * S) * ‖field F t‖ +
                ((C : ℝ) * S) * ‖field F' t‖) :=
          by
            apply add_le_add_right
            exact hthird
        _ = (A : ℝ) * R * ‖(field F - field F') t‖ +
              (B : ℝ) *
                ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  ha12
                  (field F - field F')) t‖ +
              ((C : ℝ) * S) * ‖field F t‖ +
              ((C : ℝ) * S) * ‖field F' t‖ := by ac_rfl
    have hmain := l2_four
      (T := T)
      (X := tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
      (Y := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (Z := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
      (W := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (V := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (A := (A : ℝ) * R) (B := (B : ℝ))
      (C := (C : ℝ) * S) (D := (C : ℝ) * S)
      (Ψ F - Ψ F') (field F - field F')
      (timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        ha12 (field F - field F'))
      (field F) (field F')
      (mul_nonneg A.coe_nonneg hR.le) B.coe_nonneg
      (mul_nonneg C.coe_nonneg hS) (mul_nonneg C.coe_nonneg hS) hbound
    calc
      ‖Ψ F - Ψ F'‖ ≤
          (A : ℝ) * R * ‖field F - field F'‖ +
            (B : ℝ) *
              ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                ha12 (field F - field F')‖ +
            ((C : ℝ) * S) * ‖field F‖ + ((C : ℝ) * S) * ‖field F'‖ := hmain
      _ ≤ (A : ℝ) * R * ((1 + T) * ‖ρt F - ρt F'‖) +
            (B : ℝ) * (2 * Real.sqrt T * ‖ρt F - ρt F'‖) +
            ((C : ℝ) * S) * ((1 + T) * ρ) +
            ((C : ℝ) * S) * ((1 + T) * ρ) := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left hfield_dist
                (mul_nonneg A.coe_nonneg hR.le))
              (mul_le_mul_of_nonneg_left hincl_dist B.coe_nonneg))
            (mul_le_mul_of_nonneg_left (hfield_norm F)
              (mul_nonneg C.coe_nonneg hS)))
          (mul_le_mul_of_nonneg_left (hfield_norm F')
            (mul_nonneg C.coe_nonneg hS))
      _ = Λ * ‖ρt F - ρt F'‖ := by
        rw [hΛdef]
        dsimp only [S]
        ring

  have hΨ_lip : ∀ F F', ‖Ψ F - Ψ F'‖ ≤ Λ * ‖F - F'‖ := by
    intro F F'
    refine (hΨ_retr F F').trans ?_
    have hr := hρt_lip.dist_le_mul F F'
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hr
    exact mul_le_mul_of_nonneg_left hr hΛnn
  have hcontr : ContractingWith Λ.toNNReal Ψ := by
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hΛnn]
      exact hΛlt
    · refine LipschitzWith.of_dist_le_mul (fun F F' => ?_)
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛnn]
      exact hΨ_lip F F'

  have hρt0 : ρt z₀ = z₀ :=
    recenteredBallRetraction_eq_self_of_mem (Metric.mem_closedBall_self hρ.le)
  have hfield0 : field z₀ = 0 := by
    change maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt z₀) = 0
    rw [hρt0, hz₀]
    exact maxRegDuhamelSolField_zero_zero (I := I) (M := M) (g₀ := g₀) hT hT1
  have hΨ0 : ‖Ψ z₀‖ ≤ Real.sqrt T *
      ‖Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR.le⟩‖ := by
    refine timeL2_norm_le_of_ae_bound _ (norm_nonneg _) ?_
    have hcoe : Ψ z₀ =ᵐ[timeMeasure T]
        fun t => Nfun (aeSetLift hz (field z₀) t) := by
      simpa only [hΨdef] using liftN_coe (field z₀) (hstate z₀)
    have hzeroFn := Lp.coeFn_zero
      (E := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (p := 2) (μ := timeMeasure T)
    have hfieldFn : ⇑(field z₀) =ᵐ[timeMeasure T]
        fun _ => (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
      rw [hfield0]
      exact hzeroFn
    filter_upwards [hcoe, hfieldFn, hstate z₀] with t ht htfield htstate
    rw [ht]
    have hlift : aeSetLift hz (field z₀) t =
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR.le⟩ := by
      apply Subtype.ext
      simp only [aeSetLift, dif_pos htstate, Subtype.coe_mk]
      exact htfield
    rw [hlift]
  have hsqrtTD : Real.sqrt T * D ≤ ρ / 2 := by
    have hsqrtTstay : Real.sqrt T ≤ ρ / (2 * (D + 1)) := by
      rw [show ρ / (2 * (D + 1)) = Real.sqrt ((ρ / (2 * (D + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hTstay
    calc
      Real.sqrt T * D ≤ (ρ / (2 * (D + 1))) * D :=
        mul_le_mul_of_nonneg_right hsqrtTstay hD
      _ ≤ (ρ / (2 * (D + 1))) * (D + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by field_simp
  have hΨ0' : ‖Ψ z₀‖ ≤ ρ / 2 :=
    hΨ0.trans ((mul_le_mul_of_nonneg_left hzero (Real.sqrt_nonneg T)).trans hsqrtTD)
  have hΨstay : ∀ F, ‖Ψ F‖ ≤ ρ := by
    intro F
    have hdist := hΨ_retr F z₀
    have hretr0 : ‖ρt F - ρt z₀‖ ≤ ρ := by
      rw [hρt0, hz₀, sub_zero]
      exact hρt_norm F
    calc
      ‖Ψ F‖ = ‖(Ψ F - Ψ z₀) + Ψ z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖Ψ F - Ψ z₀‖ + ‖Ψ z₀‖ := norm_add_le _ _
      _ ≤ Λ * ‖ρt F - ρt z₀‖ + ρ / 2 := add_le_add hdist hΨ0'
      _ ≤ (1 / 2) * ρ + ρ / 2 := by
        exact add_le_add
          ((mul_le_mul_of_nonneg_left hretr0 hΛnn).trans
            (mul_le_mul_of_nonneg_right hΛle hρ.le)) le_rfl
      _ = ρ := by ring

  set Fstar := ContractingWith.fixedPoint Ψ hcontr with hFstar_def
  have hfix : Ψ Fstar = Fstar := ContractingWith.fixedPoint_isFixedPt hcontr
  have hFstar : ‖Fstar‖ ≤ ρ := by rw [← hfix]; exact hΨstay Fstar
  have hρtstar : ρt Fstar = Fstar :=
    recenteredBallRetraction_eq_self_of_mem (by
      rw [Metric.mem_closedBall, hz₀, dist_zero_right]
      exact hFstar)
  set trueField := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar with htrueField
  have hfieldstar : field Fstar = trueField := by
    change maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt Fstar) = trueField
    rw [hρtstar, htrueField]
  have hstateStar : ∀ᵐ t ∂(timeMeasure T),
      trueField t ∈ lowerState (I := I) (M := M) g₀ a R := by
    rw [← hfieldstar]
    exact hstate Fstar
  have hforceEq : Fstar = liftN (field Fstar) (hstate Fstar) := by
    calc
      Fstar = Ψ Fstar := hfix.symm
      _ = liftN (field Fstar) (hstate Fstar) := by simp only [hΨdef]
  have hforceAe₀ : ⇑Fstar =ᵐ[timeMeasure T]
      fun t => Nfun (aeSetLift hz (field Fstar) t) := by
    have heq : ⇑Fstar =ᵐ[timeMeasure T] ⇑(liftN (field Fstar) (hstate Fstar)) := by
      exact Filter.Eventually.of_forall (fun t =>
        congrArg (fun F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T => F t)
          hforceEq)
    exact heq.trans (liftN_coe (field Fstar) (hstate Fstar))
  have hforceAe : ⇑Fstar =ᵐ[timeMeasure T]
      fun t => Nfun (aeSetLift hz trueField t) := by
    simpa only [hfieldstar] using hforceAe₀

  refine ⟨maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar,
    Fstar, ?_⟩
  dsimp only
  refine ⟨rfl, hstateStar, hforceAe, ?_, ?_, ?_⟩
  · rw [maxRegDuhamelMap_trace0 (I := I) (M := M) (a := (a : ℝ)) (T := T) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar, map_zero]
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) (T := T) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar]
  · simpa only [hρdef] using hFstar

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
