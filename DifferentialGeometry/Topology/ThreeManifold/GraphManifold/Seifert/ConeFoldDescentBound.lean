import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentComplete

/-!
# The gradient bound and properness for the cone-fold descent

`exhaustFn` is smooth on the descent domain (`contDiffOn_exhaustFn`). Its derivative is bounded by
the `.hyperbolicProduct` norm, `|D exhaustFn (p) v| ≤ C √g_p(v, v)` on the whole domain
(`exists_bound_fderiv_exhaustFn`): a point is `FoldRel`-related to a point `p₀` over the triangle
with fibre coordinate in `[0, 1)` by an isometry preserving `exhaustFn` near it; at `p₀` the
exhaustion is `p 1` high in the outer cusp, `(S·p) 1` deep in the inner cusp (`S z = -1/z` an
isometry), and the remaining points form the compact set `midSet` on which the derivative is
bounded by continuity and the Euclidean norm by the metric. On the interior of the carrier the
exhaustion `carrierExhaust = exhaust ∘ conePoint` is smooth (`contMDiff_carrierExhaust`) and proper
(`isProperMap_carrierExhaust`): its sublevel sets are closed subsets of the compact sets
`{x ∈ filledSet | ‖conePoint x‖ ≤ r, ‖conePoint x + 3/2‖ ≥ ρ}` with `r < 3`, `ρ > 1/2`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

universe u

namespace GC.Seifert

private abbrev coord (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

private theorem norm_modelCoordinates_le (p : ModelCoordinates) : ‖p‖ ≤ |p 0| + |p 1| + |p 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |p 0| + |p 1| + |p 2|)]
  apply Real.sqrt_le_sqrt
  have h0 := abs_nonneg (p 0)
  have h1 := abs_nonneg (p 1)
  have h2 := abs_nonneg (p 2)
  nlinarith [sq_abs (p 0), sq_abs (p 1), sq_abs (p 2)]

private theorem continuous_cuspZeroHeight_logPoint :
    Continuous fun p : ModelCoordinates => cuspZeroHeight (logPoint p : ℂ) := by
  have hL : Continuous fun p : ModelCoordinates => (logPoint p : ℂ) :=
    contDiff_coe_logPoint.continuous
  exact (Complex.continuous_normSq.comp hL).div (continuous_im.comp hL)
    fun p => (logPoint_im_pos p).ne'

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling) (hθ : σ.θ₁ * c.p = Real.pi)

theorem contDiffOn_exhaustFn (hσ : σ.θ₂ = 0) :
    ContDiffOn ℝ ∞ (D.exhaustFn.{u} c) (D.descentDomain c hθ) := by
  have h1 : ContMDiffOn (𝓡 3) PlaneCircleModel ∞ (D.mirrorMap.{u} c) (D.descentDomain c hθ) :=
    (D.isLocalDiffeomorphOn_mirrorMap c hθ hσ).contMDiffOn
  have h2 : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun p => c.conePoint (D.mirrorMap.{u} c p))
      (D.descentDomain c hθ) :=
    c.contMDiff_conePoint.comp_contMDiffOn h1
  have h3 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ D.exhaust filledBase :=
    D.contDiffOn_exhaust.contMDiffOn
  exact contMDiffOn_iff_contDiffOn.1
    (h3.comp h2 fun p hp => D.conePoint_mirrorMap_mem c hθ hσ hp)

theorem exhaustFn_comp_eventuallyEq {b : Bool} {y y' : ModelCoordinates}
    (h : D.FoldRel.{u} c hθ b y y') :
    ∃ γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates,
      Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) γ =
        coordinateModelMetric .hyperbolicProduct ∧ γ y = y' ∧
      (D.exhaustFn.{u} c ∘ γ) =ᶠ[𝓝 y] D.exhaustFn.{u} c := by
  obtain ⟨γ, hγ, hy, U, hU, hyU, -, -, hid⟩ := h
  refine ⟨γ, hγ, hy, Filter.eventually_of_mem (hU.mem_nhds hyU) fun z hz => ?_⟩
  simp only [Function.comp_apply, exhaustFn]
  rw [hid z hz, conePoint_twistMap]
  cases b
  · rfl
  · exact D.exhaust_conj _

theorem topHeight_pos : 0 < D.topHeight := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)

theorem exists_bound_fderiv_exhaustFn (hσ : σ.θ₂ = 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p ∈ D.descentDomain c hθ, ∀ v : ModelCoordinates,
      |fderiv ℝ (D.exhaustFn.{u} c) p v| ≤
        C * Real.sqrt (coordinateInner .hyperbolicProduct p v v) := by
  set N := D.descentDomain c hθ
  set Yt := D.topHeight
  set ηb := D.bottomHeight
  set yL := min (1 / 2) (ηb / (2 * (1 / (1 / 2 - σ.width) ^ 2 + 1)))
  have hYt := D.topHeight_pos
  have hw : 0 < 1 / 2 - σ.width := by have := σ.descentWidth_lt_half; linarith
  have hyL : 0 < yL := lt_min (by norm_num) (by have := D.bottomHeight_pos; positivity)
  set Kmid : Set ModelCoordinates := {p | 0 ≤ p 0} ∩ {p | p 0 ≤ σ.width} ∩
    {p | 0 ≤ σ.wallSide 2 (logPoint p)} ∩ {p | Real.log yL ≤ p 1} ∩ {p | p 1 ≤ Real.log Yt} ∩
    {p | ηb ≤ cuspZeroHeight (logPoint p : ℂ)} ∩ {p | 0 ≤ p 2} ∩ {p | p 2 ≤ 1} with hKmid
  have hL : Continuous fun p : ModelCoordinates => (logPoint p : ℂ) :=
    contDiff_coe_logPoint.continuous
  have hc (i : Fin 3) : Continuous fun p : ModelCoordinates => p i := (coord i).continuous
  have hKclosed : IsClosed Kmid :=
    ((((((((isClosed_le continuous_const (hc 0)).inter (isClosed_le (hc 0) continuous_const)).inter
      (isClosed_le continuous_const ((σ.wallSide_continuous 2).comp hL))).inter
      (isClosed_le continuous_const (hc 1))).inter (isClosed_le (hc 1) continuous_const)).inter
      (isClosed_le continuous_const continuous_cuspZeroHeight_logPoint)).inter
      (isClosed_le continuous_const (hc 2))).inter (isClosed_le (hc 2) continuous_const))
  have hKbdd : Bornology.IsBounded Kmid := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨σ.width + |Real.log yL| + |Real.log Yt| + 1, fun p hp => ?_⟩
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, -⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩ := hp
    replace h0 : 0 ≤ p 0 := h0
    replace h1 : p 0 ≤ σ.width := h1
    replace h3 : Real.log yL ≤ p 1 := h3
    replace h4 : p 1 ≤ Real.log Yt := h4
    replace h6 : 0 ≤ p 2 := h6
    replace h7 : p 2 ≤ 1 := h7
    rw [Metric.mem_closedBall, dist_zero_right]
    have e0 : |p 0| ≤ σ.width := abs_le.2 ⟨by linarith [σ.width_pos], h1⟩
    have e1 : |p 1| ≤ |Real.log yL| + |Real.log Yt| :=
      abs_le.2 ⟨by linarith [neg_abs_le (Real.log yL), abs_nonneg (Real.log Yt)],
        by linarith [le_abs_self (Real.log Yt), abs_nonneg (Real.log yL)]⟩
    have e2 : |p 2| ≤ 1 := abs_le.2 ⟨by linarith, h7⟩
    linarith [norm_modelCoordinates_le p]
  have hKc : IsCompact Kmid := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  have hKsub : Kmid ⊆ N := by
    intro p hp
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hp
    replace h0 : 0 ≤ p 0 := h0
    replace h1 : p 0 ≤ σ.width := h1
    replace h2 : 0 ≤ σ.wallSide 2 (logPoint p) := h2
    have hT : (logPoint p : ℂ) ∈ σ.triangle := by
      refine ⟨logPoint_im_pos p, fun i => ?_⟩
      fin_cases i
      · change 0 ≤ (logPoint p : ℂ).re
        rw [logPoint_re_eq']
        exact h0
      · change 0 ≤ σ.width - (logPoint p : ℂ).re
        rw [logPoint_re_eq']
        linarith
      · exact h2
    exact D.mem_descentDomain_of_patches c hθ (D.triangle_subset_patches c hθ hσ hT)
  have hcont := (D.contDiffOn_exhaustFn.{u} c hθ hσ).continuousOn_fderiv_of_isOpen N.isOpen
    (by simp)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hKsub)
  set C := max 1 (|B| * (Yt + 1))
  refine ⟨C, le_max_left _ _, fun p hp v => ?_⟩
  have hdiff : ∀ q ∈ N, DifferentiableAt ℝ (D.exhaustFn.{u} c) q := fun q hq =>
    ((D.contDiffOn_exhaustFn.{u} c hθ hσ).contDiffAt (N.isOpen.mem_nhds hq)).differentiableAt
      (by simp)
  have hQ : ∀ q w : ModelCoordinates, 0 ≤ Real.sqrt (coordinateInner .hyperbolicProduct q w w) :=
    fun _ _ => Real.sqrt_nonneg _
  have key : ∀ p₀ : ModelCoordinates, p₀ ∈ N → (logPoint p₀ : ℂ) ∈ σ.triangle → 0 ≤ p₀ 2 →
      p₀ 2 ≤ 1 → ∀ w : ModelCoordinates, |fderiv ℝ (D.exhaustFn.{u} c) p₀ w| ≤
        C * Real.sqrt (coordinateInner .hyperbolicProduct p₀ w w) := by
    intro p₀ hp₀ hT h0 h1 w
    by_cases ha : Yt < Real.exp (p₀ 1)
    · have hO : IsOpen {q : ModelCoordinates | q ∈ N ∧ Yt < Real.exp (q 1)} :=
        N.isOpen.inter (isOpen_lt continuous_const (Real.continuous_exp.comp (hc 1)))
      have hev : D.exhaustFn.{u} c =ᶠ[𝓝 p₀] fun q => q 1 :=
        Filter.eventually_of_mem (hO.mem_nhds ⟨hp₀, ha⟩) fun q hq =>
          D.exhaustFn_eq_cuspInf c hθ hσ hq.1 hq.2
      rw [hev.fderiv_eq]
      change |fderiv ℝ (coord 1) p₀ w| ≤ _
      rw [(coord 1).fderiv]
      exact (abs_one_le_sqrt_coordinateInner p₀ w).trans (le_mul_of_one_le_left (hQ _ _)
        (le_max_left _ _))
    by_cases hb : cuspZeroHeight (logPoint p₀ : ℂ) < ηb
    · have hO : IsOpen {q : ModelCoordinates | q ∈ N ∧ cuspZeroHeight (logPoint q : ℂ) < ηb} :=
        N.isOpen.inter (isOpen_lt continuous_cuspZeroHeight_logPoint continuous_const)
      set S := glOfDet invMatrix invMatrix_det
      have hS : 0 < S.det.val := glOfDet_det_pos _ _
      have hev : D.exhaustFn.{u} c =ᶠ[𝓝 p₀] fun q => coord 1 (mobiusLogMap S 0 q) :=
        Filter.eventually_of_mem (hO.mem_nhds ⟨hp₀, hb⟩) fun q hq => by
          rw [D.exhaustFn_eq_cuspZero c hθ hσ hq.1 hq.2]
          exact (mobiusLogMap_inv_one q).symm
      have hdS : DifferentiableAt ℝ (mobiusLogMap S 0) p₀ :=
        (contDiff_mobiusLogMap hS 0).differentiable (by simp) p₀
      rw [hev.fderiv_eq]
      change |fderiv ℝ (coord 1 ∘ mobiusLogMap S 0) p₀ w| ≤ _
      rw [fderiv_comp p₀ (coord 1).differentiableAt hdS, (coord 1).fderiv]
      change |(fderiv ℝ (mobiusLogMap S 0) p₀ w) 1| ≤ _
      have h := abs_one_le_sqrt_coordinateInner (mobiusLogMap S 0 p₀)
        (fderiv ℝ (mobiusLogMap S 0) p₀ w)
      rw [mobiusLogMap_coordinateInner hS 0 p₀ w w] at h
      exact h.trans (le_mul_of_one_le_left (hQ _ _) (le_max_left _ _))
    · push Not at ha hb
      have him : (logPoint p₀ : ℂ).im = Real.exp (p₀ 1) := by rw [coe_logPoint']
      have hlow := D.lowHeight_le hσ hT hb
      rw [him] at hlow
      have hmem : p₀ ∈ Kmid := by
        refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, hT.2 2⟩, ?_⟩, ?_⟩, hb⟩, h0⟩, h1⟩
        · change 0 ≤ p₀ 0
          rw [← logPoint_re_eq']
          exact hT.2 0
        · change p₀ 0 ≤ σ.width
          have := hT.2 1
          change 0 ≤ σ.width - (logPoint p₀ : ℂ).re at this
          rw [logPoint_re_eq'] at this
          linarith
        · change Real.log yL ≤ p₀ 1
          rw [← Real.log_exp (p₀ 1)]
          exact Real.log_le_log hyL hlow
        · change p₀ 1 ≤ Real.log Yt
          rw [← Real.log_exp (p₀ 1)]
          exact Real.log_le_log (Real.exp_pos _) ha
      have h1' : ‖fderiv ℝ (D.exhaustFn.{u} c) p₀‖ ≤ |B| := (hB p₀ hmem).trans (le_abs_self _)
      have h2 : |fderiv ℝ (D.exhaustFn.{u} c) p₀ w| ≤ |B| * ‖w‖ := by
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ (D.exhaustFn.{u} c) p₀).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right h1' (norm_nonneg _))
      have h3 := norm_le_mul_sqrt_coordinateInner_of_exp_le hYt.le ha w
      calc |fderiv ℝ (D.exhaustFn.{u} c) p₀ w| ≤ |B| * ‖w‖ := h2
        _ ≤ |B| * ((Yt + 1) * Real.sqrt (coordinateInner .hyperbolicProduct p₀ w w)) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = (|B| * (Yt + 1)) * Real.sqrt (coordinateInner .hyperbolicProduct p₀ w w) := by ring
        _ ≤ C * Real.sqrt (coordinateInner .hyperbolicProduct p₀ w w) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hQ _ _)
  obtain ⟨b, p₀, hT, h0, h1, hrel⟩ := D.exists_foldRel_triangle c hθ hσ hp
  obtain ⟨γ, hγ, hγp, hev⟩ := D.exhaustFn_comp_eventuallyEq c hθ hrel
  have hp₀ : p₀ ∈ N := D.mem_of_foldRel_right c hθ hrel
  have hdγ : DifferentiableAt ℝ γ p :=
    (contMDiff_iff_contDiff.1 γ.contMDiff).differentiable (by simp) p
  have hchain : fderiv ℝ (D.exhaustFn.{u} c) p v =
      fderiv ℝ (D.exhaustFn.{u} c) p₀ (fderiv ℝ γ p v) := by
    rw [← hev.fderiv_eq, fderiv_comp p (by rw [hγp]; exact hdiff p₀ hp₀) hdγ, hγp]
    rfl
  have hiso := coordinateInner_fderiv_of_pullbackMetric_eq hγ p v
  rw [hγp] at hiso
  rw [hchain, ← hiso]
  exact key p₀ hp₀ hT h0 h1.le _

def carrierExhaust (x : (descentCarrier.{u} c).pieceInterior ⊤) : ℝ :=
  D.exhaust (c.conePoint (c.descentIncl x))

theorem conePoint_descentIncl_mem (x : (descentCarrier.{u} c).pieceInterior ⊤) :
    c.conePoint (c.descentIncl x) ∈ filledBase :=
  (filledFunction_neg_iff _).1 (c.filledFunction_descentIncl x)

theorem contMDiff_carrierExhaust :
    letI := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
    ContMDiff (𝓡 3) 𝓘(ℝ) 1 (D.carrierExhaust.{u} c) := by
  let _ := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
  have h1 : ContMDiff (𝓡 3) PlaneCircleModel ∞ c.descentIncl.{u} :=
    c.isLocalDiffeomorph_descentIncl.contMDiff
  have h2 : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun x => c.conePoint (c.descentIncl.{u} x)) :=
    c.contMDiff_conePoint.comp h1
  have h3 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ D.exhaust filledBase :=
    D.contDiffOn_exhaust.contMDiffOn
  exact (h3.comp_contMDiff h2 fun x => conePoint_descentIncl_mem c x).of_le (by simp)

theorem continuous_carrierExhaust : Continuous (D.carrierExhaust.{u} c) :=
  D.contDiffOn_exhaust.continuousOn.comp_continuous
    (c.contMDiff_conePoint.continuous.comp c.continuous_descentIncl)
    fun x => conePoint_descentIncl_mem c x

theorem isProperMap_carrierExhaust : IsProperMap (D.carrierExhaust.{u} c) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨D.continuous_carrierExhaust c, fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.bddAbove
  set r := outerProfile σ.constK D.outerY₁ D.outerY₂
    (max (Real.exp (Real.log (D.outerY₂ + 1) + 1)) (Real.exp R))
  set ρ := coneProfile σ.constK
    (min (Real.exp (-(-Real.log (D.outerY₂ / 2) + 1))) (Real.exp (-R)))
  have hr : r < 3 := (D.outerProfile_props (lt_max_of_lt_left (Real.exp_pos _))).2
  have hρ : 1 / 2 < ρ := half_lt_coneProfile σ.constK_pos
    (lt_min (Real.exp_pos _) (Real.exp_pos _)).ne'
  set Kset : Set (PlaneLift.{u} × Circle) := c.filledSet ∩
    ({x | ‖c.conePoint x‖ ≤ r} ∩ {x | ρ ≤ ‖c.conePoint x + 3 / 2‖})
  have hcp : Continuous fun x : PlaneLift.{u} × Circle => c.conePoint x :=
    c.contMDiff_conePoint.continuous
  have hKset : IsCompact Kset := c.isCompact_filledSet.inter_right
    ((isClosed_le (continuous_norm.comp hcp) continuous_const).inter
      (isClosed_le continuous_const (continuous_norm.comp (hcp.add continuous_const))))
  have hsub : Kset ⊆ range c.descentIncl.{u} := by
    intro x hx
    have hb : c.conePoint x ∈ filledBase := ⟨lt_of_le_of_lt hx.2.1 hr, lt_of_lt_of_le hρ hx.2.2⟩
    exact ⟨c.toDescentInterior ((filledFunction_neg_iff _).2 hb), rfl⟩
  have hpre : IsCompact (c.descentIncl.{u} ⁻¹' Kset) := by
    rw [c.isInducing_descentIncl.isCompact_iff, image_preimage_eq_of_subset hsub]
    exact hKset
  refine hpre.of_isClosed_subset (hK.isClosed.preimage (D.continuous_carrierExhaust c))
    fun x hx => ?_
  have hxR : D.carrierExhaust c x ≤ R := hR hx
  have hu := conePoint_descentIncl_mem c x
  have ho := D.outerExhaust_nonneg ‖c.conePoint (c.descentIncl x)‖
  have hi := D.innerExhaust_nonneg ‖c.conePoint (c.descentIncl x) + 3 / 2‖
  unfold carrierExhaust exhaust at hxR
  refine ⟨(c.filledFunction_descentIncl x).le, ?_, ?_⟩
  · exact D.le_of_outerExhaust_le hu.1 (by linarith)
  · exact D.le_of_innerExhaust_le hu.2 (by linarith)

end ConeShape.FoldData

end GC.Seifert
