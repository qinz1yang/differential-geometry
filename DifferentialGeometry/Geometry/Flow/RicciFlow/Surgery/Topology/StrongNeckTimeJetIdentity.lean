import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalNeckMixedJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderTimeErrorJets

noncomputable section

open Bundle Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance terminalSigmaCompact : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
private local instance neckSigmaCompact (δ : ℝ) : SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel
      (neckBuffer δ).isOpen)

private theorem cylinderReference_inner_eq_background
    (C : CylinderReference) (δ v : ℝ) (hv : v ≤ 0) (z : neckBuffer δ)
    (w : Fin 2 → TangentSpace SpatialNeckCylinderModel (show spatialNeckBuffer δ from z)) :
    (C.metric v).inner z.1 (w 0) (w 1) =
      (strongNeckBackgroundMetric δ v).inner z (w 0) (w 1) := by
  have hC := C.inner_eq v hv z.1 (w 0) (w 1)
  have hS := scalarOneShrinkingCylinderMetric_inner v (hv.trans_lt zero_lt_one)
    z.1.1 z.1.2 (w 0).1 (w 1).1 (w 0).2 (w 1).2
  have hrestrict := SmoothRiemannianMetric.restrictOpen_inner
    (scalarOneShrinkingCylinderMetric v (hv.trans_lt zero_lt_one)) (spatialNeckBuffer δ)
      (show spatialNeckBuffer δ from z) (w 0) (w 1)
  have hbg := strongNeckBackgroundMetric_of_nonpos δ v hv
  rw [hbg]
  convert (hC.trans hS.symm).trans hrestrict.symm using 1

private theorem normalizedNeck_map_mfderiv_eq
    (L : G.TerminalLimitMetric) {t eps δ : ℝ} {k : ℕ}
    {x : G.terminalRegularOpen} (nk : StrongNeck G.flow eps x.1 t)
    (N : NormalizedNeck L.metric δ k) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (hmap : ∀ z : neckBuffer δ, (N.chart z).1 = nk.map z.1)
    (z : neckBuffer δ) (v : TangentSpace NeckCylinderModel z) :
    mfderiv NeckCylinderModel ThreeModel N.chart z v =
      mfderiv IC I3 nk.map z.1 v := by
  have hsource : z.1 ∈ nk.map.source := nk.domain
    ⟨mem_univ _, by have := z.2.1; linarith, z.2.2.trans_le hfit⟩
  have heq : (fun y : neckBuffer δ => (N.chart y).1) =
      fun y : neckBuffer δ => nk.map y.1 := funext hmap
  have hd := congrArg (fun f : neckBuffer δ → P.Carrier =>
    mfderiv NeckCylinderModel ThreeModel f z v) heq
  rw [DifferentialGeometry.mfderiv_subtypeVal_comp] at hd
  have hcomp := mfderiv_comp_apply z (nk.map.mdifferentiableAt (by simp) hsource)
    (DifferentialGeometry.hasMFDerivAt_subtype_val (I := IC) (neckBuffer δ) z).mdifferentiableAt v
  rw [DifferentialGeometry.mfderiv_subtype_val_apply] at hcomp
  exact hd.trans hcomp

theorem TerminalLimitMetric.strongNeck_comparison_timeJet_eq
    (L : G.TerminalLimitMetric)
    (B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2)
    (hzero : ∀ t, B 0 t = metricTensorField (L.extendedMetric t))
    (hderiv : ∀ q t, t ∈ Icc a s → ∀ y,
      HasDerivWithinAt (fun u => B q u y) (B (q + 1) t y) (Icc a s) t)
    {t eps δ : ℝ} {k : ℕ} {x : G.terminalRegularOpen}
    (nk : StrongNeck G.flow eps x.1 t) (N : NormalizedNeck L.metric δ k)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (hmap : ∀ z : neckBuffer δ, (N.chart z).1 = nk.map z.1)
    (q : ℕ) {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 0) (z : neckBuffer δ)
    (w : Fin 2 → TangentSpace SpatialNeckCylinderModel (show spatialNeckBuffer δ from z)) :
    nk.comparison.jet q v z.1 w =
      (G.flow.scalar t x.1 * (G.flow.scalar t x.1)⁻¹ ^ q) *
        B q (parabolicTime t (G.flow.scalar t x.1) v) (N.chart z)
          (fun j => mfderiv NeckCylinderModel ThreeModel N.chart z (w j)) -
        shrinkingCylinderTimeJet δ q v (show spatialNeckBuffer δ from z) w := by
  let Q := G.flow.scalar t x.1
  have hdomain : z.1 ∈ (univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨mem_univ _, by have := z.2.1; linarith, z.2.2.trans_le hfit⟩
  have htime : ∀ u ∈ Icc (-1 : ℝ) 0, parabolicTime t Q u ∈ Ico a s := by
    intro u hu
    apply nk.time_domain
    change t - Q⁻¹ ≤ t + u / Q ∧ t + u / Q ≤ t
    have hlo := div_le_div_of_nonneg_right hu.1 nk.Q_pos.le
    have hhi := div_nonpos_of_nonpos_of_nonneg hu.2 nk.Q_pos.le
    simp only [neg_div, one_div] at hlo
    constructor <;> linarith
  let slots := fun j => mfderiv NeckCylinderModel ThreeModel N.chart z (w j)
  let F := fun q u => (Q * Q⁻¹ ^ q) * B q (parabolicTime t Q u) (N.chart z) slots -
    shrinkingCylinderTimeJet δ q u (show spatialNeckBuffer δ from z) w
  apply derivWithin_tower_eq_of_genuine (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0))
    (fun q u => nk.comparison.jet q u z.1 w) F
    (fun q u hu => nk.comparison.jet_succ q u hu z.1 hdomain w) ?_ ?_ q v hv
  · intro b u hu
    have hB := hasDerivWithinAt_rescaled_time_tower
      (fun q u => B q u (N.chart z) slots) t Q
      (fun u hu => (htime u hu).imp_right le_of_lt)
      (fun q u hu => (tensor0SEvalCLM (I := ThreeModel) slots).hasFDerivAt.comp_hasDerivWithinAt
        u (hderiv q u hu (N.chart z))) b u hu
    have hC := shrinkingCylinderTimeJet_hasDerivWithinAt δ b hu z w
    exact hB.sub hC
  · intro u hu
    have h0 := nk.comparison.jet_zero u z.1 (fun i => (show TangentSpace IC z.1 from w i))
    have hp := nk.comparison.pullback_eq u z.1 hdomain
      (fun i => (show TangentSpace IC z.1 from w i))
    calc
      _ = _ := h0
      _ = _ := by
        rw [hp]
      _ = F 0 u := by
        change (Perelman.CanonicalNeighborhood.rescaledMetric G.flow t Q nk.Q_pos u).inner
          (nk.map z.1)
          (mfderiv IC I3 nk.map z.1 (w 0)) (mfderiv IC I3 nk.map z.1 (w 1)) -
          (nk.cylinder.metric u).inner z.1 (w 0) (w 1) = F 0 u
        dsimp [F]
        rw [pow_zero, mul_one, hzero, L.extendedMetric_before (htime u hu).2,
          metricTensorField_apply, SmoothRiemannianMetric.restrictOpen_inner,
          shrinkingCylinderTimeJet, ite_eq_left rfl]
        have hmodel := cylinderReference_inner_eq_background nk.cylinder δ u hu.2 z w
        change _ - _ = _ - (strongNeckBackgroundMetric δ u).inner z (w 0) (w 1)
        apply congrArg₂ (fun a b : ℝ => a - b) ?_ hmodel
        dsimp [slots]
        have hder0 := normalizedNeck_map_mfderiv_eq L nk N hfit hmap z
          (show TangentSpace NeckCylinderModel z from w 0)
        have hder1 := normalizedNeck_map_mfderiv_eq L nk N hfit hmap z
          (show TangentSpace NeckCylinderModel z from w 1)
        have hinner := congrArg₂ (fun (V W : ThreeSpace) =>
          Q * (G.flow.base.metric (parabolicTime t Q u)).inner (N.chart z).1 V W)
          hder0 hder1
        apply Eq.trans ?_ hinner.symm
        have hpos := hmap z
        have heq := congrArg (fun y : P.Carrier =>
          Q * (G.flow.base.metric (parabolicTime t Q u)).inner y
            (mfderiv IC I3 nk.map z.1 (show TangentSpace IC z.1 from w 0))
            (mfderiv IC I3 nk.map z.1 (show TangentSpace IC z.1 from w 1))) hpos
        exact heq.symm



end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev cylinderReferenceJet (δ : ℝ) (b : ℕ) (v : ℝ) :
    Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
  shrinkingCylinderTimeJet δ b v

private theorem covNorm_add_le {δ : ℝ}
    (g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (A B : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (r : ℕ) (x : neckBuffer δ) :
    tensor02CovDerivNormWith r (A + B) g g x ≤
      tensor02CovDerivNormWith r A g g x + tensor02CovDerivNormWith r B g g x := by
  simp only [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
    covDerivOfField_add, ContMDiffSection.coe_add, Pi.add_apply]
  exact _root_.DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_add_le g x (r + 2) _ _

private theorem historical_coefficient_mul {q Q : ℝ} (hq : q ≠ 0) (hQ : Q ≠ 0) (b : ℕ) :
    ((Q / q) * (Q / q)⁻¹ ^ b) * (q * q⁻¹ ^ b) = Q * Q⁻¹ ^ b := by
  simp only [inv_div, div_pow]
  field_simp
  simp only [← mul_pow, mul_one_div_cancel hq, mul_one_div_cancel hQ]

private theorem covNorm_error_decomposition {δ : ℝ}
    (g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (A T C₀ C₁ : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (d e c : ℝ) (hcoeff : d * c = e) (r : ℕ) (x : neckBuffer δ) :
    tensor02CovDerivNormWith r (e • T - C₁) g g x ≤
      |d| * tensor02CovDerivNormWith r (c • A - C₀) g g x +
      |e| * tensor02CovDerivNormWith r (T - A) g g x +
      tensor02CovDerivNormWith r (d • C₀ - C₁) g g x := by
  have heq : e • T - C₁ = d • (c • A - C₀) + e • (T - A) + (d • C₀ - C₁) := by
    rw [smul_sub, smul_smul, hcoeff, smul_sub]
    abel
  rw [heq]
  have htri := (covNorm_add_le g (d • (c • A - C₀) + e • (T - A))
    (d • C₀ - C₁) r x).trans
      (add_le_add (covNorm_add_le g (d • (c • A - C₀)) (e • (T - A)) r x) le_rfl)
  rw [tensor02CovDerivNormWith_smul g g d (c • A - C₀) r x,
    tensor02CovDerivNormWith_smul g g e (T - A) r x] at htri
  exact htri

private theorem covNorm_cylinder_time_le {δ u v : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 0) (hv : v ∈ Icc (-1 : ℝ) 0)
    (A : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (r : ℕ) (x : neckBuffer δ) :
    tensor02CovDerivNormWith r A (strongNeckBackgroundMetric δ v)
      (strongNeckBackgroundMetric δ v) x ≤
      Real.sqrt ((3 : ℝ) ^ (r + 2)) * tensor02CovDerivNormWith r A
        (strongNeckBackgroundMetric δ u) (strongNeckBackgroundMetric δ u) x := by
  have h := strongNeckBackground_backward_forward_covNorm_le δ (1 - u) v
    (by constructor <;> linarith [hu.1, hu.2]) hv A r x
  simp only [sub_sub_cancel] at h
  exact h

theorem historical_neck_error_decomposition_bound
    {δ : ℝ} (A T : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q) {u v : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 0) (hv : v ∈ Icc (-1 : ℝ) 0)
    (b r : ℕ) (x : neckBuffer δ) :
    tensor02CovDerivNormWith r
      ((Q * Q⁻¹ ^ b) • T - cylinderReferenceJet δ b v)
      (strongNeckBackgroundMetric δ v) (strongNeckBackgroundMetric δ v) x ≤
      |(Q / q) * (Q / q)⁻¹ ^ b| * Real.sqrt ((3 : ℝ) ^ (r + 2)) *
        tensor02CovDerivNormWith r
          ((q * q⁻¹ ^ b) • A - cylinderReferenceJet δ b u)
          (strongNeckBackgroundMetric δ u) (strongNeckBackgroundMetric δ u) x +
      |Q * Q⁻¹ ^ b| * Real.sqrt ((3 : ℝ) ^ (r + 2)) *
        tensor02CovDerivNormWith r (T - A)
          (strongNeckBackgroundMetric δ 0) (strongNeckBackgroundMetric δ 0) x +
      (|Q / q - 1| + 2 * |u - v|) * (3 * Real.sqrt 3) := by
  let c := Q / q
  let d := c * c⁻¹ ^ b
  let e := Q * Q⁻¹ ^ b
  let C₀ : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
    cylinderReferenceJet δ b u
  let C₁ : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
    cylinderReferenceJet δ b v
  let gV : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ) :=
    strongNeckBackgroundMetric δ v
  have htri := covNorm_error_decomposition gV A T C₀ C₁ d e (q * q⁻¹ ^ b)
    (historical_coefficient_mul hq.ne' hQ.ne' b) r x
  have hsource := covNorm_cylinder_time_le hu hv ((q * q⁻¹ ^ b) • A - C₀) r x
  have htime := covNorm_cylinder_time_le (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 0)
    hv (T - A) r x
  have hmodel := shrinkingCylinderTimeJet_scale_time_error_covNorm_le δ c u v
    (div_pos hQ hq) hu hv b r x
  have hs := mul_le_mul_of_nonneg_left hsource (abs_nonneg d)
  have ht := mul_le_mul_of_nonneg_left htime (abs_nonneg e)
  refine htri.trans ((add_le_add (add_le_add hs ht) hmodel).trans_eq ?_)
  dsimp only [d, e, c, C₀]
  exact congrArg₂ (fun a b : ℝ => a + b +
    (|Q / q - 1| + 2 * |u - v|) * (3 * Real.sqrt 3))
    (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem strongNeckBackground_zero_eq_round (δ : ℝ) :
    strongNeckBackgroundMetric δ 0 = roundCylinderMetric.restrictOpen (neckBuffer δ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x V W
  rw [strongNeckBackgroundMetric_of_nonpos δ 0 le_rfl, roundCylinderMetric_eq_geometry]
  have hS := scalarOneShrinkingCylinderMetric_inner 0 (by norm_num)
    x.1.1 x.1.2 V.1 W.1 V.2 W.2
  have hR := Geometry.Metric.roundCylinderMetric_inner x.1 V W
  change (scalarOneShrinkingCylinderMetric 0 (by norm_num)).inner x.1 V W =
    Geometry.Metric.roundCylinderMetric.inner x.1 V W
  apply hS.trans
  apply Eq.trans _ hR.symm
  have hr := Geometry.roundMetric_inner (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
    x.1.1 V.1 W.1
  simpa only [sub_zero, mul_one] using congrArg (fun t => 2 * t + V.2 * W.2) hr


private abbrev cylinderJet (δ : ℝ) (q : ℕ) (v : ℝ) :
    Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
  shrinkingCylinderTimeJet δ q v

theorem TerminalLimitMetric.strongNeck_timeJet_error_eq_restrict
    (L : G.TerminalLimitMetric)
    (B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2)
    (hzero : ∀ t, B 0 t = metricTensorField (L.extendedMetric t))
    (hderiv : ∀ q t, t ∈ Icc a s → ∀ y,
      HasDerivWithinAt (fun u => B q u y) (B (q + 1) t y) (Icc a s) t)
    {t eps δ : ℝ} {k : ℕ} {x : G.terminalRegularOpen}
    (nk : StrongNeck G.flow eps x.1 t) (N : NormalizedNeck L.metric δ k)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (hmap : ∀ z : neckBuffer δ, (N.chart z).1 = nk.map z.1)
    (q : ℕ) {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 0) :
    (G.flow.scalar t x.1 * (G.flow.scalar t x.1)⁻¹ ^ q) •
        N.tensorPullback (B q (parabolicTime t (G.flow.scalar t x.1) v)) -
        cylinderJet δ q v =
      restrictOpen0S 2 (V := neckBuffer δ) (nk.comparison.jet q v) := by
  ext z w
  change (G.flow.scalar t x.1 * (G.flow.scalar t x.1)⁻¹ ^ q) *
      N.tensorPullback (B q (parabolicTime t (G.flow.scalar t x.1) v)) z w -
      cylinderJet δ q v z w = nk.comparison.jet q v z.1 w
  rw [N.tensorPullback_apply]
  exact (L.strongNeck_comparison_timeJet_eq B hzero hderiv nk N hfit hmap q hv z w).symm

theorem TerminalLimitMetric.strongNeck_timeJet_error_bound
    (L : G.TerminalLimitMetric)
    (B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2)
    (hzero : ∀ t, B 0 t = metricTensorField (L.extendedMetric t))
    (hderiv : ∀ q t, t ∈ Icc a s → ∀ y,
      HasDerivWithinAt (fun u => B q u y) (B (q + 1) t y) (Icc a s) t)
    {t eps δ : ℝ} {k : ℕ} {x : G.terminalRegularOpen}
    (nk : StrongNeck G.flow eps x.1 t) (N : NormalizedNeck L.metric δ k)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (hmap : ∀ z : neckBuffer δ, (N.chart z).1 = nk.map z.1)
    (q r : ℕ) (horder : r + 2 * q ≤ ⌈eps⁻¹⌉₊)
    {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 0) (z : neckBuffer δ) :
    tensor02CovDerivNormWith r
      ((G.flow.scalar t x.1 * (G.flow.scalar t x.1)⁻¹ ^ q) •
        N.tensorPullback (B q (parabolicTime t (G.flow.scalar t x.1) v)) -
        cylinderJet δ q v)
      (strongNeckBackgroundMetric δ v) (strongNeckBackgroundMetric δ v) z ≤ eps := by
  have heq := L.strongNeck_timeJet_error_eq_restrict B hzero hderiv nk N hfit hmap q hv
  rw [heq]
  have hmodel : (nk.cylinder.metric v).restrictOpen (neckBuffer δ) =
      strongNeckBackgroundMetric δ v := by
    apply SmoothRiemannianMetric.ext_inner
    intro y V W
    have hC := nk.cylinder.inner_eq v hv.2 y.1 V W
    have hS := scalarOneShrinkingCylinderMetric_inner v (hv.2.trans_lt zero_lt_one)
      y.1.1 y.1.2 V.1 W.1 V.2 W.2
    have hmetric := strongNeckBackgroundMetric_of_nonpos δ v hv.2
    rw [hmetric]
    exact hC.trans hS.symm
  have hnorm := tensor02CovDerivNormWith_restrictOpen0S (neckBuffer δ)
    (nk.cylinder.metric v) (nk.cylinder.metric v) (nk.comparison.jet q v) r z
  rw [hmodel] at hnorm
  apply hnorm.trans_le
  exact nk.comparison.close r q horder v hv z.1
    ⟨mem_univ _, by have := z.2.1; linarith, z.2.2.trans_le hfit⟩


private theorem abs_clip_sub_le {u v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 0) :
    |max (-1) (min u 0) - v| ≤ |u - v| := by
  by_cases hl : u ≤ -1
  · rw [min_eq_left (by linarith), max_eq_left hl,
      abs_of_nonpos (by linarith [hv.1] : -1 - v ≤ 0)]
    have hh := neg_le_abs (u - v)
    linarith
  · by_cases hu : 0 ≤ u
    · rw [min_eq_right hu, max_eq_right (by norm_num), zero_sub, abs_neg,
        abs_of_nonpos hv.2]
      have hh := le_abs_self (u - v)
      linarith
    · rw [min_eq_left (le_of_not_ge hu), max_eq_right (le_of_not_ge hl)]

theorem TerminalLimitMetric.exists_historical_neck_error_bound
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : δ < 1 / 4) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (nk : ∀ n, StrongNeck G.flow eps x.1 (τ n))
    (N : ℕ → NormalizedNeck L.metric δ k) (hcenter : ∀ n, (N n).center = x)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (hmap : ∀ n, ∀ z : neckBuffer δ, ((N n).chart z).1 = (nk n).map z.1)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in atTop, ∀ z ∈ neckClosedTest δ, (N n).chart z ∈ K)
    (hbudget : 2 * Real.sqrt ((3 : ℝ) ^ (k + 2)) * eps < δ) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2,
      (∀ t, B 0 t = metricTensorField (L.extendedMetric t)) ∧
      (∀ q t, t ∈ Icc a s → ∀ y,
        B q t y = iteratedDerivWithin q
          (fun u => metricTensorField (L.extendedMetric u) y) (Icc a s) t ∧
        HasDerivWithinAt (fun u => B q u y) (B (q + 1) t y) (Icc a s) t) ∧
      ∃ η : ℝ, η < δ ∧ ∀ᶠ n in atTop, ∀ r q : ℕ, r + 2 * q ≤ k →
        ∀ v ∈ Icc (-1 : ℝ) 0, ∀ z ∈ neckClosedTest δ,
          tensor02CovDerivNormWith r
            ((metricScalarAt L.metric x * (metricScalarAt L.metric x)⁻¹ ^ q) •
              (N n).tensorPullback (B q (s + v / metricScalarAt L.metric x)) -
              cylinderJet δ q v)
            (strongNeckBackgroundMetric δ v) (strongNeckBackgroundMetric δ v) z ≤ η := by
  classical
  obtain ⟨B, hzero, hB, hconv⟩ :=
    L.exists_time_fields_clipped_neck_pullback_convergence_of_strongNecks
      hτ x hx nk hδ k N hcenter hK hcapture
  let Q := metricScalarAt L.metric x
  let qn := fun n => G.flow.scalar (τ n) x.1
  have hqn : ∀ n, 0 < qn n := fun n => (nk n).Q_pos
  have hlim : Tendsto qn atTop (𝓝 Q) := (L.tendsto_metricScalarAt x).comp hτ
  have hτ' := hτ.mono_right nhdsWithin_le_nhds
  let F := Real.sqrt ((3 : ℝ) ^ (k + 2))
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  let η := (δ + 2 * F * eps) / 2
  let ζ := η - 2 * F * eps
  have hζ : 0 < ζ := by dsimp [ζ, η, F]; linarith
  have hη : η < δ := by dsimp [η, F]; linarith
  refine ⟨B, hzero, hB, η, hη, ?_⟩
  have heps : 0 ≤ eps := (nk 0).eps_pos.le
  let E := fun n => |qn n / Q - 1| + |qn n| * |s - τ n|
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [mul_one] using Real.tendsto_rescale_time_error_bound hlim hτ' hx.ne' 1
  have hratio : Tendsto (fun n => Q / qn n) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := Q)).div hlim hx.ne'
    change Tendsto (fun n => Q / qn n) atTop (𝓝 (Q / Q)) at ht
    have hQne : Q ≠ 0 := hx.ne'
    rw [div_self hQne] at ht
    exact ht
  have hmodel : ∀ᶠ n in atTop,
      (|Q / qn n - 1| + 2 * E n) * (3 * Real.sqrt 3) < ζ / 4 := by
    have ht := ((hratio.sub_const 1).abs.add (hE.const_mul 2)).mul_const (3 * Real.sqrt 3)
    have ht0 : Tendsto (fun n => (|Q / qn n - 1| + 2 * E n) * (3 * Real.sqrt 3))
        atTop (𝓝 0) := by simpa only [sub_self, abs_zero, mul_zero, add_zero, zero_mul] using ht
    exact ht0.eventually_lt_const (by positivity)
  have hfinite (q : Fin (k + 1)) : ∀ᶠ n in atTop, ∀ r : ℕ, r + 2 * q ≤ k →
      ∀ v ∈ Icc (-1 : ℝ) 0, ∀ z ∈ neckClosedTest δ,
        tensor02CovDerivNormWith r
          ((Q * Q⁻¹ ^ (q : ℕ)) • (N n).tensorPullback (B q (s + v / Q)) -
            cylinderJet δ q v)
          (strongNeckBackgroundMetric δ v) (strongNeckBackgroundMetric δ v) z ≤ η := by
    let e := |Q * Q⁻¹ ^ (q : ℕ)|
    let α := ζ / (4 * (e + 1) * (F + 1))
    have hα : 0 < α := by dsimp [α, e]; positivity
    have hweights : ∀ᶠ n in atTop, |(Q / qn n) * (Q / qn n)⁻¹ ^ (q : ℕ)| ≤ 2 := by
      have ht := (hratio.mul ((hratio.inv₀ one_ne_zero).pow (q : ℕ))).abs
      have ht1 : Tendsto (fun n => |(Q / qn n) * (Q / qn n)⁻¹ ^ (q : ℕ)|)
          atTop (𝓝 1) := by simpa only [inv_one, one_pow, one_mul, abs_one] using ht
      exact (ht1.eventually_lt_const (by norm_num : (1 : ℝ) < 2)).mono fun _ h => h.le
    filter_upwards [hconv q α hα, hweights, hmodel] with n hn hw hm
    intro r hr v hv z hz
    let u := max (-1 : ℝ) (min (qn n * (s + v / Q - τ n)) 0)
    have hu : u ∈ Icc (-1 : ℝ) 0 :=
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
    let A := (N n).tensorPullback (B q (parabolicTime (τ n) (qn n) u))
    let T := (N n).tensorPullback (B q (s + v / Q))
    have hsource := L.strongNeck_timeJet_error_bound B hzero
      (fun q t ht y => (hB q t ht y).2) (nk n) (N n) hfit (hmap n)
      q r (hr.trans hk) hu z
    have hclip : tensor02CovDerivNormWith r (T - A)
        (strongNeckBackgroundMetric δ 0) (strongNeckBackgroundMetric δ 0) z < α := by
      have hh := hn v hv r (by omega) z hz
      have htime : parabolicTime (τ n) (qn n) u =
          Real.clippedAffineTime s (τ n) (qn n) Q v := rfl
      have heq : T - A = -((N n).tensorPullback
          (B q (Real.clippedAffineTime s (τ n) (qn n) Q v) - B q (s + v / Q))) := by
        rw [(N n).tensorPullback_sub]
        dsimp [T, A]
        rw [htime]
        abel
      rw [heq]
      have hneg : tensor02CovDerivNormWith r
          (-((N n).tensorPullback
            (B q (Real.clippedAffineTime s (τ n) (qn n) Q v) - B q (s + v / Q))))
          (strongNeckBackgroundMetric δ 0) (strongNeckBackgroundMetric δ 0) z =
          tensor02CovDerivNormWith r
            ((N n).tensorPullback
              (B q (Real.clippedAffineTime s (τ n) (qn n) Q v) - B q (s + v / Q)))
            (strongNeckBackgroundMetric δ 0) (strongNeckBackgroundMetric δ 0) z := by
        let g0 : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ) :=
          strongNeckBackgroundMetric δ 0
        have hs := tensor02CovDerivNormWith_smul g0 g0 (-1 : ℝ)
          ((N n).tensorPullback
            (B q (Real.clippedAffineTime s (τ n) (qn n) Q v) - B q (s + v / Q))) r z
        simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using hs
      rw [hneg, strongNeckBackground_zero_eq_round]
      exact hh
    have huv : |u - v| ≤ E n := by
      have hb := Real.abs_rescale_time_sub_le (q := qn n) (Q := Q) (s := s) (τ := τ n)
        (show |v| ≤ 1 from abs_le.mpr ⟨hv.1, by linarith [hv.2]⟩)
      exact (abs_clip_sub_le hv).trans (by simpa only [mul_one] using hb)
    have hfac : Real.sqrt ((3 : ℝ) ^ (r + 2)) ≤ F :=
      Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (by omega))
    have herror := historical_neck_error_decomposition_bound A T (hqn n) hx hu hv q r z
    have hs : |Q / qn n * (Q / qn n)⁻¹ ^ (q : ℕ)| *
        Real.sqrt ((3 : ℝ) ^ (r + 2)) *
        tensor02CovDerivNormWith r ((qn n * (qn n)⁻¹ ^ (q : ℕ)) • A - cylinderJet δ q u)
          (strongNeckBackgroundMetric δ u) (strongNeckBackgroundMetric δ u) z ≤
        2 * F * eps :=
      mul_le_mul (mul_le_mul hw hfac (Real.sqrt_nonneg _) (by norm_num)) hsource
        (Real.sqrt_nonneg _) (by positivity)
    have ht : e * Real.sqrt ((3 : ℝ) ^ (r + 2)) *
        tensor02CovDerivNormWith r (T - A)
          (strongNeckBackgroundMetric δ 0) (strongNeckBackgroundMetric δ 0) z ≤ ζ / 4 := by
      have hprod := mul_le_mul
        (mul_le_mul_of_nonneg_left hfac (abs_nonneg _)) hclip.le
        (Real.sqrt_nonneg _) (by positivity : 0 ≤ e * F)
      have hsmall : e * F * α ≤ ζ / 4 := by
        dsimp [α]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by dsimp [e]; positivity)).mpr
        have he : 0 ≤ e := abs_nonneg _
        nlinarith [mul_nonneg he hF]
      exact hprod.trans hsmall
    have hm' : (|Q / qn n - 1| + 2 * |u - v|) * (3 * Real.sqrt 3) < ζ / 4 :=
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans_lt hm
    exact herror.trans (by change _ ≤ η; dsimp only [ζ] at ht hm'; linarith)
  have hall := eventually_all.mpr hfinite
  filter_upwards [hall] with n hn
  intro r q hr
  exact hn ⟨q, by omega⟩ r hr

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
