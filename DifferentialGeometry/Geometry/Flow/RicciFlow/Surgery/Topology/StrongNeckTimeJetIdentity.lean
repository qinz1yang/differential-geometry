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
          shrinkingCylinderTimeJet, if_pos rfl]
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
