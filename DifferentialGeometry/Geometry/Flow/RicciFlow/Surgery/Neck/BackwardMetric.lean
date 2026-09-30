import DifferentialGeometry.Geometry.Metric.Family.CoefficientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongNeckTimeJetIdentity
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen

noncomputable section

open Bundle Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology BigOperators

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

def TerminalLimitMetric.neckMetric (L : G.TerminalLimitMetric) {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck L.metric δ k) (v : ℝ) :
    SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ) :=
  let V := N.cylindricalChart.target
  let Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V := N.cylindricalChart.chart
  scaleMetric N.scale N.scale_pos
    (Diffeomorph.pullbackMetricCross ((L.extendedMetric (s + v / N.scale)).restrictOpen V) Φ)

theorem TerminalLimitMetric.neckMetric_inner (L : G.TerminalLimitMetric) {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck L.metric δ k) (v : ℝ) (z : neckBuffer δ)
    (V W : TangentSpace NeckCylinderModel z) :
    (L.neckMetric N v).inner z V W = N.scale *
      (L.extendedMetric (s + v / N.scale)).inner (N.chart z)
        (mfderiv NeckCylinderModel ThreeModel N.chart z V)
        (mfderiv NeckCylinderModel ThreeModel N.chart z W) := by
  have hh := N.tensorPullback_apply (metricTensorField (L.extendedMetric (s + v / N.scale)))
    z ![V, W]
  have h := congrArg (fun r : ℝ => N.scale * r) hh
  simp only [metricTensorField_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

@[simp] theorem TerminalLimitMetric.neckMetric_zero (L : G.TerminalLimitMetric)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k) :
    L.neckMetric N 0 = N.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro z V W
  rw [L.neckMetric_inner, zero_div, add_zero, L.extendedMetric_terminal]
  exact (N.normalized_inner z V W).symm

theorem TerminalLimitMetric.neckMetric_inner_before (L : G.TerminalLimitMetric)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    {v : ℝ} (hv : v < 0) (z : neckBuffer δ) (V W : TangentSpace NeckCylinderModel z) :
    (L.neckMetric N v).inner z V W = N.scale *
      (G.flow.base.metric (s + v / N.scale)).inner (N.chart z).1
        (mfderiv NeckCylinderModel ThreeModel N.chart z V)
        (mfderiv NeckCylinderModel ThreeModel N.chart z W) := by
  rw [L.neckMetric_inner, L.extendedMetric_before
    (by have := div_neg_of_neg_of_pos hv N.scale_pos; linarith),
    SmoothRiemannianMetric.restrictOpen_inner]

private abbrev cylinderJet (δ : ℝ) (q : ℕ) (v : ℝ) :
    Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
  shrinkingCylinderTimeJet δ q v

private theorem background_eq_surgery_metric (δ v : ℝ) :
    strongNeckBackgroundMetric δ v =
      (shrinkingCylinderMetric ⟨min v 0, (min_le_right v 0).trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z V W
  have hs := scalarOneShrinkingCylinderMetric_inner (min v 0)
    ((min_le_right v 0).trans_lt zero_lt_one) z.1.1 z.1.2 V.1 W.1 V.2 W.2
  have hmodel := (Classical.choose_spec (exists_unique_shrinkingCylinderMetric
    (⟨min v 0, (min_le_right v 0).trans_lt zero_lt_one⟩ : Iio (1 : ℝ)))).1 z.1 V W
  have hround : (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner z.1.1 V.1 W.1 =
      inner ℝ (mfderiv (𝓡 2) ThreeModel (fun y : Sphere 2 => y.1) z.1.1 V.1)
        (mfderiv (𝓡 2) ThreeModel (fun y : Sphere 2 => y.1) z.1.1 W.1) := rfl
  apply hs.trans
  apply Eq.trans _ hmodel.symm
  rw [hround]
  unfold shrinkingCylinderInner
  have hp (A : TangentSpace NeckCylinderModel z) :
      mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => p.1.1) z.1 A =
      mfderiv (𝓡 2) ThreeModel (fun y : Sphere 2 => y.1) z.1.1 A.1 := by
    change mfderiv NeckCylinderModel ThreeModel
      ((fun y : Sphere 2 => (y.1 : ThreeSpace)) ∘ Prod.fst) z.1 A = _
    have hh := mfderiv_comp_apply z.1
      ((contMDiff_coe_sphere (E := ThreeSpace) (n := 2) (m := ∞)).mdifferentiableAt (by simp))
      mdifferentiableAt_fst (show TangentSpace NeckCylinderModel z.1 from A)
    exact hh.trans (by rw [mfderiv_fst]; rfl)
  rw [hp V, hp W, mfderiv_snd]
  rfl


theorem TerminalLimitMetric.neckMetric_timeJets
    (L : G.TerminalLimitMetric) {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (hleft : N.scale⁻¹ ≤ s - a)
    (B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2)
    (hzero : ∀ t, B 0 t = metricTensorField (L.extendedMetric t))
    (hderiv : ∀ q t, t ∈ Icc a s → ∀ y,
      HasDerivWithinAt (fun u => B q u y) (B (q + 1) t y) (Icc a s) t)
    (q : ℕ) (v : Icc (-1 : ℝ) 0) (z : neckBuffer δ) :
    ((N.scale * N.scale⁻¹ ^ q) •
        N.tensorPullback (B q (s + v.1 / N.scale)) - cylinderJet δ q v.1) z =
      iteratedDerivWithin q (fun t => metricTensorField (L.neckMetric N t) z -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) z)
          (Icc (-1 : ℝ) 0) v.1 := by
  let E := fun q u => ((N.scale * N.scale⁻¹ ^ q) •
    N.tensorPullback (B q (s + u / N.scale)) - cylinderJet δ q u) z
  have htime : MapsTo (parabolicTime s N.scale) (Icc (-1 : ℝ) 0) (Icc a s) := by
    intro u hu
    have hlo := div_le_div_of_nonneg_right hu.1 N.scale_pos.le
    simp only [neg_div, one_div] at hlo
    have hhi := div_nonpos_of_nonpos_of_nonneg hu.2 N.scale_pos.le
    constructor <;> dsimp [parabolicTime] <;> linarith
  have hE : ∀ b u, u ∈ Icc (-1 : ℝ) 0 → HasDerivWithinAt (E b) (E (b + 1) u)
      (Icc (-1 : ℝ) 0) u := by
    intro b u hu
    let basis := Module.finBasis ℝ (TangentSpace NeckCylinderModel z)
    apply tensor0S_hasDerivWithinAt_of_components basis
    intro slots
    let w := fun j => basis (slots j)
    let pushed := fun j => mfderiv NeckCylinderModel ThreeModel N.chart z (w j)
    have hA := Perelman.CanonicalNeighborhood.FiniteHorn.hasDerivWithinAt_rescaled_time_tower
      (fun b t => B b t (N.chart z) pushed) s N.scale htime
      (fun b t ht => (tensor0SEvalCLM (I := ThreeModel) pushed).hasFDerivAt.comp_hasDerivWithinAt
        t (hderiv b t ht (N.chart z))) b u hu
    have hC := shrinkingCylinderTimeJet_hasDerivWithinAt δ b hu z w
    have hsub := hA.sub hC
    have heq (b : ℕ) (u : ℝ) : E b u w =
        (N.scale * N.scale⁻¹ ^ b) * B b (parabolicTime s N.scale u) (N.chart z) pushed -
          cylinderJet δ b u z w := by
      change (N.scale * N.scale⁻¹ ^ b) *
        N.tensorPullback (B b (s + u / N.scale)) z w - cylinderJet δ b u z w = _
      rw [N.tensorPullback_apply]
      rfl
    change HasDerivWithinAt (fun s => E b s w) (E (b + 1) u w) (Icc (-1 : ℝ) 0) u
    simp_rw [heq]
    exact hsub
  have hstart : EqOn (fun t => metricTensorField (L.neckMetric N t) z -
      metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) z)
      (E 0) (Icc (-1 : ℝ) 0) := by
    intro u hu
    ext w
    change (L.neckMetric N u).inner z (w 0) (w 1) - _ = _
    rw [L.neckMetric_inner]
    change N.scale * (L.extendedMetric (s + u / N.scale)).inner (N.chart z)
      (mfderiv NeckCylinderModel ThreeModel N.chart z (w 0))
      (mfderiv NeckCylinderModel ThreeModel N.chart z (w 1)) - _ =
      (N.scale * N.scale⁻¹ ^ 0) * N.tensorPullback (B 0 (s + u / N.scale)) z w -
        cylinderJet δ 0 u z w
    rw [pow_zero, mul_one, hzero, N.tensorPullback_apply, metricTensorField_apply]
    have hbg := congrArg (fun g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ) =>
      g.inner z (w 0) (w 1)) (background_eq_surgery_metric δ u).symm
    exact congrArg (fun b : ℝ => _ - b) hbg
  exact (DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) _ E hE hstart q v.2).symm


private local instance neckC1 (δ : ℝ) : IsManifold NeckCylinderModel 1 (neckBuffer δ) :=
  IsManifold.of_le (n := ∞) (by decide)

theorem TerminalLimitMetric.neckMetric_jointContMDiffOn
    (L : G.TerminalLimitMetric) {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (hleft : N.scale⁻¹ ≤ s - a) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel)
      (NeckCylinderModel.prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
        (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] ℝ)) ∞
      (fun q : ℝ × neckBuffer δ => (⟨q.2, (L.neckMetric N q.1).inner q.2⟩ :
        TotalSpace ((EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
          (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] ℝ)
          (fun x => TangentSpace NeckCylinderModel x →L[ℝ]
            TangentSpace NeckCylinderModel x →L[ℝ] ℝ)))
      (Icc (-1 : ℝ) 0 ×ˢ univ) := by
  let g := fun v => L.extendedMetric (s + v / N.scale)
  have htime : MapsTo (fun v => s + v / N.scale) (Icc (-1 : ℝ) 0) (Icc a s) := by
    intro v hv
    have hlo := div_le_div_of_nonneg_right hv.1 N.scale_pos.le
    have hhi := div_nonpos_of_nonpos_of_nonneg hv.2 N.scale_pos.le
    simp only [neg_div, one_div] at hlo
    constructor <;> linarith
  have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × G.terminalRegularOpen => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Icc (-1 : ℝ) 0 ×ˢ univ) :=
    (L.extendedMetric_jointContMDiffOn le_rfl G.lt).comp
      ((contMDiff_const.add (contMDiff_fst.div_const N.scale)).prodMk contMDiff_snd).contMDiffOn
      (fun q hq => ⟨htime hq.1, mem_univ _⟩)
  let V := N.cylindricalChart.target
  let Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V := N.cylindricalChart.chart
  let gPull := fun v => Diffeomorph.pullbackMetricCross ((g v).restrictOpen V) Φ
  have hpull : ∀ v ∈ Icc (-1 : ℝ) 0, ∀ x (X Y : TangentSpace NeckCylinderModel x),
      (gPull v).inner x X Y = (g v).inner (N.chart x)
        (mfderiv NeckCylinderModel ThreeModel N.chart x X)
        (mfderiv NeckCylinderModel ThreeModel N.chart x Y) := by
    intro v _ x X Y
    have hh := N.tensorPullback_apply (metricTensorField (g v)) x ![X, Y]
    exact hh
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (I := NeckCylinderModel) (L.neckMetric N) (Icc (-1 : ℝ) 0)
  intro p i j
  have hp := chartGramMatrix_joint_contMDiffOn_of_parametric_pullback
    (I := ThreeModel) (J := NeckCylinderModel) g (Icc (-1 : ℝ) 0) hg
    gPull (fun _ => N.chart) (N.chart_smooth.contMDiff.comp contMDiff_snd) hpull p i j
  apply ((contMDiffOn_const (c := N.scale)).mul hp).congr
  intro q hq
  change (L.neckMetric N q.1).inner q.2
      (chartBasisVecFiber (I := NeckCylinderModel) p i q.2)
      (chartBasisVecFiber (I := NeckCylinderModel) p j q.2) =
    N.scale * (gPull q.1).inner q.2
      (chartBasisVecFiber (I := NeckCylinderModel) p i q.2)
      (chartBasisVecFiber (I := NeckCylinderModel) p j q.2)
  rfl


theorem TerminalLimitMetric.neckMetric_smooth
    (L : G.TerminalLimitMetric) {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (hleft : N.scale⁻¹ ≤ s - a) :
    ∀ p : neckBuffer δ, ∀ t ∈ Icc (-1 : ℝ) 0,
      ∃ U : Set (neckBuffer δ), IsOpen U ∧ p ∈ U ∧
        U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
          (TangentSpace NeckCylinderModel) p).baseSet ∧
        ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
          ∃ A : ℝ × neckBuffer δ → (EuclideanSpace ℝ (Fin 2) × ℝ) →
              (EuclideanSpace ℝ (Fin 2) × ℝ) → ℝ,
            (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel) 𝓘(ℝ) ∞
              (fun z => A z v w) (V ×ˢ U)) ∧
            ∀ u ∈ V ∩ Icc (-1 : ℝ) 0, ∀ x ∈ U, ∀ v w,
              A (u, x) v w = (L.neckMetric N u).inner x
                ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
                  (TangentSpace NeckCylinderModel) p).symmL ℝ x v)
                ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
                  (TangentSpace NeckCylinderModel) p).symmL ℝ x w) := by
  intro p t ht
  obtain ⟨U, hU, hp, hUb, A, hA, hEq⟩ :=
    Geometry.Metric.exists_local_metric_coefficient_extension (L.neckMetric N)
      (by norm_num : (-1 : ℝ) < 0) (L.neckMetric_jointContMDiffOn N hleft) p
  exact ⟨U, hU, hp, hUb, univ, isOpen_univ, mem_univ t, A, hA,
    fun u hu x hx v w => hEq u hu.2 x hx v w⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
