import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryProducerBase_S51
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryAssembleReal_S39
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryNaturalityFull
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterCurvatureBridge_S41
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationLevelDiam
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores

set_option autoImplicit false

/-!
# CH12-S62 G2: `herr` and `hdiam` of the stage-level collar `φ`

* `phi_err_S62`: the `C^K'` cusp-metric error (against the hyperbolic cusp of the level-`S`
  truncation) of the collar `φ`, measured in the induced (restricted) component metric of the
  normalized stage metric, is `< accuracy t`'s bound `B.accuracy t`; from `buffer_error`
  (`cuspMetricErrorBound_of_H_C4`) and the restriction transfer `cuspMetricErrorBound_transfer_S34`
  (`Subtype.val`).  Only the pulled-back (induced) metric is used.
* `truncCusp_diam_S62`: the reference torus of every level-`S` cusp has diameter
  `≤ e^{-S/2} D_max`, with `D_max` depending on `base` only.
-/

noncomputable section

open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Geometry.Curvature GC.Endpoint
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff

universe u

namespace GC.LongTime.Ch12

/-- The compact carrier of a closed oriented 3-manifold (data only; `NoCuts.carrier` without
connectedness). -/
abbrev stageCarrier_S62 (Q : ClosedOrientedManifold.{u} 3) : CompactCarrier.{u} where
  kind := .closed
  Carrier := Q.Carrier
  charts := inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q.Carrier)
  smooth := inferInstanceAs (IsManifold (𝓡 3) ∞ Q.Carrier)
  secondCountable := ChartedSpace.secondCountable_of_sigmaCompact
    (EuclideanSpace ℝ (Fin 3)) Q.Carrier
  orientation := Q.orientation

section Err

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **G2 (herr).**  The cusp-metric error of the collar `φ` of the seam index `x`, in the
restriction to the component `C` of the normalized stage metric, is bounded by `B.accuracy t`. -/
theorem phi_err_S62 (B : BufferedPersistentCores F K) {t : ℝ} (ht : B.start ≤ t)
    (D : TruncatedCutData_IF4 B.toCores t)
    (hball : ∀ i (q : Fin (D.base i).count) (p : CuspHalfSpace), p.2.val 0 ≤ D.level + 200 →
      (D.base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
        (2 * (B.accuracy t)⁻¹))
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (x : CIdx_S19 D ht C) (φ : CuspHalfSpace → (sliceM_S28 C).Carrier)
    (hφ : ∀ p ∈ cuspDomain, (φ p).val =
      B.toCores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 p))
    (hsm : ContMDiffOn halfCollarModel (𝓡 3) ∞ φ cuspDomain) :
    cuspMetricErrorBound (W := NoCuts.carrier (sliceM_S28 C))
      ((scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)).restrictOpen
        ((postStage F.observation t).toClosedOrientedManifold.componentOpen C))
      K (B.accuracy t) ((D.truncation x.1.1).cusp x.1.2) φ := by
  set gs := scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t) with hgs
  set W := stageCarrier_S62 (postStage F.observation t).toClosedOrientedManifold with hW
  have hrange : ∀ p ∈ cuspDomain, (D.truncation x.1.1).cuspMap x.1.2 p ∈ B.toCores.domain x.1.1 t :=
    fun p hp => stageCusp_mem_domain_S51 D x.1 hp
  have hf : ContMDiffOn (𝓡 3) W.model ∞ (B.toCores.map x.1.1 t ht) (B.toCores.domain x.1.1 t) :=
    B.toCores.smooth x.1.1 t ht
  have himm' : ∀ y : (B.model x.1.1).Carrier, y ∈ B.toCores.domain x.1.1 t →
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (B.toCores.map x.1.1 t ht) y) := by
    intro y hy
    exact ((isLocalDiffeomorphAt_map_S28 ht x.1.1 hy).mfderivToContinuousLinearEquiv (by simp)).injective
  have himm : ∀ y : (B.model x.1.1).Carrier, y ∈ B.toCores.domain x.1.1 t →
      Function.Injective (mfderiv (𝓡 3) W.model (B.toCores.map x.1.1 t ht) y) := himm'
  have e : rawPullbackError_C4 gs (B.model x.1.1).metric (B.toCores.map x.1.1 t ht) =
      fun y : (B.model x.1.1).Carrier => ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) y) ℝ).symm.toContinuousLinearMap.comp
        ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (B.toCores.map x.1.1 t ht) y -
          (B.model x.1.1).metric.inner y)).uncurryLeft := by
    funext y
    unfold rawPullbackError_C4
    have hl : localPullInner (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
        (postMetric F.observation t)) (B.toCores.map x.1.1 t ht) y =
        t⁻¹ • localPullInner (postMetric F.observation t) (B.toCores.map x.1.1 t ht) y :=
      localPullInner_scaleMetric_S41 _ _ _ _ _
    rw [hgs]
    erw [hl]
    rfl
  have herr : ∀ k : ℕ, k ≤ K → ∀ p ∈ cuspDomain,
      tensor0SFiberNorm (B.model x.1.1).metric ((D.truncation x.1.1).cuspMap x.1.2 p) (2 + k)
        (iteratedMetricCovariantDerivative (B.model x.1.1).metric 2
          (rawPullbackError_C4 gs (B.model x.1.1).metric (B.toCores.map x.1.1 t ht)) k
          ((D.truncation x.1.1).cuspMap x.1.2 p)) ≤ B.accuracy t := by
    intro k hk p hp
    have hp100 : p.2.val 0 < 100 := hp
    have h0 : 0 ≤ p.2.val 0 + D.level := by linarith [p.2.2, D.two_le]
    have hb : (D.truncation x.1.1).cuspMap x.1.2 p ∈ riemannianBallOf (B.model x.1.1).metric
        (B.model x.1.1).basepoint (2 * (B.accuracy t)⁻¹) :=
      hball x.1.1 x.1.2 (p.1, halfSpaceOneLift (p.2.val 0 + D.level)) (by
        rw [GC.LongTime.CuspP1.lift_height_CPA2 h0]; linarith)
    have hbe := B.buffer_error x.1.1 t ht k (hk.trans (le_max_left _ _)) _ hb
    rw [e]
    exact hbe.le
  have hstage : cuspMetricErrorBound (W := W) gs K (B.accuracy t) ((D.truncation x.1.1).cusp x.1.2)
      (B.toCores.map x.1.1 t ht ∘ (D.truncation x.1.1).cuspMap x.1.2) :=
    cuspMetricErrorBound_of_H_C4 (W := W) (D.truncation x.1.1) x.1.2 gs K (B.accuracy t)
      (B.toCores.map x.1.1 t ht) (B.toCores.domain x.1.1 t) hrange hf himm herr
  refine cuspMetricErrorBound_transfer_S34 (W₀ := stageCarrier_S62 (postStage F.observation t).toClosedOrientedManifold)
    (P := NoCuts.carrier (sliceM_S28 C)) gs Subtype.val ?_ _ ?_ K (B.accuracy t)
    ((D.truncation x.1.1).cusp x.1.2) φ _ hsm (fun p hp => hφ p hp) hstage
  · exact contMDiff_subtype_val
  · intro y v w
    have hv := mfderiv_subtype_val_apply (I := 𝓡 3)
      ((postStage F.observation t).toClosedOrientedManifold.componentOpen C) y v
    have hw := mfderiv_subtype_val_apply (I := 𝓡 3)
      ((postStage F.observation t).toClosedOrientedManifold.componentOpen C) y w
    exact congrArg₂ (fun a b => gs.inner y.val a b) hv.symm hw.symm

end Err

section Diam

/-- The reference tori of all level-`S` cusps have diameter `≤ e^{-S/2} D_max`, `D_max` depending
only on `base`. -/
theorem exists_torus_diam_S62 {n : ℕ} {H : Fin n → FiniteVolumeHyperbolicModel.{u}}
    (base : ∀ i, HyperbolicTruncation (H i)) :
    ∃ Dm : ℝ, 0 ≤ Dm ∧ ∀ (S : ℝ) (hS : 2 ≤ S) (i : Fin n) (q : Fin (base i).count) (x y : Torus),
      riemannianEDistOf ((truncationAtLevel_C1 (base i) hS).cusp q).torusMetric x y ≤
        ENNReal.ofReal (Real.exp (-S / 2) * Dm) := by
  classical
  have hc : ∀ a : (Σ i : Fin n, Fin (base i).count), ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : Torus,
      riemannianEDistOf ((base a.1).cusp a.2).torusMetric x y ≤ ENNReal.ofReal D := by
    intro a
    obtain ⟨D, hD0, hD⟩ := exists_connecting_path_bound_C1 ((base a.1).cusp a.2)
    refine ⟨D, hD0, fun x y => ?_⟩
    obtain ⟨c, hc, h0, h1, hs⟩ := hD x y
    have h := riemannianEDistOf_le_of_curve_speed_bound ((base a.1).cusp a.2).torusMetric
      (γ := c) (a := 0) (b := 1) (C := D) zero_le_one
      ((hc.of_le (by exact_mod_cast le_top)).contMDiffOn)
      (fun s _ => Real.sqrt_le_iff.mpr ⟨hD0, hs s⟩)
    rw [h0, h1] at h
    simpa using h
  choose D hD0 hD using hc
  refine ⟨∑ a, D a, Finset.sum_nonneg (fun a _ => hD0 a), fun S hS i q x y => ?_⟩
  have h1 := deepTorus_edist_C4 ((base i).cusp q) S (D ⟨i, q⟩) (hD ⟨i, q⟩) x y
  exact h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := D) (fun a _ => hD0 a) (Finset.mem_univ (⟨i, q⟩ : Σ i : Fin n, Fin (base i).count)))
    (Real.exp_pos _).le))

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **G2 (hdiam).**  For truncation data over `base`, the cusp reference tori have diameter
`≤ e^{-level/2} D_max` (`D_max` depends on `base` only, not on `t`, the level or `j`). -/
theorem truncCusp_diam_S62 (cores : PersistentHyperbolicCores F K)
    (base : ∀ i : Fin cores.count, HyperbolicTruncation (cores.model i)) :
    ∃ Dm : ℝ, 0 ≤ Dm ∧ ∀ (t : ℝ) (D : TruncatedCutData_IF4 cores t), D.base = base →
      ∀ (c : Fin cores.count) (q : Fin (D.base c).count) (x y : Torus),
        riemannianEDistOf ((D.truncation c).cusp q).torusMetric x y ≤
          ENNReal.ofReal (Real.exp (-D.level / 2) * Dm) := by
  obtain ⟨Dm, hDm, h⟩ := exists_torus_diam_S62 base
  refine ⟨Dm, hDm, fun t D hD c q x y => ?_⟩
  subst hD
  exact h D.level D.two_le c q x y

end Diam

end GC.LongTime.Ch12
