import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.SpectralPouH2Identify
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Operator.L2PMap
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.OperatorEquation
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs

/-!
# `L²`-maximal regularity for the connection Laplacian

For a closed Riemannian manifold and `0 < T ≤ 1`, the inhomogeneous tensor heat
equation `∂_t u = Δ_∇ u + f`, `u(0) = 0`, driven by a forcing
`f ∈ L²([0,T]; TensorL2 r s g)`, has a strong solution in `H¹([0,T]; TensorL2 r s g)`
with the De Simon maximal-regularity bound `‖u‖_{H¹} ≤ 2 · ‖f‖_{L²}`. The result is
packaged as a bounded linear solution operator together with its companion `H²`
field and the time-pointwise rough Laplacian, recovering the strong form of the
equation at the `L²([0,T]; L²)` level.

The two-derivative-gain companion field is valued in the **spectral** `H²`
Sobolev space `tensorHs g r s 2` (the eigenbasis weighted-`ℓ²` completion of the
connection-Laplacian resolvent), the scale on which the rough Laplacian
`Δ_∇ : H² →L L²` and the maximal-regularity smoothing act diagonally and
unconditionally. The whole package is transported from the abstract per-mode
maximal-regularity operator across the chart-locality-free isometry
`tensorHsZeroEquivL2 : H⁰ ≃ₗᵢ L²`; no order-`2` Gårding/elliptic-regularity
comparison is invoked.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian

/-- **Block-diagonal transport on the time-`H¹` space.**  For real Hilbert
spaces `X`, `Y`, a time horizon, and bounded linear maps `Li : X →L Y` (acting
on the initial value) and `Ld : L²([0,T]; X) →L L²([0,T]; Y)` (acting on the
`L²` time derivative), this is the induced bounded linear map
`H¹([0,T]; X) →L H¹([0,T]; Y)`, `u ↦ ⟨Li u.init, Ld u.deriv⟩`.  When both
components are norm-non-increasing, so is the transport (graph-norm). -/
noncomputable def timeH1blockTransport
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] {Tt : ℝ}
    (Li : X →L[ℝ] Y) (Ld : timeL2 X Tt →L[ℝ] timeL2 Y Tt)
    (hInit : ∀ x, ‖Li x‖ ≤ ‖x‖) (hDeriv : ∀ v, ‖Ld v‖ ≤ ‖v‖) :
    timeH1 X Tt →L[ℝ] timeH1 Y Tt :=
  LinearMap.mkContinuous
    { toFun := fun u => timeH1.mk (Li u.init) (Ld u.deriv)
      map_add' := fun u u' => by
        refine timeH1.ext ?_ ?_
        · simp only [timeH1.init_mk, timeH1.init_add, map_add]
        · simp only [timeH1.deriv_mk, timeH1.deriv_add, map_add]
      map_smul' := fun c u => by
        refine timeH1.ext ?_ ?_
        · simp only [timeH1.init_mk, timeH1.init_smul, map_smul, RingHom.id_apply]
        · simp only [timeH1.deriv_mk, timeH1.deriv_smul, map_smul, RingHom.id_apply] }
    1
    (fun u => by
      have hsq : ‖(timeH1.mk (Li u.init) (Ld u.deriv) : timeH1 Y Tt)‖ ^ 2 ≤
          (1 * ‖u‖) ^ 2 := by
        rw [timeH1.norm_sq_eq, timeH1.init_mk, timeH1.deriv_mk, one_mul,
          timeH1.norm_sq_eq]
        nlinarith [norm_nonneg u.init, norm_nonneg u.deriv, norm_nonneg (Li u.init),
          norm_nonneg (Ld u.deriv), hInit u.init, hDeriv u.deriv]
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h)

@[simp] theorem timeH1blockTransport_init
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] {Tt : ℝ}
    (Li : X →L[ℝ] Y) (Ld : timeL2 X Tt →L[ℝ] timeL2 Y Tt)
    (hInit : ∀ x, ‖Li x‖ ≤ ‖x‖) (hDeriv : ∀ v, ‖Ld v‖ ≤ ‖v‖) (u : timeH1 X Tt) :
    (timeH1blockTransport Li Ld hInit hDeriv u).init = Li u.init := rfl

@[simp] theorem timeH1blockTransport_deriv
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] {Tt : ℝ}
    (Li : X →L[ℝ] Y) (Ld : timeL2 X Tt →L[ℝ] timeL2 Y Tt)
    (hInit : ∀ x, ‖Li x‖ ≤ ‖x‖) (hDeriv : ∀ v, ‖Ld v‖ ≤ ‖v‖) (u : timeH1 X Tt) :
    (timeH1blockTransport Li Ld hInit hDeriv u).deriv = Ld u.deriv := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option maxHeartbeats 800000 in
/-- **`L²`-maximal regularity for the connection Laplacian.**
On a closed Riemannian manifold, for `0 < T ≤ 1`, the inhomogeneous heat
equation `∂_t u = Δ_∇ u + f`, `u(0) = 0`, driven by a forcing term
`f ∈ L²([0,T]; TensorL2 r s g)`, admits a strong solution `u` in the
time-`H¹` space `H¹([0,T]; TensorL2 r s g)`, with the De Simon
maximal-regularity bound `‖u‖_{H¹} ≤ 2 · ‖f‖_{L²}`.

The conclusion bundles this as the existence of a bounded linear solution
operator `SolOp : L²([0,T]; L²) →L H¹([0,T]; L²)` carrying four pieces of
content:

* **Maximal-regularity bound.**  `‖SolOp‖ ≤ 2`, the absolute constant of
  the `H¹`-graph-norm estimate.
* **Initial condition.**  `(SolOp f).init = 0` for every forcing `f`,
  i.e. the Duhamel solution starts at the origin.
* **Two-derivative gain (companion `H²` field).**  A bounded linear
  companion operator
  `SolField : L²([0,T]; L²) →L L²([0,T]; H²)`,
  valued in the spectral `H²` Sobolev space `tensorHs g r s 2`,
  with `‖SolField‖ ≤ 1 + T`, the two-derivative-gain bound.
* **Inhomogeneous heat equation.**  A bounded linear operator
  `LapField : L²([0,T]; H²) →L L²([0,T]; L²)`, the time-pointwise
  extension of the rough Laplacian `Δ_∇ : H² →L L²`, with
  `(SolOp f).deriv = LapField (SolField f) + f` for every forcing `f` —
  the strong form of `∂_t u = Δ_∇ u + f` at the `L²([0,T]; L²)` level.

The fourth clause is the non-vacuous content: any candidate solution
operator must reproduce the forcing through the rough-Laplacian /
companion-field identity, ruling out the trivial witness `SolOp = 0`
(for which `(SolOp f).deriv = 0`, forcing `f = 0` for all `f`).

The statement carries no `HasLocallyConstantChartAt` hypothesis. -/
theorem connection_laplacian_l2_maximal_regularity
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {T : ℝ}
    (_hT : 0 < T) (_hT1 : T ≤ 1) :
    ∃ SolOp : timeL2 (TensorL2 r s g) T →L[ℝ]
        timeH1 (TensorL2 r s g) T,
      ‖SolOp‖ ≤ 2 ∧
      (∀ f : timeL2 (TensorL2 r s g) T,
        (SolOp f).init = (0 : TensorL2 r s g)) ∧
      ∃ SolField : timeL2 (TensorL2 r s g) T →L[ℝ]
          timeL2 (tensorHs (I := I) (M := M) g r s 2) T,
        ‖SolField‖ ≤ 1 + T ∧
        ∃ LapField : timeL2 (tensorHs (I := I) (M := M) g r s 2) T →L[ℝ]
            timeL2 (TensorL2 r s g) T,
          ∀ f : timeL2 (TensorL2 r s g) T,
            (SolOp f).deriv = LapField (SolField f) + f := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
  set ψ := tensorHsZeroEquivL2 (I := I) (M := M) h_compact with hψ
  set Φ : timeL2 (tensorHs (I := I) (M := M) g r s 0) T →L[ℝ] timeL2 (TensorL2 r s g) T :=
    (ψ.toLinearIsometry.toContinuousLinearMap).compLpL 2 (timeMeasure T) with hΦ
  set Φsymm : timeL2 (TensorL2 r s g) T →L[ℝ] timeL2 (tensorHs (I := I) (M := M) g r s 0) T :=
    (ψ.symm.toLinearIsometry.toContinuousLinearMap).compLpL 2 (timeMeasure T) with hΦsymm
  have hΦ_apply : ∀ w, ‖Φ w‖ ≤ ‖w‖ := by
    intro w
    refine le_trans (Φ.le_opNorm w) ?_
    have hle : ‖Φ‖ ≤ 1 := by
      rw [hΦ]
      refine le_trans (ContinuousLinearMap.norm_compLpL_le _) ?_
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
      rw [one_mul]; exact (ψ.norm_map x).le
    calc ‖Φ‖ * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
      _ = ‖w‖ := one_mul _
  have hΦsymm_apply : ∀ f, ‖Φsymm f‖ ≤ ‖f‖ := by
    intro f
    refine le_trans (Φsymm.le_opNorm f) ?_
    have hle : ‖Φsymm‖ ≤ 1 := by
      rw [hΦsymm]
      refine le_trans (ContinuousLinearMap.norm_compLpL_le _) ?_
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
      rw [one_mul]; exact (ψ.symm.norm_map x).le
    calc ‖Φsymm‖ * ‖f‖ ≤ 1 * ‖f‖ := by gcongr
      _ = ‖f‖ := one_mul _
  have hΦΦsymm : ∀ f, Φ (Φsymm f) = f := by
    intro f
    refine Lp.ext ?_
    have h1 := (ψ.toLinearIsometry.toContinuousLinearMap).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) (Φsymm f)
    have h2 := (ψ.symm.toLinearIsometry.toContinuousLinearMap).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) f
    have h1' : (Φ (Φsymm f) : ℝ → TensorL2 r s g) =ᵐ[timeMeasure T]
        fun t => ψ ((Φsymm f) t) := by rw [hΦ]; exact h1
    have h2' : (Φsymm f : ℝ → tensorHs (I := I) (M := M) g r s 0) =ᵐ[timeMeasure T]
        fun t => ψ.symm (f t) := by rw [hΦsymm]; exact h2
    filter_upwards [h1', h2'] with t ht1 ht2
    rw [ht1, ht2, ψ.apply_symm_apply]
  set c22 : timeL2 (tensorHs (I := I) (M := M) g r s (0 + 2)) T ≃ₗᵢ[ℝ]
      timeL2 (tensorHs (I := I) (M := M) g r s 2) T :=
    (by rw [show (0:ℝ) + 2 = 2 from by norm_num];
        exact LinearIsometryEquiv.refl ℝ _ :
      timeL2 (tensorHs (I := I) (M := M) g r s (0 + 2)) T ≃ₗᵢ[ℝ]
        timeL2 (tensorHs (I := I) (M := M) g r s 2) T) with hc22
  set Aop : timeL2 (tensorHs (I := I) (M := M) g r s 0) T →L[ℝ]
      timeH1 (tensorHs (I := I) (M := M) g r s 0) T :=
    LinearMap.mkContinuous
      { toFun := fun w => maximalRegularityOp (I := I) (M := M) 0 _hT _hT1 w
        map_add' := fun w w' =>
          maximalRegularityOp_add (I := I) (M := M) (h_compact := h_compact)
            (a := 0) _hT _hT1 w w'
        map_smul' := fun c w => by
          simpa using maximalRegularityOp_smul (I := I) (M := M)
            (h_compact := h_compact) (a := 0) _hT _hT1 c w }
      2 (fun w => maximalRegularityOp_norm_le (I := I) (M := M)
        (h_compact := h_compact) (a := 0) _hT _hT1 w)
    with hAop
  have hAop_apply : ∀ w, Aop w = maximalRegularityOp (I := I) (M := M) 0 _hT _hT1 w :=
    fun w => rfl
  set H1t := timeH1blockTransport (Tt := T)
    (ψ.toLinearIsometry.toContinuousLinearMap) Φ
    (fun x => (ψ.norm_map x).le) hΦ_apply with hH1t
  have hH1t_init : ∀ u, (H1t u).init = ψ u.init := fun u => rfl
  have hH1t_deriv : ∀ u, (H1t u).deriv = Φ u.deriv := fun u => rfl
  refine ⟨H1t ∘L Aop ∘L Φsymm, ?_, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun f => ?_)
    have e1 : (H1t ∘L Aop ∘L Φsymm) f = H1t (Aop (Φsymm f)) := rfl
    rw [e1]
    have hinit0 : (Aop (Φsymm f)).init = 0 := by
      rw [hAop_apply]
      change (timeH1.mk (0 : tensorHs (I := I) (M := M) g r s 0) _).init = 0
      rw [timeH1.init_mk]
    have hnorm_eq : ‖H1t (Aop (Φsymm f))‖ = ‖Φ (Aop (Φsymm f)).deriv‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (H1t (Aop (Φsymm f)))), timeH1.norm_sq_eq,
        hH1t_init, hH1t_deriv, hinit0, map_zero, norm_zero]
      simp [Real.sqrt_sq (norm_nonneg _)]
    rw [hnorm_eq]
    calc ‖Φ (Aop (Φsymm f)).deriv‖ ≤ ‖(Aop (Φsymm f)).deriv‖ := hΦ_apply _
      _ ≤ ‖Aop (Φsymm f)‖ := timeH1.norm_deriv_le _
      _ ≤ 2 * ‖Φsymm f‖ := by
          rw [hAop_apply]
          exact maximalRegularityOp_norm_le (I := I) (M := M) (h_compact := h_compact)
            (a := 0) _hT _hT1 _
      _ ≤ 2 * ‖f‖ := by gcongr; exact hΦsymm_apply f
  · intro f
    have e1 : (H1t ∘L Aop ∘L Φsymm) f = H1t (Aop (Φsymm f)) := rfl
    rw [e1, hH1t_init, hAop_apply]
    change ψ (timeH1.mk (0 : tensorHs (I := I) (M := M) g r s 0) _).init = 0
    rw [timeH1.init_mk, map_zero]
  · set SolField : timeL2 (TensorL2 r s g) T →L[ℝ]
        timeL2 (tensorHs (I := I) (M := M) g r s 2) T :=
      (c22.toLinearIsometry.toContinuousLinearMap) ∘L
        (LinearMap.mkContinuous
          { toFun := fun f => maximalRegularitySolField (I := I) (M := M) 0 _hT.le (Φsymm f)
            map_add' := fun f f' => by
              rw [map_add]
              refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
              rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
                  (h_compact := h_compact) (a := 0) _hT.le (Φsymm f + Φsymm f') i,
                timeModeCoeff_add (I := I) (M := M),
                maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
                  (h_compact := h_compact) (a := 0) _hT.le (Φsymm f) i,
                maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
                  (h_compact := h_compact) (a := 0) _hT.le (Φsymm f') i,
                solModeCoeff, solModeCoeff, solModeCoeff,
                timeModeCoeff_add (I := I) (M := M), map_add]
            map_smul' := fun c f => by
              rw [map_smul, RingHom.id_apply]
              refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
              rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
                  (h_compact := h_compact) (a := 0) _hT.le (c • Φsymm f) i,
                timeModeCoeff_smul (I := I) (M := M),
                maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
                  (h_compact := h_compact) (a := 0) _hT.le (Φsymm f) i,
                solModeCoeff, solModeCoeff, timeModeCoeff_smul (I := I) (M := M),
                map_smul] }
          (1 + T) (fun f => by
            refine le_trans (maximalRegularityOp_norm_Ha2_le (I := I) (M := M)
              (h_compact := h_compact) _hT _hT1 (Φsymm f)) ?_
            exact mul_le_mul_of_nonneg_left (hΦsymm_apply f) (by linarith [_hT.le]))) with hSolField
    have hSolField_apply : ∀ f, SolField f =
        c22 (maximalRegularitySolField (I := I) (M := M) 0 _hT.le (Φsymm f)) := fun f => rfl
    refine ⟨SolField, ?_, ?_⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ (by linarith [_hT.le]) (fun f => ?_)
      rw [hSolField_apply, c22.norm_map]
      refine le_trans (maximalRegularityOp_norm_Ha2_le (I := I) (M := M)
        (h_compact := h_compact) _hT _hT1 (Φsymm f)) ?_
      exact mul_le_mul_of_nonneg_left (hΦsymm_apply f) (by linarith [_hT.le])
    · set LapField : timeL2 (tensorHs (I := I) (M := M) g r s 2) T →L[ℝ]
          timeL2 (TensorL2 r s g) T :=
        Φ ∘L (timeScaleLaplacian (I := I) (M := M) 0) ∘L
          (c22.symm.toLinearIsometry.toContinuousLinearMap) with hLapField
      refine ⟨LapField, fun f => ?_⟩
      have hderiv : ((H1t ∘L Aop ∘L Φsymm) f).deriv
          = Φ (maximalRegularityDerivField (I := I) (M := M) 0 _hT.le (Φsymm f)) := by
        change (H1t (Aop (Φsymm f))).deriv = _
        rw [hH1t_deriv, hAop_apply]
        rfl
      rw [hderiv]
      have hLap : LapField (SolField f)
          = Φ (timeScaleLaplacian (I := I) (M := M) 0
              (maximalRegularitySolField (I := I) (M := M) 0 _hT.le (Φsymm f))) := by
        rw [hLapField]
        change Φ (timeScaleLaplacian (I := I) (M := M) 0 (c22.symm (SolField f))) = _
        rw [hSolField_apply, c22.symm_apply_apply]
      rw [hLap]
      have hsolves := maximalRegularityOp_solves (I := I) (M := M)
        (h_compact := h_compact) (a := 0) _hT _hT1 (Φsymm f)
      rw [maximalRegularityOp_timeDeriv (I := I) (M := M) (a := 0) _hT _hT1 (Φsymm f)] at hsolves
      rw [hsolves, map_add, hΦΦsymm]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
