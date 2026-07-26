import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open TensorMultilinear
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam convexPerturbation
  convexPerturbation_gFibreOpBound realizedFam_inner_of_mem Icc_subset_realizedSmallSet)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM gInvRaisedEndo
  gInvRaisedEndo_apply gInvRaisedEndo_eq_diff_add_id gInvDiffRaisedEndo
  cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem exists_fn_of_forall_exists_bounded (N : ℕ) (Q : ℕ → ℝ → Prop)
    (h : ∀ k, k ≤ N → ∃ c : ℝ, 0 ≤ c ∧ Q k c) :
    ∃ f : ℕ → ℝ, (∀ k, 0 ≤ f k) ∧ ∀ k, k ≤ N → Q k (f k) := by
  induction N with
  | zero =>
    obtain ⟨c, hc0, hc⟩ := h 0 le_rfl
    refine ⟨fun _ => c, fun _ => hc0, ?_⟩
    intro k hk
    rw [Nat.le_zero.mp hk]
    exact hc
  | succ N ih =>
    obtain ⟨f, hf0, hf⟩ := ih (fun k hk => h k (le_trans hk (Nat.le_succ N)))
    obtain ⟨c, hc0, hc⟩ := h (N + 1) le_rfl
    refine ⟨Function.update f (N + 1) c, ?_, ?_⟩
    · intro k
      by_cases hk : k = N + 1
      · rw [hk, Function.update_self]; exact hc0
      · rw [Function.update_of_ne hk]; exact hf0 k
    · intro k hk
      by_cases hkN : k = N + 1
      · rw [hkN, Function.update_self]; exact hc
      · rw [Function.update_of_ne hkN]
        exact hf k (by omega)

private theorem lieArm1_metricInner_injective (g : SmoothRiemannianMetric I M) (x : M)
    {v w : TangentSpace I x} (h : ∀ u : TangentSpace I x, g.inner x v u = g.inner x w u) :
    v = w := by
  by_contra hne
  have hvw : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g.pos x (v - w) hvw
  have hzero : g.inner x (v - w) (v - w) = 0 := by
    have h' := h (v - w)
    rw [show (g.inner x) (v - w) = (g.inner x) v - (g.inner x) w from
        map_sub (g.inner x) v w,
      ContinuousLinearMap.sub_apply, h', sub_self]
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

private def lieArm1SharpModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (k : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  cometricLmodel (I := I) g₁ x
    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis k))

private theorem lieArm1_cometric_collapse (g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x w ((Module.finBasis ℝ E) k) • lieArm1SharpModel (I := I) g₁ x k = w := by
  classical
  refine lieArm1_metricInner_injective (I := I) g₁ x (fun u => ?_)
  rw [show g₁.inner x (∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x w ((Module.finBasis ℝ E) k) • lieArm1SharpModel (I := I) g₁ x k) u =
      ∑ k : Fin (Module.finrank ℝ E), g₁.inner x w ((Module.finBasis ℝ E) k) *
        g₁.inner x (lieArm1SharpModel (I := I) g₁ x k) u from by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl]
  have hdual : ∀ k : Fin (Module.finrank ℝ E),
      g₁.inner x (lieArm1SharpModel (I := I) g₁ x k) u =
        ((Module.finBasis ℝ E).cDualBasis k) (u : E) := fun k =>
    cometricLmodel_covectorOfCLM_inner (I := I) g₁ x ((Module.finBasis ℝ E).cDualBasis k) u
  rw [Finset.sum_congr rfl fun k _ => by rw [hdual k]]
  have hcd : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis k) (u : E) =
        (Module.finBasis ℝ E).repr (u : E) k := by
    intro k
    rw [show ((Module.finBasis ℝ E).cDualBasis k : E →L[ℝ] ℝ)
        = LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).dualBasis k) from rfl,
      LinearMap.coe_toContinuousLinearMap']
    exact Module.Basis.dualBasis_apply (Module.finBasis ℝ E) k (u : E)
  rw [Finset.sum_congr rfl fun k _ => by rw [hcd k]]
  have hrepr : (u : TangentSpace I x) = ∑ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).repr (u : E) k • ((Module.finBasis ℝ E) k : TangentSpace I x) := by
    exact_mod_cast ((Module.finBasis ℝ E).sum_repr (u : E)).symm
  conv_rhs => rw [hrepr]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rw [smul_eq_mul, mul_comm]

def lieArm1Piece (g₀ g₁ : SmoothRiemannianMetric I M) (σ' : Equiv.Perm (Fin 4))
    (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2) : SmoothCcTensor g₀ 3 2 :=
  reindexCoeffGen (I := I) (M := M) g₀ 3 2
    (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
      (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
    ρ

private def lieArm1TraceArg (g₁ : SmoothRiemannianMetric I M) (σ' : Equiv.Perm (Fin 4)) (x : M)
    (m : Fin 2 → TangentSpace I x) (k : Fin (Module.finrank ℝ E)) : Fin 4 → E :=
  (Fin.cons ((lieArm1SharpModel (I := I) g₁ x k : TangentSpace I x) : E)
    (Fin.cons (((Module.finBasis ℝ E) k : E)) (fun j : Fin 2 => ((m j : TangentSpace I x) : E)))) ∘ σ'

set_option linter.unusedSectionVars false in
private theorem lieArm1Piece_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2)
    (K : ∀ y : M, TangentSpace I y → TangentSpace I y → TangentSpace I y) (x : M)
    (hΨ : ∀ (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x),
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) om) YZ =
        om (fun _ : Fin 1 => K x (YZ 0) (YZ 1)))
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ((Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 0)
            (Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 1)
              (fun _ : Fin 1 =>
                ((K x ((lieArm1TraceArg (I := I) g₁ σ' x m k 2 : E) : TangentSpace I x)
                    ((lieArm1TraceArg (I := I) g₁ σ' x m k 3 : E) : TangentSpace I x) :
                  TangentSpace I x) : E)))) ∘ ρ) := by
  classical
  set D' : Tensor0SSpace 3 I x :=
    Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel D))
    with hD'
  have happ : (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ).toSection x) D =
      deTurckLieTraceFib (I := I) g₁ σ' x
        (slotExtendFib (I := I) (M := M) g₀ 2 3 x
          (slotExtendFib (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x)) D') := by
    rw [lieArm1Piece, reindexCoeffGen_toSection]
    rw [reindexCoeffFibGen_apply (I := I) 3 2 ρ x
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x)
      D]
    rw [appCcRS_toSection]
    rw [ContinuousLinearMap.comp_apply]
    rw [deTurckLieTraceCoeff_toSection]
    rfl
  rw [happ]
  set U : Tensor0SSpace 4 I x :=
    slotExtendFib (I := I) (M := M) g₀ 2 3 x
      (slotExtendFib (I := I) (M := M) g₀ 1 2 x
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x)) D' with hU
  have htr : Tensor0SSpace.toModel (deTurckLieTraceFib (I := I) g₁ σ' x U)
      (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel U (lieArm1TraceArg (I := I) g₁ σ' x m k) := by
    rw [show deTurckLieTraceFib (I := I) g₁ σ' x U =
        cometricDoubleTraceFib (I := I) g₁ 2 x (domDomCongrFibPerm (I := I) σ' x U) from rfl]
    rw [cometricDoubleTraceFib_toModel]
    rw [domDomCongrFibPerm_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [modelDoubleTrace_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [htr]
  refine Finset.sum_congr rfl fun k _ => ?_
  set w : Fin 4 → E := lieArm1TraceArg (I := I) g₁ σ' x m k with hw
  set D₂ : Tensor0SSpace 2 I x :=
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x) D' (w 0) with hD₂
  set om : Tensor0SSpace 1 I x :=
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) D₂ (w 1) with hom
  set kE : E := ((K x ((w 2 : E) : TangentSpace I x) ((w 3 : E) : TangentSpace I x) :
    TangentSpace I x) : E) with hkE
  calc Tensor0SSpace.toModel U w
      = Tensor0SSpace.toModel U (Fin.cons (w 0) (Matrix.vecTail w)) :=
        congrArg (Tensor0SSpace.toModel U) (Fin.cons_self_tail w).symm
    _ = Tensor0SSpace.toModel
          (slotExtendFib (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) D₂)
          (Matrix.vecTail w) := by
        rw [hU]
        exact slotExtendFib_apply_eval (I := I) (M := M) g₀ 2 3 x _ D' (w 0) (Matrix.vecTail w)
    _ = Tensor0SSpace.toModel
          (slotExtendFib (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) D₂)
          (Fin.cons (Matrix.vecTail w 0) (Matrix.vecTail (Matrix.vecTail w))) :=
        congrArg (Tensor0SSpace.toModel _) (Fin.cons_self_tail (Matrix.vecTail w)).symm
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) om)
          (Matrix.vecTail (Matrix.vecTail w)) := by
        exact slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x _ D₂ (Matrix.vecTail w 0)
          (Matrix.vecTail (Matrix.vecTail w))
    _ = om (fun _ : Fin 1 =>
          K x ((w 2 : E) : TangentSpace I x) ((w 3 : E) : TangentSpace I x)) :=
        hΨ om (fun j : Fin 2 => ((Matrix.vecTail (Matrix.vecTail w) j : E) : TangentSpace I x))
    _ = Tensor0SSpace.toModel om (fun _ : Fin 1 => kE) := rfl
    _ = Tensor0SSpace.toModel D₂ (Fin.cons (w 1) (fun _ : Fin 1 => kE)) := by
        rw [hom]
        exact tensor0S_curry_apply_eval (I := I) (M := M) (n := 1) D₂ (w 1) (fun _ : Fin 1 => kE)
    _ = Tensor0SSpace.toModel D' (Fin.cons (w 0) (Fin.cons (w 1) (fun _ : Fin 1 => kE))) := by
        rw [hD₂]
        exact tensor0S_curry_apply_eval (I := I) (M := M) (n := 2) D' (w 0)
          (Fin.cons (w 1) (fun _ : Fin 1 => kE))
    _ = Tensor0SSpace.toModel D
          ((Fin.cons (w 0) (Fin.cons (w 1) (fun _ : Fin 1 => kE))) ∘ ρ) := by
        rw [hD', Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.domDomCongr_apply]
        rfl
    _ = Tensor0SSpace.toModel D
          ((Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 0)
            (Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 1)
              (fun _ : Fin 1 =>
                ((K x ((lieArm1TraceArg (I := I) g₁ σ' x m k 2 : E) : TangentSpace I x)
                    ((lieArm1TraceArg (I := I) g₁ σ' x m k 3 : E) : TangentSpace I x) :
                  TangentSpace I x) : E)))) ∘ ρ) := rfl

def lieArm1ConnDiffBgCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection := (connDiffSection (I := I) g₁ g_bg).toSection
  hasCompactSupport := (connDiffSection (I := I) g₁ g_bg).hasCompactSupport

set_option linter.unusedSectionVars false in
@[simp] theorem lieArm1ConnDiffBgCc_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      connDiffFib (I := I) g₁ g_bg x := rfl

def lieArm1LoweredBgKappa (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection := (connDiffLoweredCc (I := I) g₁ g_bg).toSection
  hasCompactSupport := (connDiffLoweredCc (I := I) g₁ g_bg).hasCompactSupport

def lieArm1PsiB (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  appCcRS (I := I) (M := M) g₀ 1 1 2
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ (⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩ :
        Equiv.Perm (Fin 3))
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
    (sharpFlatEndoCc (I := I) g₀ g₁)

def lieArm1RhoSlot0 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

def lieArm1RhoSlot1 : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

def lieArm1SigmaA : Equiv.Perm (Fin 4) := ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩

def lieArm1SigmaASwap : Equiv.Perm (Fin 4) := ⟨![3, 0, 2, 1], ![1, 3, 2, 0], by decide, by decide⟩

def lieArm1SigmaC : Equiv.Perm (Fin 4) := ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

def lieArm1SigmaCSwap : Equiv.Perm (Fin 4) := ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

def lieArm1SigmaD : Equiv.Perm (Fin 4) := ⟨![3, 0, 2, 1], ![1, 3, 2, 0], by decide, by decide⟩

def lieArm1SigmaDSwap : Equiv.Perm (Fin 4) := ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩

def lieArm1SigmaESwap : Equiv.Perm (Fin 4) := ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

def lieArm1SigmaF : Equiv.Perm (Fin 4) := ⟨![0, 3, 2, 1], ![0, 3, 2, 1], by decide, by decide⟩

def lieArm1SigmaFSwap : Equiv.Perm (Fin 4) := ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩

set_option linter.unusedSectionVars false in
private theorem lieArm1_normSq_eq_integral (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g r s) :
    ‖W‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def (I := I) (M := M) W,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s W]

set_option linter.unusedSectionVars false in
private theorem lieArm1_icg_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in
private theorem lieArm1_normSq_icg_reindex_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i (reindexCoeffGen (I := I) (M := M) g r s W ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i W‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g r s W ρ i x

set_option linter.unusedSectionVars false in
private theorem lieArm1_normSq_icg_domDom_eq (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 s i (domDomCongrSection (I := I) g σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 s i S‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g σ S i x

set_option linter.unusedSectionVars false in
private theorem lieArm1_normSq_icg_raise_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 1 (s + 1) i
        (cometricRaiseSlot0Field (I := I) (M := M) g s W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 (s + 2) i W‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g s W i x

set_option linter.unusedSectionVars false in
theorem lieArm1_norm_isEmpty (hM : IsEmpty M) (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (W : SmoothCcTensor g r s) : ‖W‖ = 0 := by
  haveI := hM
  rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
    MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]

private theorem lieArm1_traceHessianSlotPerm_inv_mul_apply (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    traceHessianSlotPerm ((traceHessianSlotPerm⁻¹ * σ) j) = σ j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

set_option linter.unusedSectionVars false in
private theorem lieArm1_dLTC_eq_reindex_traceHessian
    (g₀ g₁ : SmoothRiemannianMetric I M) (σ ρ : Equiv.Perm (Fin 4))
    (hcomp : ∀ j : Fin 4, traceHessianSlotPerm (ρ j) = σ j) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection, traceHessianCoeff_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibPerm_apply, domDomCongrFib_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have harg : ContinuousMultilinearMap.domDomCongr σ
      (Tensor0SBundle.Tensor0SSpace.toModel D) =
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg _ (funext fun j => ?_)
    rw [hcomp j]
  rw [harg]

set_option linter.unusedSectionVars false in
theorem lieArm1_rfns_dLTC_toSection_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x) := by
  rw [lieArm1_dLTC_eq_reindex_traceHessian (I := I) (M := M) g₀ g₁ σ'
      (traceHessianSlotPerm⁻¹ * σ') (lieArm1_traceHessianSlotPerm_inv_mul_apply σ'),
    reindexCoeffGen_toSection]
  exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ 4 2 x
    (traceHessianSlotPerm⁻¹ * σ')
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)

set_option linter.unusedSectionVars false in
theorem lieArm1_normSq_icg_dLTC_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 := by
  rw [lieArm1_dLTC_eq_reindex_traceHessian (I := I) (M := M) g₀ g₁ σ'
      (traceHessianSlotPerm⁻¹ * σ') (lieArm1_traceHessianSlotPerm_inv_mul_apply σ')]
  exact lieArm1_normSq_icg_reindex_eq (I := I) (M := M) g₀ 4 2
    (traceHessianCoeff (I := I) (M := M) g₀ g₁) (traceHessianSlotPerm⁻¹ * σ') i

set_option linter.unusedSectionVars false in
theorem lieArm1_gFibreOpBound_nonneg [Nonempty M] (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) : 0 ≤ δ := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
    haveI : Nontrivial (TangentSpace I x₀) := by
      have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
        have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
        rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
      exact Module.nontrivial_of_finrank_pos hfr
    exact exists_ne 0
  have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
  have hbound := hδ x₀ v v
  have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
  have habs_nn : 0 ≤ |h x₀ v v| := abs_nonneg _
  by_contra hδc
  have hδc' : δ < 0 := lt_of_not_ge hδc
  have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
    have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
    exact mul_neg_of_neg_of_pos h1 hsqrt_pos
  linarith [le_trans habs_nn hbound]

set_option linter.unusedSectionVars false in
theorem lieArm1_convexPerturbation_ball (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) {R : ℝ} (a : ℕ)
    (hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (hT'ball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
  intro j hj
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
      = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
        + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
    rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
      iteratedCovGrad_add, lieArm1_icg_smul, lieArm1_icg_smul]
  rw [heq]
  calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
      ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
    _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * R + s * R :=
        add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
          (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
    _ = R := by ring

set_option linter.unusedSectionVars false in
theorem lieArm1_realizedFam_pack (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w) ∧
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) ∧
      (1 - s) * δ' + s * δ ≤ δ₀ := by
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  refine ⟨fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w,
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1, ?_⟩
  have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
  have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
  have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
  linarith [e1, e2, e3]

set_option linter.unusedSectionVars false in
private lemma lieArm1_toModel_om_single (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

set_option linter.unusedSectionVars false in
private lemma lieArm1_g1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

set_option linter.unusedSectionVars false in
private lemma lieArm1_g0_inner_inverseMetricSharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [lieArm1_g1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma lieArm1_sharpFlat_eq_slotInsert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [lieArm1_toModel_om_single (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [lieArm1_toModel_om_single (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [lieArm1_g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

set_option linter.unusedSectionVars false in
private lemma lieArm1_fullRaised_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = gInvDiffRaisedEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma lieArm1_slotInsert_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in
private theorem lieArm1_sharpFlat_decomp (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
  rw [lieArm1_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
    lieArm1_fullRaised_diff_split (I := I) (M := M) g₀ g₁,
    lieArm1_slotInsert_add (I := I) (M := M) g₀ 0]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private theorem lieArm1_sharpFlat_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Km, hKm_nn, hKm⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀) with hIdIns_def
  obtain ⟨S0, hS0_nn, hS0⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 1 IdIns
  refine ⟨2 * Cb 0 + 2 * S0,
    fun i => ∑ q ∈ Finset.range (i + 1),
      (2 * (Cb q * Km q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2),
    by have := hCb_nn 0; linarith,
    fun i => Finset.sum_nonneg fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hCb_nn q) (hKm_nn q)))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns :=
    lieArm1_sharpFlat_decomp (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (IdIns.toSection x) := by
      rw [hdecomp]
      rw [show ((DiffIns + IdIns).toSection x) = DiffIns.toSection x + IdIns.toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 1 x _ _
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) ≤ Cb 0 := by
      have h2 := hCb g₁ P htie hδ_le hδ0 hδ 0 x
      simp only [iteratedCovGrad_zero] at h2
      have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
        simp
      rw [hgrid0, mul_one] at h2
      exact h2
    linarith [hsplit, hD0, hS0 x]
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    obtain ⟨hgi, hgb⟩ := hKm P hPball q hq_le
    have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ Cb q * Km q := by
      have hint : MeasureTheory.Integrable
          (fun x => Cb q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint
        (fun x => hCb g₁ P htie hδ_le hδ0 hδ q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hgb (hCb_nn q)
    have htri : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ +
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ := by
      rw [hdecomp, iteratedCovGrad_add]
      exact norm_add_le _ _
    nlinarith [htri, hDq,
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q IdIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
        ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖)]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem lieArm1_connDiff_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((connDiffSection (I := I) g₁ g₀).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛK, FK, hΛK_nn, hFK_nn, hK⟩ :=
    raisedKoszul_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lieArm1_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  have h2A : ∀ k : ℕ, k ≤ a → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT' ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 n S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2) := by
    intro k _
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 1 2 1 k
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_fn_of_forall_exists_bounded a _ h2A
  refine ⟨ΛK ^ 2 * Λsf,
    fun i => ∑ q ∈ Finset.range (i + 1),
      appCcGdiag (E := E) q * (C2 q * (Λsf * FK q + ΛK ^ 2 * Fsf q)),
    mul_nonneg (sq_nonneg _) hΛsf_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛsf_nn (hFK_nn q))
        (mul_nonneg (sq_nonneg _) (hFsf_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hKsup, hKsum⟩ := hK g₁ P hδ_le hδ htie hPball
  obtain ⟨hsfsup, hsfsum⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hid : connDiffSection (I := I) g₁ g₀ =
      appCcRS (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro x
    rw [hid, appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
      (show TensorRSSpace 1 2 I x from (raisedKoszul (I := I) g₀ g₁).toSection x)
      (show TensorRSSpace 1 1 I x from (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    exact mul_le_mul (hKsup x) (hsfsup x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) (sq_nonneg ΛK)
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    have hsfsup' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ (Real.sqrt Λsf) ^ 2 := by
      intro x
      rw [Real.sq_sqrt hΛsf_nn]
      exact hsfsup x
    obtain ⟨hgi, hgb⟩ := hC2 q hq_le (raisedKoszul (I := I) g₀ g₁)
      (sharpFlatEndoCc (I := I) g₀ g₁) ΛK (Real.sqrt Λsf) hΛK_nn (Real.sqrt_nonneg _)
      hKsup hsfsup'
    rw [hid]
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      1 (2 + q)
      (iteratedCovGrad (I := I) g₀ 1 2 q
        (appCcRS (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
          (sharpFlatEndoCc (I := I) g₀ g₁)))
      (fun x => appCcGdiag (E := E) q *
        ∑ n ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (q + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 l
                    (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
      (hgi.const_mul (appCcGdiag (E := E) q))
      (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ q 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
    refine le_trans hgb ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC2_nn q)
    rw [Real.sq_sqrt hΛsf_nn]
    have e1 : Λsf * (∑ n ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2) ≤
        Λsf * FK q := mul_le_mul_of_nonneg_left (hKsum q hq_le) hΛsf_nn
    have e2 : ΛK ^ 2 * (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2) ≤
        ΛK ^ 2 * Fsf q := mul_le_mul_of_nonneg_left (hsfsum q hq_le) (sq_nonneg ΛK)
    linarith [e1, e2]

set_option linter.unusedSectionVars false in
private lemma lieArm1_cotangentToDual_map_add (x : M) (om : Tensor0SSpace 1 I x)
    (u v : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om (u + v) =
      cotangentToDual (I := I) (x := x) om u + cotangentToDual (I := I) (x := x) om v := by
  simp only [show ∀ w : TangentSpace I x, cotangentToDual (I := I) (x := x) om w =
      cotangentToDualLinear (I := I) (x := x) om w from fun w => rfl]
  exact map_add _ u v

set_option linter.unusedSectionVars false in
private lemma lieArm1_om_add (x : M) (om : Tensor0SSpace 1 I x) (u v : TangentSpace I x) :
    om (fun _ : Fin 1 => u + v) = om (fun _ : Fin 1 => u) + om (fun _ : Fin 1 => v) := by
  rw [← cotangentToDual_apply (I := I) om (u + v), ← cotangentToDual_apply (I := I) om u,
    ← cotangentToDual_apply (I := I) om v]
  exact lieArm1_cotangentToDual_map_add (I := I) (M := M) x om u v

def lieArm1FixCd (g₀ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection := (connDiffSection (I := I) g₀ g_bg).toSection
  hasCompactSupport := (connDiffSection (I := I) g₀ g_bg).hasCompactSupport

set_option linter.unusedSectionVars false in
theorem lieArm1_connDiffBg_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg =
      connDiffSection (I := I) g₁ g₀ + lieArm1FixCd (I := I) (M := M) g₀ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show (connDiffSection (I := I) g₁ g₀ + lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x =
      (connDiffSection (I := I) g₁ g₀).toSection x +
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [lieArm1ConnDiffBgCc_toSection, connDiffSection_toSection,
    show (lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x =
      connDiffFib (I := I) g₀ g_bg x from rfl]
  refine tensorRSSpace_ext 1 2 x (fun om => ?_)
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      (connDiffFib (I := I) g₁ g₀ x + connDiffFib (I := I) g₀ g_bg x : TensorRSSpace 1 2 I x)) om) =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om +
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₀ g_bg x) om from rfl]
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om +
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₀ g_bg x) om) YZ =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om) YZ +
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₀ g_bg x) om) YZ from rfl]
  rw [connDiffFib_apply_eval, connDiffFib_apply_eval, connDiffFib_apply_eval]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g_bg x (YZ 0) (YZ 1) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1) +
        PDE.DeTurck.connDiff (I := I) g₀ g_bg x (YZ 0) (YZ 1) from
    PDE.DeTurck.connDiff_cocycle (I := I) g₀ g₁ g_bg x (YZ 0) (YZ 1)]
  exact lieArm1_om_add (I := I) (M := M) x om _ _

set_option linter.unusedSectionVars false in
theorem lieArm1_rfns_toSection_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((A + B).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x (B.toSection x) := by
  rw [show (A + B).toSection x = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r s x _ _

set_option linter.unusedSectionVars false in
theorem lieArm1_normSq_icg_add_le (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q (A + B)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g r s q A‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g r s q B‖ ^ 2 := by
  have htri : ‖iteratedCovGrad (I := I) g r s q (A + B)‖ ≤
      ‖iteratedCovGrad (I := I) g r s q A‖ + ‖iteratedCovGrad (I := I) g r s q B‖ := by
    rw [iteratedCovGrad_add]
    exact norm_add_le _ _
  nlinarith [htri, norm_nonneg (iteratedCovGrad (I := I) g r s q (A + B)),
    norm_nonneg (iteratedCovGrad (I := I) g r s q A),
    norm_nonneg (iteratedCovGrad (I := I) g r s q B),
    sq_nonneg (‖iteratedCovGrad (I := I) g r s q A‖ - ‖iteratedCovGrad (I := I) g r s q B‖)]

set_option linter.unusedSectionVars false in
private theorem lieArm1_rfns_icg_sE2_le (g₀ : SmoothRiemannianMetric I M)
    (Ψ : SmoothCcTensor g₀ 1 2) (l : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 4 l
          (slotExtend (I := I) (M := M) g₀ 2 3
            (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection x) := by
  have houter := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
    (slotExtend (I := I) (M := M) g₀ 1 2 Ψ) l x
  have hinner := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2 Ψ l x
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 4 l
          (slotExtend (I := I) (M := M) g₀ 2 3
            (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 3 l
              (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)).toSection x) := houter
    _ ≤ (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection x)) :=
        mul_le_mul_of_nonneg_left hinner hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection x) := by ring

set_option linter.unusedSectionVars false in
theorem lieArm1_rfns_sE2_zero_le (g₀ : SmoothRiemannianMetric I M)
    (Ψ : SmoothCcTensor g₀ 1 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
        ((slotExtend (I := I) (M := M) g₀ 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (Ψ.toSection x) := by
  have h := lieArm1_rfns_icg_sE2_le (I := I) (M := M) g₀ Ψ 0 x
  simpa only [iteratedCovGrad_zero] using h

set_option linter.unusedSectionVars false in
theorem lieArm1_normSq_icg_sE2_le (g₀ : SmoothRiemannianMetric I M)
    (Ψ : SmoothCcTensor g₀ 1 2) (l : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 l
        (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l Ψ‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono ?_ ?_ (fun x => lieArm1_rfns_icg_sE2_le
    (I := I) (M := M) g₀ Ψ l x)
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (4 + l)
      (iteratedCovGrad (I := I) g₀ 3 4 l
        (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
  · exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (2 + l)
      (iteratedCovGrad (I := I) g₀ 1 2 l Ψ)).const_mul _

set_option linter.unusedSectionVars false in
private theorem lieArm1_piece_rfns_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ').toSection x) *
        ((Module.finrank ℝ E : ℝ) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (Ψ.toSection x)) := by
  have hdef : lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ =
      reindexCoeffGen (I := I) (M := M) g₀ 3 2
        (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
        ρ := rfl
  rw [hdef, reindexCoeffGen_toSection]
  rw [riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ 3 2 x ρ
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
        (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x)]
  rw [appCcRS_toSection]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 4 2 x
    (show TensorRSSpace 4 2 I x from
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ').toSection x)
    (show TensorRSSpace 3 4 I x from
      (slotExtend (I := I) (M := M) g₀ 2 3
        (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)).toSection x)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x _)
  exact lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ Ψ x

set_option linter.unusedSectionVars false in
theorem lieArm1_piece_normSq_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2)
    (i : ℕ) (C2i ΛS ΛT FSi FTi : ℝ) (hC2i : 0 ≤ C2i)
    (hFS : ∑ n ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 n
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')‖ ^ 2 ≤ FSi)
    (hFT : ∑ l ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 3 4 l
        (slotExtend (I := I) (M := M) g₀ 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))‖ ^ 2 ≤ FTi)
    (htwo : MeasureTheory.Integrable
        (fun x => ∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 4 2 n
                (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')).toSection x)
            * ∑ l ∈ Finset.range (i + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 3 4 l
                    (slotExtend (I := I) (M := M) g₀ 2 3
                      (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, (∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 4 2 n
                (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')).toSection x)
            * ∑ l ∈ Finset.range (i + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 3 4 l
                    (slotExtend (I := I) (M := M) g₀ 2 3
                      (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        C2i * (ΛT ^ 2 * ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')‖ ^ 2
            + ΛS ^ 2 * ∑ l ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 4 l
                (slotExtend (I := I) (M := M) g₀ 2 3
                  (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))‖ ^ 2)) :
    ‖iteratedCovGrad (I := I) g₀ 3 2 i (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ)‖ ^ 2 ≤
      appCcGdiag (E := E) i * (C2i * (ΛT ^ 2 * FSi + ΛS ^ 2 * FTi)) := by
  obtain ⟨hgi, hgb⟩ := htwo
  have hdef : lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ =
      reindexCoeffGen (I := I) (M := M) g₀ 3 2
        (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
        ρ := rfl
  rw [hdef, lieArm1_normSq_icg_reindex_eq]
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (2 + i)
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
        (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))))
    (fun x => appCcGdiag (E := E) i *
      ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 4 2 n
              (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')).toSection x)
          * ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 4 l
                  (slotExtend (I := I) (M := M) g₀ 2 3
                    (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x))
    (hgi.const_mul (appCcGdiag (E := E) i))
    (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
      (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)) x)
  refine le_trans hkey ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
  refine le_trans hgb ?_
  refine mul_le_mul_of_nonneg_left ?_ hC2i
  have e1 := mul_le_mul_of_nonneg_left hFS (sq_nonneg ΛT)
  have e2 := mul_le_mul_of_nonneg_left hFT (sq_nonneg ΛS)
  linarith [e1, e2]

set_option linter.unusedSectionVars false in
private theorem lieArm1_twoArm_top_fn (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C2 : ℕ → ℝ, (∀ k, 0 ≤ C2 k) ∧ ∀ k, k ≤ a →
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2 k * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
  have h2A : ∀ k : ℕ, k ≤ a → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
    intro k _
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_fn_of_forall_exists_bounded a _ h2A
  exact ⟨C2, hC2_nn, hC2⟩

set_option linter.unusedSectionVars false in
private theorem lieArm1_rfns_neg (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
private theorem lieArm1_rfns_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm1_rfns_icg_symmS_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)).toSection x =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T j, SmoothCcTensor.toSection_add]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection +
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection) x =
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
          ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x _ _) ?_
  rw [lieArm1_rfns_smul (I := I) (M := M) g₀ 0 (2 + j) x,
    lieArm1_rfns_smul (I := I) (M := M) g₀ 0 (2 + j) x]
  have hperm := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) T j x
  rw [hperm]
  ring_nf
  nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)]

set_option linter.unusedSectionVars false in
private lemma lieArm1_normSq_icg_symmS_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_mono ?_ ?_
    (fun x => lieArm1_rfns_icg_symmS_le (I := I) (M := M) g₀ T j x)
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T))
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j T)

set_option linter.unusedSectionVars false in
private lemma lieArm1_rfns_symmS_zero_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 0 2 x
    ((symmS (I := I) (M := M) g₀ T).toSection x) e bse hnE hbse horth]
  have hcof : coframeS (I := I) (M := M) g₀ x 0 e = fun _ : Fin 0 → Fin n =>
      unitTensor (I := I) (M := M) x := by
    funext K
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 0 e K) v =
        coframeS (I := I) (M := M) g₀ x 0 e K v from rfl]
    rw [coframeS_apply (I := I) (M := M) g₀ x 0 e K v]
    rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v =
        unitTensor (I := I) (M := M) x v from rfl]
    rw [Fin.prod_univ_zero]
    rw [unitTensor, Tensor0SSpace.ofModel]
    rfl
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (symmS (I := I) (M := M) g₀ T).toSection x)
              (coframeS (I := I) (M := M) g₀ x 0 e K))
            (fun i : Fin 2 => (e (J i) : E)) from rfl]
      rw [hcof]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun i : Fin 2 => (e (J i) : E)) =
          unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [show unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] =
          ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1)) from
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
          (symmS (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

set_option linter.unusedSectionVars false in
private def lieArm1LowFixField (g₀ g_bg : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₀ g₀ g_bg⟩

private def lieArm1LowFix (g₀ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lieArm1LowFixField (I := I) (M := M) g₀ g_bg)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private def lieArm1PbLowField (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => ccBilinConnDiffLoweredFib (I := I) g₀ P gA gB x,
    ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ P gA gB⟩

private def lieArm1PbLow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lieArm1PbLowField (I := I) (M := M) g₀ P gA gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private lemma lieArm1_kappa_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₁ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
private lemma lieArm1_connDiffLowered_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
private lemma lieArm1_LowFix_unitModel_apply (g₀ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lieArm1LowFix (I := I) (M := M) g₀ g_bg) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lieArm1LowFix (I := I) (M := M) g₀ g_bg).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lieArm1LowFixField (I := I) (M := M) g₀ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₀ g₀ g_bg x m

set_option linter.unusedSectionVars false in
private lemma lieArm1_PbLow_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lieArm1PbLow (I := I) (M := M) g₀ P gA gB) x m =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lieArm1PbLow (I := I) (M := M) g₀ P gA gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lieArm1PbLowField (I := I) (M := M) g₀ P gA gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact ccBilinConnDiffLoweredFib_toModel (I := I) g₀ P gA gB x m

set_option linter.unusedSectionVars false in
private lemma lieArm1_unitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m + unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A + B).toSection x) = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x + B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in
private lemma lieArm1_unitModel_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A - B) x m =
      unitModel (I := I) (M := M) g₀ s A x m - unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A - B).toSection x) = A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x - B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in
private lemma lieArm1_connDiff_self_zero (gA : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gA x u v = 0 := by
  have h := PDE.DeTurck.connDiff_cocycle (I := I) gA gA gA x u v
  have h2 : PDE.DeTurck.connDiff (I := I) gA gA x u v +
      PDE.DeTurck.connDiff (I := I) gA gA x u v =
      PDE.DeTurck.connDiff (I := I) gA gA x u v + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

set_option linter.unusedSectionVars false in
private lemma lieArm1_connDiff_antisymm (gA gB : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v =
      -PDE.DeTurck.connDiff (I := I) gB gA x u v := by
  have h := PDE.DeTurck.connDiff_cocycle (I := I) gB gA gA x u v
  rw [lieArm1_connDiff_self_zero (I := I) (M := M) gA x u v] at h
  exact eq_neg_of_add_eq_zero_left h.symm

set_option linter.unusedSectionVars false in
private theorem lieArm1_kappa_add_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg =
      -(connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
        + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀
        + lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg) := by
  set S : SmoothCcTensor g₀ 0 3 :=
    connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
      + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀
      + lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg with hS_def
  rw [show -S = S - (S + S) from by abel]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [lieArm1_unitModel_sub (I := I) (M := M) g₀ 3 S (S + S) x m,
    lieArm1_unitModel_add (I := I) (M := M) g₀ 3 S S x m]
  have hSval : unitModel (I := I) (M := M) g₀ 3 S x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) +
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2) +
        ccTensorBilinSymm (I := I) g₀ P x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) +
        ccTensorBilinSymm (I := I) g₀ P x
          (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2) := by
    rw [hS_def]
    rw [lieArm1_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
      lieArm1_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
      lieArm1_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m]
    rw [lieArm1_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      lieArm1_LowFix_unitModel_apply (I := I) (M := M) g₀ g_bg x m,
      lieArm1_PbLow_unitModel_apply (I := I) (M := M) g₀ P g₁ g₀ x m,
      lieArm1_PbLow_unitModel_apply (I := I) (M := M) g₀ P g₀ g_bg x m]
  have hκval : unitModel (I := I) (M := M) g₀ 3
      (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) x m =
      -(g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) +
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2) +
        ccTensorBilinSymm (I := I) g₀ P x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) +
        ccTensorBilinSymm (I := I) g₀ P x
          (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2)) := by
    rw [lieArm1_kappa_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m]
    rw [htie x (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (m 0) (m 1)) (m 2)]
    have hbg1 : PDE.DeTurck.connDiff (I := I) g_bg g₁ x (m 0) (m 1) =
        -(PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) +
          PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) := by
      rw [PDE.DeTurck.connDiff_cocycle (I := I) g₀ g_bg g₁ x (m 0) (m 1)]
      rw [lieArm1_connDiff_antisymm (I := I) (M := M) g_bg g₀ x (m 0) (m 1),
        lieArm1_connDiff_antisymm (I := I) (M := M) g₀ g₁ x (m 0) (m 1)]
      abel
    rw [hbg1]
    rw [map_neg (g₀.inner x), map_neg (ccTensorBilinSymm (I := I) g₀ P x)]
    rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply]
    rw [map_add (g₀.inner x), map_add (ccTensorBilinSymm (I := I) g₀ P x)]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    ring
  rw [hκval, hSval]
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm1_interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
private lemma lieArm1_connDiffSection_eq_raise_lowered (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lieArm1_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [lieArm1_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x ![YZ 0, YZ 1, u]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

set_option linter.unusedSectionVars false in
private lemma lieArm1_rfns_icg_lowered_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [lieArm1_connDiffSection_eq_raise_lowered (I := I) (M := M) g₀ g₁]

set_option linter.unusedSectionVars false in
private theorem lieArm1_pbLow_raise_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)) =
      appCcRS (I := I) (M := M) g₀ 1 1 2 Ψc
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricRaiseSlot0Field_toSection, appCcRS_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) u := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lieArm1_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
    have hum : unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)) x =
        Tensor0SSpace.toModel D := rfl
    rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
          unitModel (I := I) (M := M) g₀ 3
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)) x
            ![u, YZ 0, YZ 1] from by
      rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
    rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
          ![YZ 0, YZ 1, u] from by
      funext i; fin_cases i <;> simp [finRotate_succ_apply]]
    rw [lieArm1_PbLow_unitModel_apply (I := I) (M := M) g₀ P gA gB x ![YZ 0, YZ 1, u]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψc.toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)).toSection x)) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x u
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) := by
    rw [ContinuousLinearMap.comp_apply]
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψc.toSection x) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) gA gB x) from by rw [hΨc x]]
    rw [connDiffFib_apply_eval]
    set om' : Tensor0SSpace 1 I x :=
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) om with hom'
    rw [show om' (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) =
        Tensor0SSpace.toModel om'
          (fun _ : Fin 1 =>
            (show E from PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))) from rfl]
    rw [hom']
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) om =
        cometricRaiseSlot0Fib (I := I) g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)) om from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [lieArm1_interior_product_toModel_eval (I := I) (M := M) 1 x
      (inverseMetricSharpFib (I := I) g₀ x om) _
      (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    rw [← hu]
    rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from u)
            (fun k => (show E from PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)))) =
        unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ P) x
          ![u, PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)] from by
      rw [unitModel]; congr 1; funext k; fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ P) x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
  rw [hLHS, hRHS]
  exact (ccTensorBilinSymm_symm (I := I) g₀ P x u
    (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))).symm

set_option linter.unusedSectionVars false in
private lemma lieArm1_rfns_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (appCcRS (I := I) (M := M) g₀ 1 1 2 Ψc
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (symmS (I := I) (M := M) g₀ P)))).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (lieArm1PbLow (I := I) (M := M) g₀ P gA gB))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (lieArm1PbLow (I := I) (M := M) g₀ P gA gB) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (appCcRS (I := I) (M := M) g₀ 1 1 2 Ψc
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (symmS (I := I) (M := M) g₀ P)))).toSection x) := by
        rw [lieArm1_pbLow_raise_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc]

set_option linter.unusedSectionVars false in
private theorem lieArm1_twoArm_1121_fn (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C2 : ℕ → ℝ, (∀ k, 0 ≤ C2 k) ∧ ∀ k, k ≤ a →
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2 k * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2) := by
  have h2A : ∀ k : ℕ, k ≤ a → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2) := by
    intro k _
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 1 2 1 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_fn_of_forall_exists_bounded a _ h2A
  exact ⟨C2, hC2_nn, hC2⟩

set_option linter.unusedSectionVars false in
private theorem lieArm1_WB_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    {δ₀ : ℝ} (P : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2) ∧
    (∀ l : ℕ, l ≤ a →
      ‖iteratedCovGrad (I := I) g₀ 1 1 l
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P))‖ ^ 2 ≤ R ^ 2) := by
  constructor
  · intro x
    have h0 := rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
      (symmS (I := I) (M := M) g₀ P) 0 x
    simp only [iteratedCovGrad_zero] at h0
    rw [h0]
    refine le_trans (lieArm1_rfns_symmS_zero_le (I := I) (M := M) g₀ P hδ0 hδ x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hδmax : δ ≤ max δ₀ 0 := le_trans hδ_le (le_max_left _ _)
    exact pow_le_pow_left₀ hδ0 hδmax 2
  · intro l hl
    rw [lieArm1_normSq_icg_raise_eq (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P) l]
    refine le_trans (lieArm1_normSq_icg_symmS_le (I := I) (M := M) g₀ P l) ?_
    have h1 := hPball l (by omega)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

set_option linter.unusedSectionVars false in
private lemma lieArm1_normSq_icg_lowered_eq (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lieArm1_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ n x

set_option linter.unusedSectionVars false in
private lemma lieArm1_normSq_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (appCcRS (I := I) (M := M) g₀ 1 1 2 Ψc
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)))‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lieArm1_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc n x

set_option linter.unusedSectionVars false in
private lemma lieArm1_rfns_icg_raiseDomDom_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (κ' : SmoothCcTensor g₀ 0 3) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ σ κ'))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n κ').toSection x) := by
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ σ κ') n x]
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    σ κ' n x

set_option linter.unusedSectionVars false in
private lemma lieArm1_normSq_icg_raiseDomDom_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (κ' : SmoothCcTensor g₀ 0 3) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ σ κ'))‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n κ'‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lieArm1_rfns_icg_raiseDomDom_eq (I := I) (M := M) g₀ σ κ' n x

set_option linter.unusedSectionVars false in
private theorem lieArm1_appCc12_normSq_le (g₀ : SmoothRiemannianMetric I M)
    (Φ : SmoothCcTensor g₀ 1 2) (W : SmoothCcTensor g₀ 1 1) (q : ℕ)
    (C2q ΛΦ ΛW FΦq FWq : ℝ) (hC2q : 0 ≤ C2q) (hΛΦ : 0 ≤ ΛΦ) (hΛW : 0 ≤ ΛW)
    (hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (Φ.toSection x) ≤ ΛΦ)
    (hW0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (W.toSection x) ≤ ΛW)
    (hFΦ : ∑ n ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 1 2 n Φ‖ ^ 2 ≤ FΦq)
    (hFW : ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 1 1 l W‖ ^ 2 ≤ FWq)
    (htwo : ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2q * (ΛT ^ 2 * ∑ n ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2)) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 q (appCcRS (I := I) (M := M) g₀ 1 1 2 Φ W)‖ ^ 2 ≤
      appCcGdiag (E := E) q * (C2q * (ΛW * FΦq + ΛΦ * FWq)) := by
  have hΦ0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (Φ.toSection x) ≤
      (Real.sqrt ΛΦ) ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛΦ]
    exact hΦ0 x
  have hW0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (W.toSection x) ≤
      (Real.sqrt ΛW) ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛW]
    exact hW0 x
  obtain ⟨hgi, hgb⟩ := htwo Φ W (Real.sqrt ΛΦ) (Real.sqrt ΛW)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hΦ0' hW0'
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + q)
    (iteratedCovGrad (I := I) g₀ 1 2 q (appCcRS (I := I) (M := M) g₀ 1 1 2 Φ W))
    (fun x => appCcGdiag (E := E) q *
      ∑ n ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n Φ).toSection x)
          * ∑ l ∈ Finset.range (q + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l W).toSection x))
    (hgi.const_mul (appCcGdiag (E := E) q))
    (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ q 1 1 2 Φ W x)
  refine le_trans hkey ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
  refine le_trans hgb ?_
  refine mul_le_mul_of_nonneg_left ?_ hC2q
  rw [Real.sq_sqrt hΛΦ, Real.sq_sqrt hΛW]
  have e1 := mul_le_mul_of_nonneg_left hFΦ hΛW
  have e2 := mul_le_mul_of_nonneg_left hFW hΛΦ
  linarith [e1, e2]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private theorem lieArm1_kappa_feed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
    lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λlow, hΛlow_nn, hΛlow⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 3
      (lieArm1LowFix (I := I) (M := M) g₀ g_bg)
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lieArm1_twoArm_1121_fn (I := I) (M := M) g₀ a
  set nQ : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2 with hnQ_def
  have hnQ_nn : 0 ≤ nQ := by rw [hnQ_def]; positivity
  set FB : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2
    with hFB_def
  have hFB_nn : ∀ i, 0 ≤ FB i := fun i => Finset.sum_nonneg fun q _ => sq_nonneg _
  set Ffx : ℕ → ℝ := fun q => ∑ l ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ 1 2 l (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2
    with hFfx_def
  have hFfx_nn : ∀ q, 0 ≤ Ffx q := fun q => Finset.sum_nonneg fun l _ => sq_nonneg _
  set FC : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    appCcGdiag (E := E) q * (C2b q * (nQ * Fcd q + Λcd * (((q : ℝ) + 1) * R ^ 2)))
    with hFC_def
  have hFC_nn : ∀ i, 0 ≤ FC i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFcd_nn q))
        (mul_nonneg hΛcd_nn (by positivity))))
  set FD : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    appCcGdiag (E := E) q * (C2b q * (nQ * Ffx q + Λfx * (((q : ℝ) + 1) * R ^ 2)))
    with hFD_def
  have hFD_nn : ∀ i, 0 ≤ FD i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFfx_nn q))
        (mul_nonneg hΛfx_nn (by positivity))))
  refine ⟨8 * Λcd + 8 * Λlow + 4 * (Λcd * nQ) + 2 * (Λfx * nQ),
    fun i => 8 * Fcd i + 8 * FB i + 4 * FC i + 2 * FD i,
    by
      have e1 := mul_nonneg hΛcd_nn hnQ_nn
      have e2 := mul_nonneg hΛfx_nn hnQ_nn
      linarith [hΛcd_nn, hΛlow_nn, e1, e2],
    fun i => by
      have := hFcd_nn i
      have := hFB_nn i
      have := hFC_nn i
      have := hFD_nn i
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hWB0, hWBL2⟩ :=
    lieArm1_WB_feed (I := I) (M := M) g₀ a P hδ_le hδ0 hδ hPball
  obtain ⟨hcd0, hcdL2⟩ := hcd g₁ P htie hδ_le hδ0 hδ hPball
  have hκeq := lieArm1_kappa_add_decomp (I := I) (M := M) g₀ g₁ g_bg P htie
  have hΨcC : ∀ x : M, (connDiffSection (I := I) g₁ g₀).toSection x =
      connDiffFib (I := I) g₁ g₀ x := fun x => rfl
  have hΨcD : ∀ x : M, (lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x =
      connDiffFib (I := I) g₀ g_bg x := fun x => rfl
  have hWBsum : ∀ q : ℕ, q ≤ a →
      ∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 l
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P))‖ ^ 2 ≤ ((q : ℝ) + 1) * R ^ 2 := by
    intro q hq
    refine le_trans (Finset.sum_le_sum fun l hl =>
      hWBL2 l (le_trans (by have := Finset.mem_range.mp hl; omega : l ≤ q) hq)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_refl _
  refine ⟨?_, ?_⟩
  · intro x
    have hsec : (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x =
        -((connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
          + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀
          + lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg).toSection x) := by
      rw [hκeq, SmoothCcTensor.toSection_neg]
      rfl
    rw [hsec, lieArm1_rfns_neg (I := I) (M := M) g₀ 0 3 x]
    have h1 := lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
        + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)
      (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg) x
    have h2 := lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg)
      (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀) x
    have h3 := lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁) (lieArm1LowFix (I := I) (M := M) g₀ g_bg) x
    have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((connDiffLoweredCc (I := I) g₀ g₁).toSection x) ≤ Λcd := by
      have h := lieArm1_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ 0 x
      simp only [iteratedCovGrad_zero] at h
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((connDiffLoweredCc (I := I) g₀ g₁).toSection x)
          = riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
              ((connDiffSection (I := I) g₁ g₀).toSection x) := h
        _ ≤ Λcd := hcd0 x
    have hB0 := hΛlow x
    have hC0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀).toSection x) ≤ Λcd * nQ := by
      have h := lieArm1_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC 0 x
      simp only [iteratedCovGrad_zero] at h
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((appCcRS (I := I) (M := M) g₀ 1 1 2 (connDiffSection (I := I) g₁ g₀)
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (symmS (I := I) (M := M) g₀ P))).toSection x) := h
      rw [h2, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from (connDiffSection (I := I) g₁ g₀).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hcd0 x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛcd_nn
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg).toSection x) ≤ Λfx * nQ := by
      have h := lieArm1_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ g_bg
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg) hΨcD 0 x
      simp only [iteratedCovGrad_zero] at h
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((appCcRS (I := I) (M := M) g₀ 1 1 2 (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (symmS (I := I) (M := M) g₀ P))).toSection x) := h
      rw [h2, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from
          (lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hΛfx x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛfx_nn
    linarith [h1, h2, h3, hA0, hB0, hC0, hD0]
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
      intro q _
      have hnorm : ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
              + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀
              + lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
        rw [hκeq, iteratedCovGrad_neg, norm_neg]
      rw [hnorm]
      have k1 := lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
          + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)
        (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)
      have k2 := lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg)
        (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)
      have k3 := lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁) (lieArm1LowFix (I := I) (M := M) g₀ g_bg)
      linarith [k1, k2, k3]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hsplit : ∑ q ∈ Finset.range (i + 1),
        (8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2) =
        8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
          4 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit]
    have hBsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 ≤ FB i := le_rfl
    have hAsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤ Fcd i := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
        lieArm1_normSq_icg_lowered_eq (I := I) (M := M) g₀ g₁ q)) ?_
      exact hcdL2 i hi
    have hCsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 ≤ FC i := by
      rw [hFC_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lieArm1_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC q]
      exact lieArm1_appCc12_normSq_le (I := I) (M := M) g₀ (connDiffSection (I := I) g₁ g₀)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P)) q
        (C2b q) Λcd nQ (Fcd q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛcd_nn hnQ_nn hcd0 hWB0 (hcdL2 q hq_le) (hWBsum q hq_le)
        (hC2b q hq_le)
    have hDsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 ≤ FD i := by
      rw [hFD_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lieArm1_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ g_bg
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg) hΨcD q]
      refine lieArm1_appCc12_normSq_le (I := I) (M := M) g₀
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P)) q
        (C2b q) Λfx nQ (Ffx q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛfx_nn hnQ_nn hΛfx hWB0 le_rfl (hWBsum q hq_le)
        (hC2b q hq_le)
    linarith [hAsum, hCsum, hDsum, hBsum]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem lieArm1_psiB_feed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λκ, Fκ, hΛκ_nn, hFκ_nn, hκ⟩ :=
    lieArm1_kappa_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lieArm1_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lieArm1_twoArm_1121_fn (I := I) (M := M) g₀ a
  refine ⟨Λκ * Λsf,
    fun i => ∑ q ∈ Finset.range (i + 1),
      appCcGdiag (E := E) q * (C2b q * (Λsf * Fκ q + Λκ * Fsf q)),
    mul_nonneg hΛκ_nn hΛsf_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hΛsf_nn (hFκ_nn q))
        (mul_nonneg hΛκ_nn (hFsf_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hκ0, hκL2⟩ := hκ g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hsf0, hsfL2⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hdef : lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg =
      appCcRS (I := I) (M := M) g₀ 1 1 2
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
        (sharpFlatEndoCc (I := I) g₀ g₁) := rfl
  have hA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤ Λκ := by
    intro x
    have h := lieArm1_rfns_icg_raiseDomDom_eq (I := I) (M := M) g₀ lieArm1RhoSlot0
      (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) 0 x
    simp only [iteratedCovGrad_zero] at h
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
              (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) := h
      _ ≤ Λκ := hκ0 x
  have hAL2 : ∀ q : ℕ, q ≤ a →
      ∑ n ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
              (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))‖ ^ 2 ≤ Fκ q := by
    intro q hq
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ =>
      lieArm1_normSq_icg_raiseDomDom_eq (I := I) (M := M) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) n)) ?_
    exact hκL2 q hq
  refine ⟨?_, ?_⟩
  · intro x
    rw [hdef, appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
      (show TensorRSSpace 1 2 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
      (show TensorRSSpace 1 1 I x from (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    exact mul_le_mul (hA0 x) (hsf0 x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛκ_nn
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    rw [hdef]
    exact lieArm1_appCc12_normSq_le (I := I) (M := M) g₀
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
      (sharpFlatEndoCc (I := I) g₀ g₁) q
      (C2b q) Λκ Λsf (Fκ q) (Fsf q)
      (hC2b_nn q) hΛκ_nn hΛsf_nn hA0 hsf0 (hAL2 q hq_le) (hsfL2 q hq_le)
      (hC2b q hq_le)

private lemma interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SBundle.Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in

private lemma connDiffFib_toModel_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SBundle.Tensor0SSpace 1 I x) (w : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) om) w =
      Tensor0SBundle.Tensor0SSpace.toModel om
        (fun _ : Fin 1 => (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) (w 1))) := rfl

set_option linter.unusedSectionVars false in

private lemma deTurckLiePairTraceFib_toModel_eval (g₁ gA gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x)
    (w : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLiePairTraceFib (I := I) g₁ σ x
          (metricConnDiffLoweredFib (I := I) g₁ gA gB x) D) w =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr σ
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
            (Tensor0SBundle.Tensor0SSpace.toModel D)
            (Tensor0SBundle.Tensor0SSpace.toModel
              (metricConnDiffLoweredFib (I := I) g₁ gA gB x)))
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)))
            (Fin.cons ((Module.finBasis ℝ E) l)
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) w)))) := by
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply,
    Tensor0SSpace.toModel_ofModel, cometricDoubleTraceFib_toModel,
    cometricDoubleTraceFib_toModel, Tensor0SSpace.toModel_ofModel]
  simp only [modelDoubleTrace_apply]

set_option linter.unusedSectionVars false in

private lemma deTurckLieKoszulTraceFib_toModel_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x)
    (w : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieKoszulTraceFib (I := I) g₀ g₁ σ x D) w =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel D)
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k,
            (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) (w 1))] := by
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    connDiffFib_toModel_eval, cometricDoubleTraceFib_toModel, domDomCongrFibRank_apply,
    Tensor0SSpace.toModel_ofModel, modelDoubleTrace_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine congrArg _ ?_
  funext i
  fin_cases i <;> rfl

set_option linter.unusedSectionVars false in

private lemma deTurckLieArm1CoreFib_toModel_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (a b : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D) ![a, b] =
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![a,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x b ((Module.finBasis ℝ E) l))
              ((Module.finBasis ℝ E) k))
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![a,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                ((Module.finBasis ℝ E) k)) b)
      - Tensor0SBundle.Tensor0SSpace.toModel D
          ![a, b,
            (show E from
              (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                b,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a ((Module.finBasis ℝ E) k))
              ((Module.finBasis ℝ E) l))
      - (∑ k : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b),
              (Module.finBasis ℝ E) k])
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                b,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a ((Module.finBasis ℝ E) l))
              ((Module.finBasis ℝ E) k)) := by
  have hS2 : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermInnerTwo x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![a,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x b ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
    rw [deTurckLiePairTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl)
  have hB : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermCorr x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x) D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![a,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) b := by
    rw [deTurckLiePairTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl)
  have hT2 : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)
        (domDomCongrFibRank (I := I) 3 deTurckLieArm1VecSlotPerm x D)) ![a, b] =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![a, b,
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)] := by
    rw [interior_product_toModel_eval, domDomCongrFibRank_apply,
      Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl)
  have hT3 : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterZero x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              b,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l) := by
    rw [deTurckLiePairTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl)
  have hT4 : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulMidPerm x D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b),
            (Module.finBasis ℝ E) k] := by
    rw [deTurckLieKoszulTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl)
  have hT5 : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterTwo x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              b,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
    rw [deTurckLiePairTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl)
  rw [deTurckLieArm1CoreFib]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hS2, hB, hT2, hT3, hT4, hT5]

set_option linter.unusedSectionVars false in

private lemma deTurckLieArm1CoreFib_toModel_eval' (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (w : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D) w =
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![w 0,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) ((Module.finBasis ℝ E) l))
              ((Module.finBasis ℝ E) k))
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![w 0,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                ((Module.finBasis ℝ E) k)) (w 1))
      - Tensor0SBundle.Tensor0SSpace.toModel D
          ![w 0, w 1,
            (show E from
              (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                w 1,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) ((Module.finBasis ℝ E) k))
              ((Module.finBasis ℝ E) l))
      - (∑ k : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) (w 1)),
              (Module.finBasis ℝ E) k])
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                w 1,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) ((Module.finBasis ℝ E) l))
              ((Module.finBasis ℝ E) k)) := by
  have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hw]
  exact deTurckLieArm1CoreFib_toModel_eval (I := I) g₀ g₁ g_bg x D (w 0) (w 1)

set_option linter.unusedSectionVars false in

private lemma deTurckLieArm1_swapCore_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x
          (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D)) v =
      Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D) ![v 1, v 0] := by
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg (fun t : Fin 2 → E => Tensor0SBundle.Tensor0SSpace.toModel
    (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D) t)
    (by funext i; fin_cases i <;> rfl)

set_option linter.unusedSectionVars false in

private lemma deTurckLieArm1_interiorProduct_eval (g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x) D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![(show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x),
          v 0, v 1] := by
  rw [interior_product_toModel_eval]
  exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
    (by funext i; fin_cases i <;> rfl)

set_option linter.unusedSectionVars false in

private lemma deTurckLieArm1_koszulZero_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulZeroPerm x D) v =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
          ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k] := by
  rw [deTurckLieKoszulTraceFib_toModel_eval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
    (by funext i; fin_cases i <;> rfl)

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix)

set_option linter.unusedSectionVars false in
private lemma lieArm1_omega_eval (g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    om (fun _ : Fin 1 => w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om) w := by
  rw [inverseMetricSharpFib_inner (I := I) g₁ x om w, cotangentToDualLinear_apply,
    cotangentToDual_apply]

set_option linter.unusedSectionVars false in
private lemma lieArm1_psiB_raw (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg).toSection x) om) YZ =
      g₁.inner x
        (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (YZ 1)
          (inverseMetricSharpFib (I := I) g₁ x om)) (YZ 0) := by
  classical
  have hdef : lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg =
      appCcRS (I := I) (M := M) g₀ 1 1 2
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
        (sharpFlatEndoCc (I := I) g₀ g₁) := rfl
  rw [hdef, appCcRS_toSection, ContinuousLinearMap.comp_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
      (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om)) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
        (inverseMetricSharpFib (I := I) g₀ x
          (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [cometricRaiseSlot0Field_toSection]
    rw [cometricRaiseSlot0Fib_clm_apply]]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.inverseMetricSharpFib_g0FlatCLM]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁ x om with hu
  set Xfib : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      (unitTensor (I := I) (M := M) x) with hXfib
  have happ : (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x u Xfib) YZ =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x u Xfib)
        (fun j : Fin 2 => ((YZ j : TangentSpace I x) : E)) := rfl
  rw [happ, interior_product_toModel_eval]
  have hXmodel : Tensor0SSpace.toModel Xfib =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)) x := rfl
  rw [hXmodel, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply,
    lieArm1_kappa_unitModel_apply]
  rfl

private def lieArm1PsiBKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) : TangentSpace I x :=
  cometricLmodel (I := I) g₁ x
    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
      (show E →L[ℝ] ℝ from
        (g₁.inner x v).comp (PDE.DeTurck.connDiff (I := I) g_bg g₁ x w)))

set_option linter.unusedSectionVars false in
private lemma lieArm1PsiBKernel_inner (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    g₁.inner x (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x v w) u =
      g₁.inner x v (PDE.DeTurck.connDiff (I := I) g_bg g₁ x w u) := by
  rw [lieArm1PsiBKernel, cometricLmodel_covectorOfCLM_inner]
  rfl

set_option linter.unusedSectionVars false in
private lemma lieArm1_psiB_hPsi (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg).toSection x) om) YZ =
      om (fun _ : Fin 1 => lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (YZ 0) (YZ 1)) := by
  rw [lieArm1_psiB_raw, lieArm1_omega_eval (I := I) g₁ x om]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (YZ 0) (YZ 1))]
  rw [lieArm1PsiBKernel_inner]
  exact g₁.symm x
    (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (YZ 1)
      (inverseMetricSharpFib (I := I) g₁ x om)) (YZ 0)

set_option linter.unusedSectionVars false in
private lemma lieArm1PsiBKernel_inner_neg (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    g₁.inner x (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x v w) u =
      -(g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x w u) v) := by
  rw [lieArm1PsiBKernel_inner]
  rw [g₁.symm x v (PDE.DeTurck.connDiff (I := I) g_bg g₁ x w u)]
  rw [show PDE.DeTurck.connDiff (I := I) g_bg g₁ x w u =
      -PDE.DeTurck.connDiff (I := I) g₁ g_bg x w u from
    lieArm1_connDiff_antisymm (I := I) (M := M) g_bg g₁ x w u]
  rw [map_neg (g₁.inner x) (PDE.DeTurck.connDiff (I := I) g₁ g_bg x w u)]
  rw [ContinuousLinearMap.neg_apply]

set_option linter.unusedSectionVars false in
private lemma lieArm1_cometric_collapse_full (g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x w ((Module.finBasis ℝ E) k) •
          (show TangentSpace I x from
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) = w :=
  lieArm1_cometric_collapse (I := I) g₁ x w

set_option linter.unusedSectionVars false in
private lemma lieArm1_slot2_collapse (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c₀ c₁ : E) (X : TangentSpace I x) :
    Tensor0SSpace.toModel D ![c₀, c₁, (show E from X)] =
      ∑ j : Fin (Module.finrank ℝ E),
        g₁.inner x X ((Module.finBasis ℝ E) j) *
          Tensor0SSpace.toModel D
            ![c₀, c₁,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j))] := by
  classical
  have hupd : ∀ z : E, (![c₀, c₁, z] : Fin 3 → E) =
      Function.update ![c₀, c₁, (0 : E)] 2 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hstep1 : Tensor0SSpace.toModel D ![c₀, c₁, (show E from X)] =
      Tensor0SSpace.toModel D (Function.update ![c₀, c₁, (0 : E)] 2
        (show E from (∑ j : Fin (Module.finrank ℝ E),
          g₁.inner x X ((Module.finBasis ℝ E) j) •
            (show TangentSpace I x from
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j))) : TangentSpace I x))) := by
    refine Eq.trans (congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (hupd (show E from X))) ?_
    exact congrArg
      (fun z : TangentSpace I x =>
        Tensor0SSpace.toModel D (Function.update ![c₀, c₁, (0 : E)] 2 (show E from z)))
      (lieArm1_cometric_collapse_full (I := I) g₁ x X).symm
  rw [hstep1]
  have hms := ((Tensor0SSpace.toModel D).toMultilinearMap).map_update_sum
    (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := (2 : Fin 3))
    (g := fun j : Fin (Module.finrank ℝ E) =>
      g₁.inner x X ((Module.finBasis ℝ E) j) •
        (show E from
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j))))
    (m := ![c₀, c₁, (0 : E)])
  simp only [ContinuousMultilinearMap.coe_coe] at hms
  rw [hms]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(Tensor0SSpace.toModel D).map_update_smul ![c₀, c₁, (0 : E)] 2
    (g₁.inner x X ((Module.finBasis ℝ E) j))
    (show E from
      cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis j)))]
  rw [smul_eq_mul]
  refine congrArg (fun r : ℝ => g₁.inner x X ((Module.finBasis ℝ E) j) * r) ?_
  exact congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
    (hupd (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis j)))).symm

set_option linter.unusedSectionVars false in
private lemma lieArm1_slot0_collapse (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c₁ c₂ : E) (X : TangentSpace I x) :
    Tensor0SSpace.toModel D ![(show E from X), c₁, c₂] =
      ∑ j : Fin (Module.finrank ℝ E),
        g₁.inner x X ((Module.finBasis ℝ E) j) *
          Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j)),
              c₁, c₂] := by
  classical
  have hupd : ∀ z : E, (![z, c₁, c₂] : Fin 3 → E) =
      Function.update ![(0 : E), c₁, c₂] 0 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hstep1 : Tensor0SSpace.toModel D ![(show E from X), c₁, c₂] =
      Tensor0SSpace.toModel D (Function.update ![(0 : E), c₁, c₂] 0
        (show E from (∑ j : Fin (Module.finrank ℝ E),
          g₁.inner x X ((Module.finBasis ℝ E) j) •
            (show TangentSpace I x from
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j))) : TangentSpace I x))) := by
    refine Eq.trans (congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (hupd (show E from X))) ?_
    exact congrArg
      (fun z : TangentSpace I x =>
        Tensor0SSpace.toModel D (Function.update ![(0 : E), c₁, c₂] 0 (show E from z)))
      (lieArm1_cometric_collapse_full (I := I) g₁ x X).symm
  rw [hstep1]
  have hms := ((Tensor0SSpace.toModel D).toMultilinearMap).map_update_sum
    (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := (0 : Fin 3))
    (g := fun j : Fin (Module.finrank ℝ E) =>
      g₁.inner x X ((Module.finBasis ℝ E) j) •
        (show E from
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j))))
    (m := ![(0 : E), c₁, c₂])
  simp only [ContinuousMultilinearMap.coe_coe] at hms
  rw [hms]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(Tensor0SSpace.toModel D).map_update_smul ![(0 : E), c₁, c₂] 0
    (g₁.inner x X ((Module.finBasis ℝ E) j))
    (show E from
      cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis j)))]
  rw [smul_eq_mul]
  refine congrArg (fun r : ℝ => g₁.inner x X ((Module.finBasis ℝ E) j) * r) ?_
  exact congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
    (hupd (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis j)))).symm

set_option linter.unusedSectionVars false in
private lemma lieArm1_cometricTrace_eq_chartInvGram (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l •
          F ((chartModelBasis E) l) ((chartModelBasis E) k) := by
  classical
  set L₁ : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (cometricLmodel (I := I) g₁ x).comp
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)) with hL₁
  set F' : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := F.comp L₁ with hF'
  have hFapp : ∀ (φ : E →L[ℝ] ℝ) (v : E),
      F' φ v = F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) v := by
    intro φ v
    rfl
  have htrace :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cDualBasis_trace_basis_indep
      (E := E) (chartModelBasis E) F').symm
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        F' ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => (hFapp _ _).symm)]
  rw [htrace]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hFapp ((chartModelBasis E).cDualBasis k) (chartModelBasis E k)]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum
    (I := I) g₁ x k]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply]

set_option linter.unusedSectionVars false in
private lemma lieArm1_deTurckVF_cometric_trace (g₁ gB : SmoothRiemannianMetric I M) (x : M) :
    (∑ k : Fin (Module.finrank ℝ E),
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) : TangentSpace I x)) =
      (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
        Π y : M, TangentSpace I y) x := by
  classical
  refine lieArm1_metricInner_injective (I := I) g₁ x (fun u => ?_)
  set F : E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E E ℝ
        (show E →L[ℝ] ℝ from (g₁.inner x u : TangentSpace I x →L[ℝ] ℝ))).comp
      (show E →L[ℝ] E →L[ℝ] E from
        (PDE.DeTurck.connDiff (I := I) g₁ gB x :
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)) with hFdef
  have h1 : g₁.inner x
      (∑ k : Fin (Module.finrank ℝ E),
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) : TangentSpace I x)) u =
      ∑ k : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) := by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [g₁.symm x _ u]
    rfl
  rw [h1, lieArm1_cometricTrace_eq_chartInvGram (I := I) g₁ x F]
  have h2 : ∀ k l : Fin (Module.finrank ℝ E),
      F ((chartModelBasis E) l) ((chartModelBasis E) k) =
        F ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    intro k l
    change (g₁.inner x u : TangentSpace I x →L[ℝ] ℝ)
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          ((chartModelBasis E) l) ((chartModelBasis E) k)) =
      (g₁.inner x u : TangentSpace I x →L[ℝ] ℝ)
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          ((chartModelBasis E) k) ((chartModelBasis E) l))
    rw [PDE.DeTurck.connDiff_symm (I := I) g₁ gB x
      ((chartModelBasis E) l) ((chartModelBasis E) k)]
  have h3 : g₁.inner x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x) u =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l •
          F ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    rw [show ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x) =
        (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x from rfl]
    rw [PDE.DeTurck.deTurckVF_apply_eq (I := I) g₁ gB x]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply]
    rw [chartBasisVecFiber_self (I := I) x k, chartBasisVecFiber_self (I := I) x l]
    refine congrArg (fun r : ℝ =>
      chartInvGramMatrix (I := I) g₁ x x k l • r) ?_
    rw [g₁.symm x _ u]
    rfl
  rw [h3]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [h2 k l]

set_option linter.unusedSectionVars false in
private lemma lieArm1_slot2_vf_trace (g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c₀ c₁ : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![c₀, c₁,
            (show E from
              (PDE.DeTurck.connDiff (I := I) g₁ gB x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) k) : TangentSpace I x))]) =
      Tensor0SSpace.toModel D
        ![c₀, c₁,
          (show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x))] := by
  classical
  have hupd : ∀ z : E, (![c₀, c₁, z] : Fin 3 → E) =
      Function.update ![c₀, c₁, (0 : E)] 2 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hms := ((Tensor0SSpace.toModel D).toMultilinearMap).map_update_sum
    (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := (2 : Fin 3))
    (g := fun k : Fin (Module.finrank ℝ E) =>
      (show E from
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) : TangentSpace I x)))
    (m := ![c₀, c₁, (0 : E)])
  simp only [ContinuousMultilinearMap.coe_coe] at hms
  calc (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![c₀, c₁,
            (show E from
              (PDE.DeTurck.connDiff (I := I) g₁ gB x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) k) : TangentSpace I x))])
      = ∑ k : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel D
            (Function.update ![c₀, c₁, (0 : E)] 2
              (show E from
                (PDE.DeTurck.connDiff (I := I) g₁ gB x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ((Module.finBasis ℝ E) k) : TangentSpace I x))) :=
        Finset.sum_congr rfl (fun k _ =>
          congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t) (hupd _))
    _ = Tensor0SSpace.toModel D
          (Function.update ![c₀, c₁, (0 : E)] 2
            (show E from
              (∑ k : Fin (Module.finrank ℝ E),
                (PDE.DeTurck.connDiff (I := I) g₁ gB x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ((Module.finBasis ℝ E) k) : TangentSpace I x) : TangentSpace I x))) :=
        hms.symm
    _ = Tensor0SSpace.toModel D
          (Function.update ![c₀, c₁, (0 : E)] 2
            (show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x))) :=
        congrArg
          (fun z : TangentSpace I x =>
            Tensor0SSpace.toModel D
              (Function.update ![c₀, c₁, (0 : E)] 2 (show E from z)))
          (lieArm1_deTurckVF_cometric_trace (I := I) (M := M) g₁ gB x)
    _ = Tensor0SSpace.toModel D
          ![c₀, c₁,
            (show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x))] :=
        (congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t) (hupd _)).symm

set_option linter.unusedSectionVars false in
private lemma lieArm1_slot0_vf_trace (g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c₁ c₂ : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![(show E from
              (PDE.DeTurck.connDiff (I := I) g₁ gB x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) k) : TangentSpace I x)),
            c₁, c₂]) =
      Tensor0SSpace.toModel D
        ![(show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x)),
          c₁, c₂] := by
  classical
  have hupd : ∀ z : E, (![z, c₁, c₂] : Fin 3 → E) =
      Function.update ![(0 : E), c₁, c₂] 0 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hms := ((Tensor0SSpace.toModel D).toMultilinearMap).map_update_sum
    (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := (0 : Fin 3))
    (g := fun k : Fin (Module.finrank ℝ E) =>
      (show E from
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) : TangentSpace I x)))
    (m := ![(0 : E), c₁, c₂])
  simp only [ContinuousMultilinearMap.coe_coe] at hms
  calc (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![(show E from
              (PDE.DeTurck.connDiff (I := I) g₁ gB x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) k) : TangentSpace I x)),
            c₁, c₂])
      = ∑ k : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel D
            (Function.update ![(0 : E), c₁, c₂] 0
              (show E from
                (PDE.DeTurck.connDiff (I := I) g₁ gB x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ((Module.finBasis ℝ E) k) : TangentSpace I x))) :=
        Finset.sum_congr rfl (fun k _ =>
          congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t) (hupd _))
    _ = Tensor0SSpace.toModel D
          (Function.update ![(0 : E), c₁, c₂] 0
            (show E from
              (∑ k : Fin (Module.finrank ℝ E),
                (PDE.DeTurck.connDiff (I := I) g₁ gB x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ((Module.finBasis ℝ E) k) : TangentSpace I x) : TangentSpace I x))) :=
        hms.symm
    _ = Tensor0SSpace.toModel D
          (Function.update ![(0 : E), c₁, c₂] 0
            (show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x))) :=
        congrArg
          (fun z : TangentSpace I x =>
            Tensor0SSpace.toModel D
              (Function.update ![(0 : E), c₁, c₂] 0 (show E from z)))
          (lieArm1_deTurckVF_cometric_trace (I := I) (M := M) g₁ gB x)
    _ = Tensor0SSpace.toModel D
          ![(show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x)),
            c₁, c₂] :=
        (congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t) (hupd _)).symm

set_option linter.unusedSectionVars false in
private lemma lieArm1_neg_double_sum (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), -(f k l)) =
      -∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), f k l := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_neg_distrib]

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p1 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel D
        ![(show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x)),
          ((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E)] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
    (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g_bg y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g_bg x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![(show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ((Module.finBasis ℝ E) k) : TangentSpace I x)),
          ((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E)])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  exact lieArm1_slot0_vf_trace (I := I) (M := M) g₁ g_bg x D
    ((m 0 : TangentSpace I x) : E) ((m 1 : TangentSpace I x) : E)

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p2 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((m 0 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 0 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        ((m 0 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k)))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p3 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      -∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((m 0 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) (m 1) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
    (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
    (fun y u v => lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg y u v) x
    (fun om YZ => lieArm1_psiB_hPsi (I := I) (M := M) g₀ g₁ g_bg x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 0 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (show E from
            (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 1)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x
          (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 1) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        ((m 0 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 1)
          ((Module.finBasis ℝ E) k)))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      -(Tensor0SSpace.toModel D
          ![((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))] *
        g₁.inner x
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) k)
            ((Module.finBasis ℝ E) j)) (m 1)))
    (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => by
      rw [lieArm1PsiBKernel_inner_neg (I := I) (M := M) g₁ g_bg x (m 1)
        ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) j)]
      ring))) ?_
  rw [Finset.sum_comm]
  exact lieArm1_neg_double_sum (E := E) _

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p4 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel D
        ![((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E),
          (show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x))] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  exact lieArm1_slot2_vf_trace (I := I) (M := M) g₁ g₀ x D
    ((m 0 : TangentSpace I x) : E) ((m 1 : TangentSpace I x) : E)

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p5 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              ((m 1 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![(show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0)
              ((Module.finBasis ℝ E) k) : TangentSpace I x)),
          ((m 1 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j)),
            ((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot0_collapse (I := I) (M := M) g₁ x D
        ((m 1 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k)))) ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p6 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (show E from
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) : TangentSpace I x)),
            ((Module.finBasis ℝ E) k)] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  exact Finset.sum_congr rfl (fun k _ =>
    congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl))

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p7 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              ((m 1 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          ((m 1 : TangentSpace I x) : E),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            ((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((m 1 : TangentSpace I x) : E)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k)))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p8 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((m 1 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 1 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        ((m 1 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k)))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p9 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      -∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((m 1 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) (m 0) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
    (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
    (fun y u v => lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg y u v) x
    (fun om YZ => lieArm1_psiB_hPsi (I := I) (M := M) g₀ g₁ g_bg x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 1 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (show E from
            (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 0)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x
          (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 0) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        ((m 1 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 0)
          ((Module.finBasis ℝ E) k)))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      -(Tensor0SSpace.toModel D
          ![((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))] *
        g₁.inner x
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) k)
            ((Module.finBasis ℝ E) j)) (m 0)))
    (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => by
      rw [lieArm1PsiBKernel_inner_neg (I := I) (M := M) g₁ g_bg x (m 0)
        ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) j)]
      ring))) ?_
  rw [Finset.sum_comm]
  exact lieArm1_neg_double_sum (E := E) _

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p10 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel D
        ![((m 1 : TangentSpace I x) : E), ((m 0 : TangentSpace I x) : E),
          (show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x))] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 1 : TangentSpace I x) : E), ((m 0 : TangentSpace I x) : E),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  exact lieArm1_slot2_vf_trace (I := I) (M := M) g₁ g₀ x D
    ((m 1 : TangentSpace I x) : E) ((m 0 : TangentSpace I x) : E)

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p11 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              ((m 0 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![(show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1)
              ((Module.finBasis ℝ E) k) : TangentSpace I x)),
          ((m 0 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j)),
            ((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot0_collapse (I := I) (M := M) g₁ x D
        ((m 0 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k)))) ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p12 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (show E from
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) (m 0) : TangentSpace I x)),
            ((Module.finBasis ℝ E) k)] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  exact Finset.sum_congr rfl (fun k _ =>
    congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl))

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p13 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              ((m 0 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          ((m 0 : TangentSpace I x) : E),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            ((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((m 0 : TangentSpace I x) : E)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k)))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm1_match_p14 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![(show E from
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) : TangentSpace I x)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            ((Module.finBasis ℝ E) k)] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  exact Finset.sum_congr rfl (fun k _ =>
    congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl))

set_option linter.unusedSectionVars false in
private theorem lieArm1_coeff_pieces_pointwise (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
            + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀)
              + lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
                (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
              - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀)
              - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
                (connDiffSection (I := I) g₁ g₀)
              - lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
                (connDiffSection (I := I) g₁ g₀)
              - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀))
            + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀)
              + lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
                (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
              - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀)
              - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
                (connDiffSection (I := I) g₁ g₀)
              - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
                (connDiffSection (I := I) g₁ g₀)
              - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀))
            + lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
                (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) := by
  classical
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D)
      (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel D
          ![(show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x)),
            ((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E)]
        + ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              Tensor0SSpace.toModel D
                  ![((m 0 : TangentSpace I x) : E),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) l))
                  ((Module.finBasis ℝ E) k))
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![((m 0 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                      ((Module.finBasis ℝ E) k)) (m 1))
            - Tensor0SSpace.toModel D
                ![((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E),
                  (show E from
                    ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x))]
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      ((m 1 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
                    ((Module.finBasis ℝ E) l))
            - (∑ k : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                  ![cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)),
                    (show E from
                      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) :
                        TangentSpace I x)),
                    ((Module.finBasis ℝ E) k)])
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      ((m 1 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) l))
                    ((Module.finBasis ℝ E) k)))
        + ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              Tensor0SSpace.toModel D
                  ![((m 1 : TangentSpace I x) : E),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) l))
                  ((Module.finBasis ℝ E) k))
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![((m 1 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                      ((Module.finBasis ℝ E) k)) (m 0))
            - Tensor0SSpace.toModel D
                ![((m 1 : TangentSpace I x) : E), ((m 0 : TangentSpace I x) : E),
                  (show E from
                    ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x))]
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      ((m 0 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
                    ((Module.finBasis ℝ E) l))
            - (∑ k : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                  ![cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)),
                    (show E from
                      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) (m 0) :
                        TangentSpace I x)),
                    ((Module.finBasis ℝ E) k)])
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      ((m 0 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) l))
                    ((Module.finBasis ℝ E) k)))
        + ∑ k : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel D
              ![(show E from
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) : TangentSpace I x)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                ((Module.finBasis ℝ E) k)] := by
    rw [show (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
      deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x D from rfl]
    rw [deTurckLieArm1Fib]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
    rw [deTurckLieArm1_interiorProduct_eval, deTurckLieArm1CoreFib_toModel_eval',
      deTurckLieArm1_swapCore_eval, deTurckLieArm1CoreFib_toModel_eval,
      deTurckLieArm1_koszulZero_eval]
  rw [hL]
  have hR : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
          + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            + lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀))
          + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            + lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀))
          + lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)).toSection x) D)
      (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
            (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
          (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
        + (Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          + Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
                  (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E)))
        + (Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          + Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
                  (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E)))
        + Tensor0SSpace.toModel
            ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
              (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
                (connDiffSection (I := I) g₁ g₀)).toSection x) D)
            (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) := by
    simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply]
    rfl
  rw [hR]
  rw [lieArm1_match_p1 (I := I) (M := M) g₀ g₁ g_bg x D m,
    lieArm1_match_p2 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p3 (I := I) (M := M) g₀ g₁ g_bg x D m,
    lieArm1_match_p4 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p5 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p6 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p7 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p8 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p9 (I := I) (M := M) g₀ g₁ g_bg x D m,
    lieArm1_match_p10 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p11 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p12 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p13 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p14 (I := I) (M := M) g₀ g₁ x D m]
  ring

theorem deTurckLieArm1Coeff_eq_lieArm1Piece_sum (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg =
      lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
        + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          + lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          + lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hCLM : ∀ D : Tensor0SSpace 3 I x,
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
          + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            + lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀))
          + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            + lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
              (connDiffSection (I := I) g₁ g₀)
            - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀))
          + lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)).toSection x) D := by
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ) (I := I) (s := 2) (x := x)
    change Tensor0SSpace.toModel _ = Tensor0SSpace.toModel _
    apply ContinuousMultilinearMap.ext
    intro w
    exact lieArm1_coeff_pieces_pointwise (I := I) (M := M) g₀ g₁ g_bg x D
      (fun j : Fin 2 => ((w j : E) : TangentSpace I x))
  exact ContinuousLinearMap.ext hCLM

set_option linter.unusedVariables false in
theorem lieArm1Piece_connDiff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2 ≤
            P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨C2, hC2_nn, hC2⟩ := lieArm1_twoArm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => appCcGdiag (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * Λcd) * (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Fcd i))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · exact mul_nonneg (mul_nonneg (by positivity) hΛcd_nn)
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · exact mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (hFcd_nn i))
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hcd0, hcdL2⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieArm1_normSq_icg_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              g₀))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hcd0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * Fcd i := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hcdL2 i hi) (by positivity)
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd))
        (∑ n ∈ Finset.range (i + 1), Q n) ((Module.finrank ℝ E : ℝ) ^ 2 * Fcd i)
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
  · haveI hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)))
    rw [h0]
    norm_num

set_option linter.unusedVariables false in
theorem lieArm1Piece_connDiffBg_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
    obtain ⟨C2, hC2_nn, hC2⟩ := lieArm1_twoArm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => appCcGdiag (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)) *
            (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i +
              2 * ∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2)))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · refine mul_nonneg (mul_nonneg (by positivity) (by linarith))
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · refine mul_nonneg hΛcom_nn (mul_nonneg (by positivity) ?_)
        have h1 : (0 : ℝ) ≤ Fcd i := hFcd_nn i
        have h2 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 :=
          Finset.sum_nonneg fun l _ => sq_nonneg _
        linarith
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hcd0, hcdL2⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hΨ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((lieArm1ConnDiffBgCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
          2 * Λcd + 2 * Λfx := by
        intro x
        rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
        refine le_trans (lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 1 2 _ _ x) ?_
        have h1 := hcd0 x
        have h2 := hΛfx x
        linarith
      have hΨL2 : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 l
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
          2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 +
              2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := by
          intro l _
          rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
          exact lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 1 2 l _ _
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have h1 := mul_le_mul_of_nonneg_left (hcdL2 i hi) (by norm_num : (0:ℝ) ≤ 2)
        linarith
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieArm1_normSq_icg_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hΨ0_nn : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx))) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hΨ0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hΨL2 (by positivity)
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom)
        (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)))
        (∑ n ∈ Finset.range (i + 1), Q n)
        ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 l
            (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2))
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom)
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
  · haveI hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
    rw [h0]
    norm_num

set_option linter.unusedVariables false in
theorem lieArm1Piece_psiB_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1PsiB (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λpb, Fpb, hΛpb_nn, hFpb_nn, hpb⟩ :=
      lieArm1_psiB_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
    obtain ⟨C2, hC2_nn, hC2⟩ := lieArm1_twoArm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => appCcGdiag (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * Λpb) * (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Fpb i))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · exact mul_nonneg (mul_nonneg (by positivity) hΛpb_nn)
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · exact mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (hFpb_nn i))
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hpb0, hpbL2⟩ := hpb (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieArm1_normSq_icg_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (lieArm1PsiB (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hpb0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (lieArm1PsiB (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * Fpb i := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hpbL2 i hi) (by positivity)
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (lieArm1PsiB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb))
        (∑ n ∈ Finset.range (i + 1), Q n) ((Module.finrank ℝ E : ℝ) ^ 2 * Fpb i)
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
  · haveI hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (lieArm1PsiB (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
    rw [h0]
    norm_num

set_option linter.unusedVariables false in
theorem lieArm1Piece_connDiff_realizedFam_rfns_order0_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
                  g₀)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) hΛcd_nn), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    haveI := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hcd0, _⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieArm1_piece_rfns_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieArm1_rfns_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            g₀).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Λcd :=
      mul_le_mul_of_nonneg_left (hcd0 x) (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · haveI hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

set_option linter.unusedVariables false in
theorem lieArm1Piece_connDiffBg_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (by linarith)), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    haveI := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hcd0, _⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieArm1_piece_rfns_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieArm1_rfns_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have hΨ0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((lieArm1ConnDiffBgCc (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        2 * Λcd + 2 * Λfx := by
      rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
      refine le_trans (lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 1 2 _ _ x) ?_
      have h2 := hcd0 x
      have h3 := hΛfx x
      linarith
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((lieArm1ConnDiffBgCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx) :=
      mul_le_mul_of_nonneg_left hΨ0 (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · haveI hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

set_option linter.unusedVariables false in
theorem lieArm1Piece_psiB_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1PsiB (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λpb, Fpb, hΛpb_nn, hFpb_nn, hpb⟩ :=
      lieArm1_psiB_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) hΛpb_nn), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    haveI := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hpb0, _⟩ := hpb (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieArm1_piece_rfns_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (lieArm1PsiB (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieArm1_rfns_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((lieArm1PsiB (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Λpb :=
      mul_le_mul_of_nonneg_left (hpb0 x) (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · haveI hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

private theorem lieArm1_norm_block6_le {V : Type*} [SeminormedAddCommGroup V]
    (b1 b2 b3 b4 b5 b6 : V) :
    ‖b1 - b2 - b3 - b4 - b5 - b6‖ ≤ ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by
  calc ‖b1 - b2 - b3 - b4 - b5 - b6‖
      ≤ ‖b1 - b2 - b3 - b4 - b5‖ + ‖b6‖ := norm_sub_le _ _
    _ ≤ (‖b1 - b2 - b3 - b4‖ + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2 - b3 - b4) b5
        linarith
    _ ≤ ((‖b1 - b2 - b3‖ + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2 - b3) b4
        linarith
    _ ≤ (((‖b1 - b2‖ + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2) b3
        linarith
    _ ≤ ((((‖b1‖ + ‖b2‖) + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le b1 b2
        linarith
    _ = ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by ring

private theorem lieArm1_norm_block6_le' {V : Type*} [SeminormedAddCommGroup V]
    (b1 b2 b3 b4 b5 b6 : V) :
    ‖b1 + b2 - b3 - b4 - b5 - b6‖ ≤ ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by
  calc ‖b1 + b2 - b3 - b4 - b5 - b6‖
      ≤ ‖b1 + b2 - b3 - b4 - b5‖ + ‖b6‖ := norm_sub_le _ _
    _ ≤ (‖b1 + b2 - b3 - b4‖ + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2 - b3 - b4) b5
        linarith
    _ ≤ ((‖b1 + b2 - b3‖ + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2 - b3) b4
        linarith
    _ ≤ (((‖b1 + b2‖ + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2) b3
        linarith
    _ ≤ ((((‖b1‖ + ‖b2‖) + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_add_le b1 b2
        linarith
    _ = ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by ring

private theorem lieArm1_norm_sq_le_of_norm_le {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {S : ℝ} (h : ‖v‖ ≤ S) : ‖v‖ ^ 2 ≤ S ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg v) h 2

private theorem lieArm1_norm_le_sqrt {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {P : ℝ} (h : ‖v‖ ^ 2 ≤ P) : ‖v‖ ≤ Real.sqrt P := by
  have h1 : ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
  rw [h1]
  exact Real.sqrt_le_sqrt h

set_option linter.unusedVariables false in
theorem deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieArm1Coeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  obtain ⟨Pc, hPc_nn, hPc⟩ :=
    lieArm1Piece_connDiff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Pbg, hPbg_nn, hPbg⟩ :=
    lieArm1Piece_connDiffBg_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Pb, hPb_nn, hPb⟩ :=
    lieArm1Piece_psiB_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨fun i => (11 * Real.sqrt (Pc i) + 2 * Real.sqrt (Pb i) + Real.sqrt (Pbg i)) ^ 2,
    fun i => sq_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ (connDiffSection (I := I) g₁ g₀))‖ ≤
        Real.sqrt (Pc i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  have hbg : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pbg i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pb i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg]
  simp only [iteratedCovGrad_add, iteratedCovGrad_sub]
  refine lieArm1_norm_sq_le_of_norm_le ?_
  have hsqrtPc_nn : 0 ≤ Real.sqrt (Pc i) := Real.sqrt_nonneg _
  have hsqrtPb_nn : 0 ≤ Real.sqrt (Pb i) := Real.sqrt_nonneg _
  have hblock1 := lieArm1_norm_block6_le'
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have hblock2 := lieArm1_norm_block6_le'
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have htri1 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
  have htri2 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have htri3 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have h1 := hcd lieArm1SigmaA (Equiv.refl (Fin 3))
  have h2 := hpb lieArm1SigmaA (Equiv.refl (Fin 3))
  have h3 := hcd lieArm1SigmaC (Equiv.refl (Fin 3))
  have h4 := hcd lieArm1SigmaD lieArm1RhoSlot0
  have h5 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have h6 := hcd lieArm1SigmaF (Equiv.refl (Fin 3))
  have h7 := hcd lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h8 := hpb lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h9 := hcd lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have h10 := hcd lieArm1SigmaDSwap lieArm1RhoSlot0
  have h11 := hcd lieArm1SigmaESwap lieArm1RhoSlot1
  have h12 := hcd lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have h13 := hbg lieArm1SigmaC lieArm1RhoSlot0
  have h14 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  linarith [htri1, htri2, htri3, hblock1, hblock2]

private theorem lieArm1_rfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  rw [sub_eq_add_neg]
  have h := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)
  rw [lieArm1_rfns_neg (I := I) (M := M) g r s x b] at h
  exact h

private theorem lieArm1_rfns_block6_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (b1 b2 b3 b4 b5 b6 : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (b1 - b2 - b3 - b4 - b5 - b6) ≤
      32 * riemannianFiberNormSq (I := I) (M := M) g r s x b1 +
        32 * riemannianFiberNormSq (I := I) (M := M) g r s x b2 +
        16 * riemannianFiberNormSq (I := I) (M := M) g r s x b3 +
        8 * riemannianFiberNormSq (I := I) (M := M) g r s x b4 +
        4 * riemannianFiberNormSq (I := I) (M := M) g r s x b5 +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b6 := by
  have h6 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3 - b4 - b5) b6
  have h5 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3 - b4) b5
  have h4 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3) b4
  have h3 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2) b3
  have h2 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x b1 b2
  have hn5 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b5
  have hn6 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b6
  linarith

private theorem lieArm1_rfns_block6_le' (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (b1 b2 b3 b4 b5 b6 : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (b1 + b2 - b3 - b4 - b5 - b6) ≤
      32 * riemannianFiberNormSq (I := I) (M := M) g r s x b1 +
        32 * riemannianFiberNormSq (I := I) (M := M) g r s x b2 +
        16 * riemannianFiberNormSq (I := I) (M := M) g r s x b3 +
        8 * riemannianFiberNormSq (I := I) (M := M) g r s x b4 +
        4 * riemannianFiberNormSq (I := I) (M := M) g r s x b5 +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b6 := by
  have h6 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3 - b4 - b5) b6
  have h5 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3 - b4) b5
  have h4 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3) b4
  have h3 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 + b2) b3
  have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x b1 b2
  have hn5 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b5
  have hn6 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b6
  linarith

set_option linter.unusedVariables false in
theorem deTurckLieArm1Coeff_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieArm1Coeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λc, hΛc_nn, hΛc⟩ :=
    lieArm1Piece_connDiff_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Λbg, hΛbg_nn, hΛbg⟩ :=
    lieArm1Piece_connDiffBg_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Λb, hΛb_nn, hΛb⟩ :=
    lieArm1Piece_psiB_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨8 * Λbg + 800 * Λc + 400 * Λb, by linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ
          (connDiffSection (I := I) g₁ g₀)).toSection x) ≤ Λc := fun σ' ρ =>
    hΛc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ s hs x
  have hbg : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
      ((lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λbg :=
    hΛbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball lieArm1SigmaC lieArm1RhoSlot0 s hs x
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((lieArm1Piece (I := I) (M := M) g₀ g₁ σ' (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λb := fun σ' =>
    hΛb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' (Equiv.refl (Fin 3)) s hs x
  have hsec := congrArg (fun (W : SmoothCcTensor g₀ 3 2) =>
      (show TensorRSSpace 3 2 I x from W.toSection x))
    (deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg)
  simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply] at hsec
  rw [hsec]
  set A := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set B1 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B2 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set B3 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B4 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B5 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B6 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C1 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C2 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set C3 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C4 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C5 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C6 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set Dz := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  have houter1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    (A + (B1 + B2 - B3 - B4 - B5 - B6) + (C1 + C2 - C3 - C4 - C5 - C6)) Dz
  have houter2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    (A + (B1 + B2 - B3 - B4 - B5 - B6)) (C1 + C2 - C3 - C4 - C5 - C6)
  have houter3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    A (B1 + B2 - B3 - B4 - B5 - B6)
  have hblkB := lieArm1_rfns_block6_le' (I := I) (M := M) g₀ 3 2 x B1 B2 B3 B4 B5 B6
  have hblkC := lieArm1_rfns_block6_le' (I := I) (M := M) g₀ 3 2 x C1 C2 C3 C4 C5 C6
  have e1 := hcd lieArm1SigmaA (Equiv.refl (Fin 3))
  have e2 := hpb lieArm1SigmaA
  have e3 := hcd lieArm1SigmaC (Equiv.refl (Fin 3))
  have e4 := hcd lieArm1SigmaD lieArm1RhoSlot0
  have e5 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have e6 := hcd lieArm1SigmaF (Equiv.refl (Fin 3))
  have e7 := hcd lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have e8 := hpb lieArm1SigmaASwap
  have e9 := hcd lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have e10 := hcd lieArm1SigmaDSwap lieArm1RhoSlot0
  have e11 := hcd lieArm1SigmaESwap lieArm1RhoSlot1
  have e12 := hcd lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have e14 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  linarith [houter1, houter2, houter3, hblkB, hblkC, hbg, hΛc_nn, hΛb_nn, hΛbg_nn]

end DifferentialGeometry.Integral.Connection

end
