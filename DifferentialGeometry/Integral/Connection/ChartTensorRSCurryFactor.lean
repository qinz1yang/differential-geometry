import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Integral.Connection.Tensor0SChartParallelExtend
import DifferentialGeometry.Integral.Connection.Tensor0SIntrinsicChartCurryFactor

/-!
# Curry factorisation of the intrinsic chart Fréchet derivative on `(r, s)`-tensors

Given a smooth Riemannian manifold `(M, g)` modelled on `(E, H)` with model
`I`, a chart-centre `α : M`, a base point `b : M` on the chart-Levi-Civita
good set, a tangent vector field `X`, an `(r, s)`-tensor section `T`, and an
input `(0, r)`-tensor `α_input : Tensor0SSpace r I b`, the chart intrinsic
Fréchet derivative CLM
`tensorRSIntrinsicChartCLM r s α T b : TangentSpace I b →L[ℝ] TensorRSSpace r s I b`
applied to a vector `X b` and then evaluated at `α_input` admits a clean
factorisation through the `(0, s)`-tensor partial evaluation.

Mechanism: the chart-α-trivialised representation of `T` at `b'`, applied to
the constant model-fibre value
`D_α := e_r.continuousLinearMapAt b α_input`, equals the chart-α-trivialised
representation at `b'` of the partially-evaluated `(0, s)`-tensor section
`b' ↦ T b' (chartTensor0SParallelExtend r α b α_input b')`. The
chart-parallel extension is locally constant after the trivialisation, so the
Fréchet derivative of the partial-eval representation factors through the
"evaluate at `D_α`" CLM applied to the Fréchet derivative of the
`(r, s)`-representation.

## Main results

* `tensorPartialEval r s T w` — the partial evaluation of a `(r, s)`-tensor
  section at a `(0, r)`-tensor section, viewed at the bundle level.
* `tensorRSIntrinsicChartCLM_factor_via_tensorPartialEval` — the headline
  factorisation theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle Set Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- The pointwise partial evaluation of an `(r, s)`-tensor section `T` at a
`(0, r)`-tensor section `w`. At a point `b ∈ M`, this is the value of `T b`
(viewed as a CLM `Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b`) applied to
`w b ∈ Tensor0SSpace r I b`. -/
noncomputable def tensorPartialEval (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (w : Π b : M, Tensor0SSpace r I b) :
    Π b : M, Tensor0SSpace s I b :=
  fun b => (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) (w b)

/-- Pointwise unfolding of `tensorPartialEval`. -/
@[simp] lemma tensorPartialEval_apply (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (w : Π b : M, Tensor0SSpace r I b) (b : M) :
    tensorPartialEval (I := I) (M := M) r s T w b =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) (w b) := rfl

/-- The "evaluate at a fixed `(0, r)`-tensor model input" CLM: sends a model
fibre `D : TensorRSModel r s ℝ E` to `D D_α ∈ Tensor0SModel s ℝ E`. -/
noncomputable def tensorRSEvalAtCLM (r s : ℕ) (D_α : Tensor0SModel r ℝ E) :
    TensorRSModel r s ℝ E →L[ℝ] Tensor0SModel s ℝ E :=
  ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) D_α

@[simp] lemma tensorRSEvalAtCLM_apply (r s : ℕ) (D_α : Tensor0SModel r ℝ E)
    (D : TensorRSModel r s ℝ E) :
    tensorRSEvalAtCLM (E := E) r s D_α D = D D_α := by
  classical
  unfold tensorRSEvalAtCLM
  rfl

/-- On the chart-α trivialisation base set, the chart-α-trivialised
`(r, s)`-tensor representation of a fibre `T_b`, applied to a model fibre input
`D : Tensor0SModel r ℝ E`, equals
`e_s.continuousLinearMapAt b (T_b (e_r.symmL b D))`. -/
theorem tensorRSChartE_section_repr_apply_model (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (D : Tensor0SModel r ℝ E) :
    (tensorRSChartE_section_repr (I := I) r s α T b) D =
      (trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          ((trivializationAt (Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b D)) := by
  classical
  set eRS := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with heRS_def
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  have hbase_RS : b ∈ eRS.baseSet := by
    change b ∈ er.baseSet ∩ es.baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoeRS := eRS.coe_linearMapAt_of_mem (R := ℝ) hbase_RS
  unfold tensorRSChartE_section_repr
  change (eRS.linearMapAt ℝ b (T b)) D = _
  rw [show (eRS.linearMapAt ℝ b (T b)) = (eRS ⟨b, T b⟩).2 from
        congrFun hcoeRS (T b)]
  have hHom :
      eRS ⟨b, T b⟩
        = ⟨b, ((es.continuousLinearMapAt ℝ b
            : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
              ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
                ((er.symmL ℝ b)
                  : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b)))⟩ := rfl
  rw [hHom]
  change ((es.continuousLinearMapAt ℝ b
        : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
      ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
        ((er.symmL ℝ b)
          : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))) D = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

/-- On the chart-α trivialisation base set, the chart-α `(r, s)`-tensor fibre
right-inverse `symmL`, applied to a model fibre value `D : TensorRSModel r s ℝ E`
and then to a `(0, r)`-tensor input `α_input : Tensor0SSpace r I b`, equals
`e_s.symmL b (D (e_r.continuousLinearMapAt b α_input))`. -/
theorem tensorRSChartFiberFromModel_apply_at (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (D : TensorRSModel r s ℝ E) (α_input : Tensor0SSpace r I b) :
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      tensorRSChartFiberFromModel (I := I) r s α b D) α_input =
      (trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).symmL ℝ b
        (D ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b α_input)) := by
  classical
  set eRS := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with heRS_def
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  have hbase_RS : b ∈ eRS.baseSet := by
    change b ∈ er.baseSet ∩ es.baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hHomSymm : (eRS.symmL ℝ b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      (es.symmL ℝ b).comp (D.comp (er.continuousLinearMapAt ℝ b)) := by
    have h := _root_.Bundle.Pretrivialization.continuousLinearMap_symm_apply'
      (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (F₂ := Tensor0SModel s ℝ E)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (e₁ := er) (e₂ := es) (b := b) hbase_RS D
    change (eRS.symm b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) = _
    rw [show (eRS.symm b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
          ((_root_.Bundle.Pretrivialization.continuousLinearMap (𝕜₁ := ℝ) (𝕜₂ := ℝ)
            (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
            (E₁ := fun y : M => Tensor0SSpace r I y)
            (F₂ := Tensor0SModel s ℝ E)
            (E₂ := fun y : M => Tensor0SSpace s I y)
            er es).symm b D) from rfl]
    exact h
  unfold tensorRSChartFiberFromModel
  change (eRS.symmL ℝ b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) α_input = _
  rw [hHomSymm]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

theorem tensor0SChartE_section_repr_tensorPartialEval_eq_tensorRS_repr_apply
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b')
    {b : M} (_hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (α_input : Tensor0SSpace r I b)
    {b' : M} (hb' : b' ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    tensor0SChartE_section_repr (I := I) s α
        (tensorPartialEval (I := I) (M := M) r s T
          (chartTensor0SParallelExtend (I := I) r α b α_input)) b' =
      (tensorRSChartE_section_repr (I := I) r s α T b')
        ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b α_input) := by
  classical
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  set D_α : Tensor0SModel r ℝ E := er.continuousLinearMapAt ℝ b α_input with hDα_def
  have hPE_at_b' :
      chartTensor0SParallelExtend (I := I) r α b α_input b' =
        er.symmL ℝ b' D_α := rfl
  have hLHS_unfold :
      tensor0SChartE_section_repr (I := I) s α
          (tensorPartialEval (I := I) (M := M) r s T
            (chartTensor0SParallelExtend (I := I) r α b α_input)) b' =
        es.continuousLinearMapAt ℝ b'
          ((show Tensor0SSpace r I b' →L[ℝ] Tensor0SSpace s I b' from T b')
            (chartTensor0SParallelExtend (I := I) r α b α_input b')) := by
    unfold tensor0SChartE_section_repr
    rw [tensorPartialEval_apply]
  rw [hLHS_unfold]
  rw [hPE_at_b']
  rw [tensorRSChartE_section_repr_apply_model (I := I) r s α T (b := b') hb' D_α]

/-- The chart pullback of the chart-α-trivialised `(0, s)`-tensor representation
of `tensorPartialEval r s T (chartTensor0SParallelExtend r α b α_input)` agrees,
in a neighbourhood of `extChartAt I α b`, with the chart pullback of the
chart-α-trivialised `(r, s)`-tensor representation of `T` post-composed with
the evaluation-at-`D_α` CLM. -/
theorem tensorPartialEval_chartPullback_eventually_eq_evalAt_chartPullback
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b')
    {b : M} (α_input : Tensor0SSpace r I b)
    (hb_src : b ∈ (extChartAt I α).source)
    (hb_tgt : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (tensor0SChartE_section_repr (I := I) s α
        (tensorPartialEval (I := I) (M := M) r s T
          (chartTensor0SParallelExtend (I := I) r α b α_input)) ∘
        (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        tensorRSEvalAtCLM (E := E) r s
            ((trivializationAt (Tensor0SModel r ℝ E)
              (fun z : M => Tensor0SSpace r I z) α).continuousLinearMapAt ℝ b α_input)
          ((tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm) y)) := by
  classical
  set φ := extChartAt I α
  have hU_int : interior (φ.target : Set E) ∈ 𝓝 (φ b) :=
    isOpen_interior.mem_nhds hb_tgt
  have hBase_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hb_inv : φ.symm (φ b) = b := φ.left_inv hb_src
  have hcont_symm : ContinuousAt φ.symm (φ b) :=
    continuousAt_extChartAt_symm' (I := I) (x := α) (x' := b) hb_src
  have hBase_pre : φ.symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 (φ b) := by
    have hmem : (φ.symm (φ b)) ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [hb_inv]; exact hb_base
    exact hcont_symm.preimage_mem_nhds (hBase_open.mem_nhds hmem)
  filter_upwards [Filter.inter_mem hU_int hBase_pre] with y hy
  obtain ⟨_, hyBase⟩ := hy
  rw [Function.comp_apply, Function.comp_apply]
  rw [tensorRSEvalAtCLM_apply]
  exact tensor0SChartE_section_repr_tensorPartialEval_eq_tensorRS_repr_apply
    (I := I) r s α T (b := b) hb_base α_input (b' := φ.symm y) hyBase

/-- The Fréchet derivative of the chart pullback of the
chart-α-trivialised `(0, s)`-tensor representation of the partial evaluation
at `φ b` factors through the evaluate-at-`D_α` CLM applied to the Fréchet
derivative of the chart pullback of the `(r, s)`-trivialised representation
of `T`. -/
theorem fderiv_tensorPartialEval_chartPullback_eq_comp_evalAt
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b')
    {b : M} (α_input : Tensor0SSpace r I b)
    (hb_src : b ∈ (extChartAt I α).source)
    (hb_tgt : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hT : DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α
            (tensorPartialEval (I := I) (M := M) r s T
              (chartTensor0SParallelExtend (I := I) r α b α_input)) ∘
          (extChartAt I α).symm)
        (extChartAt I α b) =
      (tensorRSEvalAtCLM (E := E) r s
            ((trivializationAt (Tensor0SModel r ℝ E)
              (fun z : M => Tensor0SSpace r I z) α).continuousLinearMapAt ℝ b α_input)).comp
        (fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α T ∘
            (extChartAt I α).symm)
          (extChartAt I α b)) := by
  classical
  have heq := tensorPartialEval_chartPullback_eventually_eq_evalAt_chartPullback
    (I := I) (M := M) r s α T (b := b) α_input hb_src hb_tgt hb_base
  rw [Filter.EventuallyEq.fderiv_eq heq]
  exact (((tensorRSEvalAtCLM (E := E) r s
      ((trivializationAt (Tensor0SModel r ℝ E)
        (fun z : M => Tensor0SSpace r I z) α).continuousLinearMapAt ℝ b α_input)).hasFDerivAt
      (x := (tensorRSChartE_section_repr (I := I) r s α T ∘
        (extChartAt I α).symm) (extChartAt I α b))).comp
    (extChartAt I α b) hT.hasFDerivAt).fderiv

/-- **Curry factorisation of the `(r, s)`-intrinsic chart Fréchet derivative.**
On the chart Levi-Civita good set, applying the intrinsic chart Fréchet
derivative CLM of an `(r, s)`-tensor `T` to a vector `X b` and then evaluating
the resulting `(r, s)`-tensor at an input `α_input` agrees with the
intrinsic chart Fréchet derivative CLM of the partial evaluation
`tensorPartialEval r s T (chartTensor0SParallelExtend r α b α_input)` (a
`(0, s)`-tensor section) applied to `X b`. -/
theorem tensorRSIntrinsicChartCLM_factor_via_tensorPartialEval
    (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (α_input : Tensor0SSpace r I b)
    (hT : DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (X : Π b' : M, TangentSpace I b') :
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)) α_input =
      tensor0SIntrinsicChartCLM (I := I) s α
          (tensorPartialEval (I := I) (M := M) r s T
            (chartTensor0SParallelExtend (I := I) r α b α_input))
          b (X b) := by
  classical
  letI _h_top_rs : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI _h_top_s : TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y)) :=
    tensor0SBundle_topology s
  letI _h_top_r : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y)) :=
    tensor0SBundle_topology r
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_tgt : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  set D_α : Tensor0SModel r ℝ E := er.continuousLinearMapAt ℝ b α_input with hDα_def
  set w_E : E := trivToE (I := I) α b (X b) with hwE_def
  have hLHS_unfold :
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
        tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)) α_input =
        es.symmL ℝ b
          (fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm)
            (extChartAt I α b) w_E D_α) := by
    rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α T b (X b)]
    rw [tensorRSChartFiberFromModel_apply_at (I := I) r s α hb_base
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b))) α_input]
  rw [hLHS_unfold]
  have hRHS_unfold :
      tensor0SIntrinsicChartCLM (I := I) s α
          (tensorPartialEval (I := I) (M := M) r s T
            (chartTensor0SParallelExtend (I := I) r α b α_input))
          b (X b) =
        es.symmL ℝ b
          (fderiv ℝ
            (tensor0SChartE_section_repr (I := I) s α
                (tensorPartialEval (I := I) (M := M) r s T
                  (chartTensor0SParallelExtend (I := I) r α b α_input)) ∘
              (extChartAt I α).symm)
            (extChartAt I α b) w_E) := by
    rw [tensor0SIntrinsicChartCLM_apply (I := I) s α _ b (X b)]
    rfl
  rw [hRHS_unfold]
  have hfderivEq := fderiv_tensorPartialEval_chartPullback_eq_comp_evalAt
    (I := I) (M := M) r s α T (b := b) α_input hb_src hb_tgt hb_base hT
  have hfderiv_at_wE :
      fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α
              (tensorPartialEval (I := I) (M := M) r s T
                (chartTensor0SParallelExtend (I := I) r α b α_input)) ∘
            (extChartAt I α).symm)
          (extChartAt I α b) w_E =
        tensorRSEvalAtCLM (E := E) r s D_α
          (fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α T ∘
              (extChartAt I α).symm)
            (extChartAt I α b) w_E) := by
    have := congrArg (fun L : E →L[ℝ] Tensor0SModel s ℝ E => L w_E) hfderivEq
    simpa [ContinuousLinearMap.comp_apply] using this
  rw [hfderiv_at_wE]
  rw [tensorRSEvalAtCLM_apply]

end Connection
end Integral
end DifferentialGeometry

end
