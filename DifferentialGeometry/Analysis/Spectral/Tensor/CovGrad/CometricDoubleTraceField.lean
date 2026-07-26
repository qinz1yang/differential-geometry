import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel

/-! # The cometric raised-coframe double-trace / slot-0-raise smooth operator-field templates

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the metric-free C^∞ field-smoothness templates and the
intrinsic cometric `g₀⁻¹` double-trace operator-field constructions that feed both the curvature-trace
covariant-jet reduction of the Ricci–DeTurck curvature difference
(`SegmentMetricCurvatureDifferenceCovJet.lean`) and the cross-correction parallel two-section
contraction (`CrossCorrectionParallelContraction.lean`).

The C^∞ field-smoothness templates — the bundle interior product (`interiorProductField_contMDiff`),
the frame-free natural trace (`contractTraceField_contMDiff`), and the covariant-rank cast
(`tensor0SField_castRank_contMDiff`, through the fixed model isometry `modelRankCast`) — are the
smoothness-level analogues of the analytic `contract_*Field` lemmas, valid at every smoothness level
through the same model-bilinear `clm_apply` / `model_contract_trace`-composition arguments.

On top of them the file builds the genuine cometric `g₀⁻¹` double trace of the two leading covariant
slots: the model cometric raise `cometricLmodel` (the model reading of the smooth Hom-section sharp
`inverseMetricSharpField`), the frame-free model double trace `modelDoubleTrace` (the categorical
trace `E ⊗ E^* ≅ End E` of the cometric-raised slot with the original slot — ONE inverse,
`D : g₀⁻¹`), and their fibre realisations `ricciModelTrace42Fib`, `cometricRaiseSlot0Fib`, with the
base-point smoothness `ricciModelTrace42Fib_contMDiff` routed through the globally-smooth cometric
Hom-bundle section, with NO chart-selected non-`∇₀`-parallel ambient frame and NO single-trivialization
`symmL` factor. The model double trace is the natural trace of the cometric-raised slot
(`model_contract_trace_raiseSlot0ModelL`, `raiseSlot0ModelL`), and the bundle trace at the unit reads
as the model trace at the unit (`contract_trace_unitZero_toModel`). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The model-fibre rank cast `Tensor0SModel m → Tensor0SModel n` along `h : m = n`.**  The
continuous-linear (isometric) reindex of the model multilinear fibre, via
`ContinuousMultilinearMap.domDomCongrₗᵢ (finCongr h)`.  Used to chain the two leading-slot interior
products of the model-basis double trace across the `Nat`-equalities `4 + a = (3 + a) + 1` and
`3 + a = (2 + a) + 1` (which hold by `omega` but not `rfl`, as `Nat.add` recurses on the right). -/
noncomputable def modelRankCast {m n : ℕ} (h : m = n) :
    Tensor0SBundle.Tensor0SModel m ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
    (finCongr h)).toContinuousLinearEquiv.toContinuousLinearMap

set_option linter.unusedSectionVars false in
/-- The reflexive rank cast is the identity on the model fibre. -/
@[simp] theorem modelRankCast_refl {m : ℕ} (T : Tensor0SBundle.Tensor0SModel m ℝ E) :
    modelRankCast (E := E) (rfl : m = m) T = T := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [modelRankCast, finCongr_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **C^∞ interior-product field smoothness.**  At the C^∞ smoothness level, the bundle interior
product of a smooth `(0, s + 1)`-tensor field `α` with a smooth vector field `X` — `x ↦ interior_product s
x (X x) (α x)`, reading `X x` into the leading covariant slot — is a smooth `(0, s)`-tensor field.  This is
the C^∞ analogue of `Tensor0SBundle.contract_Tensor0SField` (which is stated only for analytic `ω`
manifolds via its section variable, hence unusable in the C^∞ context here); its proof is the *same*
model-bilinear `clm_apply` argument (`model_interior_bilinear` is continuous, applied to the trivialised
smooth `X` and `α`), valid at every smoothness level.  It is **non-vacuous**: the genuine smooth interior
product, NOT the zero field. -/
theorem interiorProductField_contMDiff (s : ℕ)
    (α : ∀ x : M, Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x (α x)))
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x (X x) (α x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  intro x₀
  rw [Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z)]
  have hα' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀).mp (hα x₀)
  have hX' := (Bundle.contMDiffAt_section (F := E) (E := TangentSpace I) x₀).mp (X.contMDiff x₀)
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E) ∞
        (fun x => Tensor0SBundle.model_interior_bilinear ℝ E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
            (fun x => Tensor0SBundle.Tensor0SSpace (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := Tensor0SBundle.model_interior_bilinear ℝ E s)).clm_apply hX').clm_apply hα'
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx

  apply ContinuousMultilinearMap.ext
  intro v
  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hsymmL
  set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hgtilde
  change (α x) (@Fin.cons s (fun _ => E) ((X x : TangentSpace I x) : E) (fun i => symmL (v i))) =
    (α x) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change ((X x : TangentSpace I x) : E) = symmL gtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := ℝ) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x (X x) = gtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rw [hcl] at h
    exact h.symm
  · intro j
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **C^∞ natural-trace field smoothness.**  At the C^∞ smoothness level, the fibrewise
frame-free natural trace of a smooth `(1 + r, s + 1)`-tensor field `T` — `x ↦ contract_trace r s x (T x)`,
contracting the leading contravariant slot against the leading covariant slot — is a smooth `(r, s)`-tensor
field.  This is the C^∞ analogue of `Tensor0SBundle.contract_TensorRSField` (stated only for analytic `ω`
manifolds via its section variable); its proof is the *same* `model_contract_trace`-composition argument
(`model_contract_trace` is continuous-linear, composed with the trivialised smooth `T`), valid at every
smoothness level.  It is **non-vacuous** (the genuine smooth natural trace). -/
theorem contractTraceField_contMDiff (r s : ℕ)
    (T : ∀ x : M, Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x (T x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
        (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x))) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  intro x₀
  rw [Bundle.contMDiffAt_section (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)]
  have hT' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀).mp (hT x₀)
  have hTrace : ContMDiffAt I 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E) ∞
      (fun x => Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
        ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨x, T x⟩).2)) x₀ :=
    (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s).contMDiffAt.comp x₀ hT'
  refine hTrace.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx

  set L : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hLdef
  set Linv : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x with hLinvdef
  set Tx : Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E :=
    Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x (T x) with hTxdef
  have hL : L.comp Linv = ContinuousLinearMap.id ℝ E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt (R := ℝ) hx z
  have hR : Linv.comp L = ContinuousLinearMap.id ℝ E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL (R := ℝ) hx z
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SSpace k I x) (v : Fin k → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt ℝ x U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).linearMapAt ℝ x) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SModel k ℝ E) (u : Fin k → E),
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ z : E, L (Linv z) = z := by
      intro z
      have h := congrArg (fun f : E →L[ℝ] E => f z) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i; exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U) u
          = ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt ℝ x
            ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt_symmL
              (R := ℝ) hx]
  have h_input :
      ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨x, T x⟩).2) =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L).comp
        (Tx.comp (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ x
        ((T x) ((trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (1 + r) I z) x₀).symmL ℝ x β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L)
        (Tx ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (1 + r) I z) x₀).symmL ℝ x β =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]; rfl
    rw [hβ]; rfl
  have h_output :
      (trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀
        ⟨x, Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x)⟩).2 =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L).comp
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx).comp
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ x
        ((Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x))
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L)
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx)
          ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]

    change ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
          ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x) (T x)))
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β))) (fun i => L (v i)) =
      (((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s) Tx)
        ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β)) (fun i => L (v i))
    have hβ2 : (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β) =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [Tensor0SBundle.model_covariantChange_apply]
      exact h_symmL r β u
    rw [hβ2]
  rw [h_input, h_output]
  exact (Tensor0SBundle.model_contract_trace_naturality (𝕜 := ℝ) (E := E)
    r s L Linv hL hR Tx).symm

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **The covariant-rank cast of a smooth `(0, m)`-field is a smooth `(0, n)`-field.**  For a covariant-rank
equality `h : m = n` and a smooth `(0, m)`-tensor field `Y`, the fibrewise `modelRankCast`-reindexed field
`x ↦ ofModel (modelRankCast h (toModel (Y x)))` is a smooth `(0, n)`-tensor field.  Proved by transport
along `h` (the cast is the identity reindex when `m = n`).  The slot reindex is a fixed model isometry,
NOT a metric- or frame-dependent operation. -/
theorem tensor0SField_castRank_contMDiff {m n : ℕ} (h : m = n)
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace m I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace n I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (modelRankCast (E := E) h (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
  subst h
  refine hY.congr (fun x => ?_)

  simp only [modelRankCast_refl, Tensor0SBundle.Tensor0SSpace.ofModel_toModel]

/-- **The model reading of the cometric index-raise `♯ : T^*_x M → T_x M`.**  The fibrewise
inverse-metric sharp `inverseMetricSharpFib g₀ x` conjugated through the model identification
`tensor0SSpace_continuousLinearEquiv 1 x`, read as a model-level continuous-linear map
`Tensor0SModel 1 → E`: a model covector `α` is sent to the `g₀`-raised tangent vector `♯α`.  This is the
SMOOTH `g₀`-raise (the model reading of the globally-smooth Hom-bundle section `inverseMetricSharpField`);
it is used to raise the leading covariant slot of a model `(0, s + 2)`-tensor before the FRAME-FREE
natural trace.  No chart-selected ambient basis enters: smoothness flows through
`inverseMetricSharpField_contMDiff`. -/
noncomputable def cometricLmodel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E :=
  (inverseMetricSharpFib (I := I) g₀ x).comp
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm.toContinuousLinearMap

/-- **The model `g₀⁻¹` double trace of the two leading covariant slots, `(0, s + 2) → (0, s)`.**  Given
the model cometric raise `L : Tensor0SModel 1 → E` (`L := cometricLmodel g₀ x`), the genuine cometric
double trace of the two leading covariant slots: raise slot `0` via `L` against the model `cDualBasis`
covector `b^k`, contract the (new leading) slot against the dual model basis vector `b_k`, and sum over
the internal model basis:
```
modelDoubleTrace s L D (m) = ∑ₖ D(L b^k, b_k, m).
```
This is the FRAME-FREE natural trace of the cometric-raised slot with the original slot (the categorical
trace `E ⊗ E^* ≅ End E`, basis-independent by `model_contract_trace_naturality`): with `L = ♯` it is the
genuine cometric `g₀^{ij}`-trace (ONE inverse), `∑ₖ D(♯b^k, b_k) = D : g₀⁻¹`.  Crucially, the internal
basis `b_k, b^k` only enters the *frame-free* trace (where it cancels); the smoothness in `x` flows
through the smooth Hom-section `♯`, NOT through any non-`∇₀`-parallel ambient frame. -/
noncomputable def modelDoubleTrace (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel (s + 2) ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel s ℝ E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s ((Module.finBasis ℝ E) k)).comp
      (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) (s + 1)
        (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))))

set_option linter.unusedSectionVars false in
/-- **Defining evaluation of the model `g₀⁻¹` double trace.**  `modelDoubleTrace s L D` evaluated on a
`Fin s`-tuple `m` reads, for each internal model basis index `k`, the cometric-raised covector `L b^k`
into the leading model slot and the dual basis vector `b_k` into the new leading slot:
```
modelDoubleTrace s L D m = ∑ₖ D (Fin.cons (L b^k) (Fin.cons b_k m)).
```
Definitional, through the leading-slot interior-product evaluations (`model_interior_product` reads its
vector into the leading slot). -/
theorem modelDoubleTrace_apply (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (m : Fin s → E) :
    modelDoubleTrace (E := E) s L D m =
      ∑ k : Fin (Module.finrank ℝ E),
        D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m)) := by
  classical
  rw [modelDoubleTrace]
  simp only [ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  rfl

/-- **The fibrewise `−2` intrinsic `g₀⁻¹` double-trace fibre operator.**  At a base point `x`, the
`−2`-scaled genuine cometric double trace `modelDoubleTrace (2 + a) (cometricLmodel g₀ x)` of the two
leading covariant slots (raise slot `0` by the smooth cometric `♯`, then the FRAME-FREE natural trace
against the original slot — giving ONE inverse, `D : g₀⁻¹`), transported through the fibre/model
continuous-linear equivalence `tensor0SSpace_continuousLinearEquiv`: a continuous-linear map between
tensor fibres `Tensor0SSpace (4 + a) I x →L Tensor0SSpace (2 + a) I x`, i.e. a `(0, 4 + a) → (0, 2 + a)`
fibre map (the slot counts `4 + a = (2 + a) + 2` are definitional).  It reads only the fibre value `D(x)`
(value-local) and depends on the background metric `g₀` only through the SMOOTH cometric Hom-section
`inverseMetricSharpField`; NO chart-selected, non-`∇₀`-parallel ambient basis enters the smoothness. -/
noncomputable def ricciModelTrace42Fib (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x :=
  (-2 : ℝ) •
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (2 + a) x).symm.toContinuousLinearMap.comp
      ((modelDoubleTrace (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)).comp
        ((modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)).comp
          (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (4 + a) x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in
/-- **The model image of the fibre operator is the `−2` intrinsic cometric double trace.**  `toModel`
intertwines `ricciModelTrace42Fib` with the model-level `−2 • modelDoubleTrace` against the cometric
raise:
`toModel (ricciModelTrace42Fib g₀ a x D) = (-2) • modelDoubleTrace (2 + a) (cometricLmodel g₀ x) (toModel D)`.
Definitional, since `Tensor0SSpace.toModel = tensor0SSpace_continuousLinearEquiv` and the equivalence is
`id`. -/
@[simp] theorem ricciModelTrace42Fib_toModel (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (4 + a) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciModelTrace42Fib (I := I) g₀ a x D) =
      (-2 : ℝ) • modelDoubleTrace (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)
        (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := rfl

/-- **The model raise of the leading covariant slot by a cometric `L : Tensor0SModel 1 → E`,
`(0, s + 2) → (1, s + 1)`.**  Feeding a model covector `β` into the contravariant slot of
`raiseSlot0ModelL s L D` reads the `L`-raised vector `L β` into the leading covariant slot of the
`(0, s + 2)`-tensor `D`: `raiseSlot0ModelL s L D β = model_interior_product (s + 1) (L β) D`.  This
is the frame-free index-raise feeding the model double trace's natural contraction; no internal frame
enters (only the variable covector slot `β`). -/
noncomputable def raiseSlot0ModelL (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel (s + 2) ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E :=
  ContinuousLinearMap.flip
    ((Tensor0SBundle.model_interior_bilinear ℝ E (s + 1)).comp L)

set_option linter.unusedSectionVars false in
/-- Defining evaluation of `raiseSlot0ModelL`. -/
@[simp] theorem raiseSlot0ModelL_apply (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (β : Tensor0SBundle.Tensor0SModel 1 ℝ E) :
    raiseSlot0ModelL (E := E) s L D β =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) (s + 1) (L β) D := rfl

set_option linter.unusedSectionVars false in
/-- **The model double trace is the natural trace of the cometric-raised slot.**  Evaluating the
frame-free natural trace `model_contract_trace 0 s` of the cometric-raised tensor `raiseSlot0ModelL s L D`
at the unit `(0, 0)`-tensor recovers the model double trace `modelDoubleTrace s L D`.  The two
expressions are termwise equal over the internal model basis: the trace's contravariant pre-contraction
against the dual basis covector `b^i` (tensored with the unit) selects `raiseSlot0ModelL s L D (b^i) =
model_interior_product (s + 1) (L b^i) D`, and the covariant post-contraction against `b_i` is the outer
`model_interior_product s (b_i)`. -/
theorem model_contract_trace_raiseSlot0ModelL (s : ℕ)
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) :
    (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) 0 s (raiseSlot0ModelL (E := E) s L D))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      modelDoubleTrace (E := E) s L D := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [Tensor0SBundle.model_contract_trace_apply_basis (Module.finBasis ℝ E) 0 s
    (raiseSlot0ModelL (E := E) s L D)
    (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) m,
    modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)

  have htw : Tensor0SBundle.model_tensorWithCovector_first (𝕜 := ℝ) (E := E) 0
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    rw [Tensor0SBundle.model_tensorWithCovector_first, LinearMap.coe_toContinuousLinearMap']
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, mul_one,
      Tensor0SBundle.model_covectorOfCLM_apply, Tensor0SBundle.model_covectorOfCLM_apply]
    rfl
  rw [htw, raiseSlot0ModelL_apply]

  rw [show ((Module.finBasis ℝ E).cDualBasis i) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) from by
        rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
        congr 1
        exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) i]
  rfl

/-- **The fibrewise cometric raise of the leading covariant slot, `(0, s + 2) → (1, s + 1)`.**  At a base
point `x` the index-raise of the leading covariant slot by the cometric `♯ = inverseMetricSharpFib g₀ x`:
the model-level `raiseSlot0ModelL` against the cometric reading `cometricLmodel g₀ x`, transported through
the fibre/model continuous-linear equivalences.  Feeding a covector `β` into its contravariant slot reads
the raised vector `♯ β` into the leading slot of the `(0, s + 2)`-tensor.  It depends on `g₀` only through
the SMOOTH cometric Hom-section, NO chart-selected ambient frame. -/
noncomputable def cometricRaiseSlot0Fib (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SBundle.TensorRSSpace 1 (s + 1) I x :=
  (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 1 (s + 1) x).symm.toContinuousLinearMap.comp
    ((raiseSlot0ModelL (E := E) s (cometricLmodel (I := I) g₀ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (s + 2) x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
/-- The model image of `cometricRaiseSlot0Fib` is `raiseSlot0ModelL` against the cometric reading. -/
@[simp] theorem cometricRaiseSlot0Fib_toModel (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (s + 2) I x) :
    Tensor0SBundle.TensorRSSpace.toModel (cometricRaiseSlot0Fib (I := I) g₀ s x D) =
      raiseSlot0ModelL (E := E) s (cometricLmodel (I := I) g₀ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The cometric raise of a fixed smooth `(0, s + 2)`-field is a smooth `(1, s + 1)`-field.**  For a
smooth `(0, s + 2)`-tensor field `Y` (presented as the smooth total-space map `hY`), the section
`x ↦ cometricRaiseSlot0Fib g₀ s x (Y x)` is a smooth section of the `(1, s + 1)`-tensor bundle.  By
`contMDiff_clm_section_of_pointwise` (over the contravariant covector slot `Tensor0SSpace 1`) it suffices
that for every smooth covector field `β` the section `x ↦ (cometricRaiseSlot0Fib g₀ s x (Y x)) (β x)` is
smooth; that value is the bundle interior product of `Y` with the smooth vector field `x ↦ ♯ (β x)`
(`contract_Tensor0SField`, smooth), where `♯` is the globally-smooth cometric Hom-section
`inverseMetricSharpField` applied to the *variable* covector `β` (`ContMDiff.clm_bundle_apply`), NEVER `♯`
of a constant frame. -/
theorem cometricRaiseSlot0Fib_section_contMDiff (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace (s + 2) I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) x
        (cometricRaiseSlot0Fib (I := I) g₀ s x (Y x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun x => (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
      cometricRaiseSlot0Fib (I := I) g₀ s x (Y x)))
  intro β

  have hsharpβ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g₀ x (β x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₀) β.contMDiff
  let sharpβ : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨fun x : M => inverseMetricSharpFib (I := I) g₀ x (β x), hsharpβ⟩

  have hcontract := interiorProductField_contMDiff (I := I) (s + 1) (fun x => Y x) hY sharpβ
  refine hcontract.congr (fun x => ?_)

  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x (sharpβ x) (Y x)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x
      ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib (I := I) g₀ s x (Y x)) (β x))

  congr 1

set_option linter.unusedSectionVars false in
/-- **The bundle frame-free trace at the unit reads as the model trace at the unit.**  For a
`(1, s + 1)`-tensor `T` at `x`, the model image of the bundle natural trace `contract_trace 0 s x T`
evaluated at the unit `(0, 0)`-section is the model natural trace `model_contract_trace 0 s` of the model
image of `T`, evaluated at the unit `(0, 0)`-model-tensor.  This bridges the `(0, s)`-as-`Hom(scalar, ·)`
realisation of the bundle trace to the direct `(0, s)` model trace.  Definitional through the
`tensorRSSpace`/`tensor0SSpace` identity equivalences and `contract_trace_apply`. -/
theorem contract_trace_unitZero_toModel (s : ℕ) (x : M)
    (T : Tensor0SBundle.TensorRSSpace 1 (s + 1) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 s x T)
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) 0 s
          (Tensor0SBundle.TensorRSSpace.toModel T))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := by
  rw [Tensor0SBundle.contract_trace]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the intrinsic `g₀⁻¹` double-trace operator field, routed through
the smooth cometric Hom-section.**  The fibre field `x ↦ ricciModelTrace42Fib g₀ a x` is a smooth
section of the `(4 + a, 2 + a)`-tensor bundle.  The fibre map is the `−2`-scaled genuine cometric double
trace of the two leading covariant slots (raise slot `0` by the cometric `♯`, then the FRAME-FREE natural
trace against the original slot, `modelDoubleTrace`).

Its smoothness is genuinely intrinsic and routes through the **globally-smooth cometric Hom-bundle
section** `inverseMetricSharpField` (`inverseMetricSharpField_contMDiff`), with **NO** chart-selected,
non-`∇₀`-parallel ambient frame and **NO** single-trivialization `symmL` factor.  The route is the
structural raise-then-natural-trace: by `contMDiff_clm_section_of_pointwise` it suffices that for every
smooth `(0, 4 + a)`-field `Y` the section `x ↦ ricciModelTrace42Fib g₀ a x (Y x)` is smooth; that is
`(−2) •` the FRAME-FREE natural trace (`contract_TensorRSField`, smooth) of the smooth raised
`(1, 3 + a)`-field `x ↦ raise_♯ (slot 0) (Y x)` — and the raise is smooth because `♯` enters as the
smooth Hom-section `inverseMetricSharpField` applied to the *variable* slot argument (an inner
`contMDiff_clm_section_of_pointwise`, per smooth covector field `β`: the interior product
`contract_Tensor0SField` of `Y` against the smooth vector field `x ↦ ♯(β x)`, `ContMDiff.clm_bundle_apply`
of `inverseMetricSharpField` on `β`), NEVER as `♯` of a constant model frame.  It is **non-vacuous** (the
genuine cometric double-trace operator field, smooth, not the zero field). -/
theorem ricciModelTrace42Fib_contMDiff (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (4 + a) (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (4 + a) (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (4 + a) (2 + a) I z) x
        (ricciModelTrace42Fib (I := I) g₀ a x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel (4 + a) ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace (4 + a) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (2 + a) ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (2 + a) I x)
    (φ := fun x => ricciModelTrace42Fib (I := I) g₀ a x)
  intro Y

  let Y' : ∀ x : M, Tensor0SBundle.Tensor0SSpace ((2 + a) + 2) I x :=
    fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
  have hY' : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((2 + a) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((2 + a) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((2 + a) + 2) I z) x (Y' x)) :=
    tensor0SField_castRank_contMDiff (I := I) (by omega : (4 + a) = (2 + a) + 2) (fun x => Y x) Y.contMDiff

  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ (2 + a) Y' hY'

  have htrace := contractTraceField_contMDiff (I := I) 0 (2 + a)
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a) I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (2 + a) x
            (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff

  have hscaled : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a) I z) x
        ((-2 : ℝ) • ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (2 + a) x
            (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) :=
    ContMDiff.const_smul_section (a := (-2 : ℝ)) htraceUnit
  refine hscaled.congr (fun x => ?_)

  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [ricciModelTrace42Fib_toModel, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  congr 1

  rw [← model_contract_trace_raiseSlot0ModelL (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)
    (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))]

  rw [contract_trace_unitZero_toModel (I := I) (2 + a) x
    (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x))]
  congr 1

open DifferentialGeometry.Integral.Connection

/-- **The fibrewise rank-generic intrinsic `g₀⁻¹` double-trace fibre operator, `(0, p + 2) → (0, p)`.**
At a base point `x`, the genuine cometric double trace `modelDoubleTrace p (cometricLmodel g₀ x)` of the
two leading covariant slots (raise slot `0` by the smooth cometric `♯`, then the FRAME-FREE natural trace
against the original slot — giving ONE inverse, `D : g₀⁻¹`), transported through the fibre/model
continuous-linear equivalence `tensor0SSpace_continuousLinearEquiv`: a continuous-linear map between
tensor fibres `Tensor0SSpace (p + 2) I x →L Tensor0SSpace p I x`, i.e. a `(0, p + 2) → (0, p)` fibre map
(the slot counts `p + 2 = p + 2` are definitional, the cast `modelRankCast` is the reflexive reindex).
This is the rank-generic, `−2`-unscaled version of `ricciModelTrace42Fib` (which is `(−2) •` this fibre at
`p := 2 + a`).  It reads only the fibre value `D(x)` (value-local) and depends on the background metric
`g₀` only through the SMOOTH cometric Hom-section `inverseMetricSharpField`; NO chart-selected,
non-`∇₀`-parallel ambient basis enters the smoothness. -/
noncomputable def cometricDoubleTraceFib (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace p I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) p x).symm.toContinuousLinearMap.comp
    ((modelDoubleTrace (E := E) p (cometricLmodel (I := I) g₀ x)).comp
      ((modelRankCast (E := E) (rfl : (p + 2) = p + 2)).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (p + 2) x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in
/-- **The model image of the rank-generic fibre operator is the intrinsic cometric double trace.**
`toModel` intertwines `cometricDoubleTraceFib` with the model-level `modelDoubleTrace` against the
cometric raise:
`toModel (cometricDoubleTraceFib g₀ p x D) = modelDoubleTrace p (cometricLmodel g₀ x) (toModel D)`.
Definitional, since `Tensor0SSpace.toModel = tensor0SSpace_continuousLinearEquiv`, the equivalence is
`id`, and the reflexive `modelRankCast` is the identity. -/
@[simp] theorem cometricDoubleTraceFib_toModel (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (p + 2) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ p x D) =
      modelDoubleTrace (E := E) p (cometricLmodel (I := I) g₀ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := by
  rw [cometricDoubleTraceFib]
  change modelDoubleTrace (E := E) p (cometricLmodel (I := I) g₀ x)
      (modelRankCast (E := E) (rfl : (p + 2) = p + 2) (Tensor0SBundle.Tensor0SSpace.toModel D)) = _
  rw [modelRankCast_refl]

set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the rank-generic intrinsic `g₀⁻¹` double-trace operator field, routed
through the smooth cometric Hom-section.**  The fibre field `x ↦ cometricDoubleTraceFib g₀ p x` is a
smooth section of the `(p + 2, p)`-tensor bundle.  Its smoothness routes through the globally-smooth
cometric Hom-bundle section `inverseMetricSharpField` (`inverseMetricSharpField_contMDiff`), with NO
chart-selected, non-`∇₀`-parallel ambient frame: by `contMDiff_clm_section_of_pointwise` it reduces to
the smooth raise (`cometricRaiseSlot0Fib_section_contMDiff`, the cometric `♯` entering as the smooth
Hom-section on the *variable* slot) followed by the FRAME-FREE natural trace
(`contractTraceField_contMDiff`).  It is **non-vacuous** (the genuine cometric double-trace operator
field, smooth, not the zero field). -/
theorem cometricDoubleTraceFib_contMDiff (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (p + 2) p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (p + 2) p ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (p + 2) p I z) x
        (cometricDoubleTraceFib (I := I) g₀ p x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel (p + 2) ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace (p + 2) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel p ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace p I x)
    (φ := fun x => cometricDoubleTraceFib (I := I) g₀ p x)
  intro Y

  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ p (fun x => Y x) Y.contMDiff

  have htrace := contractTraceField_contMDiff (I := I) 0 p
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ p x (Y x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace p I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 p x
            (cometricRaiseSlot0Fib (I := I) g₀ p x (Y x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff
  refine htraceUnit.congr (fun x => ?_)

  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricDoubleTraceFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) p (cometricLmodel (I := I) g₀ x)
    (Tensor0SBundle.Tensor0SSpace.toModel (Y x))]
  rw [contract_trace_unitZero_toModel (I := I) p x
    (cometricRaiseSlot0Fib (I := I) g₀ p x (Y x))]
  congr 1

/-- **The rank-generic intrinsic `g₀⁻¹` double-trace operator field as a smooth compactly-supported
`(p + 2, p)`-tensor.**  The fibre value at `x` is `cometricDoubleTraceFib g₀ p x` (smooth by
`cometricDoubleTraceFib_contMDiff`); on the closed manifold it has compact support.  This is the smooth
operator field whose operator-field action contracts the two leading covariant slots `{0, 1}` against
the cometric `g₀⁻¹(x)` (the `−2`-unscaled, rank-generic version of `ricciModelTrace42Field`, which is
`(−2) •` this field at rank `p := 2 + a`). -/
noncomputable def cometricDoubleTraceField (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    Integral.L2.SmoothCcTensor g₀ (p + 2) p where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace (p + 2) p I x from
          cometricDoubleTraceFib (I := I) g₀ p x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₀ p }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `cometricDoubleTraceField g₀ p` at `x` is the fibre operator
`cometricDoubleTraceFib g₀ p x`.  Definitional. -/
@[simp] theorem cometricDoubleTraceField_toSection (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M) :
    (cometricDoubleTraceField (I := I) g₀ p).toSection x =
      (show Tensor0SBundle.TensorRSSpace (p + 2) p I x from
        cometricDoubleTraceFib (I := I) g₀ p x) := rfl

set_option linter.unusedSectionVars false in
/-- **Leading-slot multilinear sum expansion.**  Evaluating a model `(0, s + 1)`-tensor on a tuple
whose leading entry is a finite sum expands the sum out of the leading slot (multilinearity, read
through the leading-slot curry equivalence). -/
private theorem model_cons_slot0_sum {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (f : ι → E) (rest : Fin s → E) :
    T (Fin.cons (∑ i ∈ fs, f i) rest) = ∑ i ∈ fs, T (Fin.cons (f i) rest) := by
  have h : ∀ u : E, T (Fin.cons u rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T u) rest := by
    intro u
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_sum, ContinuousMultilinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (h (f i)).symm

set_option linter.unusedSectionVars false in
/-- **Leading-slot multilinear scalar expansion.**  Evaluating a model `(0, s + 1)`-tensor on a tuple
whose leading entry is a scalar multiple pulls the scalar out of the leading slot. -/
private theorem model_cons_slot0_smul {s : ℕ} (c : ℝ) (u : E)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (rest : Fin s → E) :
    T (Fin.cons (c • u) rest) = c * T (Fin.cons u rest) := by
  have h : ∀ z : E, T (Fin.cons z rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T z) rest := by
    intro z
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, ← h]

set_option linter.unusedSectionVars false in
/-- **The smooth orthonormal frame is a tangent basis on its orthonormality neighbourhood.**  At any
point `y` of the orthonormality neighbourhood of the frame attached at `x`, the value family
`i ↦ smoothOrthoFrame g₀ x i y` is `g₀(y)`-orthonormal, hence linearly independent and (cardinality
`finrank`) a `Module.Basis` of `T_y M`. -/
private theorem smoothOrthoFrame_basis_at (g₀ : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y),
      ∀ i, bse i = smoothOrthoFrame (I := I) g₀ x i y := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner y (smoothOrthoFrame (I := I) g₀ x a y)
        (smoothOrthoFrame (I := I) g₀ x b y) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal (I := I) g₀ x hy a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g₀ x i y) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ x j y) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)
        (c j • smoothOrthoFrame (I := I) g₀ x j y) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

set_option linter.unusedSectionVars false in
/-- **Orthonormal expansion in the smooth orthonormal frame.**  At any point `y` of the
orthonormality neighbourhood, every tangent vector expands against the `g₀(y)`-orthonormal frame
values with metric coefficients: `u = ∑ᵢ g₀(u, Bᵢ y) • Bᵢ y`. -/
private theorem smoothOrthoFrame_expansion_at (g₀ : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) (u : TangentSpace I y) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner y u (smoothOrthoFrame (I := I) g₀ x i y) •
        smoothOrthoFrame (I := I) g₀ x i y := by
  classical
  obtain ⟨bse, hbse⟩ := smoothOrthoFrame_basis_at (I := I) g₀ x hy
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner y (smoothOrthoFrame (I := I) g₀ x a y)
        (smoothOrthoFrame (I := I) g₀ x b y) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal (I := I) g₀ x hy a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner y u (smoothOrthoFrame (I := I) g₀ x j y) = bse.repr u j := by
    intro j
    rw [g₀.symm y u (smoothOrthoFrame (I := I) g₀ x j y)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner y (smoothOrthoFrame (I := I) g₀ x j y)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner y u (smoothOrthoFrame (I := I) g₀ x i y) •
          smoothOrthoFrame (I := I) g₀ x i y := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

set_option linter.unusedSectionVars false in
/-- **The cometric raise of the `k`-th dual-basis model covector pairs to the `k`-th basis
coordinate.**  `g₀(♯b^k, u) = repr(u)ₖ`: the defining inverse property of the cometric sharp
(`inverseMetricSharpFib_inner`), read on the model dual basis `b^k := cDualBasis k` of `finBasis`. -/
private theorem cometricLmodel_dualBasis_inner (g₀ : SmoothRiemannianMetric I M) (y : M)
    (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I y) :
    g₀.inner y (cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) u =
      (Module.finBasis ℝ E).repr (u : E) k := by
  have h1 : cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₀ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₀ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => u) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => (u : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]

set_option linter.unusedSectionVars false in
/-- **The cometric dual-basis double trace equals the orthonormal-frame diagonal sum.**  At any
point `y` of the orthonormality neighbourhood of the frame attached at `x`, the frame-free cometric
double trace of a model `(0, s + 2)`-tensor `T` — slot `0` raised by the cometric `♯` of the model
dual-basis covectors, slot `1` contracted against the model basis — equals the `g₀(y)`-orthonormal
frame diagonal sum `∑ᵢ T(Bᵢ y, Bᵢ y, mm)`. -/
theorem cometric_dualTrace_eq_orthoFrame_diag (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x)
    (T : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (mm : Fin s → E) :
    ∑ k : Fin (Module.finrank ℝ E),
        T (Fin.cons (cometricLmodel (I := I) g₀ y
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) mm)) =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
  classical
  have hsharp : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I y),
      g₀.inner y (cometricLmodel (I := I) g₀ y
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) u =
        (Module.finBasis ℝ E).repr (u : E) k :=
    fun k u => cometricLmodel_dualBasis_inner (I := I) g₀ y k u
  have hexp : ∀ k : Fin (Module.finrank ℝ E),
      cometricLmodel (I := I) g₀ y
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
            smoothOrthoFrame (I := I) g₀ x i y := by
    intro k
    conv_lhs => rw [smoothOrthoFrame_expansion_at (I := I) g₀ x hy
      (cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hsharp k (smoothOrthoFrame (I := I) g₀ x i y)]
  calc ∑ k : Fin (Module.finrank ℝ E),
      T (Fin.cons (cometricLmodel (I := I) g₀ y
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) mm))
      = ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hexp k, model_cons_slot0_sum (E := E)]
        exact Finset.sum_congr rfl fun i _ => model_cons_slot0_smul (E := E) _ _ T _
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := Finset.sum_comm
    _ = ∑ i : Fin (Module.finrank ℝ E),
          T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hcurry : ∀ z : E,
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons z mm)) =
            ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
              (Fin.cons z mm) := by
          intro z
          rw [continuousMultilinearCurryLeftEquiv_apply]
        calc ∑ k : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).repr
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
              T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                  (Fin.cons ((Module.finBasis ℝ E) k) mm))
            = ∑ k : Fin (Module.finrank ℝ E),
                ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                    ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
                  (Fin.cons (((Module.finBasis ℝ E).repr
                      ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
                    ((Module.finBasis ℝ E) k)) mm) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [model_cons_slot0_smul (E := E), ← hcurry]
          _ = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                  ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
                (Fin.cons (∑ k : Fin (Module.finrank ℝ E),
                  ((Module.finBasis ℝ E).repr
                      ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
                    ((Module.finBasis ℝ E) k)) mm) :=
              (model_cons_slot0_sum (E := E) Finset.univ _ _ mm).symm
          _ = T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
              rw [(Module.finBasis ℝ E).sum_repr
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E), ← hcurry]

set_option linter.unusedSectionVars false in
/-- **The finite-sum additivity of the `(0, s)`-tensor covariant derivative.**  The bundled
Levi-Civita `(0, s)`-tensor covariant derivative distributes over a finite sum of smooth sections
(iterated `IsCovariantDerivativeOn.add` by `Finset` induction). -/
private theorem tensor0SCovDeriv_finset_sum (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {ι : Type*} (fs : Finset ι)
    (σ : ι → Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel s ℝ E,
      (fun y : M => Tensor0SBundle.Tensor0SSpace s I y)⟯) (x : M) :
    Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g₀)
        (fun y : M => ∑ i ∈ fs, σ i y) x =
      ∑ i ∈ fs, Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g₀)
        (fun y : M => σ i y) x := by
  classical
  induction fs using Finset.cons_induction with
  | empty =>
    rw [show (fun y : M => ∑ i ∈ (∅ : Finset ι), σ i y) =
        (0 : Π y : M, Tensor0SBundle.Tensor0SSpace s I y) from
      funext fun y => Finset.sum_empty]
    rw [Finset.sum_empty]
    exact (Tensor0SNabla.tensor0SCovariantDerivative I M s
      (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.zero (Set.mem_univ x)
  | cons b fs' hb ih =>
    have hsum_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) y (∑ i ∈ fs', σ i y)) := by
      refine (∑ i ∈ fs', σ i :
        Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel s ℝ E,
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y)⟯).contMDiff.congr fun y => ?_
      rw [ContMDiffSection.finset_sum_apply]
    have hadd := (Tensor0SNabla.tensor0SCovariantDerivative I M s
        (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.add
      (σ := fun y : M => σ b y) (σ' := fun y : M => ∑ i ∈ fs', σ i y) (x := x)
      (((σ b).contMDiff x).mdifferentiableAt (by norm_num))
      ((hsum_smooth x).mdifferentiableAt (by norm_num)) (Set.mem_univ x)
    rw [show (fun y : M => ∑ i ∈ Finset.cons b fs' hb, σ i y) =
        ((fun y : M => σ b y) + fun y : M => ∑ i ∈ fs', σ i y) from
      funext fun y => Finset.sum_cons hb]
    rw [hadd, ih, Finset.sum_cons]

set_option linter.unusedSectionVars false in
/-- **The fibre value of the rank-generic `g₀⁻¹` double-trace field is the orthonormal-frame
diagonal double insertion.**  At any point `y` of the orthonormality neighbourhood of the frame
attached at `x`, the double-trace fibre operator reads a `(0, p + 2)`-tensor `D` as
```
cometricDoubleTraceFib g₀ p y D = ∑ᵢ curry_p (curry_{p+1} D (Bᵢ y)) (Bᵢ y),
```
the `g₀(y)`-orthonormal diagonal trace of the two leading covariant slots.  This is the frame reading
of the frame-free cometric double trace (`cometric_dualTrace_eq_orthoFrame_diag`, the rank-generic,
`−2`-unscaled version of `ricciModelTrace42Fib_eq_orthoFrame_diag`). -/
theorem cometricDoubleTraceFib_eq_orthoFrame_diag (g₀ : SmoothRiemannianMetric I M)
    (p : ℕ) (x : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x)
    (D : Tensor0SBundle.Tensor0SSpace (p + 2) I y) :
    cometricDoubleTraceFib (I := I) g₀ p y D =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p y
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) y D
            (smoothOrthoFrame (I := I) g₀ x i y))
          (smoothOrthoFrame (I := I) g₀ x i y) := by
  classical
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun mm => ?_
  beta_reduce
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ p y D]
  rw [modelDoubleTrace_apply (E := E) p (cometricLmodel (I := I) g₀ y)
    (Tensor0SBundle.Tensor0SSpace.toModel D) mm]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p y
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) y D
              (smoothOrthoFrame (I := I) g₀ x i y))
            (smoothOrthoFrame (I := I) g₀ x i y)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p y
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) y D
              (smoothOrthoFrame (I := I) g₀ x i y))
            (smoothOrthoFrame (I := I) g₀ x i y)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) p y) _ _]
  rw [ContinuousMultilinearMap.sum_apply]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ (s := p) x hy
    (Tensor0SBundle.Tensor0SSpace.toModel D) mm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) y D
        (smoothOrthoFrame (I := I) g₀ x i y))
      (v0 := ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)) (vs := mm),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := D)
      (v0 := ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
      (vs := Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)]

set_option linter.unusedSectionVars false in
/-- **The skew moving-frame correction cancels (rank-generic).**  The two correction sums of the
orthonormal-frame diagonal Leibniz expansion cancel, by the orthonormal expansion of the frame
derivative and the connection skew-symmetry `g₀(∇ᵥBᵢ, Bⱼ) = −g₀(Bᵢ, ∇ᵥBⱼ)`
(`smoothOrthoFrame_cov_skew`). -/
private theorem orthoFrame_skew_correction_cancel (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (v : E) (T : Tensor0SBundle.Tensor0SModel (p + 2) ℝ E) (mm : Fin p → E) :
    (∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons (((LeviCivita (I := I) g₀).toFun
              (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)))
      + (∑ i : Fin (Module.finrank ℝ E),
          T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
              (Fin.cons (((LeviCivita (I := I) g₀).toFun
                  (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) mm))) = 0 := by
  classical
  set a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
      (smoothOrthoFrame (I := I) g₀ x j x) with ha_def
  have haskew : ∀ i j, a i j = - a j i := by
    intro i j
    change g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
        (smoothOrthoFrame (I := I) g₀ x j x) =
      - g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x j) x v)
        (smoothOrthoFrame (I := I) g₀ x i x)
    rw [smoothOrthoFrame_cov_skew (I := I) g₀ x i j v]
    rw [g₀.symm x (smoothOrthoFrame (I := I) g₀ x i x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x j) x v)]
  have hexp : ∀ i : Fin (Module.finrank ℝ E),
      (LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v =
        ∑ j : Fin (Module.finrank ℝ E), a i j • smoothOrthoFrame (I := I) g₀ x j x :=
    fun i => smoothOrthoFrame_expansion_at (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
  have hS1 : (∑ i : Fin (Module.finrank ℝ E),
      T (Fin.cons (((LeviCivita (I := I) g₀).toFun
            (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (((LeviCivita (I := I) g₀).toFun
          (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) =
        ((∑ j : Fin (Module.finrank ℝ E),
          a i j • smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) from by
      rw [← hexp i]]
    rw [model_cons_slot0_sum (E := E)]
    exact Finset.sum_congr rfl fun j _ => model_cons_slot0_smul (E := E) _ _ T _
  have hS2 : (∑ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
          (Fin.cons (((LeviCivita (I := I) g₀).toFun
              (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) mm)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcurry : ∀ z : E,
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
            (Fin.cons z mm)) =
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (p + 2) => E) ℝ) T
            ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E))
          (Fin.cons z mm) := by
      intro z
      rw [continuousMultilinearCurryLeftEquiv_apply]
    rw [hcurry]
    rw [show (((LeviCivita (I := I) g₀).toFun
          (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) =
        ((∑ j : Fin (Module.finrank ℝ E),
          a i j • smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) from by
      rw [← hexp i]]
    rw [model_cons_slot0_sum (E := E)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [model_cons_slot0_smul (E := E), ← hcurry]
  rw [hS1, hS2]
  have h2 : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        -(a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [haskew j i, neg_mul]
  rw [h2]
  rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      -(a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)))) =
      -(∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) from by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_neg_distrib]]
  exact add_neg_cancel _

set_option linter.unusedSectionVars false in
/-- **The fibre-level skew correction sums cancel (rank-generic).**  The two moving-frame correction
sums of the orthonormal-frame diagonal Leibniz expansion cancel as `(0, p)`-tensor fibre elements
(`orthoFrame_skew_correction_cancel` read through `toModel`-extensionality). -/
private theorem orthoFrame_corrections_sum_eq_zero (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (v : E) (W : Tensor0SBundle.Tensor0SSpace (p + 2) I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
          (smoothOrthoFrame (I := I) g₀ x i x))
      + (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) = 0 := by
  classical
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun mm => ?_
  beta_reduce
  have heval : ∀ (z₁ z₂ : TangentSpace I x),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W z₁) z₂) mm =
        Tensor0SBundle.Tensor0SSpace.toModel W
          (Fin.cons ((z₁ : TangentSpace I x) : E)
            (Fin.cons ((z₂ : TangentSpace I x) : E) mm)) := by
    intro z₁ z₂
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W z₁)
      (v0 := ((z₂ : TangentSpace I x) : E)) (vs := mm)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := W)
      (v0 := ((z₁ : TangentSpace I x) : E))
      (vs := Fin.cons ((z₂ : TangentSpace I x) : E) mm)]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) p x) _ _]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) p x) _ _]
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    heval ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
      (smoothOrthoFrame (I := I) g₀ x i x))]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    heval (smoothOrthoFrame (I := I) g₀ x i x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply]
  exact orthoFrame_skew_correction_cancel (I := I) g₀ p x v
    (Tensor0SBundle.Tensor0SSpace.toModel W) mm

set_option linter.unusedSectionVars false in
/-- **The orthonormal-frame diagonal Leibniz expansion of the double insertion (rank-generic).**  The
directional `(0, p)`-tensor covariant derivative of the doubly-frame-inserted section
`y ↦ curry_p (curry_{p+1} (w y) (Bᵢ y)) (Bᵢ y)` splits by the leading-slot Hom-Leibniz
(`tensor0SCovariantDerivative_curriedSection_hom_leibniz`, applied twice) into the diagonal jet term
plus the two moving-frame corrections. -/
private theorem covDeriv_doubleInsert_leibniz (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (w : ∀ y : M, Tensor0SBundle.Tensor0SSpace (p + 2) I y)
    (hw : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 2) I z) y (w y)))
    (x : M) (i : Fin (Module.finrank ℝ E)) (v : E) :
    Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x
            (Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2) (LeviCivita (I := I) g₀)
              (fun y : M => w y) x v)
            (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) := by
  classical
  have hCi_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (smoothOrthoFrame (I := I) g₀ x i y)) :=
    smoothOrthoFrame_smooth (I := I) g₀ x i
  let Ci : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g₀ x i y, hCi_smooth⟩
  have hu_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 1) I z) y
        ((Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
          (smoothOrthoFrame (I := I) g₀ x i y))) := by
    have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + 1) I z) y
          (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)) :=
      fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
        (I := I) (M := M) (fun z' : M => w z') y (hw y)
    exact ContMDiff.clm_bundle_apply (b := id) hcurried Ci.contMDiff
  have hu_at : TensorSectionMDiffAt (I := I) (p + 1)
      (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
        (smoothOrthoFrame (I := I) g₀ x i y)) x :=
    (hu_smooth x).mdifferentiableAt (by norm_num)
  have hw_at : TensorSectionMDiffAt (I := I) (p + 2) (fun y : M => w y) x :=
    (hw x).mdifferentiableAt (by norm_num)
  have h1 : Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
          (Tensor0SNabla.tensor0SCovariantDerivative I M (p + 1) (LeviCivita (I := I) g₀)
            (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
              (smoothOrthoFrame (I := I) g₀ x i y)) x v)
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) :=
    Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g₀ p
      (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
        (smoothOrthoFrame (I := I) g₀ x i y)) (x := x) hu_at Ci v
  have h2 : Tensor0SNabla.tensor0SCovariantDerivative I M (p + 1) (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x
          (Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2) (LeviCivita (I := I) g₀)
            (fun y : M => w y) x v)
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) :=
    Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g₀ (p + 1) (fun y : M => w y) (x := x) hw_at Ci v
  rw [h1, h2, map_add (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x),
    ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **The cometric `∇₀`-parallelism of the rank-generic `g₀⁻¹` double-trace field.**  The covariant
gradient of the rank-generic intrinsic `g₀⁻¹` double-trace operator field
(`cometricDoubleTraceField g₀ p`, contracting the two leading covariant slots `{0, 1}` against the
cometric, via the cometric index-raise `♯ = inverseMetricSharpField` then the FRAME-FREE natural
trace) vanishes:
```
covGrad g₀ (p + 2) p (cometricDoubleTraceField g₀ p) = 0.
```
This is the genuine deep cometric-parallelism core `∇₀ g₀⁻¹ = 0`, rank-generic over the passenger
count `p` (the rank-pinned `ricciModelTrace42Field_covGrad_eq_zero` is the `p := 2` special case scaled
by `−2`).

**Proof.**  It suffices that the directional covariant derivative of the field vanishes at every base
point and direction.  By the Hom-connection product rule (`tensorRSCovariantDerivative_apply`), this
reduces to the intertwining `∇₀ᵥ(Φ·w) = Φₓ(∇₀ᵥw)`.  Near `x` the frame-free cometric trace agrees with
the `g₀`-orthonormal diagonal sum against the smooth orthonormal frame attached at `x`
(`cometricDoubleTraceFib_eq_orthoFrame_diag`), so by locality and finite-sum additivity the derivative
passes to the per-frame-direction double insertions; the leading-slot Hom-Leibniz
(`covDeriv_doubleInsert_leibniz`, two peels) produces the diagonal jet term `∑ᵢ (∇₀ᵥw)(Bᵢ, Bᵢ, ·)` —
exactly `Φₓ(∇₀ᵥw)` by the value identity at `x` — plus the two moving-frame corrections, which cancel
(`orthoFrame_corrections_sum_eq_zero`, the cometric skew core read on the frame). -/
theorem cometricDoubleTraceField_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ (p + 2) p
        (cometricDoubleTraceField (I := I) g₀ p) = 0 := by
  classical
  have hdir : ∀ (x : M) (v : E),
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ (p + 2) p
        (cometricDoubleTraceField (I := I) g₀ p) x v = 0 := by
    intro x v
    apply ContinuousLinearMap.ext
    intro D
    obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
      (V := fun y : M => Tensor0SBundle.Tensor0SSpace (p + 2) I y) (n := (⊤ : ℕ∞)) x D
    have hPR := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) (p + 2) p
      (LeviCivita (I := I) g₀) (cometricDoubleTraceField (I := I) g₀ p).toSection w x v
    rw [Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) g₀ (p + 2) p
      (cometricDoubleTraceField (I := I) g₀ p) x v, ContinuousLinearMap.zero_apply, ← hw]
    refine Eq.trans hPR ?_
    rw [sub_eq_zero]
    have hCi_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
            (smoothOrthoFrame (I := I) g₀ x i y)) :=
      fun i => smoothOrthoFrame_smooth (I := I) g₀ x i
    have hu_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)
            (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 1) I z) y
            ((Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
              (smoothOrthoFrame (I := I) g₀ x i y))) := by
      intro i
      have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)
            (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + 1) I z) y
            (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)) :=
        fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
          (I := I) (M := M) (fun z' : M => w z') y (w.contMDiff y)
      exact ContMDiff.clm_bundle_apply (b := id) hcurried (hCi_smooth i)
    have ht_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
            (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) y
            ((Tensor0SNabla.curriedSection I M
              (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
                (smoothOrthoFrame (I := I) g₀ x i z)) y)
              (smoothOrthoFrame (I := I) g₀ x i y))) := by
      intro i
      have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel p ℝ E)
            (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace p I z) y
            (Tensor0SNabla.curriedSection I M
              (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
                (smoothOrthoFrame (I := I) g₀ x i z)) y)) :=
        fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
          (I := I) (M := M)
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y (hu_smooth i y)
      exact ContMDiff.clm_bundle_apply (b := id) hcurried (hCi_smooth i)
    let ti : Fin (Module.finrank ℝ E) →
        Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel p ℝ E,
          (fun y : M => Tensor0SBundle.Tensor0SSpace p I y)⟯ := fun i =>
      ⟨fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y), ht_smooth i⟩
    have hP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) y
          ((show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace p I y from
            (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (cometricDoubleTraceField (I := I) g₀ p).toSection.contMDiff w.contMDiff
    set Q : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel p ℝ E,
        (fun y : M => Tensor0SBundle.Tensor0SSpace p I y)⟯ :=
      ∑ i : Fin (Module.finrank ℝ E), ti i with hQ_def
    have hQ_coe : ∀ y : M, Q y = ∑ i : Fin (Module.finrank ℝ E), ti i y := by
      intro y
      rw [hQ_def, ContMDiffSection.finset_sum_apply]
    have hagree : ∀ᶠ y in nhds x,
        (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace p I y from
          (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y) = Q y := by
      filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
      rw [hQ_coe y]
      rw [show (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace p I y from
          (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y) =
        cometricDoubleTraceFib (I := I) g₀ p y (w y) from rfl]
      rw [cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₀ p x hy (w y)]
      rfl
    have hcongr := (Tensor0SNabla.tensor0SCovariantDerivative I M p
        (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (σ := fun y : M =>
        (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace p I y from
          (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y))
      (σ' := fun y : M => Q y) (x := x)
      ((hP_smooth x).mdifferentiableAt (by norm_num))
      ((Q.contMDiff x).mdifferentiableAt (by norm_num)) Filter.univ_mem hagree
    have hfinal : (Tensor0SNabla.tensor0SCovariantDerivative I M p
          (LeviCivita (I := I) g₀)).toFun
          (fun y : M =>
            (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace p I y from
              (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y)) x v =
        (show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace p I x from
          (cometricDoubleTraceField (I := I) g₀ p).toSection x)
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
            (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v) := by
      calc (Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g₀)).toFun
            (fun y : M =>
              (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace p I y from
                (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y)) x v
          = (Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g₀)).toFun
              (fun y : M => Q y) x v := by rw [hcongr]
        _ = ((Tensor0SNabla.tensor0SCovariantDerivative I M p
              (LeviCivita (I := I) g₀)).toFun
              (fun y : M => ∑ i : Fin (Module.finrank ℝ E), ti i y) x) v := by
            rw [show (fun y : M => Q y) =
                (fun y : M => ∑ i : Fin (Module.finrank ℝ E), ti i y) from funext hQ_coe]
        _ = ((∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SNabla.tensor0SCovariantDerivative I M p
                (LeviCivita (I := I) g₀)).toFun (fun y : M => ti i y) x) v) := by
            rw [tensor0SCovDeriv_finset_sum (I := I) g₀ p Finset.univ ti x]
        _ = (∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SNabla.tensor0SCovariantDerivative I M p
                (LeviCivita (I := I) g₀)).toFun (fun y : M => ti i y) x v) := by
            rw [ContinuousLinearMap.sum_apply]
        _ = (∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
                  (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x
                    ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
                      (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)
                    (smoothOrthoFrame (I := I) g₀ x i x))
                  (smoothOrthoFrame (I := I) g₀ x i x)
                + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
                    (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
                      ((LeviCivita (I := I) g₀).toFun
                        (smoothOrthoFrame (I := I) g₀ x i) x v))
                    (smoothOrthoFrame (I := I) g₀ x i x)
                + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
                    (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
                      (smoothOrthoFrame (I := I) g₀ x i x))
                    ((LeviCivita (I := I) g₀).toFun
                      (smoothOrthoFrame (I := I) g₀ x i) x v))) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact covDeriv_doubleInsert_leibniz (I := I) g₀ p (fun y : M => w y) w.contMDiff x i v
        _ = (∑ i : Fin (Module.finrank ℝ E),
              Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
                (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x
                  ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
                    (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)
                  (smoothOrthoFrame (I := I) g₀ x i x))
                (smoothOrthoFrame (I := I) g₀ x i x)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_assoc,
              orthoFrame_corrections_sum_eq_zero (I := I) g₀ p x v (w x), add_zero]
        _ = (show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace p I x from
              (cometricDoubleTraceField (I := I) g₀ p).toSection x)
              ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
                (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v) :=
            (cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₀ p x
              (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
              ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
                (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)).symm
    exact hfinal
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply,
    Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval
      (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p) x D m,
    hdir x (m 0), ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
