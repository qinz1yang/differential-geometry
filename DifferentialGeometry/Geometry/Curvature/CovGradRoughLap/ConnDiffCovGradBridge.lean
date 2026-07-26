import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Multilinear.Basis

/-!
# The connection-difference tensor as a bundled `(1, 2)`-tensor, and its covariant gradient

For two smooth Riemannian metrics `g₀, g₁` on a closed manifold `M` the connection-difference
tensor `A = connDiff g₁ g₀ = ∇₁ − ∇₀` (`Geometry/Flow/ConnectionDifference.lean`) is a
vector-field-valued `(1, 2)`-tensor: at each `x` it is a continuous bilinear map
`TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x` (two covariant vector slots, one
contravariant vector output).  This file packages it as a genuine `SmoothCcTensor g₀ 1 2` — the
project's `Hom(Tensor0SSpace 1, Tensor0SSpace 2)` valence — through the **metric-free dual pairing**
`A♭(om)(Y, Z) := om(A(Y, Z))` (a covector `om` paired with the vector output `A(Y, Z)`), and bridges its
bundled iterated covariant gradient `covGrad g₀ 1 2` to the directional Palatini covariant derivative
`covDerivConnDiff g₀ g₁` (`Geometry/Curvature/CurvatureOperator/RicciConnDiffPalatini.lean`).

## Main definitions

* `connDiffFib g₁ g₀ x : TensorRSSpace 1 2 I x` — the fibrewise dual-pairing packaging of
  `connDiff g₁ g₀ x` as a `(1, 2)`-tensor: `connDiffFib x om (Y, Z) = om(connDiff x Y Z)`.
* `connDiffSection g₁ g₀ : SmoothCcTensor g₀ 1 2` — the smooth, compactly-supported `(1, 2)`-tensor
  section assembled from `connDiffFib`, smooth by `connDiff_contMDiff` and the metric-free pairing,
  compactly supported because `M` is compact.

## Main theorems

* `connDiffFib_apply_eval` — the defining evaluation formula
  `(connDiffFib x om).toModel [Y, Z] = om [connDiff x Y Z]`.
* `connDiffSection_covGrad_eq_covDerivConnDiff` — **the bridge**: the bundled iterated covariant
  gradient `covGrad g₀ 1 2 (connDiffSection g₁ g₀)` (a `SmoothCcTensor g₀ 1 3`) equals the dual-pairing
  packaging of the Palatini directional covariant derivative `covDerivConnDiff g₀ g₁` of the
  connection-difference tensor.  This connects the analysis/operator-field covariant-gradient machinery
  (`covGrad`/`tensorRSCovariantDerivative`) to the vector-field/Palatini machinery
  (`covDerivConnDiff`/`covDerivDiff`), the bedrock the central Lichnerowicz `_core` consumes.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The dual-pairing packaging of the connection-difference tensor as a `(1, 2)`-tensor -/

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A `(0, 1)`-tensor `om : Tensor0SSpace 1 I x` is additive when evaluated on the single tangent slot:
`om [a + b] = om [a] + om [b]`.  This is the additivity of the arity-`1` multilinear map, transferred
through the `continuousMultilinearCurryFin1` equivalence to a genuine continuous linear functional. -/
private lemma tensor0SOne_apply_add (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) (fun _ => a + b) = _
  rw [hab, ha, hb, map_add]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A `(0, 1)`-tensor `om : Tensor0SSpace 1 I x` is homogeneous when evaluated on the single tangent
slot: `om [c • a] = c • om [a]`. -/
private lemma tensor0SOne_apply_smul (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) (fun _ => c • a) = _
  rw [hca, ha, map_smul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A `(0, 1)`-tensor `om : Tensor0SSpace 1 I x` negates when evaluated on the single tangent
slot: `om [-a] = -om [a]`.  Derived from homogeneity at `c = -1`. -/
private lemma tensor0SOne_apply_neg (x : M) (om : Tensor0SSpace 1 I x)
    (a : TangentSpace I x) :
    om (fun _ : Fin 1 => -a) = -om (fun _ : Fin 1 => a) := by
  have h := tensor0SOne_apply_smul (I := I) x om (-1) a
  simp only [neg_smul, one_smul] at h
  exact h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A `(0, 1)`-tensor `om : Tensor0SSpace 1 I x` is subtractive when evaluated on the single
tangent slot: `om [a - b] = om [a] - om [b]`.  Derived from additivity and negation. -/
private lemma tensor0SOne_apply_sub (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a - b) = om (fun _ : Fin 1 => a) - om (fun _ : Fin 1 => b) := by
  rw [show (fun _ : Fin 1 => a - b) = (fun _ : Fin 1 => a + (-b)) from by
    funext _; rw [sub_eq_add_neg]]
  rw [tensor0SOne_apply_add (I := I) x om, tensor0SOne_apply_neg (I := I) x om, sub_eq_add_neg]

/-- The `(0, 2)`-tensor fibre `(Y, Z) ↦ om(connDiff g₁ g₀ x Y Z)` paired against a covector `om`. -/
def connDiffPairing (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.add_apply, map_add]
            rw [tensor0SOne_apply_add (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.smul_apply, map_smul]
            rw [tensor0SOne_apply_smul (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) :=
          (connDiff (I := I) g₁ g₀ x).continuous₂.comp hpair
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

omit [CompactSpace M] [I.Boundaryless] in
/-- The `(0, 2)`-fibre `connDiffPairing` evaluated (FunLike) on a tangent tuple `YZ` reads `om`
against the connection-difference output `connDiff g₁ g₀ x (YZ 0) (YZ 1)`. -/
@[simp] lemma connDiffPairing_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (connDiffPairing (I := I) g₁ g₀ x om) YZ =
      om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := rfl

omit [CompactSpace M] [I.Boundaryless] in
/-- `connDiffPairing` is additive in the covector. -/
lemma connDiffPairing_add (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    connDiffPairing (I := I) g₁ g₀ x (om + om') =
      connDiffPairing (I := I) g₁ g₀ x om + connDiffPairing (I := I) g₁ g₀ x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

omit [CompactSpace M] [I.Boundaryless] in
/-- `connDiffPairing` is homogeneous in the covector. -/
lemma connDiffPairing_smul (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    connDiffPairing (I := I) g₁ g₀ x (c • om) =
      c • connDiffPairing (I := I) g₁ g₀ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

/-- **The fibrewise dual-pairing packaging of the connection-difference tensor.**  At a base point
`x`, `connDiffFib g₁ g₀ x` is the `(1, 2)`-tensor (`TensorRSSpace 1 2 I x =
Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x`) sending a covector `om` to the bilinear form
`(Y, Z) ↦ om(connDiff g₁ g₀ x Y Z)`: the metric-free pairing of `om` with the vector output of the
connection-difference tensor. -/
def connDiffFib (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => connDiffPairing (I := I) g₁ g₀ x om
        map_add' := connDiffPairing_add g₁ g₀ x
        map_smul' := connDiffPairing_smul g₁ g₀ x })

omit [CompactSpace M] [I.Boundaryless] in
/-- The `(1, 2)`-tensor `connDiffFib g₁ g₀ x` applied to a covector `om` is the `(0, 2)`-pairing
`connDiffPairing g₁ g₀ x om`. -/
@[simp] lemma connDiffFib_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from connDiffFib (I := I) g₁ g₀ x) om =
      connDiffPairing (I := I) g₁ g₀ x om := rfl

omit [CompactSpace M] [I.Boundaryless] in
/-- **The defining evaluation formula for the `(1, 2)`-tensor packaging.**  The `(1, 2)`-tensor
`connDiffFib g₁ g₀ x` applied to a covector `om` and evaluated on a pair of tangent vectors `(Y, Z)`
reads `om` against the connection-difference output `connDiff g₁ g₀ x Y Z`:
`(connDiffFib x om)[Y, Z] = om[connDiff x Y Z]`. -/
lemma connDiffFib_apply_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from connDiffFib (I := I) g₁ g₀ x) om) YZ =
      om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
  rw [connDiffFib_apply, connDiffPairing_apply]

/-! ## Smoothness of the dual-pairing packaging, and the `SmoothCcTensor` section -/

/-- The smoothness of the dual-pairing packaging as a Hom-bundle `(1, 2)`-tensor section: the field
`x ↦ connDiffFib g₁ g₀ x` is smooth.

By the Hom-bundle smoothness criterion `contMDiff_clm_section_of_pointwise` (source bundle the
covector bundle `Tensor0SSpace 1`, target the `(0, 2)`-tensor bundle `Tensor0SSpace 2`) it suffices
that for every smooth covector section `om`, the `(0, 2)`-tensor field
`x ↦ connDiffFib g₁ g₀ x (om x) = connDiffPairing g₁ g₀ x (om x)` is smooth.  That `(0, 2)`-section
smoothness is the coordinate criterion `contMDiff_multilinearSection_iff_coord`: through
`continuousMultilinearMap_basis_repr` the coordinate at a multi-index `σ : Fin 2 → Fin (finrank ℝ E)`
reads `connDiffPairing` against the trivialisation frame vectors, which on the trivialisation base set
agree with smooth tangent local frame fields `Y (σ 0), Y (σ 1)`.  There
`connDiffPairing(om x)(Y(σ 0)x, Y(σ 1)x) = om(connDiff x (Y(σ 0)x)(Y(σ 1)x))`, smooth by
`connDiff_contMDiff` (the connection-difference output is a smooth tangent field) followed by the
multilinear-section evaluation `contMDiffAt_section_apply` of the smooth covector `om` against it. -/
theorem connDiffFib_contMDiff (g₁ g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x (connDiffFib (I := I) g₁ g₀ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connDiffFib (I := I) g₁ g₀ x))

  intro om
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffPairing (I := I) g₁ g₀ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (connDiffPairing (I := I) g₁ g₀ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁

    have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (((connDiff (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))) :=
      connDiff_contMDiff (I := I) g₁ g₀ (Y (σ 0)).contMDiff (Y (σ 1)).contMDiff

    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => ((connDiff (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => ((connDiff (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))
        (fun _ => (hconn x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx

    rw [continuousMultilinearMap_basis_repr]

    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]

    change (connDiffPairing (I := I) g₁ g₀ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [connDiffPairing_apply]

    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

/-- **The connection-difference tensor as a smooth, compactly-supported `(1, 2)`-tensor section.**
Its fibre value at `x` is the dual-pairing packaging `connDiffFib g₁ g₀ x`
(`om ↦ (Y, Z) ↦ om(connDiff g₁ g₀ x Y Z)`), smooth by `connDiffFib_contMDiff`; on the closed
manifold it has compact support.  This is the bundled `SmoothCcTensor g₀ 1 2` the covariant-gradient
machinery `covGrad g₀ 1 2` consumes. -/
def connDiffSection (g₁ g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => connDiffFib (I := I) g₁ g₀ x
      contMDiff_toFun := connDiffFib_contMDiff (I := I) g₁ g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- The underlying section value of `connDiffSection g₁ g₀` at `x` is the fibre `connDiffFib g₁ g₀ x`.
Definitional. -/
@[simp] lemma connDiffSection_toSection (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffSection (I := I) g₁ g₀).toSection x = connDiffFib (I := I) g₁ g₀ x := rfl

/-! ## The covariant-gradient ↔ Palatini directional-derivative bridge -/

set_option linter.unusedSectionVars false in
/-- **Hom product-rule split of the directional covariant derivative of `connDiffSection`.**
For smooth covector field `om` and smooth tangent fields `X Y Z`, the directional covariant derivative
`tensorCovDerivAt g₀ 1 2 (connDiffSection g₁ g₀)` along `X x`, applied to the covector `om x` and read
on the tangent pair `(Y x, Z x)`, splits by the Hom-bundle product rule
(`tensorRSCovariantDerivative_apply_of_mdifferentiableAt`) into the `(0, 2)`-derivative of the
dual-pairing `y ↦ connDiffPairing g₁ g₀ y (om y)` minus the dual-pairing of the `(0, 1)`-derivative of
`om`:
```
(∇_{X x} (connDiffSection))(om x)(Y x, Z x)
  = (∇^{(0,2)}_{X x}(y ↦ connDiffPairing g₁ g₀ y (om y)))(Y x, Z x)
    − connDiffPairing g₁ g₀ x (∇^{(0,1)}_{X x} om)(Y x, Z x).
``` -/
private lemma connDiffSection_tensorCovDerivAt_homSplit
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) x (X x))
        (om x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) x (X x) -
        connDiffPairing (I := I) g₁ g₀ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => om y) x (X x)) := by
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) y
        ((connDiffSection (I := I) g₁ g₀).toSection y)) x :=
    (connDiffSection (I := I) g₁ g₀).toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) y (om y)) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) x (X x)]
  have hsplit := tensorRSCovariantDerivative_apply_of_mdifferentiableAt (I := I) (M := M)
    1 2 (LeviCivita (I := I) g₀)
    (fun y : M => (connDiffSection (I := I) g₁ g₀).toSection y) (fun y : M => om y)
    (fun y : M => X y) hτ hw hV

  have hval : (fun y : M =>
        (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
          (connDiffSection (I := I) g₁ g₀).toSection y) (om y)) =
      (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) := by
    funext y
    rw [connDiffSection_toSection]
    rfl
  rw [hsplit, hval]
  rfl

/-! ### Inline `(0, 2)`/`(0, 1)` covariant Leibniz-defect peels for the bridge -/

set_option linter.unusedSectionVars false in
/-- The dual-pairing `(0, 2)`-tensor field `y ↦ connDiffPairing g₁ g₀ y (om y)` of a smooth
covector field `om` is `MDifferentiableAt x`: it is the smooth Hom-section
`connDiffSection g₁ g₀` (smooth by `connDiffFib_contMDiff`) applied, fibrewise, to the smooth
covector `om`, which the bundle `clm`-application keeps differentiable. -/
private lemma tensorSectionMDiffAt_connDiffPairing
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) (x : M) :
    TensorSectionMDiffAt (I := I) 2
      (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) x := by
  classical
  have hval : (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) =
      (fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
        (connDiffSection (I := I) g₁ g₀).toSection y) (om y)) := by
    funext y
    rw [connDiffSection_toSection]
    rfl
  rw [hval]
  unfold TensorSectionMDiffAt
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) y
        ((connDiffSection (I := I) g₁ g₀).toSection y)) x :=
    (connDiffSection (I := I) g₁ g₀).toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) y (om y)) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := Tensor0SModel 1 ℝ E) (F₂ := Tensor0SModel 2 ℝ E)
    (E₁ := fun y : M => Tensor0SSpace 1 I y)
    (E₂ := fun y : M => Tensor0SSpace 2 I y)
    (IM := I) (IB := I)
    (b := id)
    (ϕ := fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
      (connDiffSection (I := I) g₁ g₀).toSection y))
    (v := fun y : M => om y) hτ hw

set_option linter.unusedSectionVars false in
/-- **The `(0, 2)`-target term of the bridge.**  The model value of the abstract `(0, 2)`-tensor
covariant derivative of the dual-pairing field `V y = connDiffPairing g₁ g₀ y (om y)` along `X x`,
read on the cons-tuple `(Y x, Z x)`, decomposes by the two-fold covariant Leibniz peel into the
directional derivative of the scalar `b ↦ om b (connDiff b (Y b)(Z b))` minus the two `∇₀`-slot
corrections `om x (connDiff x (∇₀_{X x} Y)(Z x))` and `om x (connDiff x (Y x)(∇₀_{X x} Z))`.

This is the inline analogue of `tensor0SCovariantDerivative02_consEval_leibnizDefect`, specialised
to the connection-difference dual-pairing section. -/
private lemma connDiffPairing_covariantDerivative02_eval
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) x (X x))
        (Fin.cons (Y x) ![Z x]) =
      directionalDerivAt (I := I)
          (fun b : M => om b (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ b (Y b) (Z b))) x (X x)
        - om x (fun _ : Fin 1 =>
            connDiff (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x))
        - om x (fun _ : Fin 1 =>
            connDiff (I := I) g₁ g₀ x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      := by
  classical
  set V : Π b : M, Tensor0SSpace 2 I b :=
    fun b => connDiffPairing (I := I) g₁ g₀ b (om b) with hVdef
  have hV : TensorSectionMDiffAt (I := I) 2 V x :=
    tensorSectionMDiffAt_connDiffPairing (I := I) g₁ g₀ om x
  set W₁ : Π b : M, Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (Y b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x := by
    have hY' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
      Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    unfold TensorSectionMDiffAt
    have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) 1 V hV
    exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
      (F₁ := E) (F₂ := Tensor0SModel 1 ℝ E)
      (E₁ := fun b : M => TangentSpace I b)
      (E₂ := fun b : M => Tensor0SSpace 1 I b)
      (IM := I) (IB := I)
      (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M V y)
      (v := fun y : M => Y y) hCurried hY'

  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 V hV Y (X x) ![Z x]

  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff Z (X x) (fun i => Fin.elim0 i)

  have hbase : Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
          (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x (X x))
        (fun i => Fin.elim0 i) =
      directionalDerivAt (I := I)
        (fun b : M => om b (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ b (Y b) (Z b))) x (X x) := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x (X x)]
    rw [directionalDerivAt_eq]
    refine congrArg (fun f => (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) ?_
    funext b
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]

    show Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₁ b (Z b))
        (fun i => Fin.elim0 i) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := W₁)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
          (T := W₁ b) (v0 := Z b) (vs := (fun i => Fin.elim0 i))]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V b (Y b))
        (Fin.cons (Z b) (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
          (T := V b) (v0 := Y b) (vs := Fin.cons (Z b) (fun i => Fin.elim0 i))]
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl

  have hcorr2 : Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)) (fun i => Fin.elim0 i)) =
      om x (fun _ : Fin 1 =>
        connDiff (I := I) g₁ g₀ x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      := by
    have hW₁x : W₁ x = Tensor0SNabla.curriedSection I M V x (Y x) := rfl
    rw [hW₁x, Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := Y x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        (fun i => Fin.elim0 i))]
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl

  have hcorr1 : Tensor0SSpace.toModel (V x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x))
          (Fin.cons (Z x) (fun i => Fin.elim0 i))) =
      om x (fun _ : Fin 1 =>
        connDiff (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x))
      := by
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl

  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) = W₁ from rfl]
  rw [show (![Z x] : Fin 1 → E) = Fin.cons (Z x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel2, hbase, hcorr2, hcorr1]
  ring

set_option linter.unusedSectionVars false in
/-- **The `(0, 1)`-source term of the bridge.**  The dual pairing of the `(0, 1)`-covariant
derivative of `om` against the connection-difference output, read on `(Y x, Z x)`, equals the
directional derivative of the scalar `b ↦ om b (connDiff b (Y b)(Z b))` minus `om` against the
covariant derivative of the connection-difference vector field `b ↦ connDiff b (Y b)(Z b)`:
```
connDiffPairing x (∇^{(0,1)}_{X x} om)(Y x, Z x)
  = ∂_{X x}(b ↦ om b (connDiff b (Y b)(Z b)))
    − om x (∇₀_{X x}(b ↦ connDiff b (Y b)(Z b))).
```
This is the slot-0 covariant Leibniz peel (`tensor0SCovariantDerivative_succ_consEval_peel` at
`s = 0`) of the covector `om` against the smooth field `b ↦ connDiff b (Y b)(Z b)` (smooth by
`connDiff_contMDiff`). -/
private lemma connDiffPairing_covariantDerivative01_eval
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    connDiffPairing (I := I) g₁ g₀ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) =
      directionalDerivAt (I := I)
          (fun b : M => om b (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ b (Y b) (Z b))) x (X x)
        - om x (fun _ : Fin 1 =>
            (LeviCivita (I := I) g₀).toFun
              (fun b => connDiff (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)) := by
  classical

  have hWYZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, connDiff (I := I) g₁ g₀ b (Y b) (Z b)⟩ : TotalSpace E (TangentSpace I))) :=
    connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  set WYZ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => connDiff (I := I) g₁ g₀ b (Y b) (Z b)) hWYZ with hWYZdef

  have hom_mdiff : TensorSectionMDiffAt (I := I) 1 (fun y : M => om y) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 (fun y : M => om y) hom_mdiff WYZ (X x) (fun i => Fin.elim0 i)

  have hLHS : connDiffPairing (I := I) g₁ g₀ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) =
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (WYZ x) (fun i => Fin.elim0 i)) := by
    rw [connDiffPairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl
  rw [hLHS, hpeel]

  have hbase : Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
          (fun y : M => Tensor0SNabla.curriedSection I M (fun y : M => om y) y (WYZ y)) x (X x))
        (fun i => Fin.elim0 i) =
      directionalDerivAt (I := I)
        (fun b : M => om b (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ b (Y b) (Z b))) x (X x) := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun y : M => Tensor0SNabla.curriedSection I M (fun y : M => om y) y (WYZ y)) x (X x)]
    rw [directionalDerivAt_eq]
    refine congrArg (fun f => (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) ?_
    funext b
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    show Tensor0SSpace.toModel
        (Tensor0SNabla.curriedSection I M (fun y : M => om y) b (WYZ b))
        (fun i => Fin.elim0 i) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := fun y : M => om y)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := om b) (v0 := WYZ b) (vs := (fun i => Fin.elim0 i))]
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl

  have hcorr : Tensor0SSpace.toModel ((fun y : M => om y) x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => WYZ b) x (X x)) (fun i => Fin.elim0 i)) =
      om x (fun _ : Fin 1 =>
        (LeviCivita (I := I) g₀).toFun
          (fun b => connDiff (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)) := by
    change Tensor0SSpace.toModel (om x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => WYZ b) x (X x))
          (fun i => Fin.elim0 i)) = _
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl
  rw [hbase, hcorr]

set_option linter.unusedSectionVars false in
/-- **The covariant-gradient ↔ Palatini directional-derivative bridge (evaluation form).**

For two smooth Riemannian metrics `g₀, g₁`, a smooth covector field `om`, and smooth tangent
vector fields `X, Y, Z`, the bundled iterated covariant gradient `covGrad g₀ 1 2` of the
connection-difference tensor `connDiffSection g₁ g₀`, evaluated at `x` on the covector `om x` and
read on the cons-tuple `(X x, Y x, Z x)`, equals the dual pairing of `om x` with the Palatini
directional covariant derivative `covDerivConnDiff g₀ g₁ X Z Y x` of the connection-difference
tensor:
```
(covGrad g₀ 1 2 (connDiffSection g₁ g₀))(x)(om x)(X x, Y x, Z x)
  = om x (covDerivConnDiff g₀ g₁ X Z Y x).
```
The argument order `X Z Y` is forced: `covDerivConnDiff` (`= covDerivDiff`) packages the
connection-difference output through `diffSec ∇₀ ∇₁ Z Y b = connDiff g₁ g₀ b (Y b)(Z b)`, with the
two trailing slots SWAPPED relative to `connDiffPairing`'s `om(connDiff x (Y, Z))`.

This is the bedrock the central Lichnerowicz `_core` consumes: it ties the analysis/operator-field
covariant-gradient machinery (`covGrad`/`tensorRSCovariantDerivative`) to the
vector-field/Palatini machinery (`covDerivConnDiff`/`covDerivDiff`). -/
theorem connDiffSection_covGrad_eq_covDerivConnDiff
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
          (om x))
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
      om x (fun _ : Fin 1 => covDerivConnDiff (I := I) g₀ g₁ X Z Y x) := by
  classical

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) x
    (om x) (Fin.cons (X x) (Fin.cons (Y x) ![Z x]))]

  rw [show (Fin.cons (X x) (Fin.cons (Y x) ![Z x]) : Fin 3 → TangentSpace I x) 0 = X x from rfl]
  rw [show Matrix.vecTail (Fin.cons (X x) (Fin.cons (Y x) ![Z x]) : Fin 3 → TangentSpace I x)
        = Fin.cons (Y x) ![Z x] from by
      funext k; simp only [Matrix.vecTail, Function.comp]
      refine Fin.cases rfl (fun j => ?_) k
      refine Fin.cases rfl (fun j' => ?_) j
      exact j'.elim0]

  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      tensorCovDerivAt (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) x (X x)) (om x)
      = _ from connDiffSection_tensorCovDerivAt_homSplit (I := I) g₁ g₀ om X x]

  rw [show Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
            (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) x (X x) -
          connDiffPairing (I := I) g₁ g₀ x
            (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
              (fun y : M => om y) x (X x)))
        (Fin.cons (Y x) ![Z x]) =
      Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
            (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) x (X x))
          (Fin.cons (Y x) ![Z x])
        - Tensor0SSpace.toModel
            (connDiffPairing (I := I) g₁ g₀ x
              (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
                (fun y : M => om y) x (X x)))
            (Fin.cons (Y x) ![Z x]) from by
      rw [Tensor0SSpace.toModel_sub]; rfl]

  rw [connDiffPairing_covariantDerivative02_eval (I := I) g₁ g₀ om X Y Z x]

  rw [show Tensor0SSpace.toModel
        (connDiffPairing (I := I) g₁ g₀ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => om y) x (X x)))
        (Fin.cons (Y x) ![Z x]) =
      connDiffPairing (I := I) g₁ g₀ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) from rfl]
  rw [connDiffPairing_covariantDerivative01_eval (I := I) g₁ g₀ om X Y Z x]

  have hvec : covDerivConnDiff (I := I) g₀ g₁ X Z Y x =
      (LeviCivita (I := I) g₀).toFun (fun b => connDiff (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)
        - connDiff (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
        - connDiff (I := I) g₁ g₀ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)) := by

    have hexpand : covDerivConnDiff (I := I) g₀ g₁ X Z Y x =
        (LeviCivita (I := I) g₀).toFun (fun b => connDiff (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)
          - connDiff (I := I) g₁ g₀ x (Y x)
              ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
          - connDiff (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x))
              (Z x) := rfl
    rw [hexpand]; abel
  rw [show (fun _ : Fin 1 => covDerivConnDiff (I := I) g₀ g₁ X Z Y x)
      = (fun _ : Fin 1 =>
          (LeviCivita (I := I) g₀).toFun (fun b => connDiff (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)
            - connDiff (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
            - connDiff (I := I) g₁ g₀ x (Y x)
                ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      from by funext k; rw [hvec]]

  rw [tensor0SOne_apply_sub (I := I) x (om x), tensor0SOne_apply_sub (I := I) x (om x)]
  ring

end Connection
end Integral
end DifferentialGeometry
