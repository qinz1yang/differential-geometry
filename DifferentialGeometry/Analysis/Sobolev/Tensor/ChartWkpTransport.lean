import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpLimit
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition

/-!
# Algebraic chart transport for raw tensor Sobolev sections

The established tensor chart-transition theorem is stated for
`SmoothCcTensor`.  Weak limits in `ChartWkpLimit.lean` are genuine dependent
tensor sections but need not be smooth.  This file isolates the fibrewise
algebra from smoothness and proves the same transition identity for every
`RSTensorSection`.

The main specialization, `secPull_raw_trans`, computes a target-chart raw
component of `secModelPull β v` as a finite sum of the scalar components of
the arbitrary model field `v`, multiplied by the existing smooth
`transitionCoeff`.  This is the exact algebraic input for a later scalar
cross-chart `W^{k,p}` estimate; no regularity is assumed here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The tensor-bundle trivialization used in the raw-section transition
proof.  It is definitionally the trivialization used by `transitionCoeff`. -/
@[reducible] private def rawRSTriv (r s : ℕ) (α : M) :
    Trivialization (TensorRSModel r s ℝ E)
      (Bundle.TotalSpace.proj (F := TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y)) :=
  trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α

private theorem rawRSTriv_base (r s : ℕ) (α : M) :
    (rawRSTriv (E := E) (I := I) (M := M) r s α).baseSet =
      (chartAt H α).source := by
  classical
  change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet) =
    (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet =
        (chartAt H α).source
  rw [Set.inter_self]
  rfl

private theorem coordChange_apply
    (r s : ℕ) (γ α : M) {x : M}
    (hxγ : x ∈ (chartAt H γ).source) (hxα : x ∈ (chartAt H α).source)
    (w : TensorRSModel r s ℝ E) :
    ((rawRSTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
        (rawRSTriv (E := E) (I := I) (M := M) r s α) x) w =
      (rawRSTriv (E := E) (I := I) (M := M) r s α).continuousLinearMapAt ℝ x
        ((rawRSTriv (E := E) (I := I) (M := M) r s γ).symmL ℝ x w) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  have hxγ' : x ∈
      (rawRSTriv (E := E) (I := I) (M := M) r s γ).baseSet := by
    rw [rawRSTriv_base]
    exact hxγ
  have hxα' : x ∈
      (rawRSTriv (E := E) (I := I) (M := M) r s α).baseSet := by
    rw [rawRSTriv_base]
    exact hxα
  rw [Bundle.Trivialization.coordChangeL_apply _ _ ⟨hxγ', hxα'⟩,
    Bundle.Trivialization.continuousLinearMapAt_apply,
    Bundle.Trivialization.coe_linearMapAt_of_mem _ hxα',
    Bundle.Trivialization.symmL_apply]

/-- On a chart overlap, the model value of an arbitrary raw section changes
by the standard bundle coordinate-change map. -/
theorem secTriv_trans
    (r s : ℕ) (S : RSTensorSection I M r s) (γ α : M) {x : M}
    (hxγ : x ∈ (chartAt H γ).source) (hxα : x ∈ (chartAt H α).source) :
    secTriv (I := I) (M := M) r s S α x =
      ((rawRSTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
        (rawRSTriv (E := E) (I := I) (M := M) r s α) x)
        (secTriv (I := I) (M := M) r s S γ x) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  have hxγ' : x ∈
      (rawRSTriv (E := E) (I := I) (M := M) r s γ).baseSet := by
    rw [rawRSTriv_base]
    exact hxγ
  rw [coordChange_apply (E := E) (I := I) (M := M)
    r s γ α hxγ hxα]
  unfold secTriv
  rw [(rawRSTriv (E := E) (I := I) (M := M) r s γ)
    .symmL_continuousLinearMapAt hxγ' (S x)]

/-- The explicit finite transition formula for an arbitrary genuine raw
tensor section.  No smoothness or Sobolev membership is used. -/
theorem secCompRaw_trans
    (r s : ℕ) (S : RSTensorSection I M r s) (γ α : M)
    (P₀ : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∈ (chartAt H γ).source ∩ (chartAt H α).source) :
    secCompRaw (I := I) (M := M) r s S α P₀.1 P₀.2 x =
      ∑ Q : TensorCompIdx (E := E) r s,
        transitionCoeff (E := E) (I := I) (M := M)
            r s γ α P₀ Q x *
          secCompRaw (I := I) (M := M) r s S γ Q.1 Q.2 x := by
  classical
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  obtain ⟨hxγ, hxα⟩ := hx
  unfold secCompRaw
  rw [secTriv_trans (E := E) (I := I) (M := M)
    r s S γ α hxγ hxα]
  set L : TensorRSModel r s ℝ E ≃L[ℝ] TensorRSModel r s ℝ E :=
    (rawRSTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
      (rawRSTriv (E := E) (I := I) (M := M) r s α) x with hL_def
  have hsum := tensorRSModel_eq_sum_basis (E := E) r s
    (secTriv (I := I) (M := M) r s S γ x)
  conv_lhs => rw [hsum]
  rw [show (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx
                (secTriv (I := I) (M := M) r s S γ x) •
              tensorChartBasisElement (E := E) r s Idx Jdx) =
        ∑ Q : TensorCompIdx (E := E) r s,
          tensorChartComponentProjection (E := E) r s Q.1 Q.2
              (secTriv (I := I) (M := M) r s S γ x) •
            tensorChartBasisElement (E := E) r s Q.1 Q.2 from
    (Finset.sum_product'
      (s := (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))))
      (t := (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
      (f := fun Idx Jdx =>
        tensorChartComponentProjection (E := E) r s Idx Jdx
            (secTriv (I := I) (M := M) r s S γ x) •
          tensorChartBasisElement (E := E) r s Idx Jdx)).symm]
  rw [map_sum L,
    map_sum (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2)]
  refine Finset.sum_congr rfl ?_
  intro Q _
  rw [map_smul L,
    map_smul (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2),
    smul_eq_mul]
  rw [show tensorChartComponentProjection (E := E) r s P₀.1 P₀.2
          (L (tensorChartBasisElement (E := E) r s Q.1 Q.2)) =
        transitionCoeff (E := E) (I := I) (M := M)
          r s γ α P₀ Q x from by
      rw [hL_def]
      rfl]
  ring

/-- In the source chart, trivializing `secModelPull α v` recovers the model
field `v` at the corresponding Euclidean coordinate. -/
theorem secPull_triv_eq
    (r s : ℕ) (α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      TensorRSModel r s ℝ E)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    secTriv (I := I) (M := M) r s
        (secModelPull (I := I) (M := M) r s α v) α x =
      v (toEuclidean (extChartAt I α x)) := by
  have hx' : x ∈
      (rawRSTriv (E := E) (I := I) (M := M) r s α).baseSet := by
    rw [rawRSTriv_base]
    exact hx
  unfold secTriv secModelPull
  rw [dif_pos hx]
  exact (rawRSTriv (E := E) (I := I) (M := M) r s α)
    .continuousLinearMapAt_symmL hx' _

/-- In its source chart, the raw component of `secModelPull α v` is exactly
the corresponding scalar projection of `v`. -/
theorem secPull_raw_eq
    (r s : ℕ) (α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      TensorRSModel r s ℝ E)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    secCompRaw (I := I) (M := M) r s
        (secModelPull (I := I) (M := M) r s α v) α Idx Jdx x =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        (v (toEuclidean (extChartAt I α x))) := by
  unfold secCompRaw
  rw [secPull_triv_eq (E := E) (I := I) (M := M) r s α v hx]

/-- A target-chart raw component of a pulled-back weak model field is a finite
transition-coefficient sum of the scalar source-model components. -/
theorem secPull_raw_trans
    (r s : ℕ) (β α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      TensorRSModel r s ℝ E)
    (P₀ : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∈ (chartAt H β).source ∩ (chartAt H α).source) :
    secCompRaw (I := I) (M := M) r s
        (secModelPull (I := I) (M := M) r s β v) α P₀.1 P₀.2 x =
      ∑ Q : TensorCompIdx (E := E) r s,
        transitionCoeff (E := E) (I := I) (M := M)
            r s β α P₀ Q x *
          tensorChartComponentProjection (E := E) r s Q.1 Q.2
            (v (toEuclidean (extChartAt I β x))) := by
  rw [secCompRaw_trans (E := E) (I := I) (M := M)
    r s (secModelPull (I := I) (M := M) r s β v) β α P₀ hx]
  refine Finset.sum_congr rfl ?_
  intro Q _
  rw [secPull_raw_eq (E := E) (I := I) (M := M)
    r s β v Q.1 Q.2 hx.1]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
