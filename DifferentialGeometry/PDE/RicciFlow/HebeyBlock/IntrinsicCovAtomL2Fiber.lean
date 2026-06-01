import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2Atoms
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberFromModelOpNormUnconditional

/-!
# Fibre-form covariant-derivative atom `L²` bound

The per-`α` covariant-derivative atom `L²` bound
`exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq`
controls the `L²`-norm of the partition-of-unity-weighted square-root sum

```
ρ_α(b) · √(∑ₖ ‖(triv α).continuousLinearMapAt b (∇^chart_k S)‖²)
```

where the per-`k` covariant-derivative atoms `∇^chart_k S` are measured
through the chart-`α` forward trivialisation in the honest model-space norm on
`TensorRSModel r s ℝ E`.

This file converts that bound into the **intrinsic fibre-norm form**, in which
each per-`k` atom is measured by the genuine Riemannian fibre norm on
`TensorRSSpace r s I b` induced by the tangent-bundle metric `g`:

```
ρ_α(b) · √(∑ₖ ‖∇^chart_k S‖²_Riem).
```

The conversion is unconditional (no chart-locality predicate). The engine is
the unconditional uniform op-norm bound on the chart-`(r, s)` inverse
trivialisation
`tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional`,
applied over the compact `tsupport` of the chart-`α` partition of unity. The
round-trip identity `(triv α).symmL (continuousLinearMapAt X) = X` on the
trivialisation base set turns the inverse-trivialisation op-norm bound into a
pointwise estimate `‖X‖_Riem ≤ C · ‖(triv α).continuousLinearMapAt X‖_model`
on the fibre, which is then squared, summed over `k`, square-rooted, and
integrated. The squared op-norm constant is absorbed into the final per-`α`
`L²` constant.

The resulting atom matches, up to the `eLpNorm`-vs-squared-integral packaging,
the covariant-derivative summand in the intrinsic G1 fibre-norm gradient
decomposition `g_inner_gradFun_le_pou_weighted_fiber_norm_atoms_on_pouTsupport_h1`,
so it is directly consumable by the downstream A.3 assembly.

## Public theorem

* `exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm` — the
  fibre-norm per-`α` covariant-derivative atom `L²` bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The `tsupport` of the chart-atlas partition-of-unity weight at `α` is
compact (closed in a compact ambient space). -/
private lemma covAtom_pouTsupport_isCompact (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

/-- The `tsupport` of the chart-atlas partition-of-unity weight at `α` is
contained in the chart-`α` source. -/
private lemma covAtom_pouTsupport_subset_chartSource (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  chartAtlasPOU_isSubordinate (I := I) (M := M) α

/-- Membership in the chart-`α` source upgrades to membership in the
chart-`(r, s)` trivialisation base set. -/
private lemma covAtom_mem_baseSet_of_mem_chartSource
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source) :
    b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
  change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet
  refine ⟨?_, ?_⟩
  all_goals
    change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hb

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-`α` fibre-norm covariant-derivative atom `L²` bound.** For a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, and a chart base point `α`,
there is a non-negative real constant `C` (depending only on `(g, r, s, α)`)
such that for every smooth compactly-supported `H¹` tensor section
`S : SmoothCcTensorH1 g r s` and all multi-indices `Idx, Jdx`,

```
eLpNorm
    (fun b ↦ ρ_α(b) · √(∑ₖ ‖∇^chart_k S(b)‖²))
    2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C · (‖S‖₊ : ℝ≥0∞),
```

where `ρ_α` is the chart-atlas partition-of-unity weight at `α` and the fibre
norm `‖·‖` on `TensorRSSpace r s I b` is the `g`-induced
`Bundle.RiemannianBundle` norm (installed via `letI`), matching the convention
of the unconditional op-norm bounds. The constant `C` is independent of `S`,
of the multi-indices, and of the base point. -/
theorem exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (_Idx : Fin r → Fin (Module.finrank ℝ E))
        (_Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  (∑ k : Fin (Module.finrank ℝ E),
                    ‖chartTensorRSCovariantDerivative (I := I) r s g α
                        (fun b' => S.toCcTensor.toSection b')
                        (chartBasisVecFiber (I := I) α k) b‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨Cg2, hCg2_nn, hG2⟩ :=
    exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
      (I := I) (M := M) g r s α
  have hK_cpt :
      IsCompact (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    covAtom_pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (chartAt H α).source :=
    covAtom_pouTsupport_subset_chartSource (I := I) (M := M) α
  obtain ⟨Cop, hCop_pos, hCop_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  have hCop_nn : 0 ≤ Cop := le_of_lt hCop_pos
  refine ⟨Cop * Cg2, mul_nonneg hCop_nn hCg2_nn, ?_⟩
  intro S _Idx _Jdx
  set gF : M → ℝ := fun b : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b‖ ^ 2)
    with hgF_def
  set gM : M → ℝ := fun b : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)
    with hgM_def
  have h_ptwise : ∀ b : M, gF b ≤ Cop * gM b := by
    intro b
    by_cases hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    · have hb_chart : b ∈ (chartAt H α).source := hK_sub hb
      have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet :=
        covAtom_mem_baseSet_of_mem_chartSource (I := I) (M := M) r s α hb_chart
      have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
        (chartAtlasPOU I M).nonneg α b
      have h_per_k : ∀ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b‖ ^ 2 ≤
            Cop ^ 2 *
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2 := by
        intro k
        set X : TensorRSSpace r s I b :=
          chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b with hX_def
        set v : TensorRSModel r s ℝ E :=
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X
          with hv_def
        have h_roundtrip :
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
              TensorRSSpace r s I b) = X := by
          rw [hv_def]
          exact (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).symmL_continuousLinearMapAt
            (R := ℝ) hb_base X
        have h_op : ‖((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
              TensorRSSpace r s I b)‖ ≤ Cop * ‖v‖ :=
          hCop_bound b hb v
        rw [h_roundtrip] at h_op
        have hX_nn : 0 ≤ ‖X‖ := norm_nonneg _
        have h_sq := mul_self_le_mul_self hX_nn h_op
        have h_lhs : ‖X‖ * ‖X‖ = ‖X‖ ^ 2 := by rw [sq]
        have h_rhs : (Cop * ‖v‖) * (Cop * ‖v‖) = Cop ^ 2 * ‖v‖ ^ 2 := by ring
        rw [hv_def] at h_sq ⊢
        nlinarith [h_sq, h_lhs, h_rhs]
      have h_sum_le :
          (∑ k : Fin (Module.finrank ℝ E),
            ‖chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b‖ ^ 2) ≤
            Cop ^ 2 *
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun k _ => h_per_k k)
      have h_sumF_nn :
          0 ≤ ∑ k : Fin (Module.finrank ℝ E),
            ‖chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b‖ ^ 2 :=
        Finset.sum_nonneg (fun k _ => sq_nonneg _)
      have h_sumM_nn :
          0 ≤ ∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b)‖ ^ 2 :=
        Finset.sum_nonneg (fun k _ => sq_nonneg _)
      have h_sqrt_le :
          Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b‖ ^ 2) ≤
            Cop *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖(trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                    (chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) := by
        have h1 := Real.sqrt_le_sqrt h_sum_le
        rwa [Real.sqrt_mul (sq_nonneg Cop), Real.sqrt_sq hCop_nn] at h1
      have h_mul :=
        mul_le_mul_of_nonneg_left h_sqrt_le hρ_nn
      rw [hgF_def, hgM_def]
      calc ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b‖ ^ 2)
            ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                (Cop *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖(trivializationAt (TensorRSModel r s ℝ E)
                          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                            ℝ b
                        (chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := h_mul
          _ = Cop *
                (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖(trivializationAt (TensorRSModel r s ℝ E)
                          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                            ℝ b
                        (chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := by ring
    · have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
        by_contra hne
        exact hb (subset_tsupport _ hne)
      simp only [hgF_def, hgM_def, hρ_zero, zero_mul, mul_zero, le_refl]
  have hgF_nn : ∀ b : M, 0 ≤ gF b := by
    intro b
    rw [hgF_def]
    exact mul_nonneg ((chartAtlasPOU I M).nonneg α b)
      (Real.sqrt_nonneg _)
  have h_mono :
      eLpNorm gF 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine eLpNorm_mono_real (fun b => ?_)
    rw [Real.norm_of_nonneg (hgF_nn b)]
    simpa [Pi.smul_apply, smul_eq_mul] using h_ptwise b
  have h_smul :
      eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) =
        ENNReal.ofReal Cop *
          eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [eLpNorm_const_smul Cop gM, Real.enorm_eq_ofReal hCop_nn]
  have hG2' :
      eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal Cg2 * (‖S‖₊ : ℝ≥0∞) := by
    rw [hgM_def]; exact hG2 S
  calc eLpNorm gF 2 (riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) := h_mono
    _ = ENNReal.ofReal Cop *
          eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) := h_smul
    _ ≤ ENNReal.ofReal Cop * (ENNReal.ofReal Cg2 * (‖S‖₊ : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left hG2' (zero_le _)
    _ = ENNReal.ofReal (Cop * Cg2) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hCop_nn, mul_assoc]

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry
