import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace IsometryEquiv

open scoped Topology

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

instance instTopologicalSpace : TopologicalSpace (X ≃ᵢ Y) :=
  TopologicalSpace.induced ((⇑) : (X ≃ᵢ Y) → X → Y) inferInstance

theorem isEmbedding_coe : Topology.IsEmbedding ((⇑) : (X ≃ᵢ Y) → X → Y) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

instance instT2Space [T2Space Y] : T2Space (X ≃ᵢ Y) :=
  isEmbedding_coe.t2Space

instance instContinuousEvalConst : ContinuousEvalConst (X ≃ᵢ Y) X Y where
  continuous_eval_const x := (continuous_apply x).comp isEmbedding_coe.continuous

theorem continuous_iff {T : Type*} [TopologicalSpace T] {f : T → X ≃ᵢ Y} :
    Continuous f ↔ ∀ x, Continuous (fun t => f t x) := by
  constructor
  · intro h x
    exact (continuous_eval_const x).comp h
  · intro h
    exact isEmbedding_coe.continuous_iff.mpr (continuous_pi h)

instance instContinuousEval : ContinuousEval (X ≃ᵢ Y) X Y where
  continuous_eval := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply EMetric.continuousAt_iff'.mpr
    intro ε hε
    have hpoint : ∀ᶠ q : (X ≃ᵢ Y) × X in 𝓝 p, edist q.2 p.2 < ε / 2 :=
      EMetric.continuousAt_iff'.mp continuous_snd.continuousAt (ε / 2) (ENNReal.half_pos hε.ne')
    have hmap : ∀ᶠ q : (X ≃ᵢ Y) × X in 𝓝 p,
        edist (q.1 p.2) (p.1 p.2) < ε / 2 :=
      EMetric.continuousAt_iff'.mp
        ((continuous_eval_const p.2).comp continuous_fst).continuousAt
        (ε / 2) (ENNReal.half_pos hε.ne')
    filter_upwards [hpoint, hmap] with q hqpoint hqmap
    calc
      edist (q.1 q.2) (p.1 p.2) ≤
          edist (q.1 q.2) (q.1 p.2) + edist (q.1 p.2) (p.1 p.2) := edist_triangle _ _ _
      _ = edist q.2 p.2 + edist (q.1 p.2) (p.1 p.2) := by rw [q.1.edist_eq]
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hqpoint hqmap
      _ = ε := ENNReal.add_halves ε

theorem continuous_trans :
    Continuous (fun p : (X ≃ᵢ Y) × (Y ≃ᵢ Z) => p.1.trans p.2) := by
  apply continuous_iff.mpr
  intro x
  exact continuous_eval.comp
    (continuous_snd.prodMk ((continuous_eval_const x).comp continuous_fst))

theorem continuous_symm : Continuous (fun f : X ≃ᵢ Y => f.symm) := by
  apply continuous_iff.mpr
  intro y
  apply continuous_iff_continuousAt.mpr
  intro f
  apply EMetric.continuousAt_iff'.mpr
  intro ε hε
  have h : ∀ᶠ g : X ≃ᵢ Y in 𝓝 f, edist (g (f.symm y)) (f (f.symm y)) < ε :=
    EMetric.continuousAt_iff'.mp (continuous_eval_const (f.symm y)).continuousAt ε hε
  filter_upwards [h] with g hg
  calc
    edist (g.symm y) (f.symm y) = edist (g (g.symm y)) (g (f.symm y)) :=
      (g.edist_eq _ _).symm
    _ = edist (g (f.symm y)) y := by rw [g.apply_symm_apply, edist_comm]
    _ < ε := by simpa only [f.apply_symm_apply] using hg

instance instIsTopologicalGroup : IsTopologicalGroup (X ≃ᵢ X) where
  continuous_mul := continuous_trans.comp continuous_swap
  continuous_inv := continuous_symm

theorem isEmbedding_toContinuousMap :
    Topology.IsEmbedding (fun f : X ≃ᵢ Y => (f : C(X, Y))) := by
  have hc : Continuous (fun f : X ≃ᵢ Y => (f : C(X, Y))) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_eval
  exact Topology.IsEmbedding.of_comp hc continuous_coeFun isEmbedding_coe

instance instMulAction : MulAction (X ≃ᵢ X) X where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance instIsIsometricSMul : IsIsometricSMul (X ≃ᵢ X) X where
  isometry_smul g := g.isometry

instance instContinuousSMul : ContinuousSMul (X ≃ᵢ X) X where
  continuous_smul := continuous_eval

end IsometryEquiv
