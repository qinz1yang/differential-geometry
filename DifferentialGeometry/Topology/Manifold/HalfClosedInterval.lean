import DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false
noncomputable section
open Set Manifold IsManifold
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Topology.Handle

namespace DifferentialGeometry.Topology.Manifold

private def intervalOpen (a b : ℝ) : TopologicalSpace.Opens (Icc a b) :=
  ⟨{p | p.val < b}, isOpen_lt continuous_subtype_val continuous_const⟩

private def intervalHomeomorph (a b : ℝ) : Ico a b ≃ₜ intervalOpen a b where
  toFun p := ⟨⟨p.val, p.property.1, p.property.2.le⟩, p.property.2⟩
  invFun p := ⟨p.val.val, p.val.property.1, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[reducible] def halfClosedIntervalChartedSpace {a b : ℝ} (hab : a < b) :
    ChartedSpace (EuclideanHalfSpace 1) (Ico a b) := by
  let : Fact (a < b) := ⟨hab⟩
  exact chartedSpaceOfHomeomorph (intervalHomeomorph a b)

theorem halfClosedInterval_isManifold {a b : ℝ} (hab : a < b) :
    letI := halfClosedIntervalChartedSpace hab
    IsManifold (𝓡∂ 1) ∞ (Ico a b) := by
  let : Fact (a < b) := ⟨hab⟩
  exact isManifoldOfHomeomorph (𝓡∂ 1) (intervalHomeomorph a b)

private def intervalDiffeomorph {a b : ℝ} (hab : a < b) :
    letI : Fact (a < b) := ⟨hab⟩
    letI := halfClosedIntervalChartedSpace hab
    Ico a b ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ intervalOpen a b := by
  let : Fact (a < b) := ⟨hab⟩
  let := halfClosedIntervalChartedSpace hab
  exact
    { toEquiv := (intervalHomeomorph a b).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (intervalHomeomorph a b) (𝓡∂ 1) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (intervalHomeomorph a b) (𝓡∂ 1) ∞ }

theorem halfClosedInterval_boundary_eq {a b : ℝ} (hab : a < b) :
    letI := halfClosedIntervalChartedSpace hab
    (𝓡∂ 1).boundary (Ico a b) = {p | p.val = a} := by
  let : Fact (a < b) := ⟨hab⟩
  let := halfClosedIntervalChartedSpace hab
  let := halfClosedInterval_isManifold hab
  rw [← (intervalDiffeomorph hab).preimage_boundary (by simp),
    ModelWithCorners.boundary_open, boundary_Icc]
  ext p
  simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, Subtype.ext_iff]
  change p.val = a ∨ p.val = b ↔ p.val = a
  exact or_iff_left p.property.2.ne

theorem halfClosedInterval_extChartAt_apply {a b : ℝ} (hab : a < b) (p q : Ico a b) :
    letI := halfClosedIntervalChartedSpace hab
    (extChartAt (𝓡∂ 1) p q) 0 = q.val - a := by
  let : Fact (a < b) := ⟨hab⟩
  let := halfClosedIntervalChartedSpace hab
  change ((chartAt (EuclideanHalfSpace 1)
    (⟨p.val, p.property.1, p.property.2.le⟩ : Icc a b))
    (⟨q.val, q.property.1, q.property.2.le⟩ : Icc a b)).val 0 = q.val - a
  rw [Icc_chartedSpaceChartAt_of_le_top p.property.2]
  rfl

theorem isSmoothEmbedding_halfClosedInterval_inclusion {a b : ℝ} (hab : a < b) :
    letI := halfClosedIntervalChartedSpace hab
    IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ) ∞ (Subtype.val : Ico a b → ℝ) := by
  let : Fact (a < b) := ⟨hab⟩
  let := halfClosedIntervalChartedSpace hab
  let := halfClosedInterval_isManifold hab
  refine ⟨?_, _root_.Topology.IsEmbedding.subtypeVal⟩
  suffices h : IsImmersionOfComplement Unit (𝓡∂ 1) 𝓘(ℝ) ∞
      (Subtype.val : Ico a b → ℝ) from h.isImmersion
  intro p
  let φ := (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 1)) Unit).trans
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))
  refine IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt φ
    (chartAt (EuclideanHalfSpace 1) p) (Homeomorph.addLeft (-a)).toOpenPartialHomeomorph
    (mem_chart_source _ p) (mem_univ _) (chart_mem_maximalAtlas _) ?_ ?_
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => -a + t)).contMDiff.contMDiffOn
    · simpa [Homeomorph.addLeft] using
        (show ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => a + t) univ from
          (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => a + t)).contMDiff.contMDiffOn)
  · intro z hz
    have heq := ((chartAt (EuclideanHalfSpace 1) p).extend (𝓡∂ 1)).right_inv hz
    have heq0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) heq
    change (extChartAt (𝓡∂ 1) p ((extChartAt (𝓡∂ 1) p).symm z)) 0 = z 0 at heq0
    rw [halfClosedInterval_extChartAt_apply hab] at heq0
    change -a + ((extChartAt (𝓡∂ 1) p).symm z).val = z 0
    linarith

end DifferentialGeometry.Topology.Manifold
