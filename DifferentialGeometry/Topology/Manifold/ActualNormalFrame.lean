import DifferentialGeometry.Topology.Manifold.ActualNormalProjectorSmooth
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! Actual varying orthogonal normal frames with smooth inverse coordinates. -/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]

def actualNormalChangeOperator (p x : Z) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - actualZeroSetNormalProjector k Z p +
    (actualZeroSetNormalProjector k Z x).comp (actualZeroSetNormalProjector k Z p)

def actualNormalFrameSynthesis (p x : Z) : (actualZeroSetTangentSpace k Z p)ᗮ →L[ℝ] H :=
  (actualZeroSetNormalProjector k Z x).comp (actualZeroSetTangentSpace k Z p)ᗮ.subtypeL

def actualNormalFrameCoordinates (p x : Z) : H →L[ℝ] (actualZeroSetTangentSpace k Z p)ᗮ :=
  (actualZeroSetTangentSpace k Z p)ᗮ.orthogonalProjectionOnto.comp
    (actualNormalChangeOperator (k := k) p x).inverse

theorem actualNormalChangeOperator_self (p : Z) :
    actualNormalChangeOperator (k := k) p p = ContinuousLinearMap.id ℝ H := by
  ext n
  change n - (actualZeroSetTangentSpace k Z p)ᗮ.starProjection n +
    (actualZeroSetTangentSpace k Z p)ᗮ.starProjection
      ((actualZeroSetTangentSpace k Z p)ᗮ.starProjection n) = n
  rw [Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem _ n)]
  abel

theorem finrank_actual_normal
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) (p : Z) :
    Module.finrank ℝ (actualZeroSetTangentSpace k Z p)ᗮ = Module.finrank ℝ H - k := by
  have ht : Module.finrank ℝ (actualZeroSetTangentSpace k Z p) = k := by
    have hi := hemb.isImmersion.mfderiv_injective (by simp) p
    have hh := LinearMap.finrank_range_of_inj hi
    change Module.finrank ℝ (actualZeroSetTangentSpace k Z p) =
      Module.finrank ℝ (Fin k → ℝ) at hh
    simpa using hh
  have hs := (actualZeroSetTangentSpace k Z p).finrank_add_finrank_orthogonal
  omega

theorem actualNormalChangeOperator_normal (p x : Z)
    (n : (actualZeroSetTangentSpace k Z p)ᗮ) :
    actualNormalChangeOperator (k := k) p x (n : H) =
      actualNormalFrameSynthesis (k := k) p x n := by
  change (n : H) - (actualZeroSetTangentSpace k Z p)ᗮ.starProjection (n : H) +
    actualZeroSetNormalProjector k Z x
      ((actualZeroSetTangentSpace k Z p)ᗮ.starProjection (n : H)) = _
  rw [Submodule.starProjection_eq_self_iff.mpr n.property, sub_self, zero_add]
  rfl

theorem actualNormalFrameSynthesis_range
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H))
    (p x : Z) (hi : (actualNormalChangeOperator (k := k) p x).IsInvertible) :
    LinearMap.range (actualNormalFrameSynthesis (k := k) p x).toLinearMap =
      (actualZeroSetTangentSpace k Z x)ᗮ := by
  have hj : Function.Injective (actualNormalFrameSynthesis (k := k) p x) := by
    intro n m hnm
    apply Subtype.ext
    apply hi.injective
    simpa only [actualNormalChangeOperator_normal] using hnm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro n ⟨m, rfl⟩
    exact Submodule.starProjection_apply_mem _ _
  · rw [LinearMap.finrank_range_of_inj hj, finrank_actual_normal hemb p,
      finrank_actual_normal hemb x]

theorem actualNormalFrameCoordinates_synthesis (p x : Z)
    (hi : (actualNormalChangeOperator (k := k) p x).IsInvertible)
    (n : (actualZeroSetTangentSpace k Z p)ᗮ) :
    actualNormalFrameCoordinates (k := k) p x (actualNormalFrameSynthesis (k := k) p x n) = n := by
  apply Subtype.ext
  change (actualZeroSetTangentSpace k Z p)ᗮ.starProjection
    ((actualNormalChangeOperator (k := k) p x).inverse
      (actualNormalFrameSynthesis (k := k) p x n)) = (n : H)
  rw [← actualNormalChangeOperator_normal, hi.inverse_apply_self]
  exact Submodule.starProjection_eq_self_iff.mpr n.property

theorem actualNormalFrameSynthesis_coordinates
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H))
    (p x : Z) (hi : (actualNormalChangeOperator (k := k) p x).IsInvertible)
    (n : H) (hn : n ∈ (actualZeroSetTangentSpace k Z x)ᗮ) :
    actualNormalFrameSynthesis (k := k) p x (actualNormalFrameCoordinates (k := k) p x n) = n := by
  rw [← actualNormalFrameSynthesis_range hemb p x hi] at hn
  obtain ⟨m, rfl⟩ := hn
  exact congrArg (actualNormalFrameSynthesis (k := k) p x)
    (actualNormalFrameCoordinates_synthesis p x hi m)

def actualNormalFrameDomain (p : Z) : Set Z :=
  {x | (actualNormalChangeOperator (k := k) p x).IsInvertible}

theorem mem_actualNormalFrameDomain (p : Z) : p ∈ actualNormalFrameDomain (k := k) p := by
  change (actualNormalChangeOperator (k := k) p p).IsInvertible
  rw [actualNormalChangeOperator_self]
  exact ⟨ContinuousLinearEquiv.refl ℝ H, rfl⟩

variable [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z]

theorem contMDiff_actualNormalChangeOperator
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) (p : Z) :
    ContMDiff 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H →L[ℝ] H) ∞
      (actualNormalChangeOperator (k := k) p) :=
  contMDiff_const.add
    ((contMDiff_actualZeroSetNormalProjector hemb).clm_comp contMDiff_const)

theorem contMDiff_actualNormalFrameSynthesis
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) (p : Z) :
    ContMDiff 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, (actualZeroSetTangentSpace k Z p)ᗮ →L[ℝ] H) ∞
      (actualNormalFrameSynthesis (k := k) p) :=
  (contMDiff_actualZeroSetNormalProjector hemb).clm_comp contMDiff_const

theorem contMDiffAt_actualNormalFrameCoordinates
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H))
    (p x : Z) (hi : (actualNormalChangeOperator (k := k) p x).IsInvertible) :
    ContMDiffAt 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H →L[ℝ] (actualZeroSetTangentSpace k Z p)ᗮ) ∞
      (actualNormalFrameCoordinates (k := k) p) x := by
  have hinv : ContMDiffAt 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H →L[ℝ] H) ∞
      (fun y => (actualNormalChangeOperator (k := k) p y).inverse) x :=
    hi.contDiffAt_map_inverse.contMDiffAt.comp x
      (contMDiff_actualNormalChangeOperator hemb p x)
  exact contMDiffAt_const.clm_comp hinv

theorem exists_actualNormalFrame_neighbourhood
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) (p : Z) :
    ∃ O : TopologicalSpace.Opens Z, p ∈ O ∧
      ContMDiffOn 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, (actualZeroSetTangentSpace k Z p)ᗮ →L[ℝ] H) ∞
        (actualNormalFrameSynthesis (k := k) p) O ∧
      ContMDiffOn 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H →L[ℝ] (actualZeroSetTangentSpace k Z p)ᗮ) ∞
        (actualNormalFrameCoordinates (k := k) p) O ∧
      ∀ x ∈ O, (actualNormalChangeOperator (k := k) p x).IsInvertible ∧
        LinearMap.range (actualNormalFrameSynthesis (k := k) p x).toLinearMap =
          (actualZeroSetTangentSpace k Z x)ᗮ ∧
        (∀ n, actualNormalFrameCoordinates (k := k) p x
          (actualNormalFrameSynthesis (k := k) p x n) = n) ∧
        ∀ n ∈ (actualZeroSetTangentSpace k Z x)ᗮ,
          actualNormalFrameSynthesis (k := k) p x
            (actualNormalFrameCoordinates (k := k) p x n) = n := by
  let O : TopologicalSpace.Opens Z :=
    ⟨{x | (actualNormalChangeOperator (k := k) p x).IsInvertible},
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
      (contMDiff_actualNormalChangeOperator hemb p).continuous⟩
  have hp : p ∈ O := by
    change (actualNormalChangeOperator (k := k) p p).IsInvertible
    rw [actualNormalChangeOperator_self]
    exact ⟨ContinuousLinearEquiv.refl ℝ H, rfl⟩
  refine ⟨O, hp, (contMDiff_actualNormalFrameSynthesis hemb p).contMDiffOn, ?_, ?_⟩
  · intro x hx
    exact (contMDiffAt_actualNormalFrameCoordinates hemb p x hx).contMDiffWithinAt
  · intro x hx
    exact ⟨hx, actualNormalFrameSynthesis_range hemb p x hx,
      actualNormalFrameCoordinates_synthesis p x hx,
      actualNormalFrameSynthesis_coordinates hemb p x hx⟩

theorem isOpen_actualNormalFrameDomain
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) (p : Z) :
    IsOpen (actualNormalFrameDomain (k := k) p) :=
  ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (contMDiff_actualNormalChangeOperator hemb p).continuous

def actualNormalFrameHomeomorph
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) (p : Z) :
    {yn : Z × H | yn.1 ∈ actualNormalFrameDomain (k := k) p ∧
      yn.2 ∈ (actualZeroSetTangentSpace k Z yn.1)ᗮ} ≃ₜ
        actualNormalFrameDomain (k := k) p × (actualZeroSetTangentSpace k Z p)ᗮ where
  toFun yn := (⟨yn.val.1, yn.property.1⟩,
    actualNormalFrameCoordinates (k := k) p yn.val.1 yn.val.2)
  invFun xv := ⟨((xv.1 : Z), actualNormalFrameSynthesis (k := k) p xv.1 xv.2),
    xv.1.property, Submodule.starProjection_apply_mem _ _⟩
  left_inv yn := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact actualNormalFrameSynthesis_coordinates hemb p yn.val.1 yn.property.1
      yn.val.2 yn.property.2
  right_inv xv := by
    refine Prod.ext rfl ?_
    exact actualNormalFrameCoordinates_synthesis p xv.1 xv.1.property xv.2
  continuous_toFun := by
    have hc : Continuous (fun x : actualNormalFrameDomain (k := k) p =>
        actualNormalFrameCoordinates (k := k) p x.val) :=
      continuousOn_iff_continuous_domRestrict.mp (fun x hx =>
        (contMDiffAt_actualNormalFrameCoordinates hemb p x hx).continuousAt.continuousWithinAt)
    have hx : Continuous (fun yn : {yn : Z × H |
        yn.1 ∈ actualNormalFrameDomain (k := k) p ∧
          yn.2 ∈ (actualZeroSetTangentSpace k Z yn.1)ᗮ} =>
        (⟨yn.val.1, yn.property.1⟩ : actualNormalFrameDomain (k := k) p)) := by fun_prop
    exact hx.prodMk ((hc.comp hx).clm_apply (by fun_prop))
  continuous_invFun := by
    have hs := (contMDiff_actualNormalFrameSynthesis hemb p).continuous
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      ((hs.comp (continuous_subtype_val.comp continuous_fst)).clm_apply
        continuous_snd) |>.subtype_mk _

theorem contMDiffOn_actualNormalFrame_transition
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) (p q : Z) :
    ContMDiffOn 𝓘(ℝ, Fin k → ℝ)
      𝓘(ℝ, (actualZeroSetTangentSpace k Z p)ᗮ →L[ℝ] (actualZeroSetTangentSpace k Z q)ᗮ) ∞
      (fun x => (actualNormalFrameCoordinates (k := k) q x).comp
        (actualNormalFrameSynthesis (k := k) p x))
      (actualNormalFrameDomain (k := k) p ∩ actualNormalFrameDomain (k := k) q) := by
  intro x hx
  exact ((contMDiffAt_actualNormalFrameCoordinates hemb q x hx.2).clm_comp
    (contMDiff_actualNormalFrameSynthesis hemb p x)).contMDiffWithinAt

end GC.MetricGeometry
