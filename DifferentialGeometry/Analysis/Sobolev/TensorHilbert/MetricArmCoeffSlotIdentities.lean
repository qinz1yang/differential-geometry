import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffPassZero
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCoefficientReindexing

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.RSTensor

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma armSlotFib_toModel_apply (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1) → E) :
    Tensor0SSpace.toModel (armSlotFib (I := I) (M := M) s x Arm D) v =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          (Arm ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))) D)
        (Matrix.vecTail v) := by
  exact armSlotFib_apply_eval (I := I) (M := M) s x Arm D
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem armSlotEndoCc_succ
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    bilinearSlotInsertionCoefficient (I := I) (M := M) g (s + 1) A =
      reindexCoeffGen (I := I) (M := M) g (s + 1 + 1) (s + 1 + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g
          (s + 1 + 1) (s + 1 + 1 + 1)
          ((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2))
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  dsimp only
  rw [armSlotEndoCc_toSection]
  rw [show (TensorRSSpace.ofCLM
      (armSlotFib (I := I) (M := M) (s + 1) x (A x)) :
        Tensor0SSpace (s + 1 + 1) I x →L[ℝ]
          Tensor0SSpace (s + 1 + 1 + 1) I x) D =
    armSlotFib (I := I) (M := M) (s + 1) x (A x) D from rfl]
  rw [armSlotFib_toModel_apply]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply,
    rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1 + 1) =>
      m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
        (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) k)) =
      Fin.cons (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0))
        (fun j : Fin (s + 1 + 1) =>
          m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]]
  rw [DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_eval]
  rw [armSlotEndoCc_toSection]
  rw [show (TensorRSSpace.ofCLM
      (armSlotFib (I := I) (M := M) s x (A x)) :
        Tensor0SSpace (s + 1) I x →L[ℝ]
          Tensor0SSpace (s + 1 + 1) I x)
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Tensor0SSpace.toModel D)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0)))) =
    armSlotFib (I := I) (M := M) s x (A x)
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Tensor0SSpace.toModel D)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0)))) from rfl]
  rw [armSlotFib_toModel_apply]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  simp only [TensorMultilinear.tensor0S_curry_toModel_apply,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => Fin.cases ?_ (fun k₂ => ?_) k₁) k
  · rfl
  · rfl
  · rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem armSlotEndoCc_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    bilinearSlotInsertionCoefficient (I := I) (M := M) g s (A - B) =
      bilinearSlotInsertionCoefficient (I := I) (M := M) g s A -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS : (show Tensor0SSpace (s + 1) I x →L[ℝ]
        Tensor0SSpace (s + 1 + 1) I x from
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g s B).toSection x) D =
      armSlotFib (I := I) (M := M) s x (A x) D -
        armSlotFib (I := I) (M := M) s x (B x) D := by
    rw [show ((bilinearSlotInsertionCoefficient (I := I) (M := M) g s A -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g s B).toSection x) =
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A).toSection x -
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s B).toSection x from rfl]
    rfl
  have hLHS : (show Tensor0SSpace (s + 1) I x →L[ℝ]
        Tensor0SSpace (s + 1 + 1) I x from
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s (A - B)).toSection x) D =
      armSlotFib (I := I) (M := M) s x ((A - B) x) D := rfl
  have hfib : armSlotFib (I := I) (M := M) s x (A x - B x) D =
      armSlotFib (I := I) (M := M) s x (A x) D -
        armSlotFib (I := I) (M := M) s x (B x) D := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp only
    rw [Tensor0SSpace.toModel_sub, sub_apply,
      armSlotFib_toModel_apply, armSlotFib_toModel_apply, armSlotFib_toModel_apply,
      sub_apply,
      slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
        (A x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)))
        (B x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))),
      sub_apply, Tensor0SSpace.toModel_sub,
      sub_apply]
  rw [hLHS, hRHS, show ((A - B) x) = A x - B x from rfl, hfib]

end DifferentialGeometry.Analysis.Sobolev
