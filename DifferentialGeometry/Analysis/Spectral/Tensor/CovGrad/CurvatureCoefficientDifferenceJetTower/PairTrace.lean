import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Palatini

open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open CurvatureCoefficientDifferenceJetTower

namespace CurvatureCoefficientDifferenceJetTower

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma operatorFieldComposition_zero_left_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (W : SmoothCcTensor g₀ a b) :
    ccOperatorFieldComp (I := I) (M := M) g₀ a b c (0 : SmoothCcTensor g₀ b c) W = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c (0 : SmoothCcTensor g₀ b c) W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
        (0 : SmoothCcTensor g₀ b c).toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((0 : SmoothCcTensor g₀ b c).toSection x) = (0 : TensorRSSpace b c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((0 : SmoothCcTensor g₀ a c).toSection x) = (0 : TensorRSSpace a c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma operatorFieldComposition_right_zero_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ (0 : SmoothCcTensor g₀ a b) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ (0 : SmoothCcTensor g₀ a b)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
          (0 : SmoothCcTensor g₀ a b).toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((0 : SmoothCcTensor g₀ a b).toSection x) = (0 : TensorRSSpace a b I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((0 : SmoothCcTensor g₀ a c).toSection x) = (0 : TensorRSSpace a c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      (0 : TensorRSSpace a b I x)) D) = 0 from rfl]
  rw [map_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_slotExtend_toSection_rsDomDomCongr_b
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
      rsDomDomCongr (I := I) (M := M) (r := r + 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  conv_rhs => rw [hfib, rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
    (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    ((slotExtend (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ)).toSection x) d m]
  conv_rhs => rw [← hfib]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (r + 1) (s + 1)
    (slotExtend (I := I) (M := M) g r s Φ) x d m]
  rw [DifferentialGeometry.Analysis.Spectral.DeTurck.tensorCovDerivAt_slotExtend_eq
    (I := I) (M := M) g r s Φ x (m 0)]
  rw [show Matrix.vecTail m =
      Fin.cons (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k))) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · change m (Fin.succ 0) = _
      rw [Fin.cons_zero]; rfl
    · change m (Fin.succ (Fin.succ i)) = _
      rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g r s Φ x (m 0))
    d (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k)))]
  rw [slotExtend_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x]
  rw [show (fun k => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))
      from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero]
      rw [Equiv.swap_apply_left]
    · rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r (s + 1) x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g r s Φ).toSection x)
    d (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
    ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (m 1))
    (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  have hdir : m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1)))) = m 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  have htail : (Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))) =
      (fun k : Fin s => m (Fin.succ (Fin.succ k))) := by
    funext k
    change m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k))) =
      m (Fin.succ (Fin.succ k))
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.succ_ne_zero _)
    · rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
      exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  rw [hdir, htail]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtend_zero_cc (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    slotExtend (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g r s (0 : SmoothCcTensor g r s)).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (0 : SmoothCcTensor g r s).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((0 : SmoothCcTensor g r s).toSection x) = (0 : TensorRSSpace r s I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (0 : TensorRSSpace r s I x)).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) =
      (0 : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D) from rfl]
  rw [ContinuousLinearMap.zero_comp,
    ContinuousLinearEquiv.map_zero (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
  rw [show ((0 : SmoothCcTensor g (r + 1) (s + 1)).toSection x) =
      (0 : TensorRSSpace (r + 1) (s + 1) I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma rsDomDomCongrSection_zero_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (0 : SmoothCcTensor g r s) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have h0 : ((0 : SmoothCcTensor g r s).toSection x) = (0 : TensorRSSpace r s I x) := by
    rw [SmoothCcTensor.toSection_zero]; rfl
  rw [rsDomDomCongrSection_toSection, h0]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace s I x) (w : Fin s → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace s I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (0 : TensorRSSpace r s I x) D m]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_slotExtend_parallel (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s)
    (hΦ : covGrad (I := I) (M := M) g r s Φ = 0) :
    covGrad (I := I) (M := M) g (r + 1) (s + 1)
      (slotExtend (I := I) (M := M) g r s Φ) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [covGrad_slotExtend_toSection_rsDomDomCongr_b (I := I) (M := M) g r s Φ x]
  rw [hΦ]
  rw [slotExtend_zero_cc (I := I) (M := M) g r (s + 1)]
  rw [show ((0 : SmoothCcTensor g (r + 1) (s + 1 + 1)).toSection x) =
      (0 : TensorRSSpace (r + 1) (s + 1 + 1) I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    (0 : TensorRSSpace (r + 1) (s + 1 + 1) I x) D m]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma slotExtendIter_parallel (g₀ : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c)
    (hΦ : covGrad (I := I) (M := M) g₀ b c Φ = 0) :
    ∀ j : ℕ, covGrad (I := I) (M := M) g₀ (b + j) (c + j)
      (slotExtendIter (I := I) (M := M) g₀ b c j Φ) = 0
  | 0 => hΦ
  | (j + 1) => by
      rw [show slotExtendIter (I := I) (M := M) g₀ b c (j + 1) Φ =
          slotExtend (I := I) (M := M) g₀ (b + j) (c + j)
            (slotExtendIter (I := I) (M := M) g₀ b c j Φ) from rfl]
      exact covGrad_slotExtend_parallel (I := I) (M := M) g₀ (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (slotExtendIter_parallel g₀ b c Φ hΦ j)

omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_operatorFieldComposition_parallel (g₀ : SmoothRiemannianMetric I M)
    (a b c : ℕ) (Φ : SmoothCcTensor g₀ b c)
    (hΦ : covGrad (I := I) (M := M) g₀ b c Φ = 0) (W : SmoothCcTensor g₀ a b) :
    ∀ j : ℕ, iteratedCovGrad (I := I) g₀ a c j (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (iteratedCovGrad (I := I) g₀ a b j W)
  | 0 => by
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | (j + 1) => by
      rw [iteratedCovGrad_succ]
      rw [iteratedCovGrad_operatorFieldComposition_parallel g₀ a b c Φ hΦ W j]
      rw [covGrad_operatorFieldComposition_eq (I := I) (M := M) g₀ a (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (iteratedCovGrad (I := I) g₀ a b j W)]
      rw [slotExtendIter_parallel (I := I) (M := M) g₀ b c Φ hΦ j]
      rw [operatorFieldComposition_zero_left_cc (I := I) (M := M) g₀ a (b + j) ((c + j) + 1)
        (iteratedCovGrad (I := I) g₀ a b j W)]
      rw [zero_add]
      rw [show covGrad (I := I) (M := M) g₀ a (b + j) (iteratedCovGrad (I := I) g₀ a b j W) =
          iteratedCovGrad (I := I) g₀ a b (j + 1) W from
        (iteratedCovGrad_succ (I := I) g₀ a b j W).symm]
      rfl

def phiDtPair (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceField (I := I) g₀ 2) (cometricDoubleTraceField (I := I) g₀ 4)

lemma phiDtPair_covGrad_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 6 2 (phiDtPair (I := I) (M := M) g₀) = 0 := by
  rw [phiDtPair]
  rw [covGrad_operatorFieldComposition_eq (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceField (I := I) g₀ 2) (cometricDoubleTraceField (I := I) g₀ 4)]
  rw [cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2]
  rw [cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 4]
  rw [operatorFieldComposition_zero_left_cc (I := I) (M := M) g₀ 6 4 3
    (cometricDoubleTraceField (I := I) g₀ 4)]
  rw [operatorFieldComposition_right_zero_cc (I := I) (M := M) g₀ 6 5 3
    (slotExtend (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2))]
  rw [add_zero]

def sigmaE0 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensor0S_zero_rank_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) • unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtendIter_two_toModel (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)) from rfl]
  have hkey1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 5)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)))
    (v0 := u 0) (vs := Matrix.vecTail u)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey1
  rw [show (Fin.cons (u 0) (Matrix.vecTail u) : Fin 6 → TangentSpace I x) = u from by
    funext k
    refine Fin.cases rfl (fun i => rfl) k] at hkey1
  rw [← hkey1]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D) (u 0)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))) from rfl]
  rw [show (Matrix.vecTail u : Fin 5 → TangentSpace I x) =
      Fin.cons (u 1) (fun k : Fin 4 => u (Fin.natAdd 2 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.succ (Fin.succ i)) = u (Fin.natAdd 2 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  have hkey2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 4)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))))
    (v0 := u 1) (vs := fun k : Fin 4 => u (Fin.natAdd 2 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey2
  rw [← hkey2]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) (u 1)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)) from rfl]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := u 1)
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := u 0) (vs := Fin.cons (u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
      (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (unitTensor (I := I) (M := M) x) from rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem mixedCoeff_backgroundDifference_eq_pairTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D) =
        (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x D -
          riemannBiContrFib (I := I) g₀ x D) from by
      rw [show ((ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) =
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x -
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
    rw [show riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x =
        riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [show riemannBiContrFib (I := I) g₀ x =
        riemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [riemannMixedBiContrFibFixedFrame_toModel (I := I) g₀ g₁
      (smoothOrthoFrame (I := I) g₀ x) x D v]
    rw [riemannBiContrFibFixedFrame_toModel (I := I) g₀ (smoothOrthoFrame (I := I) g₀ x) x D v]
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [riemannLoweredBackgroundDifference_unitModel_apply (I := I) (M := M) g₀ g₁ x
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x)]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 2 =
      smoothOrthoFrame (I := I) g₀ x a x from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 3 =
      smoothOrthoFrame (I := I) g₀ x b x from rfl]
    ring
  rw [hLHS]
  set X : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hX_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr sigmaE0
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE0
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE0 i))]
    rfl
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      2 * ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] := by
    rw [show (((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) =
        (2 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((2 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) :
        TensorRSSpace 2 2 I x) D =
        (2 : ℝ) • (((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) from rfl]
    rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    congr 1
    rw [show (((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          cometricDoubleTraceFib (I := I) g₀ 2 x)
          ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
            cometricDoubleTraceFib (I := I) g₀ 4 x) Y) from by
      rw [hY_def]
      rw [operatorFieldComposition_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ 2 x]
    rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
          cometricDoubleTraceFib (I := I) g₀ 4 x) Y))
      (fun j => (v j : E))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
    rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel Y)
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ x b x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x b x : TangentSpace I x) : E)
          (fun j => (v j : E))))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hYval]
    rfl
  rw [hRHS]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma iteratedCovGrad_smul_b (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_smul_b (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

end CurvatureCoefficientDifferenceJetTower

theorem riemannianFiberNormSq_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
  classical
  have hcB : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + j) (2 + j) x
        ((slotExtendIter (I := I) (M := M) g₀ 6 2 j
          (phiDtPair (I := I) (M := M) g₀)).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (6 + j) (2 + j)
      (slotExtendIter (I := I) (M := M) g₀ 6 2 j (phiDtPair (I := I) (M := M) g₀))
  choose cB hcB0 hcBb using hcB
  refine ⟨fun i => 4 * cB i * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)),
    fun i => by
      have := hcB0 i
      positivity, ?_⟩
  intro g₁ i x
  rw [mixedCoeff_backgroundDifference_eq_pairTrace (I := I) (M := M) g₀ g₁]
  set WB : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) with hWB_def
  have hsmul : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        WB)).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
          WB)).toSection x) := by
    rw [iteratedCovGrad_smul_b]
    rw [SmoothCcTensor.toSection_smul]
    rfl
  rw [hsmul, riemannianFiberNormSq_smul_b]
  rw [iteratedCovGrad_operatorFieldComposition_parallel (I := I) (M := M) g₀ 2 6 2
    (phiDtPair (I := I) (M := M) g₀) (phiDtPair_covGrad_zero (I := I) (M := M) g₀) WB i]
  have hcomp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
        (slotExtendIter (I := I) (M := M) g₀ 6 2 i (phiDtPair (I := I) (M := M) g₀))
        (iteratedCovGrad (I := I) g₀ 2 6 i WB)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (phiDtPair (I := I) (M := M) g₀)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) := by
    rw [operatorFieldComposition_toSection]
    exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 2 (6 + i) (2 + i) x
      ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
        (phiDtPair (I := I) (M := M) g₀)).toSection x)
      ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)
  have hWBjets : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
    have heq1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) := by
      rw [hWB_def]
      exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
    rw [heq1]
    have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 6 i
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 5 i
              (slotExtend (I := I) (M := M) g₀ 0 4
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x
    have hstep2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 5 i
          (slotExtend (I := I) (M := M) g₀ 0 4
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) i x
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 5 i
              (slotExtend (I := I) (M := M) g₀ 0 4
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) :=
          hstep1
      _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) :=
          mul_le_mul_of_nonneg_left hstep2 hfr
      _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
          ring
  have hriemannianFiberNormSq_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)
  have hCD_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
    ((iteratedCovGrad (I := I) g₀ 0 4 i
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
  calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (slotExtendIter (I := I) (M := M) g₀ 6 2 i (phiDtPair (I := I) (M := M) g₀))
          (iteratedCovGrad (I := I) g₀ 2 6 i WB)).toSection x)
      ≤ (2 : ℝ) ^ 2 * (riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (phiDtPair (I := I) (M := M) g₀)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)) := by
        exact mul_le_mul_of_nonneg_left hcomp (sq_nonneg 2)
    _ ≤ (2 : ℝ) ^ 2 * (cB i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hcBb i x) hriemannianFiberNormSq_nn) (sq_nonneg 2)
    _ ≤ (2 : ℝ) ^ 2 * (cB i * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hWBjets (hcB0 i)) (by norm_num)
    _ = (4 * cB i * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ))) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
        ring

theorem riemannianFiberNormSq_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CAd, hCAd_nn, hCAd⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_riemannianFiberNormSq_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  set BB : ℕ → ℕ → ℝ := fun i i' => ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
    ∑ l ∈ Finset.range (i + 1 - i'),
      (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) with hBB_def
  have hBBsum_nn : ∀ i i', 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
      (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) := by
    intro i i'
    refine Finset.sum_nonneg fun l _ => add_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg (by norm_num) (hCAd_nn l))
        (gridSumPairCount_nonneg (i' + 1) (l + 3))
    · exact mul_nonneg (by norm_num) (hcbg_nn l)
  have hc0fac_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1 :=
    add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
  have hBB_nn : ∀ i i', 0 ≤ BB i i' := by
    intro i i'
    rw [hBB_def]
    exact mul_nonneg hc0fac_nn (hBBsum_nn i i')
  have hBBval : ∀ i i', BB i i' = ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
      ∑ l ∈ Finset.range (i + 1 - i'),
        (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) := by
    intro i i'
    rw [hBB_def]
  clear_value BB
  refine ⟨fun i => operatorFieldApplicationGdiag (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) ^ 3 * BB i i',
    fun i => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ =>
        mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hBB_nn i i')), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgoal_eq : (∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n, b (e m)) =
      ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k := rfl
  rw [hgoal_eq]
  set WW : ℝ := ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k
    with hWW_def
  have hgsum_le_WW : ∀ m : ℕ, m ≤ i + 3 →
      (∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k) ≤ WW := by
    intro m hm
    rw [hWW_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm) ?_
    intro k _ _
    exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hWW_nn : 0 ≤ WW := by
    rw [hWW_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hWW_ge1 : (1 : ℝ) ≤ WW := by
    rw [hWW_def]
    calc (1 : ℝ) = Combinatorics.antidiagonalTupleGrid b 0 :=
          (Combinatorics.antidiagonalTupleGrid_zero b).symm
      _ ≤ ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k :=
          Finset.single_le_sum
            (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
            (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
            (Finset.mem_range.mpr (by omega))
  clear_value WW
  rw [riemannG1LoweringDifference_slotInsert_repr (I := I) (M := M) g₀ g₁ T htie]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
      (slotInsertEndoCc (I := I) (M := M) g₀ 3
        (perturbationSharpEndoField (I := I) (M := M) g₀ T))
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) i x]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 0 4 4
    (slotInsertEndoCc (I := I) (M := M) g₀ 3
      (perturbationSharpEndoField (I := I) (M := M) g₀ T))
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) x) ?_
  have hL01 : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) ≤
      2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
        2 * cbg l := by
    intro l
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) l x]
    have hsplit : riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
        riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ +
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ := by
      rw [riemannLoweredBackgroundDifference, sub_add_cancel]
    have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x := by
      rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
    have h1 := hCAd g₁ T htie hδ_le hδ0 hbound l x
    rw [show (∑ k ∈ Finset.range (l + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n, b (e m)) =
        ∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k from rfl] at h1
    have h2 := hcbg l x
    have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
    have h2' := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
    exact add_le_add (by simpa only [mul_assoc] using h1') h2'
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 4 i'
            (slotInsertEndoCc (I := I) (M := M) g₀ 3
              (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW := by
    intro i' hi'
    have hi'le : i' ≤ i := by
      rw [Finset.mem_range] at hi'; omega
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
            2 * cbg l) :=
      Finset.sum_le_sum fun l _ => hL01 l
    have hprod_nn1 : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
    have hsum2_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        (2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
          2 * cbg l) := by
      refine Finset.sum_nonneg fun l _ => add_nonneg ?_ ?_
      · exact mul_nonneg (mul_nonneg (by norm_num) (hCAd_nn l))
          (Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
      · exact mul_nonneg (by norm_num) (hcbg_nn l)
    have hpairsum : ∀ gsA : ℝ, 0 ≤ gsA →
        (∀ m3ok : ∀ l ∈ Finset.range (i + 1 - i'),
          gsA * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            gridSumPairCount (i' + 1) (l + 3) * WW, gsA ≤ WW →
        gsA * ∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) ≤
        (∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l)) * WW) := by
      intro gsA hgsA_nn hm3 hgsA_le
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun l hl => ?_
      have h1 : gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
          Combinatorics.antidiagonalTupleGrid b k)) ≤
          2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW := by
        calc gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k))
            = (2 * CAd l) * (gsA * (∑ k ∈ Finset.range (l + 3),
              Combinatorics.antidiagonalTupleGrid b k)) := by ac_rfl
          _ ≤ (2 * CAd l) * (gridSumPairCount (i' + 1) (l + 3) * WW) := by
              refine mul_le_mul_of_nonneg_left (hm3 l hl) ?_
              exact mul_nonneg (by norm_num) (hCAd_nn l)
          _ = 2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW := by ac_rfl
      have h2 : gsA * (2 * cbg l) ≤ 2 * cbg l * WW := by
        calc gsA * (2 * cbg l) = (2 * cbg l) * gsA := by ac_rfl
          _ ≤ (2 * cbg l) * WW := by
              refine mul_le_mul_of_nonneg_left hgsA_le ?_
              exact mul_nonneg (by norm_num) (hcbg_nn l)
          _ = 2 * cbg l * WW := rfl
      calc gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)
          = gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
              Combinatorics.antidiagonalTupleGrid b k)) + gsA * (2 * cbg l) :=
            mul_add _ _ _
        _ ≤ 2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW + 2 * cbg l * WW :=
            add_le_add h1 h2
        _ = (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) * WW :=
          (add_mul _ _ _).symm
    have hSIsymm : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i') x
            ((iteratedCovGrad (I := I) g₀ 0 2 i'
              (symmS (I := I) (M := M) g₀ T)).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_slotInsert3_perturbationSharp_le (I := I) (M := M) g₀ T i' x
    cases i' with
    | zero =>
        have hsym0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by
          rw [iteratedCovGrad_zero]
          refine le_trans (riemannianFiberNormSq_symmS_zero_le_of_ball (I := I) (M := M) g₀ T hδ0 hbound x) ?_
          have hδsq : δ ^ 2 ≤ δ₀ ^ 2 :=
            (sq_le_sq₀ hδ0 (le_trans hδ0 hδ_le)).2 hδ_le
          exact mul_le_mul_of_nonneg_left hδsq (sq_nonneg _)
        have hm3 : ∀ l ∈ Finset.range (i + 1 - 0),
            ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
              (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
              (gridSumPairCount (0 + 1) (l + 3) * WW) := by
          intro l hl
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hl_le : l ≤ i := by
            rw [Finset.mem_range] at hl; omega
          have hgs := gridSum_mul_gridSum_le b hb (0 + 1) (l + 3) (i + 3) (by omega)
          have h1eq : (∑ k ∈ Finset.range (0 + 1),
              Combinatorics.antidiagonalTupleGrid b k) = 1 := by
            rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero]
          rw [h1eq, one_mul] at hgs
          refine le_trans hgs ?_
          refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
          exact hgsum_le_WW (i + 3) (le_refl _)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + 0) x
              ((iteratedCovGrad (I := I) g₀ 4 4 0
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
            ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2)) *
              ∑ l ∈ Finset.range (i + 1 - 0),
                (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) := by
              refine mul_le_mul (le_trans hSIsymm ?_) hA2 hprod_nn1
                (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
                  (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
              exact mul_le_mul_of_nonneg_left hsym0
                (pow_nonneg (Nat.cast_nonneg _) 3)
          _ = (Module.finrank ℝ E : ℝ) ^ 3 *
              (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
                ∑ l ∈ Finset.range (i + 1 - 0),
                  (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                    Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)) := by ac_rfl
          _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ l ∈ Finset.range (i + 1 - 0),
                (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_le_sum fun l hl => ?_
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 :=
                mul_nonneg (sq_nonneg _) (sq_nonneg _)
              have hCADl := hCAd_nn l
              have hcbgl := hcbg_nn l
              have hml := hm3 l hl
              have hgsl_nn : 0 ≤ ∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k :=
                Finset.sum_nonneg fun k _ =>
                  Combinatorics.antidiagonalTupleGrid_nonneg b hb k
              have hgspc_nn := gridSumPairCount_nonneg (0 + 1) (l + 3)
              nlinarith only [mul_le_mul_of_nonneg_left hml (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCADl),
                mul_nonneg hc0nn hcbgl, hWW_ge1, hWW_nn,
                mul_nonneg (mul_nonneg hc0nn hcbgl) (sub_nonneg.mpr hWW_ge1)]
          _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * BB i 0) * WW := by
              rw [hBBval i 0]
              have hsum_nn := hBBsum_nn i 0
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by positivity
              have hfr3 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
              have hstep : ((∑ l ∈ Finset.range (i + 1 - 0),
                  (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                    (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW)) ≤
                  (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                    ∑ l ∈ Finset.range (i + 1 - 0),
                      (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) * WW := by
                have hsum_nn0 := hBBsum_nn i 0
                nlinarith only [mul_nonneg hsum_nn0 hWW_nn]
              calc (Module.finrank ℝ E : ℝ) ^ 3 *
                    ((∑ l ∈ Finset.range (i + 1 - 0),
                      (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW))
                  ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
                      ((((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - 0),
                          (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) * WW) :=
                    mul_le_mul_of_nonneg_left hstep hfr3
                _ = ((Module.finrank ℝ E : ℝ) ^ 3 *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - 0),
                          (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l))) * WW := by
                    ac_rfl
    | succ i'' =>
        have hb_le_grid : b (i'' + 1) ≤ Combinatorics.antidiagonalTupleGrid b (i'' + 1) := by
          have hmem : (fun _ : Fin 1 => (i'' + 1)) ∈
              Finset.Nat.antidiagonalTuple 1 (i'' + 1) := by
            rw [Finset.Nat.mem_antidiagonalTuple]
            rw [Fin.sum_univ_one]
          have := prodTerm_le_antidiagonalTupleGrid b hb (i'' + 1) 1
            (show (1 : ℕ) < (i'' + 1) + 1 by omega) (fun _ => (i'' + 1)) hmem
          simpa using this
        have hgrid_le_gsum : Combinatorics.antidiagonalTupleGrid b (i'' + 1) ≤
            ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k :=
          Finset.single_le_sum
            (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
            (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
            (Finset.mem_range.mpr (by omega))
        have hsym_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i'' + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i'' + 1)
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
            ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k :=
          le_trans (riemannianFiberNormSq_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i'' + 1) x)
            (le_trans hb_le_grid hgrid_le_gsum)
        have hm3 : ∀ l ∈ Finset.range (i + 1 - (i'' + 1)),
            (∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
              (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            gridSumPairCount ((i'' + 1) + 1) (l + 3) * WW := by
          intro l hl
          have hl_le : l ≤ i - (i'' + 1) := by
            rw [Finset.mem_range] at hl
            omega
          have hii : i'' + 1 ≤ i := hi'le
          have hgs := gridSum_mul_gridSum_le b hb ((i'' + 1) + 1) (l + 3) (i + 3) (by omega)
          refine le_trans hgs ?_
          refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
          exact hgsum_le_WW (i + 3) (le_refl _)
        have hgsA_le : (∑ k ∈ Finset.range ((i'' + 1) + 1),
            Combinatorics.antidiagonalTupleGrid b k) ≤ WW :=
          hgsum_le_WW ((i'' + 1) + 1) (by omega)
        have hgsA_nn : 0 ≤ ∑ k ∈ Finset.range ((i'' + 1) + 1),
            Combinatorics.antidiagonalTupleGrid b k :=
          Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
        have hmain := hpairsum (∑ k ∈ Finset.range ((i'' + 1) + 1),
          Combinatorics.antidiagonalTupleGrid b k) hgsA_nn
          (fun l hl => by
            calc (∑ k ∈ Finset.range ((i'' + 1) + 1),
                  Combinatorics.antidiagonalTupleGrid b k) *
                  (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k)
                ≤ gridSumPairCount ((i'' + 1) + 1) (l + 3) * WW := hm3 l hl)
          hgsA_le
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i'' + 1)) x
              ((iteratedCovGrad (I := I) g₀ 4 4 (i'' + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
            ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
              ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) := by
              refine mul_le_mul (le_trans hSIsymm ?_) hA2 hprod_nn1
                (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3) hgsA_nn)
              exact mul_le_mul_of_nonneg_left hsym_le
                (pow_nonneg (Nat.cast_nonneg _) 3)
          _ = (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
                ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                  (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                    Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)) := by ac_rfl
          _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) * WW) := by
              have hfr3' : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 :=
                pow_nonneg (Nat.cast_nonneg _) _
              exact mul_le_mul_of_nonneg_left hmain hfr3'
          _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * BB i (i'' + 1)) * WW := by
              rw [hBBval i (i'' + 1)]
              have hsum_nn := hBBsum_nn i (i'' + 1)
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 :=
                mul_nonneg (sq_nonneg _) (sq_nonneg _)
              have hfr3 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 :=
                pow_nonneg (Nat.cast_nonneg _) _
              have hstep : (∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                  (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) ≤
                  ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                    ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                      (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l) := by
                have hfac : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1 :=
                  le_add_of_nonneg_left hc0nn
                simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac hsum_nn
              calc (Module.finrank ℝ E : ℝ) ^ 3 *
                    ((∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                      (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) * WW)
                  = ((Module.finrank ℝ E : ℝ) ^ 3 *
                      ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                        (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) *
                      WW := by ac_rfl
                _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                          (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l))) *
                      WW := by
                    refine mul_le_mul_of_nonneg_right ?_ hWW_nn
                    exact mul_le_mul_of_nonneg_left hstep hfr3
  calc operatorFieldApplicationGdiag (E := E) i *
        ∑ i' ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 4 i'
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
      ≤ operatorFieldApplicationGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), ((Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (operatorFieldApplicationGdiag_nonneg (E := E) i)
    _ = (operatorFieldApplicationGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW := by
        rw [← Finset.sum_mul]
        ac_rfl

namespace CurvatureCoefficientDifferenceJetTower

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotInsertEndoCc_add_endo_c (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma metricComparisonEndomorphismField_diff_split_c (g₀ g₁ : SmoothRiemannianMetric I M) :
    metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁ =
      metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) x) =
      metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [metricComparisonEndomorphismField_apply, ContinuousLinearMap.add_apply]
  rw [show (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x) = metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x
    from rfl]
  rw [metricComparisonEndomorphismField_apply]
  rw [metricComparisonEndomorphism_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndomorphism (I := I) g₀ g₀ x v = v from by
    rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM]]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma g1_inner_metricComparisonEndomorphism_left_c (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndomorphism (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [metricComparisonEndomorphism_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma operatorFieldComposition_sub_left_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g₀ b c) (W : SmoothCcTensor g₀ a b) :
    ccOperatorFieldComp (I := I) (M := M) g₀ a b c (Φ₁ - Φ₂) W =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₁ W - ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₁ W -
        ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₂ W).toSection x) =
      (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₁ W).toSection x -
        (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₂ W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c (Φ₁ - Φ₂) W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from (Φ₁ - Φ₂).toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₁ W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ₁.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₂ W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ₂.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((Φ₁ - Φ₂).toSection x) = Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma operatorFieldComposition_sub_right_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) (W₁ W₂ : SmoothCcTensor g₀ a b) :
    ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ (W₁ - W₂) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₁ - ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₁ -
        ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₂).toSection x) =
      (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₁).toSection x -
        (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₂).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ (W₁ - W₂)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from (W₁ - W₂).toSection x) D))
      from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₁).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₂).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((W₁ - W₂).toSection x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      W₁.toSection x - W₂.toSection x) D) =
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D -
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D from rfl]
  rw [map_sub]

instance tensorRSModelNormedSpaceCC {r s : ℕ} :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

set_option backward.isDefEq.respectTransparency false in
def pureDoubleTraceField (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma operatorFieldComposition_slotInsert_id_eq (g₀ : SmoothRiemannianMetric I M) (s c : ℕ)
    (Φ : SmoothCcTensor g₀ (s + 1) c) :
    ccOperatorFieldComp (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (slotInsertEndoCc (I := I) (M := M) g₀ s
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀)) = Φ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (slotInsertEndoCc (I := I) (M := M) g₀ s
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))).toSection x) D =
      ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  refine congrArg _ ?_
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slotInsertEndoFib_apply_eval]
  rw [show (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ x (m 0)) = m 0 from by
    rw [metricComparisonEndomorphismField_apply, metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [Function.update_eq_self]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_cons_sum_smul (_x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_cons_cons_sum_smul (_x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma orthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma pureDoubleTraceField_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    pureDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndomorphism (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [operatorFieldComposition_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := orthoFrame_center_repr (I := I) (M := M) g₁ x
      (metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from metricComparisonEndomorphism (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [g1_inner_metricComparisonEndomorphism_left_c (I := I) (M := M) g₀ g₁ x
      (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndomorphism (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := toModel_cons_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := orthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma operatorFieldComposition_add_left_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g₀ b c) (W : SmoothCcTensor g₀ a b) :
    ccOperatorFieldComp (I := I) (M := M) g₀ a b c (Φ₁ + Φ₂) W =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₁ W +
        ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ₂ W := by
  exact operatorFieldComposition_add_left (I := I) (M := M) g₀ a b c Φ₁ Φ₂ W

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma operatorFieldComposition_add_right_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) (W₁ W₂ : SmoothCcTensor g₀ a b) :
    ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ (W₁ + W₂) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₁ +
        ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W₂ := by
  exact operatorFieldComposition_add_right (I := I) (M := M) g₀ a b c Φ W₁ W₂

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtend_sub_cc (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : SmoothCcTensor g₀ r s) :
    slotExtend (I := I) (M := M) g₀ r s (X - Y) =
      slotExtend (I := I) (M := M) g₀ r s X - slotExtend (I := I) (M := M) g₀ r s Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotExtend (I := I) (M := M) g₀ r s X -
        slotExtend (I := I) (M := M) g₀ r s Y).toSection x) =
      (slotExtend (I := I) (M := M) g₀ r s X).toSection x -
        (slotExtend (I := I) (M := M) g₀ r s Y).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((slotExtend (I := I) (M := M) g₀ r s (X - Y)).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (X - Y).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g₀ r s X).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g₀ r s Y).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((X - Y).toSection x) = X.toSection x - Y.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      X.toSection x - Y.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) =
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) -
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from by
    apply ContinuousLinearMap.ext
    intro w
    rfl]
  rw [map_sub]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma rsDomDomCongrSection_sub_cc (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (X Y : SmoothCcTensor g₀ r s) :
    rsDomDomCongrSection (I := I) (M := M) g₀ r s σ (X - Y) =
      rsDomDomCongrSection (I := I) (M := M) g₀ r s σ X -
        rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hsub : ((X - Y).toSection x) = X.toSection x - Y.toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  have hsub2 : ((rsDomDomCongrSection (I := I) (M := M) g₀ r s σ X -
      rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Y).toSection x) =
      (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ X).toSection x -
        (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Y).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [rsDomDomCongrSection_toSection, hsub, hsub2]
  rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
  have hfib : ∀ (y : Tensor0SSpace s I x) (w : Fin s → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace s I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x - Y.toSection x) D m]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      rsDomDomCongr σ (X.toSection x) - rsDomDomCongr σ (Y.toSection x)) D) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (Y.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (X.toSection x - Y.toSection x : TensorRSSpace r s I x)) D) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x) D from rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (Y.toSection x)) D : Tensor0SSpace s I x) m =
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (X.toSection x)) D : Tensor0SSpace s I x) m -
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (Y.toSection x)) D : Tensor0SSpace s I x) m from rfl]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x) D m]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (Y.toSection x) D m]
  rfl

def pairTraceOp (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
    (pureDoubleTraceField (I := I) (M := M) g₀ gm 2)
    (pureDoubleTraceField (I := I) (M := M) g₀ gm 4)

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma pairTraceOp_apply_toModel (g₀ gm : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ gm)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr sigmaE0
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE0
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE0 i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ gm)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) gm 2 x
        (cometricDoubleTraceFib (I := I) gm 4 x Y) from by
    rw [hY_def]
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) gm 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) gm 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) gm 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem riemannCoeff_eq_pairTrace_L11 (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      ((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) D) =
      (2 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) D) := by
    rw [show (((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (pairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) =
        (2 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hsmul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [pairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x) D) =
      riemannBiContrFib (I := I) g₁ x D from rfl]
  rw [show riemannBiContrFib (I := I) g₁ x =
      riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [riemannBiContrFibFixedFrame_toModel (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x D v]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g₁ x
    (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x)]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x) 2 =
    smoothOrthoFrame (I := I) g₁ x b x from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x) 3 =
    smoothOrthoFrame (I := I) g₁ x a x from rfl]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem riemannMixedCoeff_eq_pairTrace_L01 (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      ((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)))).toSection x) D) =
      (2 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)))).toSection x) D) := by
    rw [show (((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (pairTraceOp (I := I) (M := M) g₀ g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)))).toSection x) =
        (2 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hsmul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [pairTraceOp_apply_toModel (I := I) (M := M) g₀ g₀
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x) D) =
      riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x D from rfl]
  rw [show riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x =
      riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
        (smoothOrthoFrame (I := I) g₀ x) x from rfl]
  rw [riemannMixedBiContrFibFixedFrame_toModel (I := I) g₀ g₁
    (smoothOrthoFrame (I := I) g₀ x) x D v]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₁ x
    (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x)]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x) 2 =
    smoothOrthoFrame (I := I) g₀ x b x from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x) 3 =
    smoothOrthoFrame (I := I) g₀ x a x from rfl]
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma iteratedCovGrad_zero_of_covGrad_zero (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (Φ : SmoothCcTensor g₀ r s)
    (hΦ : covGrad (I := I) (M := M) g₀ r s Φ = 0) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ r s (m + 1) Φ = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact hΦ
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma pureDoubleTraceField_self_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    pureDoubleTraceField (I := I) (M := M) g₀ g₀ s = cometricDoubleTraceField (I := I) g₀ s := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceField_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma pairTraceOp_self_eq (g₀ : SmoothRiemannianMetric I M) :
    pairTraceOp (I := I) (M := M) g₀ g₀ = phiDtPair (I := I) (M := M) g₀ := by
  rw [pairTraceOp, phiDtPair, pureDoubleTraceField_self_eq (I := I) (M := M) g₀ 2,
    pureDoubleTraceField_self_eq (I := I) (M := M) g₀ 4]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma pureDoubleTraceField_cross_split (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    pureDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) +
      cometricDoubleTraceField (I := I) g₀ s := by
  rw [pureDoubleTraceField_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  rw [metricComparisonEndomorphismField_diff_split_c (I := I) (M := M) g₀ g₁]
  rw [slotInsertEndoCc_add_endo_c (I := I) (M := M) g₀ (s + 1)]
  rw [operatorFieldComposition_add_right_cc (I := I) (M := M) g₀ (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)]
  rw [operatorFieldComposition_slotInsert_id_eq (I := I) (M := M) g₀ (s + 1) s
    (cometricDoubleTraceField (I := I) g₀ s)]

end CurvatureCoefficientDifferenceJetTower

noncomputable def pureTrace (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s :=
  pureDoubleTraceField (I := I) (M := M) g₀ g₁ s

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem pureTrace_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    (pureTrace (I := I) (M := M) g₀ g₁ s).toSection x =
      (show TensorRSSpace (s + 2) s I x from
        cometricDoubleTraceFib (I := I) g₁ s x) := rfl

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem pureTrace_split (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    pureTrace (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) +
      cometricDoubleTraceField (I := I) g₀ s := by
  exact pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ s

end Spectral
end Analysis
end DifferentialGeometry

end
