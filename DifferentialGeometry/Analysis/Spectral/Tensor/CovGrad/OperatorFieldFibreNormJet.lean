import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldApplicationDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedOperatorFieldApplicationLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SlotExtendCovariantParallelism
import DifferentialGeometry.Geometry.Connection.TensorNabla.FiberNorm.SliceBound

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.TensorMultilinear
open DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
private lemma exists_orthoFrame_basis (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
      (∀ i : Fin (Module.finrank ℝ E), bse i = e i) ∧
      (∀ a b : Fin (Module.finrank ℝ E),
        g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) := by
  classical
  obtain ⟨n, e0, hn, horth0, _hpars, _hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g 0 0 x
  subst hn
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x := e0 with he_def
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := horth0
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  refine ⟨e, basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_, horth⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_eq_sum_componentSq_of_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s S n e K J) ^ 2 :=
  DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_eq_sum_component_sq_of_basis
    (I := I) (M := M) g r s x S e bse hn hbse horth

alias riemannianFiberNormSq_rs_eq_sum_componentSq_of_basis :=
  riemannianFiberNormSq_eq_sum_componentSq_of_basis

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma fiberNormSqComponent_slotExtendFib_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K' : Fin (r + 1) → Fin n) (J' : Fin (s + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) r s x
          A)
        n e K' J' =
      (if J' 0 = K' 0 then (1 : ℝ) else 0) *
        fiberNormSqComponent (I := I) (M := M) g x r s
          (show TensorRSSpace r s I x from A) n e
          (fun k => K' (Fin.succ k)) (fun k => J' (Fin.succ k)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) r s x
          A)
        n e K' J' =
      Tensor0SSpace.eval
        (slotExtendPointwise (I := I) (M := M) r s x A
          (coframeS (I := I) (M := M) g x (r + 1) e K'))
        (Fin.cons (e (J' 0)) (fun k : Fin s => e (J' (Fin.succ k)))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
          (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) r s x
            A)
          n e K' J' =
        Tensor0SSpace.eval
          (slotExtendPointwise (I := I) (M := M) r s x A
            (coframeS (I := I) (M := M) g x (r + 1) e K'))
          (fun k => e (J' k)) from rfl]
    congr 1
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
  rw [hcomp]
  rw [slotExtendFib_apply_natural (I := I) (M := M) r s x A
    (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 0))
    (fun k : Fin s => e (J' (Fin.succ k)))]
  have hcurry : (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
        (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 0)) =
      (if J' 0 = K' 0 then (1 : ℝ) else 0) •
        coframeS (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) := by
    apply tensor0SSpace_ext (𝕜 := ℝ) r x
    intro u
    change Tensor0SSpace.eval
        ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
          (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 0))) u =
      Tensor0SSpace.eval ((if J' 0 = K' 0 then (1 : ℝ) else 0) •
        coframeS (I := I) (M := M) g x r e (fun k => K' (Fin.succ k))) u
    rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := r)
      (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 0)) u]
    rw [Tensor0SSpace.eval_eq]
    rw [coframeS_apply (I := I) (M := M) g x (r + 1) e K' (Fin.cons (e (J' 0)) u)]
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [horth (K' 0) (J' 0)]
    rw [Tensor0SSpace.eval_smul, smul_eq_mul, Tensor0SSpace.eval_eq]
    rw [coframeS_apply (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) u]
    by_cases h : K' 0 = J' 0
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [hcurry, map_smul, Tensor0SSpace.eval_smul, smul_eq_mul]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma riemannianFiberNormSq_slotExtendFib_eq_frame
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1) x
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) r s x
          A) =
      (n : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r s x (show TensorRSSpace r s I x from A) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g (r + 1) (s + 1) x
    (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) r s x A)
    e bse hn hbse horth]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g r s x
    (show TensorRSSpace r s I x from A) e bse hn hbse horth]
  have hcompsq : ∀ (K' : Fin (r + 1) → Fin n) (J' : Fin (s + 1) → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
          (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) r s x
            A)
          n e K' J') ^ 2 =
        (if J' 0 = K' 0 then (1 : ℝ) else 0) *
          (fiberNormSqComponent (I := I) (M := M) g x r s (show TensorRSSpace r s I x from A) n e
            (fun k => K' (Fin.succ k)) (fun k => J' (Fin.succ k))) ^ 2 := by
    intro K' J'
    rw [fiberNormSqComponent_slotExtendFib_eq (I := I) (M := M) g r s x A e horth K' J']
    by_cases h : J' 0 = K' 0
    · rw [if_pos h]; ring
    · rw [if_neg h]; ring
  rw [Finset.sum_congr rfl (fun K' _ => Finset.sum_congr rfl (fun J' _ => hcompsq K' J'))]
  set comp : (Fin r → Fin n) → (Fin s → Fin n) → ℝ := fun K J =>
    (fiberNormSqComponent (I := I) (M := M) g x r s (show TensorRSSpace r s I x from A) n e K J) ^ 2
    with hcomp_def
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
        (fun pr : Fin n × (Fin r → Fin n) =>
          ∑ J' : Fin (s + 1) → Fin n,
            (if J' 0 = pr.1 then (1 : ℝ) else 0) * comp pr.2 (fun k => J' (Fin.succ k)))
        (fun K' : Fin (r + 1) → Fin n =>
          ∑ J' : Fin (s + 1) → Fin n,
            (if J' 0 = K' 0 then (1 : ℝ) else 0) * comp (fun k => K' (Fin.succ k))
              (fun k => J' (Fin.succ k)))
        (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]
  rw [show (∑ k0 : Fin n, ∑ K : Fin r → Fin n, ∑ J' : Fin (s + 1) → Fin n,
        (if J' 0 = k0 then (1 : ℝ) else 0) * comp K (fun k => J' (Fin.succ k))) =
      ∑ k0 : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n, comp K J from by
    refine Finset.sum_congr rfl (fun k0 _ => Finset.sum_congr rfl (fun K _ => ?_))
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun pr : Fin n × (Fin s → Fin n) =>
            (if pr.1 = k0 then (1 : ℝ) else 0) * comp K pr.2)
          (fun J' : Fin (s + 1) → Fin n =>
            (if J' 0 = k0 then (1 : ℝ) else 0) * comp K (fun k => J' (Fin.succ k)))
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    rw [show (∑ j0 : Fin n, ∑ J : Fin s → Fin n, (if j0 = k0 then (1 : ℝ) else 0) * comp K J) =
        ∑ J : Fin s → Fin n, comp K J from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ k0 (fun _ => (1 : ℝ)),
        if_pos (Finset.mem_univ k0), one_mul]]]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
theorem riemannianFiberNormSq_slotExtendFib_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1) x
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) r s x
          A) =
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r s x (show TensorRSSpace r s I x from A) := by
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  exact riemannianFiberNormSq_slotExtendFib_eq_frame (I := I) (M := M) g r s x A e bse rfl hbse horth

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_slotExtend_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1) x
        ((slotExtend (I := I) (M := M) g r s Φ).toSection x) =
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) := by
  rw [slotExtend_toSection (I := I) (M := M) g r s Φ x]
  exact riemannianFiberNormSq_slotExtendFib_eq (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_covGrad_slotExtend_eq_swap
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (Φ : SmoothCcTensor g r s)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K' : Fin (r + 1) → Fin n) (J' : Fin (s + 1 + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) n e K' J' =
      fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) n e K'
          (J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  have hLHS : fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) n e K' J' =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J' 0))))
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
            (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 1))))
        (fun k : Fin s => e (J' (Fin.succ (Fin.succ k)))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
          ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)).toSection x) n e K' J' =
        Tensor0SSpace.eval
          ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            (covGrad (I := I) (M := M) g (r + 1) (s + 1)
              (slotExtend (I := I) (M := M) g r s Φ)).toSection x)
            (coframeS (I := I) (M := M) g x (r + 1) e K'))
          (fun k => e (J' k)) from rfl]
    rw [covGrad_toSection_apply_natural (I := I) (M := M) g (r + 1) (s + 1)
      (slotExtend (I := I) (M := M) g r s Φ) x (coframeS (I := I) (M := M) g x (r + 1) e K')
      (fun k => e (J' k))]
    rw [DifferentialGeometry.Analysis.Spectral.DeTurck.tensorCovDerivAt_slotExtend_eq
      (I := I) (M := M) g r s Φ x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J' 0)))]
    rw [show Matrix.vecTail (fun k => e (J' k)) =
        Fin.cons (e (J' 1))
          (fun k : Fin s => e (J' (Fin.succ (Fin.succ k))))
        from by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · change e (J' (Fin.succ 0)) = _
        rw [Fin.cons_zero]; rfl
      · change e (J' (Fin.succ (Fin.succ i))) = _
        rw [Fin.cons_succ]]
    rw [slotExtendFib_apply_natural (I := I) (M := M) r s x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g r s Φ x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J' 0))))
      (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 1))
      (fun k : Fin s => e (J' (Fin.succ (Fin.succ k))))]
  have hRHS : fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) n e K'
          (J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J' 0))))
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
            (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 1))))
        (fun k : Fin s => e (J' (Fin.succ (Fin.succ k)))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
          ((slotExtend (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ)).toSection x) n e K'
            (J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) =
        Tensor0SSpace.eval
          ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            (slotExtend (I := I) (M := M) g r (s + 1)
              (covGrad (I := I) (M := M) g r s Φ)).toSection x)
            (coframeS (I := I) (M := M) g x (r + 1) e K'))
          (fun k => e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) from rfl]
    rw [slotExtend_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x]
    rw [show (fun k => e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
        Fin.cons (e (J' 1))
          (fun k : Fin (s + 1) => e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Fin.succ k))) from by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero, Function.comp_apply]
        rw [Equiv.swap_apply_left]
      · rw [Fin.cons_succ]]
    rw [slotExtendFib_apply_natural (I := I) (M := M) r (s + 1) x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g r s Φ).toSection x)
      (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 1))
      (fun k : Fin (s + 1) => e
        ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
    rw [show ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
          (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 1)) :
          Tensor0SSpace r I x) =
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
          (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 1)) from rfl]
    rw [covGrad_toSection_apply_natural (I := I) (M := M) g r s Φ x
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
        (coframeS (I := I) (M := M) g x (r + 1) e K') (e (J' 1)))
      (fun k : Fin (s + 1) => e
        ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
    have hdir : e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ 0)) =
        e (J' 0) := by
      simp only [Function.comp_apply]
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
    have htail : (Matrix.vecTail (fun k : Fin (s + 1) =>
          e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))) =
        (fun k : Fin s => e (J' (Fin.succ (Fin.succ k)))) := by
      funext k
      change e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k))) =
        e (J' (Fin.succ (Fin.succ k)))
      simp only [Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · exact (Fin.succ_ne_zero _)
      · rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
    rw [hdir, htail]
  exact hLHS.trans hRHS.symm

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_covGrad_slotExtend_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1 + 1) x
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g (r + 1) (s + 1 + 1) x _
    e bse rfl
    hbse horth]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g (r + 1) (s + 1 + 1) x _
    e bse rfl
    hbse horth]
  refine Finset.sum_congr rfl (fun K' _ => ?_)
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Equiv.refl (Fin (Module.finrank ℝ E))))
    (fun J' : Fin (s + 1 + 1) → Fin (Module.finrank ℝ E) =>
      (fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) (Module.finrank ℝ E) e K' J') ^ 2)
    (fun J' : Fin (s + 1 + 1) → Fin (Module.finrank ℝ E) =>
      (fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) (Module.finrank ℝ E) e K' J') ^ 2)
    (fun J' => ?_)
  have heqv : (Equiv.arrowCongr (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (Equiv.refl (Fin (Module.finrank ℝ E)))) J' =
      J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1 := by
    funext a; simp [Equiv.arrowCongr]
  rw [heqv]
  rw [fiberNormSqComponent_covGrad_slotExtend_eq_swap (I := I) (M := M) g r s x Φ e K' J']

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_covGrad_slotExtend_scale (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) =
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
          ((covGrad (I := I) (M := M) g r s Φ).toSection x) := by
  rw [riemannianFiberNormSq_covGrad_slotExtend_eq (I := I) (M := M) g r s Φ x]
  exact riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_slotExtendIter_eq (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ (w : ℕ) (Φ : SmoothCcTensor g r s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g (r + w) (s + w) x
          ((slotExtendIter (I := I) (M := M) g r s w Φ).toSection x) =
        (Module.finrank ℝ E : ℝ) ^ w *
          riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) := by
  intro w
  induction w with
  | zero => intro Φ x; simp [slotExtendIter]
  | succ w ih =>
      intro Φ x
      have hrec : slotExtendIter (I := I) (M := M) g r s (w + 1) Φ =
          slotExtend (I := I) (M := M) g (r + w) (s + w)
            (slotExtendIter (I := I) (M := M) g r s w Φ) := rfl
      change riemannianFiberNormSq (I := I) (M := M) g ((r + w) + 1) ((s + w) + 1) x
          ((slotExtendIter (I := I) (M := M) g r s (w + 1) Φ).toSection x) = _
      rw [hrec]
      calc
        _ = (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g (r + w) (s + w) x
              ((slotExtendIter (I := I) (M := M) g r s w Φ).toSection x) :=
          riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g (r + w) (s + w)
            (slotExtendIter (I := I) (M := M) g r s w Φ) x
        _ = _ := by rw [ih Φ x, pow_succ]; ring

def tensorRSDomDomCongr {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) : TensorRSSpace r s I x :=
  TensorRSSpace.ofCLM
    ((((tensor0SSpaceContinuousLinearEquiv s x).symm.toContinuousLinearMap).comp
        (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ σ).toContinuousLinearEquiv
            : Tensor0SModel s ℝ E ≃L[ℝ] Tensor0SModel s ℝ E).toContinuousLinearMap.comp
          ((tensor0SSpaceContinuousLinearEquiv s x).toContinuousLinearMap))).comp
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma toModel_rsDomDomCongr_apply {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) (d : Tensor0SSpace r I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from tensorRSDomDomCongr σ T) d) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)) := by
  rw [tensorRSDomDomCongr, TensorRSSpace.ofCLM]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [Tensor0SSpace.toModel]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma rsDomDomCongr_apply_eval {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) (d : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorRSDomDomCongr σ T) d) v =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
        (fun k => v (σ k)) := by
  classical
  have hL := toModel_rsDomDomCongr_apply (I := I) (M := M) σ T d
  rw [← Tensor0SSpace.toModel_apply_tangent, hL,
    ContinuousMultilinearMap.domDomCongr_apply,
    Tensor0SSpace.toModel_apply_tangent]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma rsDomDomCongr_rsDomDomCongr {r s : ℕ} {x : M} (σ τ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) :
    tensorRSDomDomCongr (I := I) (M := M) σ (tensorRSDomDomCongr (I := I) (M := M) τ T) =
      tensorRSDomDomCongr (I := I) (M := M) (τ.trans σ) T := by
  apply ContinuousLinearMap.ext
  intro d
  apply tensor0SSpace_ext (𝕜 := ℝ) s x
  intro v
  change Tensor0SSpace.eval _ v = Tensor0SSpace.eval _ v
  calc
    _ = Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorRSDomDomCongr (I := I) (M := M) τ T) d) (fun k => v (σ k)) :=
      rsDomDomCongr_apply_eval (I := I) (M := M) σ
        (tensorRSDomDomCongr (I := I) (M := M) τ T) d v
    _ = Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
        (fun k => v (σ (τ k))) :=
      rsDomDomCongr_apply_eval (I := I) (M := M) τ T d (fun k => v (σ k))
    _ = Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
        (fun k => v ((τ.trans σ) k)) := by rfl
    _ = _ := (rsDomDomCongr_apply_eval (I := I) (M := M) (τ.trans σ) T d v).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma fiberNormSqComponent_rsDomDomCongr {r s : ℕ} (g : SmoothRiemannianMetric I M) (x : M)
    (σ : Equiv.Perm (Fin s)) (T : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r s (tensorRSDomDomCongr σ T) n e K J =
      fiberNormSqComponent (I := I) (M := M) g x r s T n e K (fun k => J (σ k)) := by
  rw [fiberNormSqComponent, fiberNormSqComponent]
  exact rsDomDomCongr_apply_eval (I := I) (M := M) σ T _ (fun k => e (J k))

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
theorem riemannianFiberNormSq_domDomCongr_covariant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (σ : Equiv.Perm (Fin s)) (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (tensorRSDomDomCongr σ T) =
      riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g r s x
    (tensorRSDomDomCongr σ T)
    e bse rfl hbse horth]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g r s x T e bse rfl hbse
    horth]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  refine Fintype.sum_equiv
    (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (Module.finrank ℝ E))))
    (fun J => (fiberNormSqComponent (I := I) (M := M) g x r s (tensorRSDomDomCongr σ T)
      (Module.finrank ℝ E) e K J) ^ 2)
    (fun J => (fiberNormSqComponent (I := I) (M := M) g x r s T
      (Module.finrank ℝ E) e K J) ^ 2)
    (fun J => ?_)
  have heqv : (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (Module.finrank ℝ E)))) J =
      (fun k => J (σ k)) := by
    funext a; simp [Equiv.arrowCongr]
  rw [heqv]
  rw [fiberNormSqComponent_rsDomDomCongr (I := I) (M := M) g x σ T e K J]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private theorem riemannianFiberNormSq_toSection_heq_congr_rs (g : SmoothRiemannianMetric I M)
    {r a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad (I := I) (M := M) g r s Φ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) Φ).toSection x) :=
  riemannianFiberNormSq_toSection_heq_congr_rs g (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq' g r s m Φ) x

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covGrad_slotExtend_toSection_rsDomDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
      tensorRSDomDomCongr (I := I) (M := M) (r := r + 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  apply ContinuousLinearMap.ext
  intro d
  apply tensor0SSpace_ext (𝕜 := ℝ) (s + 1 + 1) x
  intro m
  refine Eq.trans ?_ (rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
    (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    ((slotExtend (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s Φ)).toSection x) d m).symm
  change Tensor0SSpace.eval
      ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) d) m =
    Tensor0SSpace.eval
      ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) d)
      (fun k => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k))
  rw [covGrad_toSection_apply_natural (I := I) (M := M) g (r + 1) (s + 1)
    (slotExtend (I := I) (M := M) g r s Φ) x d m]
  rw [DifferentialGeometry.Analysis.Spectral.DeTurck.tensorCovDerivAt_slotExtend_eq
    (I := I) (M := M) g r s Φ x
      (tangentSpaceModelContinuousLinearEquiv (I := I) x (m 0))]
  rw [show Matrix.vecTail m =
      Fin.cons (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k))) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · change m (Fin.succ 0) = _
      rw [Fin.cons_zero]; rfl
    · change m (Fin.succ (Fin.succ i)) = _
      rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_natural (I := I) (M := M) r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g r s Φ x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x (m 0)))
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
  rw [slotExtendFib_apply_natural (I := I) (M := M) r (s + 1) x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g r s Φ).toSection x)
    d (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  rw [covGrad_toSection_apply_natural (I := I) (M := M) g r s Φ x
    ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) d (m 1))
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

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma covGrad_castCcTensorRank (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r b
        (DifferentialGeometry.Analysis.Spectral.castCcTensorRank g r h W) =
      DifferentialGeometry.Analysis.Spectral.castCcTensorRank g r (by rw [h] : a + 1 = b + 1)
        (covGrad (I := I) (M := M) g r a W) := by
  subst h; rfl

private lemma heq_swap_zero_one_of_eq {p q : ℕ} (h : p = q) :
    HEq (Equiv.swap (0 : Fin (p + 1)) 1) (Equiv.swap (0 : Fin (q + 1)) 1) := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma succ_step_cast_transposition_eq {r a b : ℕ} (h : a = b)
    (g : SmoothRiemannianMetric I M)
    (P Q : SmoothCcTensor g (r + 1) a) (x : M)
    (sigmaHat swapB : Equiv.Perm (Fin b)) (swapA : Equiv.Perm (Fin a)) (hswap : HEq swapA swapB)
    (hPQ : P.toSection x = tensorRSDomDomCongr (I := I) (M := M) swapA (Q.toSection x)) :
    tensorRSDomDomCongr (I := I) (M := M) sigmaHat
        ((DifferentialGeometry.Analysis.Spectral.castCcTensorRank g (r + 1) h P).toSection x) =
      tensorRSDomDomCongr (I := I) (M := M) (swapB.trans sigmaHat)
        ((DifferentialGeometry.Analysis.Spectral.castCcTensorRank g (r + 1) h Q).toSection
          x) := by
  subst h
  rw [eq_of_heq hswap] at hPQ
  simp only [DifferentialGeometry.Analysis.Spectral.castCcTensorRank]
  rw [hPQ, rsDomDomCongr_rsDomDomCongr]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma exists_iteratedCovGrad_slotExtend_rsDomDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (i : ℕ) :
    ∃ σ : Equiv.Perm (Fin ((s + 1) + i)),
      ∀ x : M,
        (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
          tensorRSDomDomCongr (I := I) (M := M) σ
            ((DifferentialGeometry.Analysis.Spectral.castCcTensorRank g (r + 1)
              (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g r (s + i)
                (iteratedCovGrad (I := I) g r s i Φ))).toSection x) := by
  classical
  induction i with
  | zero =>
      refine ⟨Equiv.refl _, fun x => ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      apply ContinuousLinearMap.ext
      intro d
      apply tensor0SSpace_ext (𝕜 := ℝ) ((s + 1) + 0) x
      intro m
      exact (rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
        (Equiv.refl (Fin ((s + 1) + 0)))
        ((DifferentialGeometry.Analysis.Spectral.castCcTensorRank g (r + 1)
          (by omega : (s + 0) + 1 = (s + 1) + 0)
          (slotExtend (I := I) (M := M) g r (s + 0) Φ)).toSection x) d m).symm
  | succ i ih =>
      obtain ⟨σ, hσ⟩ := ih
      refine ⟨(Equiv.swap (0 : Fin (((s + 1) + i) + 1)) 1).trans
        (Equiv.Perm.decomposeFin.symm (0, σ)), fun x => ?_⟩
      rw [iteratedCovGrad_succ (I := I) g (r + 1) (s + 1) i (slotExtend (I := I) (M := M) g r s Φ)]
      have hcov : (covGrad (I := I) (M := M) g (r + 1) ((s + 1) + i)
            (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
              (slotExtend (I := I) (M := M) g r s Φ))).toSection x =
          tensorRSDomDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, σ))
            ((covGrad (I := I) (M := M) g (r + 1) ((s + 1) + i)
              (DifferentialGeometry.Analysis.Spectral.castCcTensorRank g (r + 1)
                (by omega : (s + i) + 1 = (s + 1) + i)
                (slotExtend (I := I) (M := M) g r (s + i)
                  (iteratedCovGrad (I := I) g r s i Φ)))).toSection x) := by
        apply ContinuousLinearMap.ext
        intro d
        apply Tensor0SSpace.toModel_injective
        apply ContinuousMultilinearMap.ext
        intro w
        let v : Fin (((s + 1) + i) + 1) → TangentSpace I x :=
          fun j => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w j)
        have hmodel := covGrad_rs_toModel_domDomCongr (I := I) (M := M) g
          (r + 1) ((s + 1) + i) σ
          (DifferentialGeometry.Analysis.Spectral.castCcTensorRank g (r + 1)
            (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ)))
          (iteratedCovGrad (I := I) g (r + 1) (s + 1) i (slotExtend (I := I) (M := M) g r s Φ))
          (fun y d' => by
            have := hσ y
            rw [this]
            exact toModel_rsDomDomCongr_apply (I := I) (M := M) σ _ d') x d v
        have hdomEq := toModel_rsDomDomCongr_apply (I := I) (M := M)
          (Equiv.Perm.decomposeFin.symm (0, σ))
          ((covGrad (I := I) (M := M) g (r + 1) ((s + 1) + i)
            (DifferentialGeometry.Analysis.Spectral.castCcTensorRank g (r + 1)
              (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g r (s + i)
                (iteratedCovGrad (I := I) g r s i Φ)))).toSection x) d
        have hdom := congrArg (fun F => F
          (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (v j))) hdomEq
        have hv : (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (v j)) = w := by
          funext j
          exact ContinuousLinearEquiv.apply_symm_apply
            (tangentSpaceModelContinuousLinearEquiv (I := I) x) (w j)
        rw [hv] at hmodel hdom
        exact hmodel.trans hdom.symm
      refine hcov.trans ?_
      rw [covGrad_castCcTensorRank (I := I) (M := M) g (r + 1)
        (by omega : (s + i) + 1 = (s + 1) + i)
        (slotExtend (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ))]
      rw [iteratedCovGrad_succ (I := I) g r s i Φ]
      exact succ_step_cast_transposition_eq (I := I) (M := M)
        (by omega : (s + i) + 1 + 1 = (s + 1) + i + 1) g
        (covGrad (I := I) (M := M) g (r + 1) (s + i + 1)
          (slotExtend (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ)))
        (slotExtend (I := I) (M := M) g r (s + (i + 1))
          (covGrad (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ)))
        x (Equiv.Perm.decomposeFin.symm (0, σ))
        (Equiv.swap (0 : Fin (((s + 1) + i) + 1)) 1)
        (Equiv.swap (0 : Fin (((s + i) + 1) + 1)) 1)
        (heq_swap_zero_one_of_eq (by omega : (s + i) + 1 = (s + 1) + i))
        (covGrad_slotExtend_toSection_rsDomDomCongr (I := I) (M := M) g r (s + i)
          (iteratedCovGrad (I := I) g r s i Φ) x)

omit [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
  obtain ⟨σ, hσ⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M) g r s Φ i
  rw [hσ x]
  rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g (r + 1) ((s + 1) + i) x σ
    ((DifferentialGeometry.Analysis.Spectral.castCcTensorRank g (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i)
      (slotExtend (I := I) (M := M) g r (s + i)
        (iteratedCovGrad (I := I) g r s i Φ))).toSection x)]
  rw [← riemannianFiberNormSq_toSection_heq_congr_rs g (by omega : (s + i) + 1 = (s + 1) + i)
    (DifferentialGeometry.Analysis.Spectral.castCcTensorRank_heq g (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i)
      (slotExtend (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ))).symm x]
  rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ) x]

def diagonalGridGrowthFactor (j : ℕ) : ℝ := (2 * ((Module.finrank ℝ E : ℝ) + 1)) ^ j


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem operatorFieldApplicationGdiag_nonneg (j : ℕ) : 0 ≤ diagonalGridGrowthFactor (E := E) j := by
  rw [diagonalGridGrowthFactor]; positivity

private lemma diagonalGrid_step_le (n : ℝ) (hn : 0 ≤ n) (j : ℕ) (cΦ cW : ℕ → ℝ)
    (hcΦ : ∀ i, 0 ≤ cΦ i) (hcW : ∀ l, 0 ≤ cW l) :
    (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
        n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) ≤
      (n + 1) * ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
  classical
  set D : ℝ := ∑ i ∈ Finset.range (j + 1 + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l
    with hD_def
  have hcell_nn : ∀ i, 0 ≤ cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
    intro i; exact mul_nonneg (hcΦ i) (Finset.sum_nonneg (fun l _ => hcW l))
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun i _ => hcell_nn i)
  have hWshift : ∀ m : ℕ, (∑ l ∈ Finset.range m, cW (l + 1)) ≤ ∑ l ∈ Finset.range (m + 1), cW
    l := by
    intro m
    rw [Finset.sum_range_succ' (fun l => cW l) m]
    exact le_add_of_nonneg_right (hcW 0)
  have hA : (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) ≤
    D := by
    rw [hD_def]
    rw [Finset.sum_range_succ' (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn 0))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (hcΦ (i + 1))
    rw [show j + 1 + 1 - (i + 1) = j + 1 - i from by omega]
  have hB : (∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) ≤
    D := by
    rw [hD_def]
    rw [Finset.sum_range_succ (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn (j + 1)))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left ?_ (hcΦ i)
    refine le_trans (hWshift (j + 1 - i)) (le_of_eq ?_)
    rw [show j + 1 - i + 1 = j + 1 + 1 - i from by omega]
  calc (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
          n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
      ≤ D + n * D := by
        refine add_le_add hA ?_
        exact mul_le_mul_of_nonneg_left hB hn
    _ = (n + 1) * D := by ring

omit [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_le (g : SmoothRiemannianMetric I M) :
    ∀ (j a b : ℕ) (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g 0 a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (b + j) x
          ((iteratedCovGrad (I := I) g 0 b j
            (ccOperatorFieldComp (I := I) (M := M) g 0 a b Φ W)).toSection x) ≤
        diagonalGridGrowthFactor (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
                ((iteratedCovGrad (I := I) g a b i Φ).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g 0 (a + l) x
                  ((iteratedCovGrad (I := I) g 0 a l W).toSection x) := by
  intro j
  induction j with
  | zero =>
      intro a b Φ W x
      rw [iteratedCovGrad_zero, diagonalGridGrowthFactor, pow_zero, one_mul]
      rw [Finset.sum_range_one, Finset.sum_range_one, iteratedCovGrad_zero, iteratedCovGrad_zero]
      simp only [Nat.add_zero]
      rw [operatorFieldComposition_toSection (I := I) (M := M) g 0 a b Φ W x]
      have h := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g 0 a b x
        (show TensorRSSpace a b I x from Φ.toSection x)
        (show TensorRSSpace 0 a I x from W.toSection x)
      simpa using h
  | succ j ih =>
      intro a b Φ W x
      classical
      rw [← riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g 0 b j
        (ccOperatorFieldComp (I := I) (M := M) g 0 a b Φ W) x]
      rw [covGrad_operatorFieldComposition_eq (I := I) (M := M) g 0 a b Φ W]
      rw [iteratedCovGrad_add]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 ((b + 1) + j) x
        ((iteratedCovGrad (I := I) g 0 (b + 1) j
          (ccOperatorFieldComp (I := I) (M := M) g 0 a (b + 1)
            (covGrad (I := I) (M := M) g a b Φ) W)).toSection x)
        ((iteratedCovGrad (I := I) g 0 (b + 1) j
          (ccOperatorFieldComp (I := I) (M := M) g 0 (a + 1) (b + 1)
            (slotExtend (I := I) (M := M) g a b Φ)
            (covGrad (I := I) (M := M) g 0 a W))).toSection x)) ?_
      set cΦ : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
        ((iteratedCovGrad (I := I) g a b i Φ).toSection x) with hcΦ_def
      set cW : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (a + l) x
        ((iteratedCovGrad (I := I) g 0 a l W).toSection x) with hcW_def
      have hcΦ_nn : ∀ i, 0 ≤ cΦ i := fun i =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g a (b + i) x _
      have hcW_nn : ∀ l, 0 ≤ cW l := fun l =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (a + l) x _
      have hGj_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) j := operatorFieldApplicationGdiag_nonneg (E := E) j
      have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      have hArmA : riemannianFiberNormSq (I := I) (M := M) g 0 ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g 0 (b + 1) j
              (ccOperatorFieldComp (I := I) (M := M) g 0 a (b + 1)
                (covGrad (I := I) (M := M) g a b Φ) W)).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j *
            ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l := by
        refine le_trans (ih a (b + 1) (covGrad (I := I) (M := M) g a b Φ) W x) ?_
        refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) hGj_nn
        rw [hcΦ_def]
        dsimp only
        rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g a b i Φ x]
      have hArmB : riemannianFiberNormSq (I := I) (M := M) g 0 ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g 0 (b + 1) j
              (ccOperatorFieldComp (I := I) (M := M) g 0 (a + 1) (b + 1)
                (slotExtend (I := I) (M := M) g a b Φ)
                (covGrad (I := I) (M := M) g 0 a W))).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j *
            ((Module.finrank ℝ E : ℝ) *
              ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
        refine le_trans (ih (a + 1) (b + 1) (slotExtend (I := I) (M := M) g a b Φ)
          (covGrad (I := I) (M := M) g 0 a W) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ hGj_nn
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hWinner : (∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((a + 1) + l) x
                ((iteratedCovGrad (I := I) g 0 (a + 1) l
                  (covGrad (I := I) (M := M) g 0 a W)).toSection x)) =
            ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hcW_def]
          dsimp only
          rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g 0 a l W x]
        rw [hWinner]
        have hΦle : riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
              ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                (slotExtend (I := I) (M := M) g a b Φ)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) * cΦ i := by
          rw [hcΦ_def]
          dsimp only
          exact riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g a b Φ i x
        calc riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
                ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                  (slotExtend (I := I) (M := M) g a b Φ)).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
            ≤ ((Module.finrank ℝ E : ℝ) * cΦ i) * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) :=
                mul_le_mul_of_nonneg_right hΦle
                  (Finset.sum_nonneg (fun l _ => hcW_nn (l + 1)))
          _ = (Module.finrank ℝ E : ℝ) * (cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
                ring
      refine le_trans (add_le_add
        (mul_le_mul_of_nonneg_left hArmA (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hArmB (by norm_num : (0:ℝ) ≤ 2))) ?_
      set Gj : ℝ := diagonalGridGrowthFactor (E := E) j with hGj_def
      set SA : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l
        with hSA_def
      set SB : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
        with hSB_def
      set DG : ℝ := ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l with hDG_def
      have hstep : SA + (Module.finrank ℝ E : ℝ) * SB ≤ ((Module.finrank ℝ E : ℝ) + 1) * DG := by
        rw [hSA_def, hSB_def, hDG_def]
        exact diagonalGrid_step_le (Module.finrank ℝ E : ℝ) hn_nn j cΦ cW hcΦ_nn hcW_nn
      have hGdiag_succ : diagonalGridGrowthFactor (E := E) (j + 1) =
        (2 * ((Module.finrank ℝ E : ℝ) + 1)) * Gj := by
        rw [hGj_def, diagonalGridGrowthFactor, diagonalGridGrowthFactor, pow_succ]; ring
      rw [hGdiag_succ]
      have hGj_nn' : (0 : ℝ) ≤ Gj := hGj_nn
      nlinarith only [mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 2 * Gj), hGj_nn',
        hstep]

omit [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le
    (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (W : SmoothCcTensor g 0 b₀) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + j) x
        ((iteratedCovGrad (I := I) g 0 s₀ j
          (operatorFieldApply (I := I) (M := M) g b₀ s₀ C W)).toSection x) ≤
      diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g b₀ (s₀ + i) x
              ((iteratedCovGrad (I := I) g b₀ s₀ i C).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g 0 (b₀ + l) x
                ((iteratedCovGrad (I := I) g 0 b₀ l W).toSection x) := by
  rw [← operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g b₀ s₀ C W]
  exact riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_le (I := I) (M := M) g j b₀ s₀ C W x

private lemma sum_finZeroFun_eq {N : ℕ} (f : (Fin 0 → Fin N) → ℝ) :
    ∑ K : Fin 0 → Fin N, f K = f (fun k : Fin 0 => k.elim0) := by
  refine Finset.sum_eq_single (fun k : Fin 0 => k.elim0) ?_ ?_
  · exact fun K _ hK => absurd (funext (fun k : Fin 0 => k.elim0)) hK
  · exact fun h => absurd (Finset.mem_univ _) h

private lemma sum_consEquiv {N t : ℕ} (F : (Fin (t + 1) → Fin N) → ℝ) :
    ∑ J : Fin (t + 1) → Fin N, F J =
      ∑ j0 : Fin N, ∑ J' : Fin t → Fin N, F (Fin.cons j0 J') := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (t + 1) => Fin N))
      (fun pr : Fin N × (Fin t → Fin N) => F (Fin.cons pr.1 pr.2)) F
      (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma tensor00Scalar_coframe0_eq_one (g : SmoothRiemannianMetric I M) (x : M)
    {N : ℕ} (e : Fin N → TangentSpace I x) (K : Fin 0 → Fin N) :
    tensor00Scalar (I := I) (M := M) x (coframeS (I := I) (M := M) g x 0 e K) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
    coframeS_apply (I := I) (M := M) g x 0 e K (fun k : Fin 0 => k.elim0)]
  simp


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma riemannianFiberNormSq_zero_eq_sum_componentSq
    (g : SmoothRiemannianMetric I M) (x : M) (m : ℕ) (S : TensorRSSpace 0 m I x)
    {N : ℕ} (e : Fin N → TangentSpace I x)
    (bse : Module.Basis (Fin N) ℝ (TangentSpace I x))
    (hn : N = Module.finrank ℝ E) (hbse : ∀ i : Fin N, bse i = e i)
    (horth : ∀ a b : Fin N, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
      ∑ J : Fin m → Fin N,
        (fiberNormSqComponent (I := I) (M := M) g x 0 m S N e (fun k : Fin 0 => k.elim0) J) ^
          2 := by
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g 0 m x S e bse hn hbse
    horth]
  rw [sum_finZeroFun_eq]

private noncomputable def operatorFieldApplicationSlice (g : SmoothRiemannianMetric I M) (r : ℕ) (x : M)
    {N : ℕ} (e : Fin N → TangentSpace I x) (W : SmoothCcTensor g 0 (r + 1))
    (j0 : Fin N) : TensorRSSpace 0 r I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
        (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
      (e j0))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma operatorFieldApplicationSlice_apply_coframe0 (g : SmoothRiemannianMetric I M) (r : ℕ) (x : M)
    {N : ℕ} (e : Fin N → TangentSpace I x) (W : SmoothCcTensor g 0 (r + 1))
    (j0 : Fin N) (K : Fin 0 → Fin N) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from operatorFieldApplicationSlice (I := I) (M := M) g r x e W
      j0)
        (coframeS (I := I) (M := M) g x 0 e K) =
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
          (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
        (e j0) := by
  rw [operatorFieldApplicationSlice, ContinuousLinearMap.smulRight_apply,
    tensor00Scalar_coframe0_eq_one (I := I) (M := M) g x e K, one_smul]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma fiberNormSqComponent_zero_eq_eval
    (g : SmoothRiemannianMetric I M) (x : M) (m : ℕ) (S : TensorRSSpace 0 m I x)
    {N : ℕ} (e : Fin N → TangentSpace I x) (K : Fin 0 → Fin N) (J : Fin m → Fin N) :
    fiberNormSqComponent (I := I) (M := M) g x 0 m S N e K J =
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from S)
          (coframeS (I := I) (M := M) g x 0 e K))
        (fun k => e (J k)) := rfl

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_comp_slotExtend_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 (r + 1)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ) W).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1) x (W.toSection x) := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  have hdiamond : ∀ (j0 : Fin (Module.finrank ℝ E))
      (J' : Fin s → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1)
          ((operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ) W).toSection x)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) (Fin.cons j0 J') =
        fiberNormSqComponent (I := I) (M := M) g x 0 s
          (show TensorRSSpace 0 s I x from
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
                operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0))
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) J' := by
    intro j0 J'
    have hL : fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1)
          ((operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ) W).toSection x)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) (Fin.cons j0 J') =
        Tensor0SSpace.eval
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
                (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
              (e j0)))
          (fun k : Fin s => e (J' k)) := by
      rw [fiberNormSqComponent_zero_eq_eval (I := I) (M := M) g x (s + 1)
        ((operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ) W).toSection x) e (fun k : Fin 0 => k.elim0)
        (Fin.cons j0 J')]
      rw [operatorFieldApplication_toSection, slotExtend_toSection, ContinuousLinearMap.comp_apply]
      rw [show (fun k => e ((Fin.cons j0 J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) =
          Fin.cons (e j0) (fun k : Fin s => e (J' k)) from by
        funext k
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
        · simp only [Fin.cons_zero]
        · simp only [Fin.cons_succ]]
      rw [slotExtendFib_apply_natural (I := I) (M := M) r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
          (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
        (e j0) (fun k : Fin s => e (J' k))]
    have hR : fiberNormSqComponent (I := I) (M := M) g x 0 s
          (show TensorRSSpace 0 s I x from
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
                operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0))
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) J' =
        Tensor0SSpace.eval
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
                (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
              (e j0)))
          (fun k : Fin s => e (J' k)) := by
      rw [fiberNormSqComponent_zero_eq_eval (I := I) (M := M) g x s
        (show TensorRSSpace 0 s I x from
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
              operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0)) e (fun k : Fin 0 => k.elim0) J']
      rw [ContinuousLinearMap.comp_apply,
        operatorFieldApplicationSlice_apply_coframe0 (I := I) (M := M) g r x e W j0 (fun k : Fin 0 => k.elim0)]
    rw [hL, hR]
  have hVW : ∀ (j0 : Fin (Module.finrank ℝ E))
      (P : Fin r → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g x 0 r
          (operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) P =
        fiberNormSqComponent (I := I) (M := M) g x 0 (r + 1) (W.toSection x)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) (Fin.cons j0 P) := by
    intro j0 P
    have hL : fiberNormSqComponent (I := I) (M := M) g x 0 r
          (operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) P =
        Tensor0SSpace.eval
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
            (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
          (Fin.cons (e j0) (fun k : Fin r => e (P k))) := by
      rw [fiberNormSqComponent_zero_eq_eval (I := I) (M := M) g x r
        (operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0) e (fun k : Fin 0 => k.elim0) P]
      rw [operatorFieldApplicationSlice_apply_coframe0 (I := I) (M := M) g r x e W j0 (fun k : Fin 0 => k.elim0)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
          (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
        (e j0) (fun k : Fin r => e (P k))]
    have hR : fiberNormSqComponent (I := I) (M := M) g x 0 (r + 1) (W.toSection x)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) (Fin.cons j0 P) =
        Tensor0SSpace.eval
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
            (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
          (fun k => e ((Fin.cons j0 P : Fin (r + 1) → Fin (Module.finrank ℝ E)) k)) :=
      fiberNormSqComponent_zero_eq_eval (I := I) (M := M) g x (r + 1) (W.toSection x)
        e (fun k : Fin 0 => k.elim0) (Fin.cons j0 P)
    rw [hL, hR]
    congr 1
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  have hLHS : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ) W).toSection x) =
        ∑ j0 : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (show TensorRSSpace 0 s I x from
              (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
                  operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0)) := by
    rw [riemannianFiberNormSq_zero_eq_sum_componentSq (I := I) (M := M) g x (s + 1)
      ((operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ) W).toSection x) e bse rfl hbse horth]
    rw [sum_consEquiv]
    refine Finset.sum_congr rfl (fun j0 _ => ?_)
    rw [riemannianFiberNormSq_zero_eq_sum_componentSq (I := I) (M := M) g x s
      (show TensorRSSpace 0 s I x from
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0)) e bse rfl hbse horth]
    refine Finset.sum_congr rfl (fun J' _ => ?_)
    rw [hdiamond j0 J']
  have hsum : ∑ j0 : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 r x
          (operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1) x (W.toSection x) := by
    rw [riemannianFiberNormSq_zero_eq_sum_componentSq (I := I) (M := M) g x (r + 1) (W.toSection x)
      e bse rfl hbse horth]
    rw [sum_consEquiv]
    refine Finset.sum_congr rfl (fun j0 _ => ?_)
    rw [riemannianFiberNormSq_zero_eq_sum_componentSq (I := I) (M := M) g x r
      (operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0) e bse rfl hbse horth]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [hVW j0 P]
  rw [hLHS]
  calc ∑ j0 : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (show TensorRSSpace 0 s I x from
              (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
                  operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0))
      ≤ ∑ j0 : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 r x
              (operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0) :=
        Finset.sum_le_sum (fun j0 _ => riemannianFiberNormSq_compRS_le_mul (I := I) (M := M)
          g 0 r s x (Φ.toSection x) (operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0))
    _ = riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
          ∑ j0 : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g 0 r x
              (operatorFieldApplicationSlice (I := I) (M := M) g r x e W j0) := by
        rw [Finset.mul_sum]
    _ = riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1) x (W.toSection x) := by
        rw [hsum]

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_iteratedCovGrad_order_congr (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad (I := I) g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad (I := I) g r s n' S).toSection x) := by
  subst h; rfl

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma iteratedCovGrad_zero_arg (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g r s m (0 : SmoothCcTensor g r s) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private lemma one_le_operatorFieldApplicationGdiag (j : ℕ) : (1 : ℝ) ≤ diagonalGridGrowthFactor (E := E) j := by
  have hbase : (1 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    linarith
  calc (1 : ℝ) = 1 ^ j := (one_pow j).symm
    _ ≤ (2 * ((Module.finrank ℝ E : ℝ) + 1)) ^ j :=
        pow_le_pow_left₀ (by norm_num) hbase j
    _ = diagonalGridGrowthFactor (E := E) j := by rw [diagonalGridGrowthFactor]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private lemma operatorFieldApplicationGdiag_succ_eq (j : ℕ) :
    diagonalGridGrowthFactor (E := E) (j + 1) =
      2 * ((Module.finrank ℝ E : ℝ) + 1) * diagonalGridGrowthFactor (E := E) j := by
  rw [diagonalGridGrowthFactor, diagonalGridGrowthFactor, pow_succ]
  ring


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem operatorFieldApplicationLeibnizPsi_zero_right_eq (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) :
    operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i 0 =
      iteratedCovGrad (I := I) g b c i Φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) 0 =
          covGrad (I := I) (M := M) g (b + 0) (c + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i 0) from rfl]
      rw [ih]
      rfl


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma operatorFieldApplicationLeibnizPsi_succ_succ_eq (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i j : ℕ) :
    operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        slotExtend (I := I) (M := M) g (b + j) (c + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i j) := by
  rw [show operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
          (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + j) (c + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i j))) from rfl]
  rw [castCcTensorRank, castCcTensorSourceRank]

omit [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_iteratedCovGrad_operatorFieldApplicationLeibnizPsi_window_le (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) :
    ∀ (i k m : ℕ), k ≤ i → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (b + k) ((c + i) + m) x
          ((iteratedCovGrad (I := I) g (b + k) (c + i) m
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k)).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i *
          riemannianFiberNormSq (I := I) (M := M) g b (c + ((i - k) + m)) x
            ((iteratedCovGrad (I := I) g b c ((i - k) + m) Φ).toSection x) := by
  intro i
  induction i with
  | zero =>
      intro k m hk x
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      rw [riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g b c
        (show (0 - 0) + m = m from by omega) Φ x]
      rw [show diagonalGridGrowthFactor (E := E) 0 = (1 : ℝ) from by rw
                                                                       [diagonalGridGrowthFactor,
        pow_zero], one_mul]
      exact le_of_eq rfl
  | succ i ih =>
      intro k m hk x
      cases k with
      | zero =>
          rw [operatorFieldApplicationLeibnizPsi_zero_right_eq (I := I) (M := M) g b c Φ (i + 1)]
          rw [riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g b c
            (show ((i + 1) - 0) + m = (i + 1) + m from by omega) Φ x]
          have hcomp : riemannianFiberNormSq (I := I) (M := M) g (b + 0) ((c + (i + 1)) + m) x
              ((iteratedCovGrad (I := I) g (b + 0) (c + (i + 1)) m
                (iteratedCovGrad (I := I) g b c (i + 1) Φ)).toSection x) =
              riemannianFiberNormSq (I := I) (M := M) g b (c + ((i + 1) + m)) x
                ((iteratedCovGrad (I := I) g b c ((i + 1) + m) Φ).toSection x) :=
            riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g b c (i + 1) m Φ x
          rw [hcomp]
          exact le_mul_of_one_le_left
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g b (c + ((i + 1) + m)) x _)
            (one_le_operatorFieldApplicationGdiag (E := E) (i + 1))
      | succ j =>
          have hji : j ≤ i := by omega
          rw [operatorFieldApplicationLeibnizPsi_succ_succ_eq (I := I) (M := M) g b c Φ i j]
          set Aif := (if j + 1 < i + 1 then
              covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
            else 0) with hAif_def
          set Bse := slotExtend (I := I) (M := M) g (b + j) (c + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i j) with hBse_def
          rw [iteratedCovGrad_add (I := I) g (b + (j + 1)) (c + (i + 1)) m Aif Bse]
          rw [show ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) m Aif +
                iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) m Bse).toSection x) =
              (iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) m Aif).toSection x +
                (iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) m Bse).toSection x from by
            rw [SmoothCcTensor.toSection_add]; rfl]
          refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g (b + (j + 1))
            ((c + (i + 1)) + m) x _ _) ?_
          set R := riemannianFiberNormSq (I := I) (M := M) g b
            (c + (((i + 1) - (j + 1)) + m)) x
            ((iteratedCovGrad (I := I) g b c (((i + 1) - (j + 1)) + m) Φ).toSection x) with hR_def
          have hR_nn : 0 ≤ R := riemannianFiberNormSq_nonneg (I := I) (M := M) g b _ x _
          have hG_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i := operatorFieldApplicationGdiag_nonneg (E := E) i
          have hB : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1))
              ((c + (i + 1)) + m) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) m Bse).toSection x) ≤
              (Module.finrank ℝ E : ℝ) * (diagonalGridGrowthFactor (E := E) i * R) := by
            refine le_trans
              (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g (b + j) (c + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i j) m x)
              (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
            have hbound := ih j m hji x
            rw [riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g b c
              (show (i - j) + m = ((i + 1) - (j + 1)) + m from by omega) Φ x] at hbound
            exact hbound
          have hA : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1))
              ((c + (i + 1)) + m) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) m Aif).toSection x) ≤
              diagonalGridGrowthFactor (E := E) i * R := by
            rcases lt_or_ge (j + 1) (i + 1) with hlt | hge
            · rw [hAif_def, if_pos hlt]
              have hcomp : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1))
                  ((c + (i + 1)) + m) x
                  ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) m
                    (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)))).toSection x) =
                  riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1))
                    ((c + i) + (1 + m)) x
                    ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + i) (1 + m)
                      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))).toSection x) :=
                riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g (b + (j + 1)) (c + i)
                  1 m
                  (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)) x
              rw [hcomp]
              have hbound := ih (j + 1) (1 + m) (by omega : j + 1 ≤ i) x
              rw [riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g b c
                (show (i - (j + 1)) + (1 + m) = ((i + 1) - (j + 1)) + m from by omega) Φ x]
                at hbound
              exact hbound
            · have hji' : j = i := by omega
              subst hji'
              rw [hAif_def, if_neg (by omega : ¬ (j + 1 < j + 1))]
              rw [iteratedCovGrad_zero_arg (I := I) (M := M) g (b + (j + 1)) (c + (j + 1)) m]
              rw [show ((0 : SmoothCcTensor g (b + (j + 1)) (c + (j + 1) + m)).toSection x :
                  TensorRSSpace (b + (j + 1)) (c + (j + 1) + m) I x) = 0 from by
                rw [SmoothCcTensor.toSection_zero]; rfl]
              rw [riemannianFiberNormSq_zero (I := I) (M := M) g (b + (j + 1))
                (c + (j + 1) + m) x]
              exact mul_nonneg hG_nn hR_nn
          rw [operatorFieldApplicationGdiag_succ_eq (E := E) i]
          nlinarith only [hA, hB, hR_nn, hG_nn,
            mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2),
            mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2)]


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem iteratedCovGrad_operatorFieldApplication_eq_coeffCorner_add_lower (g : SmoothRiemannianMetric I M)
    (b s : ℕ) (Φ : SmoothCcTensor g b s) (W : SmoothCcTensor g 0 b) (i : ℕ) :
    iteratedCovGrad (I := I) g 0 s i (operatorFieldApply (I := I) (M := M) g b s Φ W) =
      operatorFieldApply (I := I) (M := M) g b (s + i) (iteratedCovGrad (I := I) g b s i Φ) W +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g 0 (b + (k + 1)) (s + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b s Φ i (k + 1))
            (iteratedCovGrad (I := I) g 0 b (k + 1) W) := by
  rw [iteratedCovGrad_operatorFieldApply_eq (I := I) (M := M) g b s Φ W i]
  rw [Finset.sum_range_succ' (fun k =>
    ccOperatorFieldComp (I := I) (M := M) g 0 (b + k) (s + i)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b s Φ i k)
      (iteratedCovGrad (I := I) g 0 b k W)) i]
  have hf0 : ccOperatorFieldComp (I := I) (M := M) g 0 (b + 0) (s + i)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b s Φ i 0)
      (iteratedCovGrad (I := I) g 0 b 0 W) =
      operatorFieldApply (I := I) (M := M) g b (s + i) (iteratedCovGrad (I := I) g b s i Φ) W := by
    rw [operatorFieldApplicationLeibnizPsi_zero_right_eq (I := I) (M := M) g b s Φ i]
    exact operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g b (s + i)
      (iteratedCovGrad (I := I) g b s i Φ) W
  rw [hf0]
  exact add_comm _ _


omit [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_iteratedCovGrad_operatorFieldApplication_coeffLower_le (g : SmoothRiemannianMetric I M)
    (b s : ℕ) (Φ : SmoothCcTensor g b s) (W : SmoothCcTensor g 0 b) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g 0 (b + (k + 1)) (s + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b s Φ i (k + 1))
            (iteratedCovGrad (I := I) g 0 b (k + 1) W)).toSection x) ≤
      (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
        ∑ k ∈ Finset.range i,
          riemannianFiberNormSq (I := I) (M := M) g b (s + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g b s (i - (k + 1)) Φ).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 (b + (k + 1)) x
              ((iteratedCovGrad (I := I) g 0 b (k + 1) W).toSection x) := by
  rw [SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 (s + i) x
    (Finset.range i) (fun k =>
      (ccOperatorFieldComp (I := I) (M := M) g 0 (b + (k + 1)) (s + i)
        (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b s Φ i (k + 1))
        (iteratedCovGrad (I := I) g 0 b (k + 1) W)).toSection x)) ?_
  rw [Finset.card_range, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk_le : k + 1 ≤ i := by
    simp only [Finset.mem_range] at hk
    omega
  rw [operatorFieldComposition_toSection (I := I) (M := M) g 0 (b + (k + 1)) (s + i)
    (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b s Φ i (k + 1))
    (iteratedCovGrad (I := I) g 0 b (k + 1) W) x]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g 0 (b + (k + 1))
    (s + i) x _ _) ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (b + (k + 1)) x _)
  exact riemannianFiberNormSq_iteratedCovGrad_operatorFieldApplicationLeibnizPsi_window_le (I := I) (M := M) g b s Φ i (k + 1) 0 hk_le x


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem iteratedCovGrad_operatorFieldComposition_eq_argCorner_add_lower (g : SmoothRiemannianMetric I M)
    (p a b : ℕ) (Θ : SmoothCcTensor g a b) (X : SmoothCcTensor g p a) (i : ℕ) :
    iteratedCovGrad (I := I) g p b i (ccOperatorFieldComp (I := I) (M := M) g p a b Θ X) =
      ccOperatorFieldComp (I := I) (M := M) g p (a + i) (b + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g a b Θ i i)
          (iteratedCovGrad (I := I) g p a i X) +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g p (a + k) (b + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g a b Θ i k)
            (iteratedCovGrad (I := I) g p a k X) := by
  rw [iteratedCovGrad_operatorFieldComposition_eq (I := I) (M := M) g p a b Θ X i]
  rw [Finset.sum_range_succ]
  exact add_comm _ _


omit [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_operatorFieldComposition_argLower_le (g : SmoothRiemannianMetric I M)
    (p a b : ℕ) (Θ : SmoothCcTensor g a b) (X : SmoothCcTensor g p a) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g p (b + i) x
        ((∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g p (a + k) (b + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g a b Θ i k)
            (iteratedCovGrad (I := I) g p a k X)).toSection x) ≤
      (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
        ∑ k ∈ Finset.range i,
          riemannianFiberNormSq (I := I) (M := M) g a (b + (i - k)) x
              ((iteratedCovGrad (I := I) g a b (i - k) Θ).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g p (a + k) x
              ((iteratedCovGrad (I := I) g p a k X).toSection x) := by
  rw [SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g p (b + i) x
    (Finset.range i) (fun k =>
      (ccOperatorFieldComp (I := I) (M := M) g p (a + k) (b + i)
        (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g a b Θ i k)
        (iteratedCovGrad (I := I) g p a k X)).toSection x)) ?_
  rw [Finset.card_range, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk_le : k ≤ i := by
    simp only [Finset.mem_range] at hk
    omega
  rw [operatorFieldComposition_toSection (I := I) (M := M) g p (a + k) (b + i)
    (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g a b Θ i k)
    (iteratedCovGrad (I := I) g p a k X) x]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g p (a + k)
    (b + i) x _ _) ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g p (a + k) x _)
  have hbound := riemannianFiberNormSq_iteratedCovGrad_operatorFieldApplicationLeibnizPsi_window_le (I := I) (M := M) g a b Θ i k 0
    hk_le x
  rw [riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g a b
    (show (i - k) + 0 = i - k from by omega) Θ x] at hbound
  exact hbound

private def slotExtendIterFib (g : SmoothRiemannianMetric I M) (b c : ℕ) (x : M)
    (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) :
    ∀ w : ℕ, Tensor0SSpace (b + w) I x →L[ℝ] Tensor0SSpace (c + w) I x
  | 0 => A
  | (w + 1) => slotExtendPointwise (I := I) (M := M) (b + w) (c + w) x
      (slotExtendIterFib g b c x A w)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma fiberNormSqComponent_comp_eq
    (g : SmoothRiemannianMetric I M) (p a c : ℕ) (x : M)
    (Φx : TensorRSSpace a c I x) (Wx : TensorRSSpace p a I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin p → Fin n) (J : Fin c → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x p c
        (show TensorRSSpace p c I x from
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
            (show Tensor0SSpace p I x →L[ℝ] Tensor0SSpace a I x from Wx)) n e K J =
      ∑ P : Fin a → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x p a Wx n e K P *
          fiberNormSqComponent (I := I) (M := M) g x a c Φx n e P J := by
  classical
  change (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from Φx)
      ((show Tensor0SSpace p I x →L[ℝ] Tensor0SSpace a I x from Wx)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin p) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K k)))))
      (fun k => e (J k)) = _
  set wval : Tensor0SSpace a I x :=
    (show Tensor0SSpace p I x →L[ℝ] Tensor0SSpace a I x from Wx)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin p) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k)))) with hwval
  have hexp := tensorS_coframe_expansion (I := I) (M := M) g x a e bse hbse horth wval
  conv_lhs => rw [hexp]
  rw [map_sum]
  rw [show (∑ P : Fin a → Fin n,
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from Φx)
          ((wval (fun k : Fin a => e (P k))) • coframeS (I := I) (M := M) g x a e P)) =
      ∑ P : Fin a → Fin n, (wval (fun k : Fin a => e (P k))) •
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x a e P) from by
    refine Finset.sum_congr rfl (fun P _ => ?_); rw [map_smul]]
  rw [show ((∑ P : Fin a → Fin n, (wval (fun k : Fin a => e (P k))) •
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x a e P)) (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.eval (∑ P : Fin a → Fin n, (wval (fun k : Fin a => e (P k))) •
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x a e P)) (fun k => e (J k)) from rfl]
  rw [Tensor0SSpace.eval_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Tensor0SSpace.eval_smul]
  have hΦcomp : Tensor0SSpace.eval
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from Φx)
        (coframeS (I := I) (M := M) g x a e P)) (fun k => e (J k)) =
      fiberNormSqComponent (I := I) (M := M) g x a c Φx n e P J := rfl
  rw [hΦcomp]
  have hwcomp : wval (fun k : Fin a => e (P k)) =
      fiberNormSqComponent (I := I) (M := M) g x p a Wx n e K P := rfl
  rw [hwcomp, smul_eq_mul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma sum_sq_component_slotExtendIterFib_le (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    ∀ (w b c : ℕ) (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x)
      (V : (Fin (b + w) → Fin n) → ℝ),
      ∑ J : Fin (c + w) → Fin n,
          (∑ P : Fin (b + w) → Fin n,
            V P * fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
              (show TensorRSSpace (b + w) (c + w) I x from
                slotExtendIterFib (I := I) (M := M) g b c x A w) n e P J) ^ 2 ≤
        (∑ P : Fin (b + w) → Fin n, (V P) ^ 2) *
          ∑ Q : Fin b → Fin n, ∑ L : Fin c → Fin n,
            (fiberNormSqComponent (I := I) (M := M) g x b c
              (show TensorRSSpace b c I x from A) n e Q L) ^ 2 := by
  intro w
  induction w with
  | zero =>
      intro b c A V
      refine le_trans (Finset.sum_le_sum (fun J (_ : J ∈ Finset.univ) =>
        Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
          (fun P : Fin (b + 0) → Fin n => V P)
          (fun P : Fin (b + 0) → Fin n =>
            fiberNormSqComponent (I := I) (M := M) g x (b + 0) (c + 0)
              (show TensorRSSpace (b + 0) (c + 0) I x from
                slotExtendIterFib (I := I) (M := M) g b c x A 0) n e P J))) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_)
        (Finset.sum_nonneg (fun P _ => sq_nonneg _))
      rw [Finset.sum_comm]
      rfl
  | succ w ihw =>
      intro b c A V
      set cw : (Fin (b + w) → Fin n) → (Fin (c + w) → Fin n) → ℝ := fun P J =>
        fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
          (show TensorRSSpace (b + w) (c + w) I x from
            slotExtendIterFib (I := I) (M := M) g b c x A w) n e P J with hcw_def
      have hpeel : ∀ (P : Fin (b + (w + 1)) → Fin n) (J : Fin (c + (w + 1)) → Fin n),
          fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
              (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J =
            (if J 0 = P 0 then (1 : ℝ) else 0) *
              cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k)) := fun P J =>
        fiberNormSqComponent_slotExtendFib_eq (I := I) (M := M) g (b + w) (c + w) x
          (slotExtendIterFib (I := I) (M := M) g b c x A w) e horth P J
      have hstep : ∀ J : Fin (c + (w + 1)) → Fin n,
          (∑ P : Fin (b + (w + 1)) → Fin n,
            V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
              (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J) =
          ∑ P' : Fin (b + w) → Fin n,
            V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k)) := by
        intro J
        calc (∑ P : Fin (b + (w + 1)) → Fin n,
              V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
                (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                  slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J)
            = ∑ P : Fin (b + (w + 1)) → Fin n,
                V P * ((if J 0 = P 0 then (1 : ℝ) else 0) *
                  cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k))) :=
              Finset.sum_congr rfl (fun P _ => by rw [hpeel P J])
          _ = ∑ pr : Fin n × (Fin (b + w) → Fin n),
                V (Fin.cons pr.1 pr.2) * ((if J 0 = pr.1 then (1 : ℝ) else 0) *
                  cw pr.2 (fun k => J (Fin.succ k))) :=
              (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (b + w + 1) => Fin n))
                (fun pr : Fin n × (Fin (b + w) → Fin n) =>
                  V (Fin.cons pr.1 pr.2) * ((if J 0 = pr.1 then (1 : ℝ) else 0) *
                    cw pr.2 (fun k => J (Fin.succ k))))
                (fun P => V P * ((if J 0 = P 0 then (1 : ℝ) else 0) *
                  cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k))))
                (fun pr => by simp [Fin.consEquiv])).symm
          _ = ∑ p₀ : Fin n, ∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons p₀ P') * ((if J 0 = p₀ then (1 : ℝ) else 0) *
                  cw P' (fun k => J (Fin.succ k))) := Fintype.sum_prod_type _
          _ = ∑ P' : Fin (b + w) → Fin n, ∑ p₀ : Fin n,
                V (Fin.cons p₀ P') * ((if J 0 = p₀ then (1 : ℝ) else 0) *
                  cw P' (fun k => J (Fin.succ k))) := Finset.sum_comm
          _ = ∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k)) := by
              refine Finset.sum_congr rfl (fun P' _ => ?_)
              simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_zero]
              rw [Finset.sum_ite_eq Finset.univ (J 0) (fun p₀ =>
                V (Fin.cons p₀ P') * cw P' (fun k => J (Fin.succ k)))]
              rw [if_pos (Finset.mem_univ (J 0))]
      calc (∑ J : Fin (c + (w + 1)) → Fin n,
            (∑ P : Fin (b + (w + 1)) → Fin n,
              V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
                (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                  slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J) ^ 2)
          = ∑ J : Fin (c + (w + 1)) → Fin n,
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k))) ^ 2 :=
            Finset.sum_congr rfl (fun J _ => by rw [hstep J])
        _ = ∑ pr : Fin n × (Fin (c + w) → Fin n),
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons pr.1 P') * cw P' pr.2) ^ 2 :=
            (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (c + w + 1) => Fin n))
              (fun pr : Fin n × (Fin (c + w) → Fin n) =>
                (∑ P' : Fin (b + w) → Fin n, V (Fin.cons pr.1 P') * cw P' pr.2) ^ 2)
              (fun J => (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k))) ^ 2)
              (fun pr => by simp [Fin.consEquiv])).symm
        _ = ∑ j₀ : Fin n, ∑ J' : Fin (c + w) → Fin n,
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons j₀ P') * cw P' J') ^ 2 := Fintype.sum_prod_type _
        _ ≤ ∑ j₀ : Fin n,
              ((∑ P' : Fin (b + w) → Fin n, (V (Fin.cons j₀ P')) ^ 2) *
                ∑ Q : Fin b → Fin n, ∑ L : Fin c → Fin n,
                  (fiberNormSqComponent (I := I) (M := M) g x b c
                    (show TensorRSSpace b c I x from A) n e Q L) ^ 2) :=
            Finset.sum_le_sum (fun j₀ _ => ihw b c A (fun P' => V (Fin.cons j₀ P')))
        _ = (∑ j₀ : Fin n, ∑ P' : Fin (b + w) → Fin n, (V (Fin.cons j₀ P')) ^ 2) *
              ∑ Q : Fin b → Fin n, ∑ L : Fin c → Fin n,
                (fiberNormSqComponent (I := I) (M := M) g x b c
                  (show TensorRSSpace b c I x from A) n e Q L) ^ 2 :=
            (Finset.sum_mul _ _ _).symm
        _ = (∑ P : Fin (b + (w + 1)) → Fin n, (V P) ^ 2) *
              ∑ Q : Fin b → Fin n, ∑ L : Fin c → Fin n,
                (fiberNormSqComponent (I := I) (M := M) g x b c
                  (show TensorRSSpace b c I x from A) n e Q L) ^ 2 := by
            refine congrArg (fun t : ℝ => t *
              ∑ Q : Fin b → Fin n, ∑ L : Fin c → Fin n,
                (fiberNormSqComponent (I := I) (M := M) g x b c
                  (show TensorRSSpace b c I x from A) n e Q L) ^ 2) ?_
            exact Eq.trans (Fintype.sum_prod_type
                (fun pr : Fin n × (Fin (b + w) → Fin n) => (V (Fin.cons pr.1 pr.2)) ^ 2)).symm
              (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (b + w + 1) => Fin n))
                (fun pr : Fin n × (Fin (b + w) → Fin n) => (V (Fin.cons pr.1 pr.2)) ^ 2)
                (fun P => (V P) ^ 2)
                (fun pr => by simp [Fin.consEquiv]))


omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
private theorem riemannianFiberNormSq_comp_slotExtendIterFib_le (g : SmoothRiemannianMetric I M) (x : M)
    (w p b c : ℕ) (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x)
    (U : Tensor0SSpace p I x →L[ℝ] Tensor0SSpace (b + w) I x) :
    riemannianFiberNormSq (I := I) (M := M) g p (c + w) x
        (show TensorRSSpace p (c + w) I x from
          (slotExtendIterFib (I := I) (M := M) g b c x A w).comp U) ≤
      riemannianFiberNormSq (I := I) (M := M) g b c x (show TensorRSSpace b c I x from A) *
        riemannianFiberNormSq (I := I) (M := M) g p (b + w) x
          (show TensorRSSpace p (b + w) I x from U) := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g p (c + w) x _ e bse rfl
    hbse horth]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g b c x _ e bse rfl hbse
    horth]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g p (b + w) x _ e bse rfl
    hbse horth]
  have hcomp : ∀ (K : Fin p → Fin (Module.finrank ℝ E))
      (J : Fin (c + w) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g x p (c + w)
          (show TensorRSSpace p (c + w) I x from
            (slotExtendIterFib (I := I) (M := M) g b c x A w).comp U)
          (Module.finrank ℝ E) e K J =
        ∑ P : Fin (b + w) → Fin (Module.finrank ℝ E),
          fiberNormSqComponent (I := I) (M := M) g x p (b + w)
            (show TensorRSSpace p (b + w) I x from U) (Module.finrank ℝ E) e K P *
            fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
              (show TensorRSSpace (b + w) (c + w) I x from
                slotExtendIterFib (I := I) (M := M) g b c x A w)
              (Module.finrank ℝ E) e P J :=
    fun K J => fiberNormSqComponent_comp_eq (I := I) (M := M) g p (b + w) (c + w) x
      (show TensorRSSpace (b + w) (c + w) I x from
        slotExtendIterFib (I := I) (M := M) g b c x A w)
      (show TensorRSSpace p (b + w) I x from U) e bse hbse horth K J
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun J (_ : J ∈ Finset.univ) => by rw [hcomp K J]))]
  refine le_trans (Finset.sum_le_sum (fun K (_ : K ∈ Finset.univ) =>
    sum_sq_component_slotExtendIterFib_le (I := I) (M := M) g x e horth w b c A
      (fun P => fiberNormSqComponent (I := I) (M := M) g x p (b + w)
        (show TensorRSSpace p (b + w) I x from U) (Module.finrank ℝ E) e K P))) ?_
  rw [← Finset.sum_mul]
  rw [mul_comm]


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma operatorFieldApplicationLeibnizPsi_diag_toSection (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) (x : M) :
    ((operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i i).toSection x :
        Tensor0SSpace (b + i) I x →L[ℝ] Tensor0SSpace (c + i) I x) =
      slotExtendIterFib (I := I) (M := M) g b c x
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hdiag : operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (i + 1) =
          slotExtend (I := I) (M := M) g (b + i) (c + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i i) := by
        rw [operatorFieldApplicationLeibnizPsi_succ_succ_eq (I := I) (M := M) g b c Φ i i]
        rw [if_neg (by omega : ¬ (i + 1 < i + 1)), zero_add]
      rw [hdiag]
      rw [show (slotExtendIterFib (I := I) (M := M) g b c x
            (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) (i + 1)) =
          slotExtendPointwise (I := I) (M := M) (b + i) (c + i) x
            (slotExtendIterFib (I := I) (M := M) g b c x
              (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i)
          from rfl]
      rw [← ih]
      rfl

omit [BoundarylessManifold I M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (g : SmoothRiemannianMetric I M)
    (p b c : ℕ) (Φ : SmoothCcTensor g b c) (i : ℕ)
    (U : SmoothCcTensor g p (b + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g p (c + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g p (b + i) (c + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i i) U).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g p (b + i) x (U.toSection x) := by
  rw [operatorFieldComposition_toSection (I := I) (M := M) g p (b + i) (c + i)
    (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i i) U x]
  rw [show (show Tensor0SSpace (b + i) I x →L[ℝ] Tensor0SSpace (c + i) I x from
        (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i i).toSection x) =
      slotExtendIterFib (I := I) (M := M) g b c x
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i from
    operatorFieldApplicationLeibnizPsi_diag_toSection (I := I) (M := M) g b c Φ i x]
  exact riemannianFiberNormSq_comp_slotExtendIterFib_le (I := I) (M := M) g x i p b c
    (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
    (show Tensor0SSpace p I x →L[ℝ] Tensor0SSpace (b + i) I x from U.toSection x)

omit [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
    (g : SmoothRiemannianMetric I M) :
    ∀ (j p a b : ℕ) (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g p a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g p (b + j) x
          ((iteratedCovGrad (I := I) g p b j
            (ccOperatorFieldComp (I := I) (M := M) g p a b Φ W)).toSection x) ≤
        diagonalGridGrowthFactor (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
                ((iteratedCovGrad (I := I) g a b i Φ).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g p (a + l) x
                  ((iteratedCovGrad (I := I) g p a l W).toSection x) := by
  intro j
  induction j with
  | zero =>
      intro p a b Φ W x
      rw [iteratedCovGrad_zero, diagonalGridGrowthFactor, pow_zero, one_mul]
      rw [Finset.sum_range_one, Finset.sum_range_one, iteratedCovGrad_zero, iteratedCovGrad_zero]
      simp only [Nat.add_zero]
      rw [operatorFieldComposition_toSection (I := I) (M := M) g p a b Φ W x]
      have h := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g p a b x
        (show TensorRSSpace a b I x from Φ.toSection x)
        (show TensorRSSpace p a I x from W.toSection x)
      simpa using h
  | succ j ih =>
      intro p a b Φ W x
      classical
      rw [← riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g p b j
        (ccOperatorFieldComp (I := I) (M := M) g p a b Φ W) x]
      rw [covGrad_operatorFieldComposition_eq (I := I) (M := M) g p a b Φ W]
      rw [iteratedCovGrad_add]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g p ((b + 1) + j) x
        ((iteratedCovGrad (I := I) g p (b + 1) j
          (ccOperatorFieldComp (I := I) (M := M) g p a (b + 1)
            (covGrad (I := I) (M := M) g a b Φ) W)).toSection x)
        ((iteratedCovGrad (I := I) g p (b + 1) j
          (ccOperatorFieldComp (I := I) (M := M) g p (a + 1) (b + 1)
            (slotExtend (I := I) (M := M) g a b Φ)
            (covGrad (I := I) (M := M) g p a W))).toSection x)) ?_
      set cΦ : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
        ((iteratedCovGrad (I := I) g a b i Φ).toSection x) with hcΦ_def
      set cW : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g p (a + l) x
        ((iteratedCovGrad (I := I) g p a l W).toSection x) with hcW_def
      have hcΦ_nn : ∀ i, 0 ≤ cΦ i := fun i =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g a (b + i) x _
      have hcW_nn : ∀ l, 0 ≤ cW l := fun l =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g p (a + l) x _
      have hGj_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) j := operatorFieldApplicationGdiag_nonneg (E := E) j
      have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      have hArmA : riemannianFiberNormSq (I := I) (M := M) g p ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g p (b + 1) j
              (ccOperatorFieldComp (I := I) (M := M) g p a (b + 1)
                (covGrad (I := I) (M := M) g a b Φ) W)).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j *
            ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l := by
        refine le_trans (ih p a (b + 1) (covGrad (I := I) (M := M) g a b Φ) W x) ?_
        refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) hGj_nn
        rw [hcΦ_def]
        dsimp only
        rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g a b i Φ x]
      have hArmB : riemannianFiberNormSq (I := I) (M := M) g p ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g p (b + 1) j
              (ccOperatorFieldComp (I := I) (M := M) g p (a + 1) (b + 1)
                (slotExtend (I := I) (M := M) g a b Φ)
                (covGrad (I := I) (M := M) g p a W))).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j *
            ((Module.finrank ℝ E : ℝ) *
              ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
        refine le_trans (ih p (a + 1) (b + 1) (slotExtend (I := I) (M := M) g a b Φ)
          (covGrad (I := I) (M := M) g p a W) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ hGj_nn
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hWinner : (∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g p ((a + 1) + l) x
                ((iteratedCovGrad (I := I) g p (a + 1) l
                  (covGrad (I := I) (M := M) g p a W)).toSection x)) =
            ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hcW_def]
          dsimp only
          rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g p a l W x]
        rw [hWinner]
        have hΦle : riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
              ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                (slotExtend (I := I) (M := M) g a b Φ)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) * cΦ i := by
          rw [hcΦ_def]
          dsimp only
          exact riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g a b Φ i x
        calc riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
                ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                  (slotExtend (I := I) (M := M) g a b Φ)).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
            ≤ ((Module.finrank ℝ E : ℝ) * cΦ i) * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) :=
                mul_le_mul_of_nonneg_right hΦle
                  (Finset.sum_nonneg (fun l _ => hcW_nn (l + 1)))
          _ = (Module.finrank ℝ E : ℝ) * (cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
                ring
      refine le_trans (add_le_add
        (mul_le_mul_of_nonneg_left hArmA (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hArmB (by norm_num : (0:ℝ) ≤ 2))) ?_
      set Gj : ℝ := diagonalGridGrowthFactor (E := E) j with hGj_def
      set SA : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l
        with hSA_def
      set SB : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
        with hSB_def
      set DG : ℝ := ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l with hDG_def
      have hstep : SA + (Module.finrank ℝ E : ℝ) * SB ≤ ((Module.finrank ℝ E : ℝ) + 1) * DG := by
        rw [hSA_def, hSB_def, hDG_def]
        exact diagonalGrid_step_le (Module.finrank ℝ E : ℝ) hn_nn j cΦ cW hcΦ_nn hcW_nn
      have hGdiag_succ : diagonalGridGrowthFactor (E := E) (j + 1) =
          (2 * ((Module.finrank ℝ E : ℝ) + 1)) * Gj := by
        rw [hGj_def, diagonalGridGrowthFactor, diagonalGridGrowthFactor, pow_succ]; ring
      rw [hGdiag_succ]
      have hGj_nn' : (0 : ℝ) ≤ Gj := hGj_nn
      nlinarith only [mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 2 * Gj), hGj_nn',
        hstep]


abbrev rsDomDomCongr {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) : TensorRSSpace r s I x :=
  tensorRSDomDomCongr (I := I) (M := M) σ T

abbrev operatorFieldApplicationGdiag (j : ℕ) : ℝ := diagonalGridGrowthFactor (E := E) j

alias operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le :=
  riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le

end Spectral
end Analysis
end DifferentialGeometry

end
