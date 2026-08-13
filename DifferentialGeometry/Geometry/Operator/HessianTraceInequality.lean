import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

omit [NeZero (Module.finrank ℝ E)] in
private theorem fin_two_sum_rewrite
    {Idx : Type*} [Fintype Idx]
    (G : (Fin 2 → Idx) → ℝ) :
    (∑ I0 : Fin 2 → Idx, G I0) =
      ∑ i : Idx, ∑ j : Idx, G (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  let etof : (Fin 2 → Idx) → Idx × Idx := fun I0 => (I0 0, I0 1)
  let einv : Idx × Idx → (Fin 2 → Idx) :=
    fun p => (fun a : Fin 2 => if a = 0 then p.1 else p.2)
  let e : (Fin 2 → Idx) ≃ (Idx × Idx) :=
    { toFun := etof
      invFun := einv
      left_inv := by
        intro I0
        funext a
        fin_cases a <;> simp [etof, einv]
      right_inv := by
        intro p
        cases p with
        | mk i j => simp [etof, einv] }
  rw [Fintype.sum_equiv e G (fun p : Idx × Idx =>
      G (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr 1
    change I0 = fun a : Fin 2 => if a = 0 then (etof I0).1 else (etof I0).2
    funext a
    fin_cases a <;> simp [etof]

omit [NeZero (Module.finrank ℝ E)] in
private theorem hessianTrace_parseval_of_orthonormal
    (g : SmoothRiemannianMetric I M)
    (x : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hON : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (f : M → ℝ) :
    normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (hessFun (I := I) g f x (basis i) (basis j))^2 := by
  classical
  rw [normSq0S_eq_coord (I := I) g x 2 basis
    (fun i j => if i = j then (1 : ℝ) else 0)
    (metricInverseInBasis_of_orthonormal (I := I) g basis hON)
    (hessTensorAt (I := I) g f x)]
  unfold coordInner0S
  simp only [tensor0SComponent_apply]
  have hprod2 : ∀ (i j k l : Fin (Module.finrank ℝ E)),
      (∏ a : Fin 2,
        (if (fun a' : Fin 2 => if a' = 0 then i else j) a =
            (fun a' : Fin 2 => if a' = 0 then k else l) a then (1 : ℝ) else 0)) =
        (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0) := by
    intro i j k l
    rw [Fin.prod_univ_two]
    simp
  have hvec : ∀ (i j : Fin (Module.finrank ℝ E)),
      (fun a : Fin 2 => basis (if a = 0 then i else j)) = vec2 (basis i) (basis j) := by
    intro i j
    funext a
    fin_cases a <;> simp [vec2]
  have hinner : ∀ (i j : Fin (Module.finrank ℝ E)),
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (∏ a : Fin 2,
            (if (fun a' : Fin 2 => if a' = 0 then i else j) a =
                (fun a' : Fin 2 => if a' = 0 then k else l) a then (1 : ℝ) else 0)) *
              hessTensorAt (I := I) g f x
                (fun a' : Fin 2 => basis (if a' = 0 then i else j)) *
              hessTensorAt (I := I) g f x
                (fun a : Fin 2 => basis (if a = 0 then k else l))) =
        (hessFun (I := I) g f x (basis i) (basis j))^2 := by
    intro i j
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            (∏ a : Fin 2,
              (if (fun a' : Fin 2 => if a' = 0 then i else j) a =
                  (fun a' : Fin 2 => if a' = 0 then k else l) a then (1 : ℝ) else 0)) *
                hessTensorAt (I := I) g f x
                  (fun a' : Fin 2 => basis (if a' = 0 then i else j)) *
                hessTensorAt (I := I) g f x
                  (fun a : Fin 2 => basis (if a = 0 then k else l))) =
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0) *
                hessTensorAt (I := I) g f x
                  (fun a' : Fin 2 => basis (if a' = 0 then i else j)) *
                hessTensorAt (I := I) g f x (vec2 (basis k) (basis l)) from by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hprod2 i j k l]
        congr 1]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl]
        rw [hvec i j]
        rw [hessTensorAt_apply]
        ring
      · intro l _ hlj
        have hjl : ¬ j = l := fun h => hlj h.symm
        rw [if_neg (by exact fun h => hlj h.symm)]
        simp
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · intro k _ hki
      have hik : ¬ i = k := fun h => hki h.symm
      rw [if_neg (by exact fun h => hki h.symm)]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  calc
    (∑ I0 : Fin 2 → Fin (Module.finrank ℝ E),
        ∑ J0 : Fin 2 → Fin (Module.finrank ℝ E),
          (∏ a : Fin 2, (if I0 a = J0 a then (1 : ℝ) else 0)) *
            hessTensorAt (I := I) g f x (fun a => basis (I0 a)) *
            hessTensorAt (I := I) g f x (fun a => basis (J0 a)))
        = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (hessFun (I := I) g f x (basis i) (basis j))^2 := by
          rw [fin_two_sum_rewrite]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [fin_two_sum_rewrite]
          exact hinner i j

omit [NeZero (Module.finrank ℝ E)] in
private theorem hessianTrace_chart_norm_of_boundaryless
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) =
      chartHessFrobeniusSq (I := I) g f x := by
  classical
  let hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  let cbasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) x hbase
  let cgInv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartInvGramMatrix (I := I) g x x i j
  have hcinv : MetricInverseInBasis_gen (I := I) g x cbasis cgInv := by
    intro i j
    constructor
    · have hmatrix := congrArg (fun A => A i j)
        (chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, cbasis, cgInv,
        chartBasisFamily_apply] using hmatrix
    · have hmatrix := congrArg (fun A => A i j)
        (chartGramMatrix_mul_chartInvGramMatrix (I := I) g x hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, cbasis, cgInv,
        chartBasisFamily_apply] using hmatrix
  have hcb : ∀ i : Fin (Module.finrank ℝ E), cbasis i = (chartModelBasis E) i := by
    intro i
    rw [show cbasis i = chartBasisVecFiber (I := I) x i x by
      exact chartBasisFamily_apply (I := I) x hbase i]
    exact chartBasisVecFiber_self (I := I) x i
  have hvecb : ∀ (i j : Fin (Module.finrank ℝ E)),
      (fun a : Fin 2 => cbasis (if a = 0 then i else j)) = vec2 (cbasis i) (cbasis j) := by
    intro i j
    funext a
    fin_cases a <;> simp [vec2]
  have hcomp : ∀ (i j : Fin (Module.finrank ℝ E)),
      hessTensorAt (I := I) g f x (vec2 (cbasis i) (cbasis j)) =
        chartHessianTensor (I := I) g x f i j x := by
    intro i j
    rw [hessTensorAt_apply]
    rw [hcb i, hcb j]
    rw [hessFun_eq_cov_grad (I := I) g hf x ((chartModelBasis E) i) ((chartModelBasis E) j)]
    rw [← chartHessianTensor_eq_inner_cov_gradFun_basis_of_matrix_identity
      (I := I) g hf x (chartHessianMatrixIdentity_holds (I := I) g hf x) i j]
  rw [normSq0S_eq_coord (I := I) g x 2 cbasis cgInv hcinv (hessTensorAt (I := I) g f x)]
  unfold coordInner0S
  simp only [tensor0SComponent_apply]
  rw [chartHessFrobeniusSq_def]
  rw [fin_two_sum_rewrite]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [fin_two_sum_rewrite (fun J0 : Fin 2 → Fin (Module.finrank ℝ E) =>
    (∏ a : Fin 2, cgInv ((fun a' : Fin 2 => if a' = 0 then i else j) a) (J0 a)) *
      hessTensorAt (I := I) g f x
        (fun a' : Fin 2 => cbasis (if a' = 0 then i else j)) *
      hessTensorAt (I := I) g f x (fun a : Fin 2 => cbasis (J0 a)))]
  have hsummand : ∀ (k l : Fin (Module.finrank ℝ E)),
      (∏ a : Fin 2, cgInv ((fun a' : Fin 2 => if a' = 0 then i else j) a)
        ((fun a' : Fin 2 => if a' = 0 then k else l) a)) *
          hessTensorAt (I := I) g f x
            (fun a' : Fin 2 => cbasis (if a' = 0 then i else j)) *
          hessTensorAt (I := I) g f x
            (fun a' : Fin 2 => cbasis (if a' = 0 then k else l)) =
        cgInv i k * cgInv j l *
          chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k l x := by
    intro k l
    rw [show (∏ a : Fin 2, cgInv ((fun a' : Fin 2 => if a' = 0 then i else j) a)
        ((fun a' : Fin 2 => if a' = 0 then k else l) a)) = cgInv i k * cgInv j l by
      rw [Fin.prod_univ_two]
      simp]
    rw [hvecb i j, hvecb k l, hcomp i j, hcomp k l]
  have hsum : (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (∏ a : Fin 2, cgInv ((fun a' : Fin 2 => if a' = 0 then i else j) a)
            ((fun a' : Fin 2 => if a' = 0 then k else l) a)) *
              hessTensorAt (I := I) g f x
                (fun a' : Fin 2 => cbasis (if a' = 0 then i else j)) *
              hessTensorAt (I := I) g f x
                (fun a' : Fin 2 => cbasis (if a' = 0 then k else l))) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            cgInv i k * cgInv j l *
              chartHessianTensor (I := I) g x f i j x *
              chartHessianTensor (I := I) g x f k l x := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact hsummand k l
  rw [hsum]

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacian_sq_le_dim_mul_hessianFrobeniusSq_of_boundaryless
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (Δ_g (I := I) g ⟨f, hf⟩ x)^2 ≤
      (Module.finrank ℝ E : ℝ) * chartHessFrobeniusSq (I := I) g f x := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have htr : Δ_g (I := I) g ⟨f, hf⟩ x =
      ∑ i : Fin (Module.finrank ℝ E), hessFun (I := I) g f x (basis i) (basis i) := by
    have hlap : laplacian (I := I) (LeviCivita (I := I) g) g f x =
        metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g f x) :=
      lap_eq_hess_on (I := I) g isOpen_univ hf.contMDiffOn (Set.mem_univ x)
    have htrace : metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g f x) =
        ∑ i : Fin (Module.finrank ℝ E), hessFun (I := I) g f x (basis i) (basis i) := by
      rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
        (fun i j => if i = j then (1 : ℝ) else 0)
        (metricInverseInBasis_of_orthonormal (I := I) g basis hON)
        (hessTensorAt (I := I) g f x)]
      simp only [hessTensorAt_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have hij : ¬ i = j := fun h => hji h.symm
        rw [if_neg hij]
        ring
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [← laplacian_levi_eq (I := I) g hf x]
    exact hlap.trans htrace
  have hineq : (∑ i : Fin (Module.finrank ℝ E),
        hessFun (I := I) g f x (basis i) (basis i))^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (hessFun (I := I) g f x (basis i) (basis j))^2 := by
    have hb := bilinForm_trace_sq_le_card_mul_frobenius_sq
      (V := TangentSpace I x) (B := hessFun (I := I) g f x) (v := basis)
    simpa [Fintype.card_fin] using hb
  have hpv : normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (hessFun (I := I) g f x (basis i) (basis j))^2 :=
    hessianTrace_parseval_of_orthonormal (I := I) g x basis hON f
  have hfr : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (hessFun (I := I) g f x (basis i) (basis j))^2) =
      chartHessFrobeniusSq (I := I) g f x :=
    Eq.trans (Eq.symm hpv)
      (hessianTrace_chart_norm_of_boundaryless (I := I) g hf x)
  have htr' : (Δ_g (I := I) g ⟨f, hf⟩ x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (hessFun (I := I) g f x (basis i) (basis j))^2 := by
    rw [htr]
    exact hineq
  rw [← hfr]
  exact htr'

end DivergenceTheorem
end Integral
end DifferentialGeometry

end
