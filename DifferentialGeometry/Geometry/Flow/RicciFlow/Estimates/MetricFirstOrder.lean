import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Local
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Restart.SolutionBounds

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

theorem exists_uniform_metric_first_order_bound_on_slab
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alphaMinus alpha b C : Real}
    (hbuffer : alphaMinus < alpha)
    (halphaB : alpha < b)
    (hslab : Set.Icc alphaMinus b ⊆ D.carrier)
    (hreg : Set.Ioc alphaMinus b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric alphaMinus))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Set.Icc alphaMinus b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C) :
    ∃ Lambda C1 : Real, 1 ≤ Lambda ∧ 0 ≤ C1 ∧
      (∀ t ∈ Set.Icc alpha b,
        MetricUniformEquivalentOn (I := I) Set.univ
          (S.base.metric alpha) (S.base.metric t) Lambda) ∧
      (∀ t ∈ Set.Icc alpha b,
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1
          (S.base.metric t) (S.base.metric alpha) C1) := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
      let _ : IsEmpty M := hEmpty
      refine ⟨1, 0, le_rfl, le_rfl, ?_, ?_⟩
      · intro t ht
        refine ⟨le_rfl, ?_⟩
        intro x
        exact isEmptyElim x
      · intro t ht x
        exact isEmptyElim x
  | inr hNonempty =>
      let _ : Nonempty M := hNonempty
      let K : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt C
      have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
      have hric : ∀ t ∈ Set.Icc alphaMinus b, ∀ x : M,
          ∀ v : TangentSpace I x,
            |ricciTensor (I := I) (S.base.metric t) x v v| ≤
              K * (S.base.metric t).inner x v v := by
        intro t ht x v
        exact ricci_quadratic_form_bound_of_solution_curvature_bound
          (I := I) S x v (hcurv t ht x)
      have hslabAB : Set.Icc alpha b ⊆ D.carrier := by
        intro t ht
        exact hslab ⟨hbuffer.le.trans ht.1, ht.2⟩
      have hregAB : Set.Ioo alpha b ⊆ D.regular := by
        intro t ht
        exact hreg ⟨hbuffer.trans ht.1, ht.2.le⟩
      have hpde := metricPDE_Icc (I := I) S hS hslabAB hregAB
      let Lambda : Real := Real.exp (2 * K * (b - alpha))
      have hLambda : 1 ≤ Lambda := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonneg (mul_nonneg (by norm_num) hK) (sub_nonneg.mpr halphaB.le))
      have hequiv : ∀ t ∈ Set.Icc alpha b,
          MetricUniformEquivalentOn (I := I) Set.univ
            (S.base.metric alpha) (S.base.metric t) Lambda := by
        intro t ht
        refine ⟨hLambda, ?_⟩
        intro x hx v
        have hpair := metricEquiv_Icc (I := I) (fun s => S.base.metric s) hpde
          (fun s hs y w => hric s ⟨hbuffer.le.trans hs.1, hs.2⟩ y w) t ht x v
        have htime : 0 ≤ t - alpha ∧ t - alpha ≤ b - alpha := by
          constructor <;> linarith [ht.1, ht.2]
        constructor
        · have hfactor : Lambda⁻¹ ≤ Real.exp (-(2 * K * (t - alpha))) := by
            rw [show Lambda⁻¹ = Real.exp (-(2 * K * (b - alpha))) by
              simpa [Lambda] using (Real.exp_neg (2 * K * (b - alpha))).symm]
            exact Real.exp_le_exp.mpr
              (neg_le_neg (mul_le_mul_of_nonneg_left htime.2
                (mul_nonneg (by norm_num) hK)))
          exact (mul_le_mul_of_nonneg_right hfactor
            (Geometry.Riemannian.Exponential.gInner_self_nonneg
              (I := I) (S.base.metric alpha) x v)).trans hpair.1
        · exact hpair.2.trans (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime.2
              (mul_nonneg (by norm_num) hK)))
            (Geometry.Riemannian.Exponential.gInner_self_nonneg
              (I := I) (S.base.metric alpha) x v))
      let F : CheegerGromovCompactness.PointedFlowData (I := I) D := {
        M := M
        topology := inferInstance
        charted := inferInstance
        smooth := inferInstance
        sigmaCompact := inferInstance
        t2 := inferInstance
        t2TangentBundle := by infer_instance
        basepoint := Classical.choice hNonempty
        S := S
        isSolution := hS
      }
      obtain ⟨KShi, hKShi, hShi⟩ := CheegerGromovCompactness.movingShi_complete
        (I := I) F hbuffer halphaB.le hslab hreg hcomplete.complete hC hcurv 1
      let gSeq : Nat → Real → SmoothRiemannianMetric I M :=
        fun _ t => S.base.metric t
      let gRef : SmoothRiemannianMetric I M := S.base.metric alpha
      have hShi' : MovingShiBoundOn (I := I) Set.univ alpha b gSeq 1 KShi := by
        simpa [F, gSeq] using hShi
      have hDreg : ∀ {t : Real}, t ∈ D.regular → D.regular ∈ nhds t :=
        fun {_t} ht => D.regular_isOpen.mem_nhds ht
      have hev : ∀ i : Nat, ∀ x ∈ (Set.univ : Set M),
          ∀ s ∈ Set.Icc alpha b, ∀ v : Fin (1 + 2) → TangentSpace I x,
            HasDerivAt
              (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef 1 x v)
              (((-2 : Real) • nablaRicReal (I := I) gSeq gRef 1 i s x) v) s := by
        intro i x hx s hs
        exact (hevComp_of_solutions (I := I) (β := alpha) (ψ := b) (N := 1)
          (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl)
          (fun _ t ht => hreg ⟨hbuffer.trans_le ht.1, ht.2⟩)
          (fun _ p hp V x0 =>
            solutionTowerSwap_regularity (I := I) gRef S hS 1 hDreg p hp V x0)) i x s hs
      let Cg : Nat → Real := fun _ => 0
      let C1 : Real := metricCovOrderEvolutionConstant
        (ricTowerCoeffs (Module.finrank Real E) 1 Lambda Cg KShi).slope
        (ricTowerCoeffs (Module.finrank Real E) 1 Lambda Cg KShi).offset
        (b - alpha) 0
      have horder : MetricCovDerivOrderBoundOnWindow (I := I) Set.univ alpha b
          gSeq gRef 1 C1 := by
        exact covOrderBound_stage_on (I := I) isOpen_univ 1 (by omega) Lambda hLambda
          (fun _ t ht => by simpa [gSeq, gRef] using hequiv t ht) Cg
          (by intro r hr hr'; omega) KShi hKShi hShi'
          ⟨le_rfl, halphaB.le⟩ hev 0 le_rfl
          (by intro i x hx; exact le_of_eq (by
            simpa [gSeq, gRef] using covNorm_self_succ (I := I) gRef 0 x))
          (b - alpha)
          (by intro t ht
              rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
              linarith [ht.2])
      refine ⟨Lambda, C1, hLambda, Real.sqrt_nonneg _, hequiv, ?_⟩
      intro t ht
      exact horder 0 t ht

end DifferentialGeometry.PDE.RicciFlow
