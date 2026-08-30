import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Local

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem shi_curvature_derivative_bound_on_slab
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alpha beta psi C : Real}
    (halphaBeta : alpha < beta)
    (hbetaPsi : beta <= psi)
    (hslab : Set.Icc alpha psi ⊆ D.carrier)
    (hreg : Set.Ioc alpha psi ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric alpha))
    (hC : 0 <= C)
    (hcurv : ∀ t ∈ Set.Icc alpha psi, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I)
        (S.base.metric t) x 4 (S.base.rm04 t x) <= C) :
    ∃ KShi : Real, 0 <= KShi ∧
      ∀ k : Nat, k <= 2 → ∀ t ∈ Set.Icc beta psi, ∀ x : M,
        nablaKRm04NormSqIntrinsic (I := I) S k t x <= KShi := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
      let _ : IsEmpty M := hEmpty
      refine ⟨0, le_rfl, ?_⟩
      intro _k _hk _t _ht x
      exact isEmptyElim x
  | inr hNonempty =>
      let F : DifferentialGeometry.HCGCompactness.PointedFlowData
          (I := I) D := {
        M := M
        topology := ‹TopologicalSpace M›
        charted := ‹ChartedSpace H M›
        smooth := ‹IsManifold I ∞ M›
        sigmaCompact := ‹SigmaCompactSpace M›
        t2 := ‹T2Space M›
        t2TangentBundle := by infer_instance
        basepoint := Classical.choice hNonempty
        S := S
        isSolution := hS
      }
      have hCompleteF : DifferentialGeometry.HCGCompactness.MetricComplete
          (I := I) (F.atTime (I := I) alpha) := by
        exact hcomplete.complete
      have hCurvF : ∀ t ∈ Set.Icc alpha psi, ∀ x : F.M,
          F.rmNormSq (I := I) t x <= C := by
        exact hcurv
      have hRm := DifferentialGeometry.HCGCompactness.movingRm_of_bound
        (I := I) F halphaBeta hbetaPsi hslab hreg hCompleteF hC hCurvF 2
      let KShi : Real := ∑ k ∈ Finset.range 3,
        max 0 (DifferentialGeometry.HCGCompactness.rmOpenBound
          (Module.finrank Real E) C alpha beta psi 2 k)
      refine ⟨KShi, ?_, ?_⟩
      · exact Finset.sum_nonneg fun _ _ ↦ le_max_left 0 _
      · intro k hk t ht x
        have hkMem : k ∈ Finset.range 3 := by
          simp only [Finset.mem_range]
          omega
        calc
          nablaKRm04NormSqIntrinsic (I := I) S k t x <=
              DifferentialGeometry.HCGCompactness.rmOpenBound
                (Module.finrank Real E) C alpha beta psi 2 k := by
            simpa [F] using hRm k hk t ht x
          _ <= max 0 (DifferentialGeometry.HCGCompactness.rmOpenBound
                (Module.finrank Real E) C alpha beta psi 2 k) := le_max_right _ _
          _ <= KShi := by
            exact Finset.single_le_sum
              (fun j _ ↦ le_max_left 0
                (DifferentialGeometry.HCGCompactness.rmOpenBound
                  (Module.finrank Real E) C alpha beta psi 2 j)) hkMem

end DifferentialGeometry.PDE.RicciFlow
