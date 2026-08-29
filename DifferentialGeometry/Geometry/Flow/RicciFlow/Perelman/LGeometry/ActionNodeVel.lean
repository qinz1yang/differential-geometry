import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionNodeMatch
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramInv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
theorem lNode_vel_match
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (t : Fin 3 → Real) (p : Fin 2 → M) (gamma : Real → M)
    (u : (i : Fin 2) → timeH1 E (lSegLen t i))
    (hpos : ∀ i : Fin 2, t i.castSucc < t i.succ)
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hreg : ∀ s ∈ Icc (t 0) (t (Fin.last 2)), T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta (t 0) = gamma (t 0) →
      delta (t (Fin.last 2)) = gamma (t (Fin.last 2)) →
      lRegAction S T gamma (t 0) (t (Fin.last 2)) ≤
        lRegAction S T delta (t 0) (t (Fin.last 2))) :
    tangentCoordChange I (p 0) (p 1) (gamma (t 1))
        (derivWithin (u 0).toFun
          (Icc (0 : Real) (lSegLen t 0)) (lSegLen t 0)) =
      derivWithin (u 1).toFun (Icc (0 : Real) (lSegLen t 1)) 0 := by
  classical
  have hfin0c : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  have hfin0s : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  have hfin1c : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  have hfin1s : (1 : Fin 2).succ = Fin.last 2 := rfl
  have ht01 : t 0 < t 1 := by
    simpa only [hfin0c, hfin0s] using hpos 0
  have ht12 : t 1 < t (Fin.last 2) := by
    simpa only [hfin1c, hfin1s] using hpos 1
  have hp : gamma (t 1) ∈ (extChartAt I (p 0)).source := by
    rw [extChartAt_source]
    exact hsrc 0 ⟨ht01.le, le_rfl⟩
  have hq : gamma (t 1) ∈ (extChartAt I (p 1)).source := by
    rw [extChartAt_source]
    exact hsrc 1 ⟨le_rfl, ht12.le⟩
  let v₀ := derivWithin (u 0).toFun
    (Icc (0 : Real) (lSegLen t 0)) (lSegLen t 0)
  let v₁ := derivWithin (u 1).toFun
    (Icc (0 : Real) (lSegLen t 1)) 0
  let J := tangentCoordChange I (p 0) (p 1) (gamma (t 1))
  let Jrev := tangentCoordChange I (p 1) (p 0) (gamma (t 1))
  have hJrev (y : E) : J (Jrev y) = y := by
    calc
      J (Jrev y) =
          tangentCoordChange I (p 1) (p 1) (gamma (t 1)) y :=
        tangentCoordChange_comp (I := I) (w := p 1) (x := p 0)
          (y := p 1) (z := gamma (t 1)) ⟨⟨hq, hp⟩, hq⟩
      _ = y := tangentCoordChange_self (I := I) hq
  have hmom := lNode_mom_match (I := I) S hS T t p gamma u
    hpos hsrc hrep hreg hmin
  have hGram :
      chartGramOp (I := I) S.family (p 1)
          (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1))) (J v₀) =
        chartGramOp (I := I) S.family (p 1)
          (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1))) v₁ := by
    apply ext_inner_right Real
    intro y
    let z := Jrev y
    have hzy : J z = y := hJrev y
    calc
      inner Real
          (chartGramOp (I := I) S.family (p 1)
            (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1))) (J v₀)) y =
          inner Real
            (chartGramOp (I := I) S.family (p 1)
              (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1))) (J v₀))
            (J z) := by rw [hzy]
      _ = inner Real
          (chartGramOp (I := I) S.family (p 0)
            (T - (t 1) ^ 2, extChartAt I (p 0) (gamma (t 1))) v₀) z :=
        (chartGramOp_change (I := I) S.family hp hq
          (T - (t 1) ^ 2) v₀ z).symm
      _ = inner Real
          (chartGramOp (I := I) S.family (p 1)
            (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1))) v₁) (J z) :=
        hmom z
      _ = inner Real
          (chartGramOp (I := I) S.family (p 1)
            (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1))) v₁) y := by
        rw [hzy]
  have htreg : T - (t 1) ^ 2 ∈ D.regular :=
    hreg (t 1) ⟨ht01.le, ht12.le⟩
  have htarget : extChartAt I (p 1) (gamma (t 1)) ∈
      interior (extChartAt I (p 1)).target := by
    rw [(isOpen_extChartAt_target (I := I) (p 1)).interior_eq]
    exact (extChartAt I (p 1)).map_source hq
  have hunit : IsUnit
      (chartGramOp (I := I) S.family (p 1)
        (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1)))) :=
    chartGramOp_unit (I := I) hS.smoothMetric
      (J := {T - (t 1) ^ 2}) (by simpa only [singleton_subset_iff] using htreg)
      (p 1) (K := {extChartAt I (p 1) (gamma (t 1))})
      (by simpa only [singleton_subset_iff] using htarget) _ (by simp)
  have hinj : Function.Injective
      (chartGramOp (I := I) S.family (p 1)
        (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1)))) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  simpa only [J, v₀, v₁] using hinj hGram

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
