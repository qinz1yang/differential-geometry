import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TowerHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.ResidualBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.TowerSwapRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckBaseProducer

/-!
# Local-frame residual data from a Ricci-flow solution

The positive-tail regularity producer and the dimension-three level-zero
curvature equation discharge every standing input of `resStarBoundLF`.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The canonical whole residual field, fixed recursively before any point or
orthonormal-frame choice. -/
noncomputable def rmResidualField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) :
    (k : Nat) → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)
  | 0 => e0Field (I := I) S (t : Real)
  | k + 1 => resStarNext (I := I) S t k (rmResidualField S t k)

omit [BoundarylessManifold I M] in
/-- The canonical residual field has the exact recursive constructor cost in
every finite component index type. -/
theorem rmResidualField_cost
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D)
    {Idx : Type*} [Fintype Idx]
    (k : Nat) :
    StarSum2Cost (I := I) Idx S (t : Real) k
      (rmResidualField (I := I) S t k)
      (rmResidualCost (Fintype.card Idx) k) := by
  classical
  induction k with
  | zero =>
      simpa only [rmResidualField] using
        (e0Residual (I := I) S hS t (Idx := Idx)).1
  | succ k ih =>
      simpa only [rmResidualField] using
        resStarNext_cost (I := I) S hS k t
          (rmResidualField (I := I) S t k) ih

omit [BoundarylessManifold I M] in
/-- On one orthonormal local-frame patch, the fixed recursive field realizes
the component heat equation at every tower level. -/
private theorem rmResidual_local
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (frame : Idx → (y : M) → TangentSpace I y)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (horthU : ∀ y : M, y ∈ u → ∀ i j : Idx,
      (S.base.metric (t : Real)).inner y (frame i y) (frame j y) =
        if i = j then (1 : Real) else 0)
    (baseDt : Real → M → (Fin 4 → Idx) → Real)
    (chrDt : Real → M → Idx → Idx → Idx → Real)
    (hrm : ∀ (y : M), y ∈ u → ∀ m : Fin 4 → Idx,
      HasDerivWithinAt (fun s : Real => lfBase (I := I) S frame s y m)
        (baseDt (t : Real) y m) D.carrier (t : Real))
    (hchr : ∀ (y : M), y ∈ u → ∀ i a p : Idx,
      HasDerivWithinAt (fun s : Real => lfChr (I := I) S frame hframe s y i a p)
        (chrDt (t : Real) y i a p) D.carrier (t : Real))
    (hchrId : ∀ (y : M), y ∈ u → ∀ i j p : Idx,
      chrDt (t : Real) y i j p =
        -ricciCovDerivCompInFrame (I := I) S frame (t : Real) y i j p
        -ricciCovDerivCompInFrame (I := I) S frame (t : Real) y j i p
        +ricciCovDerivCompInFrame (I := I) S frame (t : Real) y p i j)
    (hswap : ∀ (y : M), y ∈ u → ∀ (k : Nat) (d : Idx)
        (m : Fin (4 + k) → Idx),
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun z : M =>
              iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe)
                (lfBase (I := I) S frame) k s z m) y (frame d y))
        (extDerivFun (I := I)
          (fun z : M =>
            iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
              (lfBase (I := I) S frame) baseDt k (t : Real) z m) y (frame d y))
        D.carrier (t : Real)) :
    ∀ (k : Nat) (y : M) (hy : y ∈ u) (I0 : Fin (4 + k) → Idx),
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k y)
            (fun i => frame i y) I0)
        (tensor0SComponent (I := I)
          (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
              (identityInvMetric (Idx := Idx))
              (nablaKRm04Field (I := I) S (t : Real) (k + 2) y) +
            rmResidualField (I := I) S t k y)
          (fun i => frame i y) I0)
        D.carrier (t : Real) := by
  intro k
  induction k with
  | zero =>
      intro y hy I0
      have horth : ∀ i j : Idx,
          (S.base.metric (t : Real)).inner y
              ((hframe.toBasisAt hy) i) ((hframe.toBasisAt hy) j) =
            if i = j then (1 : Real) else 0 := by
        intro i j
        rw [hframe.toBasisAt_coe hy i, hframe.toBasisAt_coe hy j]
        exact horthU y hy i j
      simpa only [rmResidualField, hframe.toBasisAt_coe hy] using
        (e0Residual (I := I) S hS t (Idx := Idx)).2
          y (hframe.toBasisAt hy) horth I0
  | succ k ih =>
      have hnext := resStarNext_spec (I := I) S hS k t frame hframe hu horthU
        baseDt chrDt hrm hchr hchrId hswap
        (rmResidualField (I := I) S t k)
        (rmResidualField_cost (I := I) S hS t k)
        (fun y hy I0 => ih y hy I0)
      intro y hy I0
      simpa only [rmResidualField] using hnext.2 y hy I0

/-- A Ricci-flow solution produces one globally fixed costed residual field at
every order.  Pointwise orthonormal bases are chosen only after the field. -/
theorem rmResidual_cost
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (k : Nat) (t : RealTimeInterval.RegularTime D) :
    ∃ T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k),
      StarSum2Cost (I := I) (Fin (Module.finrank Real E)) S (t : Real) k T
          (rmResidualCost (Module.finrank Real E) k) ∧
      ∀ x : M,
        ∃ basis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x),
          (∀ i j : Fin (Module.finrank Real E),
            (S.base.metric (t : Real)).inner x (basis i) (basis j) =
              if i = j then (1 : Real) else 0) ∧
          ∀ I0 : Fin (4 + k) → Fin (Module.finrank Real E),
            HasDerivWithinAt
              (fun r : Real =>
                tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k x)
                  (fun i => basis i) I0)
              (tensor0SComponent (I := I)
                (metricTrace0S2TensorInBasis (I := I) basis
                    (identityInvMetric (Idx := Fin (Module.finrank Real E)))
                    (nablaKRm04Field (I := I) S (t : Real) (k + 2) x) + T x)
                (fun i => basis i) I0)
              D.carrier (t : Real) := by
  classical
  let T := rmResidualField (I := I) S t k
  refine ⟨T, by
    simpa only [Fintype.card_fin] using
      rmResidualField_cost (I := I) S hS t
        (Idx := Fin (Module.finrank Real E)) k, ?_⟩
  intro x
  let g := S.base.metric (t : Real)
  let frame := smoothOrthoFrame (I := I) g x
  let u := smoothOrthoOpen (I := I) (M := M) x
  have hu : IsOpen u := by
    simpa only [u] using smoothOrthoOpen_open (I := I) (M := M) x
  have hx : x ∈ u := by
    simpa only [u] using mem_smoothOrthoOpen (I := I) (M := M) x
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u := by
    simpa only [frame, u] using smoothOrtho_local (I := I) g x
  have horthU : ∀ y : M, y ∈ u → ∀ i j : Fin (Module.finrank Real E),
      (S.base.metric (t : Real)).inner y (frame i y) (frame j y) =
        if i = j then (1 : Real) else 0 := by
    intro y hy i j
    simpa only [g, frame, u] using
      smoothOrthoFrame_orthonormal (I := I) g x (interior_subset hy) i j
  obtain ⟨hframe1, baseDt, chrDt, hrm, hchr, hchrId, hswap⟩ :=
    towerDataAt (I := I) S hS t frame hframe hu horthU
  let basis := hframe1.toBasisAt hx
  have horth : ∀ i j : Fin (Module.finrank Real E),
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    simpa only [basis, IsLocalFrameOn.toBasisAt_coe] using horthU x hx i j
  refine ⟨basis, horth, ?_⟩
  intro I0
  simpa only [T, basis, IsLocalFrameOn.toBasisAt_coe] using
    rmResidual_local (I := I) S hS t frame hframe1 hu horthU
      baseDt chrDt hrm hchr hchrId hswap k x hx I0

/-- On a positive-time tail, a dimension-three Ricci-flow solution produces
the local-frame StarSum residual and its component bound without additional
time-regularity or derivative-swap assumptions. -/
theorem resStarSol [CompactSpace M]
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0) (hT0Omega : t0 < omega)
    (k : Nat)
    (t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen t0 omega hT0Omega))
    {u : Set M}
    (frame : Fin 3 -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (hdim : ∀ y : M, Module.finrank Real (TangentSpace I y) = 3)
    (horthU : ∀ y : M, y ∈ u -> ∀ i j : Fin 3,
      ((S.timeRestrict
        (RealTimeInterval.closedOpen t0 omega hT0Omega)).base.metric
          (t : Real)).inner y (frame i y) (frame j y) =
        if i = j then (1 : Real) else 0) :
    ∃ T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k),
      StarSum2 (I := I)
          (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega))
          (t : Real) k T ∧
      ∃ C : Real, C = resStarCost k ∧ 0 ≤ C ∧
        (∀ (y : M) (hy : y ∈ u) (I0 : Fin (4 + k) -> Fin 3),
          HasDerivWithinAt
            (fun r : Real =>
              tensor0SComponent (I := I)
                (nablaKRm04Field (I := I)
                  (S.timeRestrict
                    (RealTimeInterval.closedOpen t0 omega hT0Omega))
                  r k y)
                (fun i => frame i y) I0)
            (tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
                  (identityInvMetric (Idx := Fin 3))
                  (nablaKRm04Field (I := I)
                    (S.timeRestrict
                      (RealTimeInterval.closedOpen t0 omega hT0Omega))
                    (t : Real) (k + 2) y) + T y)
              (fun i => frame i y) I0)
            (RealTimeInterval.closedOpen t0 omega hT0Omega).carrier (t : Real)) ∧
        (∀ (y : M) (hy : y ∈ u) (m : Fin (4 + k) -> Fin 3),
          |T y (fun p => frame (m p) y)| ≤
            C * ∑ j ∈ Finset.range (k + 1),
              Real.sqrt (stNormSq (I := I)
                (S.timeRestrict
                  (RealTimeInterval.closedOpen t0 omega hT0Omega))
                (t : Real) j y (hframe.toBasisAt hy)) *
              Real.sqrt (stNormSq (I := I)
                (S.timeRestrict
                  (RealTimeInterval.closedOpen t0 omega hT0Omega))
                (t : Real) (k - j) y (hframe.toBasisAt hy))) := by
  classical
  let D' := RealTimeInterval.closedOpen t0 omega hT0Omega
  let S' := S.timeRestrict D'
  have hS' : IsSolutionOn (I := I) S' := by
    simpa [S', D'] using isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega
  obtain ⟨hframe1, baseDt, chrDt, hrm, hchr, hchrId, hswap⟩ :=
    tailTowerData (I := I) hS hAlphaT0 hT0Omega frame hframe hu
  have hbase := rm04Base_of_sol (I := I) S' hS' t hdim
  have hrm' : ∀ (y : M), y ∈ u -> ∀ m : Fin 4 -> Fin 3,
      HasDerivWithinAt (fun s : Real => lfBase (I := I) S' frame s y m)
        (baseDt (t : Real) y m) D'.carrier (t : Real) := by
    intro y hy m
    simpa only [lfBase, S', D'] using hrm t y hy m
  have hchr' : ∀ (y : M), y ∈ u -> ∀ i a p : Fin 3,
      HasDerivWithinAt
        (fun s : Real => lfChr (I := I) S' frame hframe1 s y i a p)
        (chrDt (t : Real) y i a p) D'.carrier (t : Real) := by
    intro y hy i a p
    simpa only [lfChr, S', D'] using hchr t y hy i a p
  have hchrId' : ∀ (y : M), y ∈ u -> ∀ i j p : Fin 3,
      chrDt (t : Real) y i j p =
        -ricciCovDerivCompInFrame (I := I) S' frame (t : Real) y i j p
        -ricciCovDerivCompInFrame (I := I) S' frame (t : Real) y j i p
        +ricciCovDerivCompInFrame (I := I) S' frame (t : Real) y p i j := by
    intro y hy i j p
    simpa only [S', D'] using hchrId t y hy (horthU y hy) i j p
  have hswap' : ∀ (y : M), y ∈ u -> ∀ (k' : Nat) (d : Fin 3)
      (m : Fin (4 + k') -> Fin 3),
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun z : M =>
              iteratedRmComp (I := I) frame (lfChr (I := I) S' frame hframe1)
                (lfBase (I := I) S' frame) k' s z m)
            y (frame d y))
        (extDerivFun (I := I)
          (fun z : M =>
            iteratedRmCompDt (I := I) frame (lfChr (I := I) S' frame hframe1)
              chrDt (lfBase (I := I) S' frame) baseDt k' (t : Real) z m)
          y (frame d y))
        D'.carrier (t : Real) := by
    intro y hy k' d m
    simpa only [lfChr, lfBase, S', D'] using
      hswap k' m (t : Real) t.2 y hy (frame d y)
  simpa only [S', D'] using
    resStarBoundLF (I := I) S' hS' k t frame hframe1 hu hdim horthU
      hbase baseDt chrDt hrm' hchr' hchrId' hswap'

end DifferentialGeometry.PDE.RicciFlow
