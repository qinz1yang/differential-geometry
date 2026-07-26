import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TimeRecursion

/-!
# P4 bridge: the local-frame residual heat bound

The closed P3 endpoint `resStarLFU` realizes the residual `(∂ₜ − Δ)∇ᵏRm` as a `StarSum2` element
`T` (with a uniform per-component time-derivative identity over a neighborhood `u`).  `StarSum2.bound`
turns any `StarSum2` element into a Cauchy–Schwarz bound by the tower norms `stNormSq`.

`resStarBoundLF` is the smallest honest composition of the two: it exposes both the witness `T` (with
its derivative identity) AND a single nonnegative constant `C` controlling the frame components of `T`
by `Σⱼ √wⱼ·√w_{k−j}`.  This is the first step of P4 toward `TowerHeatBoundOn`; the global
scalar/Bernstein consumer (frame-existence + reaction assembly) is left for a later pass.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
open DifferentialGeometry.Dim3Reaction in
/-- **P4 residual bound (local-frame).**  Composing the P3 endpoint `resStarLFU` with
`StarSum2.bound`: the heat residual `(∂ₜ − Δ)∇ᵏRm` is realized by a `StarSum2` witness `T` whose
frame components are controlled, uniformly on `u`, by the tower norms

`|T y (frame · y)| ≤ C · Σⱼ √(stNormSq j) · √(stNormSq (k−j))`,

with the same per-component time-derivative identity that `resStarLFU` supplies.  Takes exactly the
`resStarLFU` hypotheses (no new residual assumption). -/
theorem resStarBoundLF
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (k : ℕ) (t : RealTimeInterval.RegularTime D)
    {u : Set M}
    (frame : Fin 3 → (y : M) → TangentSpace I y)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (hdim : ∀ y : M, Module.finrank Real (TangentSpace I y) = 3)
    (horthU : ∀ y : M, y ∈ u → ∀ i j : Fin 3,
      (S.base.metric (t : Real)).inner y (frame i y) (frame j y) = if i = j then (1 : Real) else 0)
    (hbase : ∀ (y : M) (bas : Module.Basis (Fin 3) Real (TangentSpace I y))
        (_horth : ∀ i j : Fin 3,
          (S.base.metric (t : Real)).inner y (bas i) (bas j) = if i = j then (1 : Real) else 0)
        (I0 : Fin 4 → Fin 3),
        HasDerivWithinAt
          (fun r : Real => S.base.rm04 r y (fun p => bas (I0 p)))
          (tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) bas (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : Real) 2 y)) (fun i => bas i) I0
            + (-2 * (Bt (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 1) (I0 2) (I0 3)
                    - Bt (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 1) (I0 3) (I0 2)
                    + Bt (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 2) (I0 1) (I0 3)
                    - Bt (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 3) (I0 1) (I0 2))
                - drift (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 1) (I0 2) (I0 3)))
          D.carrier (t : Real))
    (baseDt : Real → M → (Fin 4 → Fin 3) → Real)
    (chrDt : Real → M → Fin 3 → Fin 3 → Fin 3 → Real)
    (hrm : ∀ (y : M), y ∈ u → ∀ m : Fin 4 → Fin 3,
      HasDerivWithinAt (fun s : Real => lfBase (I := I) S frame s y m)
        (baseDt (t : Real) y m) D.carrier (t : Real))
    (hchr : ∀ (y : M), y ∈ u → ∀ i a p : Fin 3,
      HasDerivWithinAt (fun s : Real => lfChr (I := I) S frame hframe s y i a p)
        (chrDt (t : Real) y i a p) D.carrier (t : Real))
    (hchrId : ∀ (y : M), y ∈ u → ∀ i j p : Fin 3,
      chrDt (t : Real) y i j p =
        - ricciCovDerivCompInFrame (I := I) S frame (t : Real) y i j p
        - ricciCovDerivCompInFrame (I := I) S frame (t : Real) y j i p
        + ricciCovDerivCompInFrame (I := I) S frame (t : Real) y p i j)
    (hswap : ∀ (y : M), y ∈ u → ∀ (k' : ℕ) (d : Fin 3) (m : Fin (4 + k') → Fin 3),
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun z : M =>
              iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe) (lfBase (I := I) S frame)
                k' s z m) y (frame d y))
        (extDerivFun (I := I)
          (fun z : M =>
            iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
              (lfBase (I := I) S frame) baseDt k' (t : Real) z m) y (frame d y))
        D.carrier (t : Real)) :
    ∃ T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k),
      StarSum2 (I := I) S (t : Real) k T ∧
      ∃ C : Real, C = resStarCost k ∧ 0 ≤ C ∧
        (∀ (y : M) (hy : y ∈ u) (I0 : Fin (4 + k) → Fin 3),
          HasDerivWithinAt
            (fun r : Real =>
              tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k y) (fun i => frame i y) I0)
            (tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
                  (identityInvMetric (Idx := Fin 3))
                  (nablaKRm04Field (I := I) S (t : Real) (k + 2) y) + T y)
              (fun i => frame i y) I0)
            D.carrier (t : Real)) ∧
        (∀ (y : M) (hy : y ∈ u) (m : Fin (4 + k) → Fin 3),
          |T y (fun p => frame (m p) y)| ≤
            C * ∑ j ∈ Finset.range (k + 1),
              Real.sqrt (stNormSq (I := I) S (t : Real) j y (hframe.toBasisAt hy)) *
                Real.sqrt (stNormSq (I := I) S (t : Real) (k - j) y (hframe.toBasisAt hy))) := by
  -- P3 endpoint: the residual is a `StarSum2` witness with the uniform derivative identity.
  obtain ⟨T, hTcost, hcomp⟩ :=
    resStarLFU (I := I) S hS k t frame hframe hu hdim horthU hbase baseDt chrDt hrm hchr hchrId hswap
  have hT := hTcost.mem
  have hC0 := hTcost.nonneg
  have hCbound := hTcost.bound
  refine ⟨T, hT, resStarCost k, rfl, hC0, hcomp, ?_⟩
  intro y hy m
  -- Orthonormality for the `family` metric at the pointwise basis (`family = base`, `rfl`).
  have horthFam : ∀ i j : Fin 3,
      (S.family.metric (t : Real)).inner y ((hframe.toBasisAt hy) i) ((hframe.toBasisAt hy) j)
        = if i = j then (1 : Real) else 0 := by
    intro i j
    rw [hframe.toBasisAt_coe hy i, hframe.toBasisAt_coe hy j]
    exact horthU y hy i j
  -- Specialize the bound; reduce the basis tuple to the frame tuple.
  have hb := hCbound y (hframe.toBasisAt hy) horthFam m
  have htuple : (fun p => (hframe.toBasisAt hy) (m p)) = (fun p => frame (m p) y) := by
    funext p; exact hframe.toBasisAt_coe hy (m p)
  rwa [htuple] at hb

end DifferentialGeometry.PDE.RicciFlow
