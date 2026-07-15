import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowSolutions

/-!
# Pullback transport of the `SolWindowData` analytic sub-records

For a diffeomorphism `Φ : M ≃ₘ N`, the analytic window bounds that feed `winGInfOfData`
(metric equivalence, lower metric control, …) transport from `N` to `M`.  Because `Φ` is an
isometry between `(M, Φ^*g)` and `(N, g)` — `(Φ^*g).inner x v v = g.inner (Φ x) (dΦ v) (dΦ v)`
(`Diffeomorph.pullbackMetric_inner`) — every *ratio* of metric values is preserved, so an
equivalence/lower-bound constant transports unchanged; the only bookkeeping is moving the spatial
set along `Φ`.

This file is the consuming-side companion to `SolutionPullback.lean` (which builds the solution
data `solutionOn_pullback` and the regularity package `isSolutionOn_pullback`).  Together they are
the per-field producers for a pulled-back `SolWindowData`.

## Contents
* `metricUniformEquivalentOn_pullback` — pointwise equivalence transports with the same constant.
* `metricUniformEquivalentOnWindow_pullback` — the time-window version.
* `solLowData_pullback` — global lower metric control transports (same constant, `Φ` a bijection).
-/

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- **Pointwise metric equivalence transports under pullback, with the same constant.**  If `gRef`
and `h` are `C`-equivalent on `K ⊆ N`, then `Φ^*gRef` and `Φ^*h` are `C`-equivalent on any `V ⊆ M`
with `Φ '' V ⊆ K`.  The constant is unchanged because both metrics are evaluated at the same
transported vector `dΦ v`, so their ratio is preserved. -/
theorem metricUniformEquivalentOn_pullback
    (K : Set N) (gRef h : SmoothRiemannianMetric I N) (C : ℝ)
    (hequiv : MetricUniformEquivalentOn (I := I) K gRef h C)
    (Φ : M ≃ₘ⟮I, I⟯ N) {V : Set M} (hV : ∀ x ∈ V, (Φ : M → N) x ∈ K) :
    MetricUniformEquivalentOn (I := I) V
      (Diffeomorph.pullbackMetric (I := I) gRef Φ)
      (Diffeomorph.pullbackMetric (I := I) h Φ) C := by
  obtain ⟨hC, hbound⟩ := hequiv
  refine ⟨hC, fun x hx v => ?_⟩
  rw [Diffeomorph.pullbackMetric_inner, Diffeomorph.pullbackMetric_inner]
  exact hbound (Φ x) (hV x hx) (mfderiv I I (Φ : M → N) x v)

/-- **Time-window metric equivalence transports under pullback.**  The window version of
`metricUniformEquivalentOn_pullback`, applied at each `(i, t)`. -/
theorem metricUniformEquivalentOnWindow_pullback
    (K : Set N) (β ψ : ℝ) (gRef : SmoothRiemannianMetric I N)
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N) (B : ℝ → ℝ)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B)
    (Φ : M ≃ₘ⟮I, I⟯ N) {V : Set M} (hV : ∀ x ∈ V, (Φ : M → N) x ∈ K) :
    MetricUniformEquivalentOnWindow (I := I) V β ψ
      (Diffeomorph.pullbackMetric (I := I) gRef Φ)
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ) B := by
  intro i t ht
  exact metricUniformEquivalentOn_pullback (I := I) K gRef (gSeq i t) (B t)
    (hequiv i t ht) Φ hV

/-- **Global lower metric control transports under pullback, with the same constant.**  `SolLowData`
carries no spatial set, and `Φ` is a bijection, so the lower bound `c · gRef ≤ gSeq` transports to
`c · Φ^*gRef ≤ Φ^*gSeq` with the same `c`. -/
theorem solLowData_pullback
    (β ψ : ℝ) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N)
    (gRef : SmoothRiemannianMetric I N)
    (hLow : SolLowData (I := I) β ψ gSeq gRef)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolLowData (I := I) β ψ
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) := by
  intro ρ hρ t ht
  obtain ⟨c, hc, hbound⟩ := hLow ρ hρ t ht
  refine ⟨c, hc, fun k x v => ?_⟩
  rw [Diffeomorph.pullbackMetric_inner, Diffeomorph.pullbackMetric_inner]
  exact hbound k (Φ x) (mfderiv I I (Φ : M → N) x v)

/-- **The metric covariant-derivative norm is pullback-invariant** (evaluated at the moved point).
`metricCovDerivNorm a (Φ^*h) (Φ^*gRef) x = metricCovDerivNorm a h gRef (Φ x)`, from the tower
naturality `metricCovDeriv_pullback` and the orthonormal-trace norm transport
`normSq0S_pullback_eval_of_orthonormal`.  This is the cov-derivative analog of
`ricCovTower_normSq0S_pullback` and feeds the `initC`/order-bound fields of `SolCovData`/`SolLipData`. -/
theorem metricCovDerivNorm_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    (a : ℕ) (h gRef : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M) :
    metricCovDerivNorm (I := I) a
        (Diffeomorph.pullbackMetric (I := I) h Φ)
        (Diffeomorph.pullbackMetric (I := I) gRef Φ) x
      = metricCovDerivNorm (I := I) a h gRef (Φ x) := by
  obtain ⟨B, hB⟩ := exists_gOrthonormalBasis (Diffeomorph.pullbackMetric (I := I) gRef Φ) x
  unfold metricCovDerivNorm
  rw [normSq0S_pullback_eval_of_orthonormal (I := I) gRef Φ x (a + 2) B hB
    (metricCovDeriv (I := I) (Diffeomorph.pullbackMetric (I := I) h Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) a x)
    (metricCovDeriv (I := I) h gRef a (Φ x))
    (metricCovDeriv_pullback (I := I) h gRef Φ a x)]

/-- **Exact-order covariant-derivative bound transports under pullback** (same constant).  Pointwise
form: from `metricCovDerivNorm_pullback`, an order-`a` bound on `K ⊆ N` becomes the same bound on any
`V ⊆ M` with `Φ '' V ⊆ K`. -/
theorem metricCovDerivOrderBoundOn_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    (K : Set N) (a : ℕ) (h gRef : SmoothRiemannianMetric I N) (C : ℝ)
    (hbound : MetricCovDerivOrderBoundOn (I := I) K a h gRef C)
    (Φ : M ≃ₘ⟮I, I⟯ N) {V : Set M} (hV : ∀ x ∈ V, (Φ : M → N) x ∈ K) :
    MetricCovDerivOrderBoundOn (I := I) V a
      (Diffeomorph.pullbackMetric (I := I) h Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) C := by
  intro x hx
  rw [metricCovDerivNorm_pullback (I := I) a h gRef Φ x]
  exact hbound (Φ x) (hV x hx)

/-- **Time-window exact-order covariant-derivative bound transports under pullback.**  The window
version of `metricCovDerivOrderBoundOn_pullback`. -/
theorem metricCovDerivOrderBoundOnWindow_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    (K : Set N) (β ψ : ℝ) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N)
    (gRef : SmoothRiemannianMetric I N) (a : ℕ) (C : ℝ)
    (hbound : MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a C)
    (Φ : M ≃ₘ⟮I, I⟯ N) {V : Set M} (hV : ∀ x ∈ V, (Φ : M → N) x ∈ K) :
    MetricCovDerivOrderBoundOnWindow (I := I) V β ψ
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) a C := by
  intro i t ht
  exact metricCovDerivOrderBoundOn_pullback (I := I) K a (gSeq i t) gRef C (hbound i t ht) Φ hV

/-- **Zero-order time-Lipschitz producer data transports under pullback.**  The metric-equivalence
field is `metricUniformEquivalentOnWindow_pullback`; the order-0 Shi bound transports by
`ricCovTower_normSq0S_pullback` (the pulled-back Ricci-covariant tower has the same `gSeq`-norm at
`Φ x`).  Spatial sets move along `Φ` by preimage; all constants are unchanged. -/
noncomputable def solLip0Data_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    (K : Set N) (β ψ : ℝ)
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N) (gRef : SmoothRiemannianMetric I N)
    (hData : SolLip0Data (I := I) K β ψ gSeq gRef)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolLip0Data (I := I) ((Φ : M → N) ⁻¹' K) β ψ
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) where
  U0 := (Φ : M → N) ⁻¹' hData.U0
  hKU0 := fun _x hx => hData.hKU0 hx
  B0 := hData.B0
  hequiv0 := metricUniformEquivalentOnWindow_pullback (I := I) hData.U0 β ψ gRef gSeq
    hData.B0 hData.hequiv0 Φ (fun _x hx => hx)
  Bmax0 := hData.Bmax0
  hBmax01 := hData.hBmax01
  hBmax0 := hData.hBmax0
  KShi0 := hData.KShi0
  hKShi00 := hData.hKShi00
  hShi0 := fun i t ht x hx => by
    have key :
        Tensor0SBundle.normSq0S (I := I)
            (Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ) x 2
            (ricCovTower (I := I) (Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
              (Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ) 0 x)
          = Tensor0SBundle.normSq0S (I := I) (gSeq i t) (Φ x) 2
              (ricCovTower (I := I) (gSeq i t) (gSeq i t) 0 (Φ x)) :=
      ricCovTower_normSq0S_pullback (I := I) (gSeq i t) Φ 0 x
    rw [key]
    exact hData.hShi0 i t ht (Φ x) hx

/-- **Spatial P2 producer data transports under pullback.**  Each compact `K' ⊆ M` is handled by
applying the source `pack` at the compact image `Φ '' K' ⊆ N` and pulling the witness open set back
to `Φ⁻¹' U`.  Metric equivalence, the Shi tower bound, and the initial covariant-derivative bound
transport by `metricUniformEquivalentOnWindow_pullback`, `ricCovTower_normSq0S_pullback`, and
`metricCovDerivNorm_pullback`; the scalar/time conditions are unchanged. -/
noncomputable def solCovData_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    (β ψ t0 : ℝ) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N)
    (gRef : SmoothRiemannianMetric I N) (D : ℕ → RealTimeInterval)
    (S : (i : ℕ) → SolutionOn (I := I) (M := N) (D i))
    (hData : SolCovData (I := I) β ψ t0 gSeq gRef D S) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolCovData (I := I) β ψ t0
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) D
      (fun i => solutionOn_pullback (I := I) (S i) Φ) where
  pack := by
    intro K' hK' n hn
    obtain ⟨U, hUopen, hK'U, B, Bmax, KShi, initC, timeRadius,
        hequiv, hBmax1, hBmax, hKShi0, hShi, ht0, hreg, hinitC0, hinitCbound, htime⟩ :=
      hData.pack ((Φ : M → N) '' K') (hK'.image Φ.continuous) n hn
    refine ⟨(Φ : M → N) ⁻¹' U, hUopen.preimage Φ.continuous, ?_, B, Bmax, KShi, initC,
      timeRadius, ?_, hBmax1, hBmax, hKShi0, ?_, ht0, hreg, hinitC0, ?_, htime⟩
    · exact fun x hx => hK'U ⟨x, hx, rfl⟩
    · exact metricUniformEquivalentOnWindow_pullback (I := I) U β ψ gRef gSeq B hequiv Φ
        (fun _x hx => hx)
    · intro s hs i t ht x hx
      rw [ricCovTower_normSq0S_pullback (I := I) (gSeq i t) Φ s x]
      exact hShi s hs i t ht (Φ x) hx
    · intro r hr1 hrn i x hx
      rw [metricCovDerivNorm_pullback (I := I) r (gSeq i t0) gRef Φ x]
      exact hinitCbound r hr1 hrn i (Φ x) hx

/-- **Positive-order time-Lipschitz producer data transports under pullback.**  The fixed compact
set `K` moves to its preimage `Φ⁻¹' K`, and each witness open set to `Φ⁻¹' U`.  Metric equivalence,
the lower-order covariant-derivative bounds, the Shi tower bound, and the top-order bound transport
by the corresponding `*_pullback` keystones; all constants are unchanged. -/
noncomputable def solLipData_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    (K : Set N) (β ψ : ℝ) (p : ℕ) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N)
    (gRef : SmoothRiemannianMetric I N) (D : ℕ → RealTimeInterval)
    (S : (i : ℕ) → SolutionOn (I := I) (M := N) (D i))
    (hData : SolLipData (I := I) K β ψ p gSeq gRef D S) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolLipData (I := I) ((Φ : M → N) ⁻¹' K) β ψ p
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) D
      (fun i => solutionOn_pullback (I := I) (S i) Φ) where
  pack := by
    intro a ha1 hap
    obtain ⟨U, hUopen, hKU, B, Bmax, Cg, KShi, CN,
        hequiv, hBmax1, hBmax, hCg, hKShi0, hShi, hCN0, hCN⟩ := hData.pack a ha1 hap
    refine ⟨(Φ : M → N) ⁻¹' U, hUopen.preimage Φ.continuous, fun x hx => hKU hx,
      B, Bmax, Cg, KShi, CN, ?_, hBmax1, hBmax, ?_, hKShi0, ?_, hCN0, ?_⟩
    · exact metricUniformEquivalentOnWindow_pullback (I := I) U β ψ gRef gSeq B hequiv Φ
        (fun _x hx => hx)
    · intro r hr1 hra
      exact metricCovDerivOrderBoundOnWindow_pullback (I := I) U β ψ gSeq gRef r (Cg r)
        (hCg r hr1 hra) Φ (fun _x hx => hx)
    · intro s hs i t ht x hx
      rw [ricCovTower_normSq0S_pullback (I := I) (gSeq i t) Φ s x]
      exact hShi s hs i t ht (Φ x) hx
    · exact metricCovDerivOrderBoundOnWindow_pullback (I := I) K β ψ gSeq gRef a CN hCN Φ
        (fun _x hx => hx)

/-- `solnMetricField` of the pulled-back solution evaluates as the pullback of the source
metric field (`metricTensorField` + `pullbackMetric_inner`). -/
theorem solnMetricField_pullback
    [SigmaCompactSpace N] [T2Space N]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (r : ℝ) (y : M) (slots : Fin 2 → TangentSpace I y) :
    solnMetricField (I := I) (solutionOn_pullback (I := I) S Φ) r y slots
      = solnMetricField (I := I) S r (Φ y)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) y (slots q)) := by
  simp only [solnMetricField]
  rw [Tensor0SBundle.metricTensorField_apply, Tensor0SBundle.metricTensorField_apply]
  exact Diffeomorph.pullbackMetric_inner (I := I) (S.family.metric r) Φ y (slots 0) (slots 1)

/-- `solnRicField` of the pulled-back solution evaluates as the pullback of the source Ricci field
(`ricciSection_pullback`). -/
theorem solnRicField_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (t : ℝ) (y : M) (slots : Fin 2 → TangentSpace I y) :
    solnRicField (I := I) (solutionOn_pullback (I := I) S Φ) t y slots
      = solnRicField (I := I) S t (Φ y)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) y (slots q)) :=
  ricciSection_pullback (I := I) (S.family.metric t) Φ y slots

/-- `solnEvolField` of the pulled-back solution evaluates as the pullback of the source evolution
field (`-2 • solnRicField`, scaled through `solnRicField_pullback`). -/
theorem solnEvolField_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (t : ℝ) (y : M) (slots : Fin 2 → TangentSpace I y) :
    solnEvolField (I := I) (solutionOn_pullback (I := I) S Φ) t y slots
      = solnEvolField (I := I) S t (Φ y)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) y (slots q)) := by
  simp only [solnEvolField, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousMultilinearMap.smul_apply, solnRicField_pullback (I := I) S Φ t y slots]

/-- **The time-derivative-swap producer data transports under pullback.**  `SolSwapData` is the one
record that is not a spatial bound: it asserts a time/covariant-derivative commutation
(`FixedBaseExtDerivTimeDerivativeOnRegular`).  Transport pushes the section family `V` forward to
`N` (`pushFwdSection`), instantiates the source datum at `(pushFwd V, Φ x0)`, and converts each
`extDerivFun (F_pb s) x V_dir` to `extDerivFun (F_source s) (Φ x) (dΦ V_dir)` via
`covDerivOfField_pullback` (general base, with `hA0` from `solnMetricField_pullback` /
`solnEvolField_pullback`), `pushFwdSection_apply_at_image`, and the directional-derivative chain rule
`extDerivFun_comp_diffeomorph`.  Because `Φ` is time-independent, the source `HasDerivWithinAt` in
`s` carries over verbatim. -/
theorem solSwapData_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    {D : ℕ → RealTimeInterval} (gRef : SmoothRiemannianMetric I N)
    (S : (i : ℕ) → SolutionOn (I := I) (M := N) (D i))
    (hData : SolSwapData (I := I) gRef D S) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolSwapData (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Φ) D
      (fun i => solutionOn_pullback (I := I) (S i) Φ) := by
  intro i n p' hp' V x0 t ht x hx Vdir
  -- generic field-pullback step: covDerivOfField of a pulled-back base, evaluated at `V`,
  -- is the source field at `Φ y` evaluated at the pushed-forward family.
  have hfield : ∀ (A0M : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
      (A0N : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2),
      (∀ (y : M) (sl : Fin 2 → TangentSpace I y),
          A0M y sl = A0N (Φ y) (fun q => mfderiv I I (Φ : M → N) y (sl q))) →
      (fun y : M => covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Φ)
            A0M p' y (fun a => V a y))
        = fun y : M => (fun z : N => covDerivOfField (I := I) gRef A0N p' z
            (fun a => (pushFwdSection (I := I) Φ (V a)) z)) (Φ y) := by
    intro A0M A0N hA0
    funext y
    rw [covDerivOfField_pullback (I := I) gRef Φ A0M A0N hA0 p' y (fun a => V a y)]
    congr 1
    funext a
    rw [pushFwdSection_apply_at_image]
  -- smoothness of each source field for the chain rule's differentiability hypothesis
  have hMDiff : ∀ (A0N : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z : N => covDerivOfField (I := I) gRef A0N p' z
          (fun a => (pushFwdSection (I := I) Φ (V a)) z)) (Φ x) := by
    intro A0N
    exact (covDerivOfField_eval_contMDiff (I := I) gRef A0N p'
      (fun a => pushFwdSection (I := I) Φ (V a))).contMDiffAt.mdifferentiableAt (by simp)
  -- the directional-derivative transport for both the metric and evolution fields
  have hconv : ∀ (A0M : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
      (A0N : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2),
      (∀ (y : M) (sl : Fin 2 → TangentSpace I y),
          A0M y sl = A0N (Φ y) (fun q => mfderiv I I (Φ : M → N) y (sl q))) →
      extDerivFun (I := I)
          (fun y : M => covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Φ)
            A0M p' y (fun a => V a y)) x Vdir
        = extDerivFun (I := I)
            (fun z : N => covDerivOfField (I := I) gRef A0N p' z
              (fun a => (pushFwdSection (I := I) Φ (V a)) z)) (Φ x)
            (mfderiv I I (Φ : M → N) x Vdir) := by
    intro A0M A0N hA0
    rw [hfield A0M A0N hA0]
    exact extDerivFun_comp_diffeomorph
      (fun z : N => covDerivOfField (I := I) gRef A0N p' z
        (fun a => (pushFwdSection (I := I) Φ (V a)) z)) Φ x Vdir (hMDiff A0N)
  -- assemble: rewrite the time-function and the derivative value, then use the source datum
  have hfun : (fun s : ℝ => extDerivFun (I := I)
        (fun y : M => covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Φ)
          (solnMetricField (I := I) (solutionOn_pullback (I := I) (S i) Φ) s) p' y
          (fun a => V a y)) x Vdir)
      = fun s : ℝ => extDerivFun (I := I)
          (fun z : N => covDerivOfField (I := I) gRef (solnMetricField (I := I) (S i) s) p' z
            (fun a => (pushFwdSection (I := I) Φ (V a)) z)) (Φ x)
          (mfderiv I I (Φ : M → N) x Vdir) := by
    funext s
    exact hconv _ _ (fun y sl => solnMetricField_pullback (I := I) (S i) Φ s y sl)
  rw [hfun, hconv _ _ (fun y sl => solnEvolField_pullback (I := I) (S i) Φ t y sl)]
  exact hData i n p' hp' (fun a => pushFwdSection (I := I) Φ (V a)) (Φ x0) t ht (Φ x)
    (by rw [Set.mem_singleton_iff] at hx ⊢; rw [hx]) (mfderiv I I (Φ : M → N) x Vdir)

/-- **The full `SolWindowData` transports under pullback** (the capstone of the consuming phase).
For a diffeomorphism `Φ : M ≃ₘ N`, a window-solution package on `N` recenters to one on `M`:
the compact set pulls back to `Φ⁻¹' K` (compact as `Φ.symm '' K`), the metric/solution data become
their pullbacks, `IsSolutionOn` is `isSolutionOn_pullback`, and the five analytic sub-records are the
`sol*Data_pullback` producers.  This is directly consumable by `winGInfOfData`. -/
noncomputable def solWindowData_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    (W : SolWindowData (I := I) (M := N)) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolWindowData (I := I) (M := M) := by
  cases W with
  | mk K hK beta psiT t0 hbeta p gSeq gRef D S hS hmet hreg H0 hswap Hcov Hlip hlow =>
    refine SolWindowData.mk ((Φ : M → N) ⁻¹' K) ?_ beta psiT t0 hbeta p
      (fun i r => Diffeomorph.pullbackMetric (I := I) (gSeq i r) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) D
      (fun i => solutionOn_pullback (I := I) (S i) Φ)
      (fun i => isSolutionOn_pullback (I := I) (S i) (hS i) Φ)
      (fun i r => congrArg (fun g => Diffeomorph.pullbackMetric (I := I) g Φ) (hmet i r))
      hreg
      (solLip0Data_pullback (I := I) K beta psiT gSeq gRef H0 Φ)
      (solSwapData_pullback (I := I) gRef S hswap Φ)
      (solCovData_pullback (I := I) beta psiT t0 gSeq gRef D S Hcov Φ)
      (solLipData_pullback (I := I) K beta psiT p gSeq gRef D S Hlip Φ)
      (solLowData_pullback (I := I) beta psiT gSeq gRef hlow Φ)
    -- compactness of the pulled-back set: `Φ⁻¹' K = Φ.symm '' K`, a continuous image of a compact.
    have hset : (Φ : M → N) ⁻¹' K = (Φ.symm : N → M) '' K := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hz
        exact ⟨Φ z, hz, Φ.symm_apply_apply z⟩
      · rintro ⟨k, hk, rfl⟩
        rwa [Φ.apply_symm_apply]
    rw [hset]
    exact hK.image Φ.symm.continuous

/-- **The window pre-convergence conclusion for a `Φ`-recentered flow.**  Composes the capstone
`solWindowData_pullback` with the abstract endpoint `winGInfOfData`: a window-solution package on `N`
yields, after recentering by `Φ : M ≃ₘ N`, the g_∞ pre-convergence conclusion on `M`.  This is the
pullback-layer entry point into the MSM135 Ch4 Thm 3.10 ⇐ 3.9 conv field. -/
noncomputable def winGInfOfPullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [SigmaCompactSpace N] [T2Space N]
    (hne : Nonempty M) (W : SolWindowData (I := I) (M := N)) (Φ : M ≃ₘ⟮I, I⟯ N) :
    WindowMetricPreconvConclusion (E := E) (H := H) (I := I) (M := M) :=
  winGInfOfData (I := I) hne (solWindowData_pullback (I := I) W Φ)

end HCGCompactness
end DifferentialGeometry
