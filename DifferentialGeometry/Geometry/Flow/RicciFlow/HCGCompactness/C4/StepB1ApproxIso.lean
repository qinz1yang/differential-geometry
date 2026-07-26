import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringOrdered
import DifferentialGeometry.Geometry.Comparison.ExpBallDiffeo

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step B1 (`lbl397`) — the comparison maps `F_{kℓ;r}` are approximate isometries

This file exposes the honest B1 assembly boundary.  `StepB1RawInput` records the raw C-track
comparison-map producers (local diffeomorphism, injectivity, basepoint, and forward/reverse
metric bounds); `stepB1_of_raw` converts those producers into the book's partial approximate
isometry with no additional mathematical assumption.

MSM135 chapter4.tex L1622–1881 (`lbl400`/`lbl402`/`lbl403`).  For each `r > 0`, `ε > 0`, `p ∈ ℕ`,
the center-of-mass comparison map
`F_{kℓ;r}(x) := cm{ F_{kℓ}⁰(x), …, F_{kℓ}^{A(r)}(x) }` (weights `φ_k^α(x)`, `lbl400`) between the
`k`-th and `ℓ`-th manifolds of the pointed sequence is, for `k, ℓ` large enough (`≥ k₀(r,ε,p)`):
- a **diffeomorphism** onto its image on `B(O_k, r)` (`lbl403`), and
- an **`(ε, p)`-approximate isometry** there (`lbl402`: the local versions `G_{kℓ;r}^β` satisfy
  `|∇^p(G_{kℓ;r}^β − id_β)| ≤ ε`), i.e. the pullback metric is `C^p`-close to the target metric —
  `BookApproxIsoPartialData` (MSM135 Def 4.1 on the ball, partial-diffeomorphism carrier).

## Producers each obligation consumes (for the assembly session)
- **The map `F_{kℓ;r}` and its `C¹` (`lbl430`) regularity** — `StepCSmoothness.centerOfMass_hasStrictFDerivAt`
  (C2, this project): `F_{kℓ;r}` is the center of mass with weights `φ_k^α`, strictly differentiable
  in its argument; the full `|∇^p F| ≤ C̃_{p+1}` bound is `lbl430` at order `p`.
- **`F_{kℓ}^α → id` on compacts in `C^∞`** — `StepCProducers.stepCJoin` (C3, this project, green):
  the averaged concrete `normalTransition` maps converge to `id` on `hatSourceBall`, along a
  subsequence `L.φ`.  This is the `lbl399 ⇒ lbl436` convergence feeding `lbl402`.
- **The `C^p` composition/accumulation estimates** — `ApproxIsometryCompHigher.comp_cov_le` /
  `comp_cov_accum` (F5/F6): turn the per-summand covariant-derivative smallness into the
  `metricCovDerivNorm ≤ ε` bound of `BookApproxIsometryData`.
- **The `lbl394` metric limits** — `Step B` (`StepBTransition`/`GoodCovering*`): the pulled-back
  metrics `g_ℓ^β` and their `C^∞` limits, on which the `G_{kℓ;r}^β → id` convergence is measured.

## Status of the honest inputs still above C3/C2
The `centerOfMass_hasStrictFDerivAt` consumption still carries C2's two open inputs (`CmHessianInput`
and the cm-continuity producer `hc_cont`); `stepCJoin` is green.  These obligations belong in a
producer of `StepB1RawInput`, rather than being hidden behind a theorem whose only hypotheses are
properness of the sequence members.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

section Glue

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] [MetricSpace M] [Nonempty M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]

/-- **Transport of `PreApproxIsoDataOn` along a locally-equal map.**  If a map `F` carries
`(ε, p)` pre-approximate-isometry data on `K`, then so does any `F'` that is *eventually equal* to
`F` at every point of `K` (same tensor field; the `C⁰`/`C^p` error bounds are unchanged, the smooth
map and its `mfderiv` agree pointwise on `K`).  This is the data-level `congr` the B1 assembly and
the Step-D composition both need to move data between the raw center-average map and the partial
diffeomorphism realizing it. -/
noncomputable def PreApproxIsoDataOn.congr {K : Set M} {ε : Real} {p : Nat} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hdata : PreApproxIsoDataOn (I := I) K ε p F g h)
    (hev : ∀ x ∈ K, F' =ᶠ[nhds x] F) :
    PreApproxIsoDataOn (I := I) K ε p F' g h where
  eps_pos := hdata.eps_pos
  eps_lt_one := hdata.eps_lt_one
  smoothOn := hdata.smoothOn.congr (fun x hx => (hev x hx).self_of_nhds)
  pullback := hdata.pullback
  pullback_apply := by
    intro x hx v
    rw [(hev x hx).self_of_nhds, (hev x hx).mfderiv_eq]
    exact hdata.pullback_apply x hx v
  c0_small := hdata.c0_small
  cov_deriv_small := hdata.cov_deriv_small

/-- **B1 glue (`lbl397`) — from a raw ball-onto-image center-average map to the partial-diffeomorphism
carrier.**  Given the map `F` on the ball `B(Ok, R)` that is (`lbl403`) a local diffeomorphism and
injective there, fixes the basepoint, and (`lbl402`) carries forward/reverse pre-approximate-isometry
data on the closed `r`-ball (`r < R`) and its image, produce the `BookApproxIsoPartialData` witness:
`exists_diffeo_of_injOn` realizes `F` as a partial diffeomorphism `Φ` with source `B(Ok, R)`, the
closed `r`-ball sits in the source, `Φ Ok = Oℓ`, and the forward/reverse data transport to `Φ`/`Φ⁻¹`
via `PreApproxIsoDataOn.congr`.  The hypotheses are exactly the C-track producer outputs; this lemma
is the (statement-fixed, book-faithful) assembly. -/
theorem stepB1_glue
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (Ok : M) (Oℓ : N) (r : Real) (ε : Real) (p : Nat)
    (U : Set M) (hU : IsOpen U) (hOkU : Ok ∈ U)
    (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M → N)
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U)
    (hbase : F Ok = Oℓ)
    (hfwd : PreApproxIsoDataOn (I := I) (Metric.closedBall Ok r) ε p F g h)
    (hrev : PreApproxIsoDataOn (I := I) (F '' Metric.closedBall Ok r) ε p
      (Function.invFunOn F U) h g) :
    ∃ Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (BookApproxIsoPartialData (I := I) (Metric.closedBall Ok r) ε p Phi g h) := by
  obtain ⟨Φ, hsrc, htgt, hEq⟩ := exists_diffeo_of_injOn hloc hU hinj
  have hclosed_sub : Metric.closedBall Ok r ⊆ Φ.source := by rw [hsrc]; exact hKU
  -- forward transport: `Φ =ᶠ F` at each point of the closed ball (both agree on the open set `U`).
  have hev_fwd : ∀ x ∈ Metric.closedBall Ok r, (Φ : M → N) =ᶠ[nhds x] F := fun x hx =>
    Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hx)) hEq
  have fwdΦ : PreApproxIsoDataOn (I := I) (Metric.closedBall Ok r) ε p (Φ : M → N) g h :=
    hfwd.congr hev_fwd
  -- reverse: `Φ.symm` and `invFunOn F U` agree on the target.
  have hsymmEq : Set.EqOn (Φ.symm : N → M) (Function.invFunOn F U) Φ.target := by
    intro z hz
    rw [htgt] at hz
    obtain ⟨x, hxU, rfl⟩ := hz
    have hΦx : (Φ : M → N) x = F x := hEq hxU
    have h1 : (Φ.symm : N → M) (F x) = x := by
      rw [← hΦx]; exact Φ.toPartialEquiv.left_inv (by rw [hsrc]; exact hxU)
    have h2 : Function.invFunOn F U (F x) = x := hinj.leftInvOn_invFunOn hxU
    rw [h1, h2]
  have hsetEq : (Φ : M → N) '' Metric.closedBall Ok r = F '' Metric.closedBall Ok r :=
    Set.EqOn.image_eq (fun x hx => hEq (hKU hx))
  have revΦ : PreApproxIsoDataOn (I := I) ((Φ : M → N) '' Metric.closedBall Ok r) ε p
      (Φ.symm : N → M) h g := by
    rw [hsetEq]
    refine hrev.congr (fun y hy => ?_)
    have hy_tgt : y ∈ Φ.target := by rw [htgt]; exact Set.image_mono hKU hy
    exact Filter.eventuallyEq_of_mem (Φ.open_target.mem_nhds hy_tgt) hsymmEq
  exact ⟨Φ, hclosed_sub, (hEq hOkU).trans hbase,
    ⟨{ source_sub := hclosed_sub, forward := fwdΦ, reverse := revΦ }⟩⟩

end Glue

/-- **Honest C-track input boundary for MSM135 `lbl397`.**  For every requested radius,
tolerance, and derivative order, the C-track supplies a threshold and raw comparison maps with
the local-diffeomorphism, injectivity, basepoint, and two-sided metric estimates needed by
`stepB1_glue`.  This deliberately stores producer data rather than the final
`BookApproxIsoPartialData` conclusion. -/
structure StepB1RawInput (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) : Prop where
  comparison : ∀ (r : Real), 0 < r → ∀ (ε : Real), 0 < ε → ε < 1 → ∀ (p : Nat),
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      letI : Nonempty (X.obj k).M := ⟨(X.obj k).basepoint⟩
      ∃ (R : Real) (_ : r < R) (F : (X.obj k).M → (X.obj ℓ).M),
        IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F (Metric.ball (X.obj k).basepoint R) ∧
        Set.InjOn F (Metric.ball (X.obj k).basepoint R) ∧
        F (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (PreApproxIsoDataOn (I := I) (Metric.closedBall (X.obj k).basepoint r) ε p F
          (X.obj k).metric (X.obj ℓ).metric) ∧
        Nonempty (PreApproxIsoDataOn (I := I) (F '' Metric.closedBall (X.obj k).basepoint r) ε p
          (Function.invFunOn F (Metric.ball (X.obj k).basepoint R))
          (X.obj ℓ).metric (X.obj k).metric)

/-- **MSM135 `lbl397` (B1) — the comparison maps `F_{kℓ;r}` are approximate isometries.**
This is the proved assembly from the honest raw C-track input `StepB1RawInput`.  It is a
conditional consumer, not the final producer theorem of the book.

For every radius `r > 0`, tolerance `ε ∈ (0,1)`, and order `p`, there is a subsequence-threshold
`k₀` such that for all `k, ℓ ≥ k₀` there is a **partial** diffeomorphism
`Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M ∞` whose source contains the closed `r`-ball
about the `k`-th basepoint `O_k`, mapping it diffeomorphically onto its image in `M_ℓ` as an
`(ε, p)`-approximate isometry (`BookApproxIsoPartialData`) — the center-of-mass comparison map
`F_{kℓ;r}` (`lbl400`) of the C3 join `stepCJoin`, whose regularity is the C2 endpoint
`centerOfMass_hasStrictFDerivAt`.  `Phi O_k = O_ℓ` (the weights fix the basepoint).

Statement correction (2026-07-05): the book's `F_{kℓ;r} : B(O_k,r) → F_{kℓ;r}(B(O_k,r)) ⊆ M_ℓ`
(chapter4.tex L1515) is a ball-onto-image diffeomorphism.  An earlier skeleton demanded a global
`(X.obj k).M ≃ₘ (X.obj ℓ).M`, which is unprovable — bounded-geometry sequence members need not be
diffeomorphic (e.g. a sequence alternating a round sphere and Euclidean space satisfies every
Theorem 3.9 hypothesis). -/
theorem stepB1_of_raw (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P)
    (r : Real) (hr : 0 < r) (ε : Real) (hε : 0 < ε) (hε1 : ε < 1) (p : Nat) :
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      ∃ Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M (∞ : WithTop ℕ∞),
        Metric.closedBall (X.obj k).basepoint r ⊆ Phi.source ∧
        Phi (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (BookApproxIsoPartialData (I := I)
          (Metric.closedBall (X.obj k).basepoint r)
          ε p Phi (X.obj k).metric (X.obj ℓ).metric) := by
  obtain ⟨k₀, hk₀⟩ := B.comparison r hr ε hε hε1 p
  refine ⟨k₀, fun k ℓ hk hl => ?_⟩
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
  letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
  letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
  letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
  letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
  letI : MetricSpace (X.obj k).M := (P k).ms
  letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
  haveI : Nonempty (X.obj k).M := ⟨(X.obj k).basepoint⟩
  obtain ⟨R, hRr, F, hloc, hinj, hbase, ⟨hfwd⟩, ⟨hrev⟩⟩ := hk₀ k ℓ hk hl
  have hR0 : (0 : Real) < R := lt_trans hr hRr
  have hU : IsOpen (Metric.ball (X.obj k).basepoint R) := by
    have hb := Metric.isOpen_ball (x := (X.obj k).basepoint) (ε := R)
    rwa [ProperMetricOn.top_eq (X.obj k) (P k)] at hb
  exact stepB1_glue (X.obj k).metric (X.obj ℓ).metric (X.obj k).basepoint (X.obj ℓ).basepoint
    r ε p (Metric.ball (X.obj k).basepoint R) hU (Metric.mem_ball_self hR0)
    (Metric.closedBall_subset_ball hRr) F hloc hinj hbase hfwd hrev

end HCGCompactness
end DifferentialGeometry
