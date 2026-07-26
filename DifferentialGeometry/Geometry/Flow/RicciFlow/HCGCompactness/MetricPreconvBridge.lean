import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvDiag
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.WindowPreconv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# P3 Brick C-II (SCAFFOLD MODE) — norm bridge + the P3 endpoints

Per `P3_PLAN.md` PLANNER RULING 2, the limit metric `gInf` is NOT constructed in
P3 (the inverse-componentize gate is the foundational brick C-G); C-II's endpoints
are PARAMETERIZED by `gInf : SmoothRiemannianMetric I M` together with
chart/frame-component convergence hypotheses.  When C-G + C1b land, C1b discharges
those hypotheses.

Three deliverables:

* `metricDerivNorm_le_compSq` (C2 norm bridge, local) — at a good-frame patch
  (`exists_goodFrame_compBound`, `RicBoundGoodFrame.lean`), the intrinsic
  `metricDerivNorm` of the covariant difference tower is bounded by a constant
  times the `ℓ²` of the **difference of the per-metric frame components**
  (`component0S` is additive over the fibre subtraction defining
  `metricDiffCovDerivAt`).  This is the genuine "sup-component differences →
  `metricDerivNorm` differences" content; C1b applies it on a finite good-frame
  cover of a compact to produce `metricCInfConvOnCompacts_of_normConv`'s input.

* `metricCInfConvOnCompacts_of_normConv` (the spatial P3 endpoint, scaffolded) —
  uniform-on-compacts pointwise `metricDerivNorm` convergence of `gSeq` to a GIVEN
  `gInf` ⇒ `MetricCInfConvOnCompacts`.  The `sSup` lift, via
  `metricDerivNormSupOn_le_of_forall` (WindowPreconv).

* `exists_subseq_hconv` (the dense-time diagonal wiring) — per-time *refinable*
  spatial preconvergence (the `exists_diag_subseq` `hstep` shape, one time per
  index) ⇒ ONE subsequence `φ` along which the spatial convergence holds at every
  dense time.  This is exactly `windowPreconv`'s `hconv` for `S = Set.range e`.
  Via `exists_diag_subseq` (C0, `MetricPreconvDiag.lean`); the `hsub`/`hextend`
  stabilities of the convergence property are discharged inline.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle TensorLieDeriv
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- **C2 — the local norm bridge.**  At a good-frame patch around `x` (the
`exists_goodFrame_compBound` output), the intrinsic `metricDerivNorm` of the
order-`a` covariant difference tower of two metrics is bounded by a constant `Cu`
(depending only on `dim E` and `a`) times the `ℓ²` of the difference of the
per-metric frame components.

`component0S` is additive over the fibre subtraction that defines
`metricDiffCovDerivAt`, so the difference-tower's frame components are the
difference of each metric's frame components — the form C1b feeds after extracting
per-metric component convergence from the Arzelà–Ascoli engine. -/
theorem metricDerivNorm_le_compSq_uniform
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    ∃ (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
      (u' : Set M) (Cu : Real),
      IsOpen u' ∧ x ∈ u' ∧
      u' ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet ∧ 1 ≤ Cu ∧
      ∀ (gk gInf : SmoothRiemannianMetric I M),
      ∀ z ∈ u', ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
        metricDerivNorm (I := I) a gk gInf gRef z ≤
          Cu * Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
            (Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gk gRef a z) I0
              - Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2) := by
  classical
  obtain ⟨basisE, u', ε, hopen, hxu', hsub, hε0, hnε, hgram, hONx, hfwd, hrev⟩ :=
    exists_goodFrame_compBound (I := I) gRef x
  refine ⟨basisE, u', ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2),
    hopen, hxu', hsub, ?_, fun gk gInf z hzu' hz => ?_⟩
  · -- 1 ≤ Cu
    have hcard : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) :=
      Nat.cast_nonneg _
    exact one_le_pow₀ (by nlinarith)
  · -- the bound at z
    set bz := (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
        I 1 basisE).toBasisAt hz) with hbz
    have hcomp : ∀ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
        Tensor0SBundle.component0S (I := I) bz
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0
          = Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
            - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0 :=
      fun I0 => rfl
    have hsumeq : (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
          Tensor0SBundle.component0S (I := I) bz
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2)
        = ∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
          (Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
            - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2 := by
      refine Finset.sum_congr rfl fun I0 _ => ?_
      rw [hcomp I0]
    have hb := hrev z hz hzu' (a + 2) (metricDiffCovDerivAt (I := I) a gk gInf gRef z)
    have hCge1 : (1 : Real) ≤ (3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1) := by
      have : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) := Nat.cast_nonneg _
      nlinarith
    have hCpow1 : (1 : Real) ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) :=
      one_le_pow₀ hCge1
    have hsqrtle : Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2))
        ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) := by
      have h2 : ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)
          ≤ (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)) ^ 2 := by
        nlinarith [hCpow1]
      calc Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2))
          ≤ Real.sqrt ((((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) :=
            Real.sqrt_sq (by positivity)
    rw [metricDerivNorm]
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (a + 2)
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z))
        ≤ Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) *
            ∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) :=
          Real.sqrt_mul (by positivity) _
      _ ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) :=
          mul_le_mul_of_nonneg_right hsqrtle (Real.sqrt_nonneg _)
      _ = ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              (Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
                - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2) := by
          rw [hsumeq]

/-- The pre-constants-first binder order (good-frame data bound after `gk`/`gInf`),
as a specialization of `metricDerivNorm_le_compSq_uniform`.  Prefer the `_uniform`
form for any sequence-level use: there the good-frame witnesses depend only on
`gRef`, `a`, `x` (chosen before `gk`/`gInf`). -/
theorem metricDerivNorm_le_compSq
    (gRef gk gInf : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    ∃ (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
      (u' : Set M) (Cu : Real),
      IsOpen u' ∧ x ∈ u' ∧
      u' ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet ∧ 1 ≤ Cu ∧
      ∀ z ∈ u', ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
        metricDerivNorm (I := I) a gk gInf gRef z ≤
          Cu * Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
            (Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gk gRef a z) I0
              - Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2) := by
  obtain ⟨basisE, u', Cu, hopen, hxu', hsub, hCu, h⟩ :=
    metricDerivNorm_le_compSq_uniform (I := I) gRef a x
  exact ⟨basisE, u', Cu, hopen, hxu', hsub, hCu, fun z hzu' hz => h gk gInf z hzu' hz⟩

/-- **C2 — the spatial P3 endpoint (scaffolded).**  Uniform-on-compacts pointwise
`metricDerivNorm` convergence of `gSeq` to a GIVEN limit `gInf` upgrades to
`MetricCInfConvOnCompacts`.  Just the `sSup` lift (`metricDerivNormSupOn_le_of_forall`,
WindowPreconv): control the finite sup over `a ≤ p` and `x ∈ K` by `ε/2 < ε`.

When C-G + C1b land, `gInf` is the constructed limit metric and `hnorm` is produced
by `metricDerivNorm_le_compSq` on a finite good-frame cover of each compact. -/
theorem metricCInfConvOnCompacts_of_normConv
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hnorm : ∀ (p : ℕ) (K : Set M), IsCompact K → ∀ ε : Real, 0 < ε →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
        metricDerivNorm (I := I) a (gSeq k) gInf gRef x < ε) :
    MetricCInfConvOnCompacts (I := I) gSeq gInf gRef := by
  intro K hK p ε hε
  obtain ⟨k0, hk0⟩ := hnorm p K hK (ε / 2) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  refine lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p (gSeq k) gInf gRef (ε / 2) (by positivity)
      (fun a hap x hxK => (hk0 k hk a hap x hxK).le)) (by linarith)

/-- **C2 — the dense-time diagonal wiring** (discharges `windowPreconv`'s `hconv`).
Given per-time *refinable* spatial preconvergence — for each dense time `e n` and
each subsequence `φ`, a further refinement `φ ∘ ψ` along which the spatial metrics
converge (the `exists_diag_subseq` `hstep` shape) — there is ONE subsequence `φ`
along which the spatial convergence holds at every dense time `e n`.

This is exactly `windowPreconv`'s `hconv` for the dense set `S = Set.range e`.  The
subsequence- and tail-stabilities of the convergence property are discharged inline
(`StrictMono.le_apply`, a `Nat` tail shift); `exists_diag_subseq` (C0) does the
diagonal. -/
theorem exists_subseq_hconv
    (K : Set M) (p : ℕ)
    (gSeq : ℕ → Real → SmoothRiemannianMetric I M)
    (gInf : Real → SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (e : ℕ → Real)
    (hstep : ∀ n : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
          metricDerivNorm (I := I) a (gSeq ((φ ∘ ψ) k) (e n)) (gInf (e n)) gRef x < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
        metricDerivNorm (I := I) a (gSeq (φ k) (e n)) (gInf (e n)) gRef x < ε := by
  refine exists_diag_subseq
    (fun n φ => ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a (gSeq (φ k) (e n)) (gInf (e n)) gRef x < ε)
    hstep ?_ ?_
  · -- hsub: subsequence-stability
    intro n φ ψ hψ hP ε hε
    obtain ⟨k0, hk0⟩ := hP ε hε
    exact ⟨k0, fun k hk a hap x hxK => hk0 (ψ k) (le_trans hk hψ.le_apply) a hap x hxK⟩
  · -- hextend: tail-stability
    intro n φ m hP ε hε
    obtain ⟨k0, hk0⟩ := hP ε hε
    refine ⟨k0 + m, fun k hk a hap x hxK => ?_⟩
    have hval := hk0 (k - m) (by omega) a hap x hxK
    simp only [Nat.sub_add_cancel (show m ≤ k by omega)] at hval
    exact hval

/-- **C2 — the window capstone (interface check).**  Composes `exists_subseq_hconv`
with `windowPreconv` (Brick D, verbatim): from the uniform time-Lipschitz control
of `gSeq`/`gInf`, a dense enumeration `e` of the window, and the per-time *refinable*
spatial preconvergence (`hstep`), there is ONE subsequence `φ` along which the
spatial metrics converge `C^p` uniformly over the whole window `[β,ψ]`.

This type-checks the `exists_subseq_hconv` output against the EXACT `windowPreconv`
`hconv` shape (for `S = Set.range e`), so the P3 assembly fits together once C-G +
C1b supply `gInf` and discharge `hstep`/`hgLip`/`hInfLip`. -/
theorem windowPreconv_of_perTime
    (K : Set M) (β ψ : Real) (p : ℕ)
    (gSeq : ℕ → Real → SmoothRiemannianMetric I M)
    (gInf : Real → SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (L : Real) (hL : 0 ≤ L)
    (hgLip : ∀ k : ℕ, ∀ s ∈ Set.Icc β ψ, ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x ≤ L * |s - t|)
    (hInfLip : ∀ s ∈ Set.Icc β ψ, ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x ≤ L * |s - t|)
    (e : ℕ → Real) (he : ∀ n : ℕ, e n ∈ Set.Icc β ψ)
    (hdense : ∀ t ∈ Set.Icc β ψ, ∀ δ : Real, 0 < δ → ∃ n : ℕ, |t - e n| < δ)
    (hstep : ∀ n : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
          metricDerivNorm (I := I) a (gSeq ((φ ∘ ψ) k) (e n)) (gInf (e n)) gRef x < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t ∈ Set.Icc β ψ,
        metricDerivNormSupOn (I := I) K p (gSeq (φ k) t) (gInf t) gRef < ε := by
  obtain ⟨φ, hφ, hconv⟩ := exists_subseq_hconv (I := I) K p gSeq gInf gRef e hstep
  refine ⟨φ, hφ, ?_⟩
  refine windowPreconv (I := I) K β ψ p (fun k => gSeq (φ k)) gInf gRef L hL
    (fun k => hgLip (φ k)) hInfLip (Set.range e) ?_ ?_
  · intro t ht δ hδ
    obtain ⟨n, hn⟩ := hdense t ht δ hδ
    exact ⟨e n, ⟨n, rfl⟩, he n, hn⟩
  · rintro τ ⟨n, rfl⟩ _ ε hε
    exact hconv n ε hε

end HCGCompactness
end DifferentialGeometry
