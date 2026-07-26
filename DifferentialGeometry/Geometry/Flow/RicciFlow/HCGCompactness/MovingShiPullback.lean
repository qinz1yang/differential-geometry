import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback

/-!
# P1.3 — Shi-bound pullback transfer (`MovingShiBoundOn` under `Φ : M ≃ₘ N`)

The covariant Ricci-derivative tower `ricCovTower` transports under a (non-endo)
diffeomorphism `Φ`, and its `normSq0S` is preserved by the pullback metric.  Hence
the moving-metric Shi bound `MovingShiBoundOn` transfers from `g` (on the target)
to the pullback `Φ^* g` (on the source).

The tower pullback is assembled from `covDerivOfField_pullback` (general base tower
naturality) with the Ricci base supplied by `ricciSection_pullback`, reindexed from
the `covDerivOfField` `(s+2)` indexing to the `iterCov`/`ricCovTower` `(2+s)` indexing
via `covDerivOfField_eq_iterCov`.  The norm equality is `normSq0S_pullback_eval_of_orthonormal`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Connection.CovariantDerivative

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- Evaluated form of `covDerivOfField_eq_iterCov`: `covDerivOfField gRef A0 m` at `x`
on `slots` equals `iterCov gRef 2 A0 m` at `x` on the `acEquiv m`-reindexed slots. -/
theorem covDerivOfField_apply_eq_iterCov
    [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (m : ℕ) (x : M) (slots : Fin (m + 2) → TangentSpace I x) :
    covDerivOfField (I := I) gRef A0 m x slots
      = iterCov (I := I) gRef 2 A0 m x (slots ∘ ⇑(acEquiv m)) := by
  rw [covDerivOfField_eq_iterCov]
  rfl

/-- **Pullback naturality of the Ricci-derivative tower `ricCovTower`** under
`Φ : M ≃ₘ N`.  `ricCovTower (Φ^*g)(Φ^*g) s` at `x` evaluated on `slots` equals
`ricCovTower g g s` at `Φ x` evaluated on the pushed-forward slots.  Assembled from
`covDerivOfField_pullback` (Ricci base via `ricciSection_pullback`), reindexed to the
`iterCov` indexing of `ricCovTower` by `covDerivOfField_apply_eq_iterCov`. -/
theorem ricCovTower_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (s : ℕ) (x : M)
    (slots : Fin (2 + s) → TangentSpace I x) :
    ricCovTower (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ)
        (Diffeomorph.pullbackMetric (I := I) g Φ) s x slots
      = ricCovTower (I := I) g g s (Φ x)
          (fun q => mfderiv I I (Φ : M → N) x (slots q)) := by
  have hpb := covDerivOfField_pullback (I := I) g Φ
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ))
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
        (Diffeomorph.pullbackMetric (I := I) g Φ)))
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g))
    (ricciSection_pullback (I := I) g Φ) s x (slots ∘ (acEquiv s).symm)
  rw [covDerivOfField_apply_eq_iterCov, covDerivOfField_apply_eq_iterCov] at hpb
  have e1 : (slots ∘ ⇑(acEquiv s).symm) ∘ ⇑(acEquiv s) = slots := by
    funext i; simp [Function.comp, Equiv.symm_apply_apply]
  have e2 : (fun q => mfderiv I I (Φ : M → N) x ((slots ∘ ⇑(acEquiv s).symm) q))
        ∘ ⇑(acEquiv s)
      = fun q => mfderiv I I (Φ : M → N) x (slots q) := by
    funext i; simp [Function.comp, Equiv.symm_apply_apply]
  rw [e1, e2] at hpb
  exact hpb

/-- **The Ricci-tower `normSq0S` is preserved by the pullback metric.**  In a
`Φ^*g`-orthonormal source frame, `normSq0S (Φ^*g) x (ricCovTower (Φ^*g)(Φ^*g) s x)`
equals `normSq0S g (Φ x) (ricCovTower g g s (Φ x))`.  Combines `ricCovTower_pullback`
(the evaluated tower naturality) with `normSq0S_pullback_eval_of_orthonormal`. -/
theorem ricCovTower_normSq0S_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (s : ℕ) (x : M) :
    Tensor0SBundle.normSq0S (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x (2 + s)
        (ricCovTower (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ)
          (Diffeomorph.pullbackMetric (I := I) g Φ) s x)
      = Tensor0SBundle.normSq0S (I := I) g (Φ x) (2 + s)
          (ricCovTower (I := I) g g s (Φ x)) := by
  obtain ⟨B, hB⟩ := exists_gOrthonormalBasis (Diffeomorph.pullbackMetric (I := I) g Φ) x
  exact normSq0S_pullback_eval_of_orthonormal (I := I) g Φ x (2 + s) B hB
    (ricCovTower (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ)
      (Diffeomorph.pullbackMetric (I := I) g Φ) s x)
    (ricCovTower (I := I) g g s (Φ x))
    (fun slots => ricCovTower_pullback (I := I) g Φ s x slots)

/-- **P1.3 — the moving-metric Shi bound transfers under pullback.**  If the Shi
bound `MovingShiBoundOn` holds for the metric sequence `gSeq` on a target set `U`
(of `N`), then it holds for the pulled-back sequence `i t ↦ Φ^*(gSeq i t)` on any
source set `V` (of `M`) mapped by `Φ` into `U`.  Per-point, the Ricci-tower
`√normSq0S` is preserved by `ricCovTower_normSq0S_pullback`, so the bound at `Φ x`
gives the bound at `x`. -/
theorem movingShiBoundOn_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N)
    (U : Set N) (β ψ : ℝ) (Nord : ℕ) (KShi : ℝ) (V : Set M)
    (hV : ∀ x ∈ V, Φ x ∈ U)
    (hShi : MovingShiBoundOn (I := I) U β ψ gSeq Nord KShi) :
    MovingShiBoundOn (I := I) V β ψ
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ) Nord KShi := by
  intro s hs i t ht x hx
  rw [ricCovTower_normSq0S_pullback (I := I) (gSeq i t) Φ s x]
  exact hShi s hs i t ht (Φ x) (hV x hx)

end HCGCompactness
end DifferentialGeometry

end
