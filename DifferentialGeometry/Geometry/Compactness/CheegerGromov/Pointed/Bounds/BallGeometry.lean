import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.LocalJetSubsequence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter
open scoped Manifold Topology ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

structure SeqBallGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  C : Nat → Nat → Real
  nonneg : ∀ n p : Nat, 0 ≤ C n p
  bound : ∀ n p j : Nat, n + p ≤ j →
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (X.obj j).M := (X.obj j).t2
    letI : SigmaCompactSpace (X.obj j).M := (X.obj j).sigmaCompact
    ∀ x : (X.obj j).M,
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x ≤
        ENNReal.ofReal (n : Real) →
      curvDerivNorm (I := I) p (X.obj j).metric x ≤ C n p

namespace SeqBallGeometry

omit [CompleteSpace E] in
def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallGeometry (I := I) X) (f : Nat → Nat) (hf : ∀ j : Nat, j ≤ f j) :
    SeqBallGeometry (I := I) (X.subseq f) where
  C := h.C
  nonneg := h.nonneg
  bound := by
    intro n p j hnj
    with_unfolding_all
      exact h.bound n p (f j) (le_trans hnj (hf j))

omit [CompleteSpace E] in
def of_boundedGeometry
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBoundedGeometry (I := I) X) :
    SeqBallGeometry (I := I) X where
  C := fun _ p => h.C p
  nonneg := fun _ p => h.nonneg p
  bound := by
    intro n p j _hnj
    with_unfolding_all
      exact fun x _hx => h.bound j p x

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem bound_of_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallGeometry (I := I) X)
    {n n' p : Nat} (hn : n' ≤ n) :
    ∀ j : Nat, n + p ≤ j →
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (X.obj j).M := (X.obj j).t2
    letI : SigmaCompactSpace (X.obj j).M := (X.obj j).sigmaCompact
    ∀ x : (X.obj j).M,
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x ≤
        ENNReal.ofReal (n' : Real) →
      curvDerivNorm (I := I) p (X.obj j).metric x ≤ h.C n p := by
  intro j hnj x hx
  exact h.bound n p j hnj x (hx.trans (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hn)))

end SeqBallGeometry

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem exists_subseq_seqBallGeometry_of_local_jets
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hjets : ∀ A : Real, 0 < A → ∀ p : Nat, ∃ C : Real, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C) :
    ∃ φ : Nat → Nat, StrictMono φ ∧
      Nonempty (SeqBallGeometry (I := I) (X.subseq φ)) := by
  obtain ⟨φ, hφ, C, hC0, hC⟩ :=
    exists_subsequence_curvDerivNorm_ball_le_of_local_jets X hjets
  exact ⟨φ, hφ, ⟨{ C := C, nonneg := hC0, bound := fun n p j hnj => hC n p j hnj }⟩⟩

end CheegerGromovCompactness
end DifferentialGeometry
