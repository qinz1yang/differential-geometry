import DifferentialGeometry.Topology.DirectLimit.Manifold
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace SmoothSeqSystem

open TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type u} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
  (U : ∀ n, Opens (M n)) [∀ n, IsManifold I ∞ (U n)] [∀ n, Nonempty (U n)]
  (Φ : ∀ n, PartialDiffeomorph I I (M n) (M (n + 1)) (∞ : WithTop ℕ∞))
  (hU : ∀ n, (U n : Set (M n)) ⊆ (Φ n).source)
  (hmap : ∀ n, (Φ n : M n → M (n + 1)) '' (U n : Set (M n)) ⊆
    (U (n + 1) : Set (M (n + 1))))

def ofPartialDiffeomorphs : SmoothSeqSystem I (fun n => U n) :=
  ofSucc
    (fun n => PartialDiffeomorph.opensMap (Φ n) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_isOpenEmb (Φ n) (hU n) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_contMDiff (Φ n) (hU n) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_invFun_contMDiffOn (Φ n) (hU n) (hmap n))

theorem ofPartialDiffeomorphs_map_apply (n k : ℕ) (x : U n) :
    (((ofPartialDiffeomorphs U Φ hU hmap).toSeqSystem.map
      (Nat.le_add_right n k) x : U (n + k)) : M (n + k)) =
        CheegerGromovCompactness.chainComp Φ n k x := by
  let S := ofPartialDiffeomorphs U Φ hU hmap
  induction k with
  | zero => exact congrArg Subtype.val (S.toSeqSystem.map_self n x)
  | succ k ih =>
      have heq := S.toSeqSystem.map_map (Nat.le_add_right n k)
        (Nat.le_succ (n + k)) x
      change _ = (Φ (n + k)) (CheegerGromovCompactness.chainComp Φ n k x)
      rw [show (ofPartialDiffeomorphs U Φ hU hmap).toSeqSystem.map
          (Nat.le_add_right n (k + 1)) x =
            S.toSeqSystem.map (Nat.le_succ (n + k))
              (S.toSeqSystem.map (Nat.le_add_right n k) x) from heq.symm]
      simp only [S, ofPartialDiffeomorphs, ofSucc_map_succ]
      exact congrArg (Φ (n + k) : M (n + k) → M (n + k + 1)) ih

theorem ofPartialDiffeomorphs_invIncl_incl (n k : ℕ) (x : U n) :
    ((Function.invFun ((ofPartialDiffeomorphs U Φ hU hmap).toSeqSystem.incl (n + k))
      ((ofPartialDiffeomorphs U Φ hU hmap).toSeqSystem.incl n x) :
        U (n + k)) : M (n + k)) = CheegerGromovCompactness.chainComp Φ n k x := by
  rw [(ofPartialDiffeomorphs U Φ hU hmap).invIncl_incl_le (Nat.le_add_right n k)]
  exact ofPartialDiffeomorphs_map_apply U Φ hU hmap n k x

end SmoothSeqSystem
end DifferentialGeometry
