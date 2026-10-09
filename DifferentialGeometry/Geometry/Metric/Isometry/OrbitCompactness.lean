import DifferentialGeometry.Geometry.Metric.Isometry.Compactness
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Sequences

namespace ContinuousMap

open Filter (Tendsto atTop)
open scoped Topology

variable {G X Y : Type*} [Group G]
  [MetricSpace X] [ProperSpace X] [MetricSpace Y] [ProperSpace Y]
  [MulAction G X] [IsIsometricSMul G X] [MulAction G Y] [IsIsometricSMul G Y]

theorem exists_isometry_orbit_subsequence (F : C(X, Y))
    (hF : ∀ (γ : G) (x : X), F (γ • x) = γ • F x) (o : X)
    (a : ℕ → Y ≃ᵢ Y) (b : ℕ → X ≃ᵢ X) (γ : ℕ → G)
    {D : Set X} {K : Set Y} (hD : IsCompact D) (hK : IsCompact K)
    (hb : ∀ n, γ n • b n o ∈ D) (ha : ∀ n, a n (F (b n o)) ∈ K) :
    ∃ (k : ℕ → ℕ) (A : Y ≃ᵢ Y) (B : X ≃ᵢ X), StrictMono k ∧
      Tendsto (fun n => (a (k n) *
        (IsometryEquiv.constSMul (γ (k n)) : Y ≃ᵢ Y).symm : C(Y, Y)))
        atTop (𝓝 (A : C(Y, Y))) ∧
      Tendsto (fun n => ((IsometryEquiv.constSMul (γ (k n)) : X ≃ᵢ X) *
        b (k n) : C(X, X))) atTop (𝓝 (B : C(X, X))) ∧
      Tendsto (fun n => (a (k n) : C(Y, Y)).comp (F.comp (b (k n) : C(X, X))))
        atTop (𝓝 ((A : C(Y, Y)).comp (F.comp (B : C(X, X))))) := by
  let U (n : ℕ) : Y ≃ᵢ Y := a n * (IsometryEquiv.constSMul (γ n) : Y ≃ᵢ Y).symm
  let V (n : ℕ) : X ≃ᵢ X := (IsometryEquiv.constSMul (γ n) : X ≃ᵢ X) * b n
  have hcomp (n : ℕ) (x : X) : U n (F (V n x)) = a n (F (b n x)) := by
    change a n ((IsometryEquiv.constSMul (γ n) : Y ≃ᵢ Y).symm
      (F ((IsometryEquiv.constSMul (γ n) : X ≃ᵢ X) (b n x)))) = _
    rw [IsometryEquiv.constSMul_symm]
    change a n ((γ n)⁻¹ • F (γ n • b n x)) = _
    rw [hF, inv_smul_smul]
  obtain ⟨R, hR⟩ := (hD.image F.continuous).isBounded.subset_closedBall (F o)
  obtain ⟨S, hS⟩ := hK.isBounded.subset_closedBall (F o)
  have hU (n : ℕ) : U n (F o) ∈ Metric.closedBall (F o) (R + S) := by
    have hdist : dist (U n (F o)) (a n (F (b n o))) ≤ R := by
      rw [← hcomp n o, (U n).dist_eq, dist_comm]
      exact hR ⟨V n o, hb n, rfl⟩
    exact (dist_triangle (U n (F o)) (a n (F (b n o))) (F o)).trans
      (add_le_add hdist (hS (ha n)))
  have hleft := isCompact_setOf_isometry_surjective (F o)
    (isCompact_closedBall (F o) (R + S))
  have hright := isCompact_setOf_isometry_surjective o hD
  obtain ⟨p, hp, k, hk, hlim⟩ := (hleft.prod hright).tendsto_subseq
    (x := fun n => ((U n : C(Y, Y)), (V n : C(X, X))))
    (fun n => ⟨⟨(U n).isometry, (U n).surjective, hU n⟩,
      ⟨(V n).isometry, (V n).surjective, hb n⟩⟩)
  let A : Y ≃ᵢ Y :=
    { toEquiv := Equiv.ofBijective p.1 ⟨hp.1.1.injective, hp.1.2.1⟩
      isometry_toFun := hp.1.1 }
  let B : X ≃ᵢ X :=
    { toEquiv := Equiv.ofBijective p.2 ⟨hp.2.1.injective, hp.2.2.1⟩
      isometry_toFun := hp.2.1 }
  have hA : Tendsto (fun n => (U (k n) : C(Y, Y))) atTop (𝓝 (A : C(Y, Y))) :=
    (continuous_fst.tendsto p).comp hlim
  have hB : Tendsto (fun n => (V (k n) : C(X, X))) atTop (𝓝 (B : C(X, X))) :=
    (continuous_snd.tendsto p).comp hlim
  refine ⟨k, A, B, hk, hA, hB, ?_⟩
  have hfixed : Tendsto (fun _ : ℕ => F) atTop (𝓝 F) := tendsto_const_nhds
  exact (hA.compCM (hfixed.compCM hB)).congr'
    (Filter.Eventually.of_forall fun n => by
      ext x
      exact hcomp (k n) x)

end ContinuousMap
