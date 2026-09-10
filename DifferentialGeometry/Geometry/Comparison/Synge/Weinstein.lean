import DifferentialGeometry.Geometry.Geodesic.SyngeReturnDeterminant
import DifferentialGeometry.Geometry.Geodesic.ParallelOrientation
import DifferentialGeometry.Bundle.Orientation.Map

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.VectorBundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

theorem synge_weinstein_fixed_point {n : ℕ} (hdim : Module.finrank ℝ E = n) (hn : 2 ≤ n)
    (g : SmoothRiemannianMetric I M) (hsec : HasPositiveSectionalCurvature g)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n))
    (ho : IsCompatibleOrientation (F := E) (TangentSpace I) o)
    (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (hsign : (Even n ∧ ∀ p, Orientation.map (Fin n)
        (F.mfderivToContinuousLinearEquiv (by decide) p).toLinearEquiv (o p) = o (F p)) ∨
      (Odd n ∧ ∀ p, Orientation.map (Fin n)
        (F.mfderivToContinuousLinearEquiv (by decide) p).toLinearEquiv (o p) = -o (F p))) :
    ∃ p : M, F p = p := by
  let : NeZero n := ⟨by omega⟩
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  by_contra hnot
  have hfree : ∀ p, F p ≠ p := fun p hp => hnot ⟨p, hp⟩
  obtain ⟨L, γ, hL, hγ, _, htw, _, _, _, hdet⟩ :=
    exists_minimal_twisted_geodesic_with_return_det_eq g hsec F hF hfree
  let P := parallelTransportLinearEquivOnIcc (I := I) g γ (hγ.of_le (by decide)) hL
  let D := (F.mfderivToContinuousLinearEquiv (by decide) (γ 0)).toLinearEquiv
  let A : TangentSpace I (γ 0) ≃ₗ[ℝ] TangentSpace I (γ 0) := D.trans P.symm
  have hP : Orientation.map (Fin n) P (o (γ 0)) = o (γ L) :=
    parallelTransport_preserves_orientation hdim g γ hγ hL o ho
  have hPi : Orientation.map (Fin n) P.symm (o (γ L)) = o (γ 0) :=
    (congrArg (Orientation.map (Fin n) P).symm hP).symm.trans
      ((Orientation.map (Fin n) P).symm_apply_apply _)
  have hbase : (o (F (γ 0)) : Orientation ℝ E (Fin n)) = o (γ L) := by
    rw [htw]
  have hpow : A.toLinearMap.det = (-1 : ℝ) ^ (n - 1) := by
    simpa only [A, D, P, hdim] using hdet
  rcases hsign with ⟨heven, hsign⟩ | ⟨hodd, hsign⟩
  · have hD : Orientation.map (Fin n) D (o (γ 0)) = o (γ L) :=
      (hsign (γ 0)).trans hbase
    have hA : Orientation.map (Fin n) A (o (γ 0)) = o (γ 0) :=
      (map_orientation_trans_between D P.symm (o (γ 0))).symm.trans
        ((congrArg (Orientation.map (Fin n) P.symm) hD).trans hPi)
    have hpos := ((o (γ 0)).map_eq_iff_det_pos A (by
      rw [Fintype.card_fin]
      exact hdim.symm)).mp hA
    have hodd' : Odd (n - 1) := Nat.Even.sub_odd (by omega) heven odd_one
    rw [hpow, hodd'.neg_one_pow] at hpos
    norm_num at hpos
  · have hD : Orientation.map (Fin n) D (o (γ 0)) = -o (γ L) :=
      (hsign (γ 0)).trans (congrArg (fun q : Orientation ℝ E (Fin n) => -q) hbase)
    have hA : Orientation.map (Fin n) A (o (γ 0)) = -o (γ 0) := by
      exact (map_orientation_trans_between D P.symm (o (γ 0))).symm.trans
        ((congrArg (Orientation.map (Fin n) P.symm) hD).trans
          ((Orientation.map_neg _ _).trans (congrArg (fun q => -q) hPi)))
    have hneg := ((o (γ 0)).map_eq_neg_iff_det_neg A (by
      rw [Fintype.card_fin]
      exact hdim.symm)).mp hA
    have heven' : Even (n - 1) := Nat.Odd.sub_odd hodd odd_one
    rw [hpow, heven'.neg_one_pow] at hneg
    norm_num at hneg

end DifferentialGeometry.Geometry
