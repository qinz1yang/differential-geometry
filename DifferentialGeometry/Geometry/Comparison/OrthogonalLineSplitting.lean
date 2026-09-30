import DifferentialGeometry.Geometry.Comparison.OrthogonalLineFactor
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanProductCoordinates

set_option autoImplicit false
open Set Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

theorem exists_oriented_euclidean_splitting {k : ℕ} {X : Type u} [MetricSpace X] [ProperSpace X]
    (p : X) (hs : fourPointComparison 0 (univ : Set X))
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (γ : Fin k → ℝ → X) (hγ : ∀ j, Isometry (γ j)) (hγ0 : ∀ j, γ j 0 = p)
    (hangle : ∀ j l, j ≠ l → germComparisonAngle 0 (γ j) (γ l) = Real.pi / 2) :
    ∃ (Z : Type u) (m : MetricSpace Z), letI := m
      ∃ (z : Z) (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)),
        e p = WithLp.toLp 2 (0, z) ∧
        (∀ j t, e (γ j t) = WithLp.toLp 2 (PiLp.single 2 j t, z)) ∧
        ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
        (∀ a b : Z, ∃ f : Icc (0 : ℝ) 1 → Z,
          Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) := by
  classical
  induction k generalizing X with
  | zero =>
      let e := (IsometryEquiv.withLpUniqueProd 2 (EuclideanSpace ℝ (Fin 0)) X).symm
      refine ⟨X, inferInstance, p, e, ?_, ?_, inferInstance, inferInstance, hs, hsegments⟩
      · apply (WithLp.equiv 2 _).injective
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl
      · intro j
        exact Fin.elim0 j
  | succ k ih =>
      let last : Fin (k + 1) := Fin.last k
      let Y := {x : X // lineCoordinate (γ last) x = 0}
      let q : Y := ⟨γ last 0, lineCoordinate_apply_isometry (hγ last) 0⟩
      let : ProperSpace Y := properSpace_lineCoordinate_zero hs (hγ last)
      have hbase (j : Fin k) : γ last 0 = γ j.castSucc 0 :=
        (hγ0 last).trans (hγ0 j.castSucc).symm
      have hright (j : Fin k) : germComparisonAngle 0 (γ last) (γ j.castSucc) = Real.pi / 2 :=
        hangle last j.castSucc (Fin.castSucc_ne_last j).symm
      let β (j : Fin k) : ℝ → Y := orthogonalLineInFactor hs (hγ last) (hγ j.castSucc)
        (hbase j) (hright j)
      have hβ (j : Fin k) : Isometry (β j) :=
        isometry_orthogonalLineInFactor hs (hγ last) (hγ j.castSucc) (hbase j) (hright j)
      have hβ0 (j : Fin k) : β j 0 = q :=
        orthogonalLineInFactor_zero hs (hγ last) (hγ j.castSucc) (hbase j) (hright j)
      have hβangle (j l : Fin k) (hjl : j ≠ l) :
          germComparisonAngle 0 (β j) (β l) = Real.pi / 2 := by
        rw [germComparisonAngle_orthogonalLineInFactor]
        exact hangle j.castSucc l.castSucc (fun h => hjl (Fin.castSucc_inj.mp h))
      obtain ⟨Z, mZ, z, eY, heY0, heYaxis, hproper, hcomplete, hcomp, hseg⟩ :=
        ih q (fourPointComparison_lineCoordinate_zero hs)
          (exists_segment_lineCoordinate_zero hs (hγ last) hsegments) β hβ hβ0 hβangle
      let := mZ
      let e0 := lineSplitting hs (hγ last) hsegments
      let e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin (k + 1)) × Z) :=
        ((((((e0.trans (IsometryEquiv.withLpProdComm 2 ℝ Y)).trans
          (IsometryEquiv.withLpProdCongr 2 eY (IsometryEquiv.refl ℝ))).trans
          (IsometryEquiv.withLpProdAssoc 2 (EuclideanSpace ℝ (Fin k)) Z ℝ)).trans
          (IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl (EuclideanSpace ℝ (Fin k)))
            (IsometryEquiv.withLpProdComm 2 Z ℝ))).trans
          (IsometryEquiv.withLpProdAssoc 2 (EuclideanSpace ℝ (Fin k)) ℝ Z).symm).trans
          (IsometryEquiv.withLpProdCongr 2 (EuclideanSpace.finSuccProdIsometry k).symm.toIsometryEquiv
            (IsometryEquiv.refl Z)))
      have he (x : X) : e x = WithLp.toLp 2
          ((EuclideanSpace.finSuccProdIsometry k).symm
            (WithLp.toLp 2 ((eY (e0 x).snd).fst, (e0 x).fst)), (eY (e0 x).snd).snd) := rfl
      have he0 (t : ℝ) : e0 (γ last t) = WithLp.toLp 2 (t, q) :=
        lineSplitting_apply_line hs (hγ last) hsegments t
      have heβ (j : Fin k) (t : ℝ) : e0 (γ j.castSucc t) = WithLp.toLp 2 (0, β j t) :=
        lineSplitting_apply_of_lineCoordinate_eq_zero hs (hγ last) hsegments (γ j.castSucc t)
          (lineCoordinate_crossing_isometry_eq_zero_of_right_angle hs (hγ last) (hγ j.castSucc)
            (hbase j) (hright j) t)
      refine ⟨Z, mZ, z, e, ?_, ?_, hproper, hcomplete, hcomp, hseg⟩
      · rw [← hγ0 last, he, he0]
        change WithLp.toLp 2 ((EuclideanSpace.finSuccProdIsometry k).symm
          (WithLp.toLp 2 ((eY q).fst, 0)), (eY q).snd) = _
        rw [heY0]
        change WithLp.toLp 2 ((EuclideanSpace.finSuccProdIsometry k).symm 0, z) = _
        rw [map_zero]
      · intro j t
        refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [he, he0]
          change WithLp.toLp 2 ((EuclideanSpace.finSuccProdIsometry k).symm
            (WithLp.toLp 2 ((eY q).fst, t)), (eY q).snd) = _
          rw [heY0]
          change WithLp.toLp 2 ((EuclideanSpace.finSuccProdIsometry k).symm (WithLp.toLp 2 (0, t)), z) = _
          rw [EuclideanSpace.finSuccProdIsometry_symm_single_last]
        · rw [he, heβ]
          change WithLp.toLp 2 ((EuclideanSpace.finSuccProdIsometry k).symm
            (WithLp.toLp 2 ((eY (β j t)).fst, 0)), (eY (β j t)).snd) = _
          rw [heYaxis]
          change WithLp.toLp 2 ((EuclideanSpace.finSuccProdIsometry k).symm
            (WithLp.toLp 2 (PiLp.single 2 j t, 0)), z) = _
          rw [EuclideanSpace.finSuccProdIsometry_symm_single_castSucc]

end DifferentialGeometry.Geometry.Comparison.Toponogov
