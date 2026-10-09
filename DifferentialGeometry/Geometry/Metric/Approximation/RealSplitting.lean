import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport

set_option autoImplicit false
namespace GC.MetricGeometry

universe u v
variable {X : Type u} [MetricSpace X] {p : X} {ε : ℝ}

theorem hasEuclideanSplitting_one_iff :
    HasEuclideanSplitting.{u, v} p 1 ε ↔
      ∃ (Y : Type v) (mY : MetricSpace Y), letI := mY
        ∃ q : Y, Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) ε) := by
  let e := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  constructor
  · rintro ⟨Y, mY, q, ⟨F⟩⟩
    let := mY
    exact ⟨Y, mY, q, ⟨F.mapTargetIsometryAt
      (e.symm.toIsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl Y))
      (WithLp.toLp 2 ((0 : ℝ), q)) (by
        change WithLp.toLp 2 (e.symm 0, q) = WithLp.toLp 2 ((0 : ℝ), q)
        exact congrArg (fun t : ℝ => WithLp.toLp 2 (t, q)) e.symm.map_zero)⟩⟩
  · rintro ⟨Y, mY, q, ⟨F⟩⟩
    let := mY
    exact ⟨Y, mY, q, ⟨F.mapTargetIsometryAt
      (e.toIsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl Y))
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), q)) (by
        change WithLp.toLp 2 (e 0, q) = WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), q)
        exact congrArg (fun t : EuclideanSpace ℝ (Fin 1) => WithLp.toLp 2 (t, q)) e.map_zero)⟩⟩

theorem hasEuclideanSplitting_two_of_plane_approximation
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) ε) :
    HasEuclideanSplitting.{u, v} p 2 ε := by
  let e₁ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let e₂ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 1 ⊕ Fin 1 => ℝ))
  let e := ((e₁.withLpProdCongr 2 e₁).trans e₂.symm).toIsometryEquiv.trans
    (IsometryEquiv.withLpProdUnique 2 (EuclideanSpace ℝ (Fin 2)) PUnit.{v + 1}).symm
  exact ⟨PUnit.{v + 1}, inferInstance, PUnit.unit,
    ⟨F.mapTargetIsometryAt e (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), PUnit.unit)) (by
      change WithLp.toLp 2 (e₂.symm ((e₁.withLpProdCongr 2 e₁) 0), PUnit.unit) = _
      rw [(e₁.withLpProdCongr 2 e₁).map_zero, e₂.symm.map_zero])⟩⟩

theorem splittingRank_one_real_model_and_no_plane {β : ℕ → ℝ} {N : ℕ}
    (hN : 2 ≤ N) (hrank : splittingRank.{u, v} p β N = 1) :
    (∃ (Y : Type v) (mY : MetricSpace Y), letI := mY
      ∃ q : Y, Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) (β 1))) ∧
      ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (β 2)) := by
  obtain ⟨_, hyes, hno⟩ := (splittingRank_eq_iff p β N 1).mp hrank
  refine ⟨hasEuclideanSplitting_one_iff.mp (hyes (by decide)), ?_⟩
  rintro ⟨F⟩
  exact hno 2 (by decide) hN (hasEuclideanSplitting_two_of_plane_approximation F)

end GC.MetricGeometry
