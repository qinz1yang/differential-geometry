import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanProduct

namespace EuclideanSpace

theorem finSuccProdIsometry_fst_apply (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin k) :
    (finSuccProdIsometry k v).fst i = v i.castSucc := rfl

theorem finSuccProdIsometry_snd (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    (finSuccProdIsometry k v).snd = v (Fin.last k) := by
  change (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    (WithLp.toLp 2 (fun i : Fin 1 => v (finSumFinEquiv (Sum.inr i)))) = _
  apply (OrthonormalBasis.singleton (Fin 1) ℝ).repr.injective
  ext i
  simp only [LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply,
    OrthonormalBasis.singleton_repr]
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem finSuccProdIsometry_symm_single_castSucc (k : ℕ) (j : Fin k) (t : ℝ) :
    (finSuccProdIsometry k).symm (WithLp.toLp 2 (PiLp.single 2 j t, 0)) =
      PiLp.single 2 j.castSucc t := by
  apply (finSuccProdIsometry k).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · ext i
    change (PiLp.single 2 j t : EuclideanSpace ℝ (Fin k)) i = (finSuccProdIsometry k (PiLp.single 2 j.castSucc t)).fst i
    rw [finSuccProdIsometry_fst_apply]
    simp only [PiLp.single_apply, Fin.castSucc_inj]
  · change 0 = (finSuccProdIsometry k (PiLp.single 2 j.castSucc t)).snd
    rw [finSuccProdIsometry_snd, PiLp.single_eq_of_ne _ (Fin.castSucc_ne_last j).symm]

theorem finSuccProdIsometry_symm_single_last (k : ℕ) (t : ℝ) :
    (finSuccProdIsometry k).symm (WithLp.toLp 2 (0, t)) = PiLp.single 2 (Fin.last k) t := by
  apply (finSuccProdIsometry k).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · ext i
    change 0 = (finSuccProdIsometry k (PiLp.single 2 (Fin.last k) t)).fst i
    rw [finSuccProdIsometry_fst_apply, PiLp.single_eq_of_ne _ (Fin.castSucc_ne_last i)]
  · change t = (finSuccProdIsometry k (PiLp.single 2 (Fin.last k) t)).snd
    rw [finSuccProdIsometry_snd, PiLp.single_eq_same]

end EuclideanSpace
