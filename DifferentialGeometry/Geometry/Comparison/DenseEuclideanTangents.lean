import DifferentialGeometry.Geometry.Comparison.DenseAngularFrames
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentFrame
import DifferentialGeometry.Geometry.Comparison.GlobalTangentDimension

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_dense_euclidean_tangents_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (univ : Set X) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∃ S : Set X, IsGδ S ∧ Dense S ∧ ∀ q ∈ S,
        letI : HasAnglesAt q := by
          obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
          exact hasAnglesAt_of_local_fourPointComparison
            (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
        ∃ e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m), e EuclideanCone.tip = 0 := by
  obtain ⟨m, hmn, hglobal, hopen, hpoints⟩ :=
    exists_global_tangent_dimH_and_directions_of_local_comparison_and_dimH hcurves hdim hlocal
  have hdimlarger : dimH (univ : Set X) ≤ (n + 1 : ℕ) :=
    hdim.trans (by exact_mod_cast Nat.le_succ n)
  have hpointwise (q : X) :
      letI : HasAnglesAt q := by
        obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
        exact hasAnglesAt_of_local_fourPointComparison
          (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
      ∀ v : (Fin m × Bool) → SpaceOfDirections q,
        (∀ i, dist (v (i, true)) (v (i, false)) = Real.pi) →
        (∀ i j, i ≠ j → dist (v (i, true)) (v (j, true)) = Real.pi / 2) →
        ∃ e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m), e EuclideanCone.tip = 0 := by
    let : HasAnglesAt q := by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
      exact hasAnglesAt_of_local_fourPointComparison
        (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    obtain ⟨_, hproper, hcomp, hsegments, _⟩ :=
      tangent_geometry_and_blowup_of_local_comparison_and_dimH hcurves isOpen_univ
        (by omega : 1 ≤ n + 1) hdimlarger (fun z _ => hlocal z) (mem_univ q)
    let : ProperSpace (TangentCone q) := hproper
    intro v hopposite horthogonal
    exact exists_pointed_euclidean_tangent_of_orthogonal_frame q hcomp hsegments
      (hpoints q).1.le v hopposite horthogonal
  rcases subsingleton_or_nontrivial X with hsub | hnontrivial
  · have hz : dimH (univ : Set X) = 0 :=
      (show (univ : Set X).Subsingleton from fun _ _ _ _ => Subsingleton.elim _ _).dimH_zero
    have hmzero : m = 0 := by exact_mod_cast hglobal.symm.trans hz
    subst m
    refine ⟨0, hmn, hglobal, hopen, univ, IsGδ.univ, dense_univ, ?_⟩
    intro q _
    exact hpointwise q (fun v => Fin.elim0 v.1)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  · obtain ⟨k, _, hglobalK, _, S, hGS, hDS, hframe⟩ :=
      exists_dense_isGδ_orthogonal_direction_frames_of_local_comparison_and_dimH hcurves hdim hlocal
    have hkm : k = m := by exact_mod_cast hglobalK.symm.trans hglobal
    subst k
    refine ⟨m, hmn, hglobal, hopen, S, hGS, hDS, ?_⟩
    intro q hq
    obtain ⟨v, hopposite, hcross⟩ := hframe q hq
    exact hpointwise q v hopposite (fun i j hij => hcross i j hij true true)

end DifferentialGeometry.Geometry.Comparison.Toponogov
