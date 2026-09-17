import DifferentialGeometry.Topology.Planar.InscribedPolygon
import DifferentialGeometry.Analysis.Calculus.PolygonalRounding
import DifferentialGeometry.Analysis.Calculus.Periodic.Affine
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

open Set
open scoped ContDiff NNReal

namespace DifferentialGeometry.Topology.Planar

private theorem norm_lineMap_sub_left_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ‖AffineMap.lineMap x y τ - x‖ ≤ ‖y - x‖ := by
  rw [← dist_eq_norm, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hτ.1,
    dist_comm, dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) hτ.2

theorem exists_inscribed_rounding_injOn_interpolation_forall_width
    {γ : ℝ → Schoenflies.Plane} (hγ : ContDiff ℝ ∞ γ)
    (hne : ∀ t, deriv γ t ≠ 0) (hperiod : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ P : Schoenflies.PrePolygon m,
      1 / (m + 3 : ℝ) < ε ∧
      (∀ i, P.vertex i = γ ((i.val : ℝ) / (m + 3))) ∧
      let h := 1 / (m + 3 : ℝ)
      ∀ σ ∈ Ioo (0 : ℝ) (h / 2),
      let g := DifferentialGeometry.Analysis.roundedPolygonalCurve h σ
        (fun k : ℤ => γ (k * h))
      let F := fun q : ℝ × ℝ => AffineMap.lineMap (γ q.2) (g q.2) q.1
      ContDiff ℝ ∞ F ∧ (∀ τ, Function.Periodic (fun t => F (τ, t)) 1) ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, InjOn (fun t => F (τ, t)) (Ico (0 : ℝ) 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, deriv (fun x => F (τ, x)) t ≠ 0 := by
  have hd (t : ℝ) : HasDerivAt γ (deriv γ t) t := (hγ.differentiable (by simp) t).hasDerivAt
  have hv : Continuous (deriv γ) := hγ.continuous_deriv (by simp)
  have hvperiod : Function.Periodic (deriv γ) 1 := by
    intro t
    have heq := congrArg (fun f : ℝ → Schoenflies.Plane => deriv f t) hperiod.funext
    simpa only [deriv_comp_add_const] using heq
  obtain ⟨B, hB, hbound⟩ :=
    DifferentialGeometry.Analysis.exists_bound_of_continuous_unit_periodic hv hvperiod
  have hLip : LipschitzWith ⟨B, hB.le⟩ γ :=
    lipschitzWith_of_nnnorm_deriv_le (hγ.differentiable (by simp)) (fun t => by
      exact_mod_cast hbound t)
  obtain ⟨η, hη, hstable⟩ := PeriodicCurve.exists_pos_forall_injOn_of_periodic
    hv hd hne hperiod hinj
  obtain ⟨δ, hδ, happrox⟩ :=
    DifferentialGeometry.Analysis.roundedPolygonalCurve.exists_uniform_deriv_approximation hd
      (DifferentialGeometry.Analysis.uniformContinuous_of_continuous_unit_periodic hv hvperiod)
      (half_pos hη)
  obtain ⟨m, P, hmesh, hp, _⟩ := exists_inscribed_prePolygon hv hd hne hperiod hinj
    (show 0 < min δ (min (η / (2 * B)) ε) from
      lt_min hδ (lt_min (div_pos hη (mul_pos (by norm_num) hB)) hε))
  let h : ℝ := 1 / (m + 3 : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hhδ : h < δ := hmesh.trans_le (min_le_left _ _)
  have hhη : h < η / (2 * B) := hmesh.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hhε : h < ε := hmesh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨m, P, hhε, hp, ?_⟩
  dsimp only
  intro σ hσ
  let g := DifferentialGeometry.Analysis.roundedPolygonalCurve h σ
    (fun k : ℤ => γ (k * h))
  have hg : ContDiff ℝ ∞ g := DifferentialGeometry.Analysis.roundedPolygonalCurve.contDiff
    hh hσ.1 hσ.2 _
  have hgperiod : Function.Periodic g 1 := by
    have hpint : Function.Periodic (fun k : ℤ => γ (k * h)) (m + 3 : ℤ) := by
      intro k
      have heq : (((k + (m + 3) : ℤ) : ℝ)) * h = k * h + 1 := by
        dsimp [h]
        push_cast
        field_simp
      change γ ((((k + (m + 3) : ℤ) : ℝ)) * h) = γ (k * h)
      rw [heq]
      exact hperiod _
    have hper := DifferentialGeometry.Analysis.roundedPolygonalCurve.periodic hh.ne' σ hpint
    have hperiod_eq : ((m + 3 : ℤ) : ℝ) * h = 1 := by
      dsimp [h]
      push_cast
      field_simp
    simpa only [hperiod_eq] using hper
  have hclose (t : ℝ) : ‖g t - γ t‖ < η := by
    have hb := DifferentialGeometry.Analysis.roundedPolygonalCurve.norm_sub_le_of_lipschitz
      hh hσ.1 hLip t
    have hhB : h * (2 * B) < η := (lt_div_iff₀ (by positivity)).mp hhη
    exact hb.trans_lt (by change (h + 2 * σ) * B < η; nlinarith [hσ.2])
  have hdclose (t : ℝ) : ‖deriv g t - deriv γ t‖ < η :=
    (happrox h ⟨hh, hhδ⟩ σ hσ t).trans_lt (half_lt_self hη)
  refine ⟨?_, ?_, ?_⟩
  · exact (hγ.comp contDiff_snd).lineMap (hg.comp contDiff_snd) contDiff_fst
  · intro τ t
    change AffineMap.lineMap (γ (t + 1)) (g (t + 1)) τ = _
    rw [hperiod t, hgperiod t]
  · intro τ hτ
    let w := fun t => AffineMap.lineMap (deriv γ t) (deriv g t) τ
    have hderiv (t : ℝ) : HasDerivAt (fun x => AffineMap.lineMap (γ x) (g x) τ) (w t) t := by
      simp only [AffineMap.lineMap_apply_module, w]
      exact ((hd t).const_smul (1 - τ)).add
        (((hg.differentiable (by simp) t).hasDerivAt).const_smul τ)
    have hfperiod : Function.Periodic (fun t => AffineMap.lineMap (γ t) (g t) τ) 1 := by
      intro t
      change AffineMap.lineMap (γ (t + 1)) (g (t + 1)) τ = _
      rw [hperiod t, hgperiod t]
    obtain ⟨hfi, hfn⟩ := hstable hderiv hfperiod
      (fun t => (norm_lineMap_sub_left_le (γ t) (g t) hτ).trans_lt (hclose t))
      (fun t => (norm_lineMap_sub_left_le (deriv γ t) (deriv g t) hτ).trans_lt (hdclose t))
    exact ⟨hfi, fun t ht => (hderiv t).deriv ▸ hfn t ht⟩

theorem exists_inscribed_rounding_injOn_interpolation
    {γ : ℝ → Schoenflies.Plane} (hγ : ContDiff ℝ ∞ γ)
    (hne : ∀ t, deriv γ t ≠ 0) (hperiod : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ P : Schoenflies.PrePolygon m,
      1 / (m + 3 : ℝ) < ε ∧
      (∀ i, P.vertex i = γ ((i.val : ℝ) / (m + 3))) ∧
      let h := 1 / (m + 3 : ℝ)
      let g := DifferentialGeometry.Analysis.roundedPolygonalCurve h (h / 4)
        (fun k : ℤ => γ (k * h))
      let F := fun q : ℝ × ℝ => AffineMap.lineMap (γ q.2) (g q.2) q.1
      ContDiff ℝ ∞ F ∧ (∀ τ, Function.Periodic (fun t => F (τ, t)) 1) ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, InjOn (fun t => F (τ, t)) (Ico (0 : ℝ) 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, deriv (fun x => F (τ, x)) t ≠ 0 := by
  obtain ⟨m, P, hmesh, hp, hround⟩ :=
    exists_inscribed_rounding_injOn_interpolation_forall_width hγ hne hperiod hinj hε
  refine ⟨m, P, hmesh, hp, hround _ ?_⟩
  have hh : 0 < 1 / (m + 3 : ℝ) := by positivity
  exact ⟨by positivity, by linarith⟩

end DifferentialGeometry.Topology.Planar
