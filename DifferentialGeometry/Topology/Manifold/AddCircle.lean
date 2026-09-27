import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import DifferentialGeometry.Topology.Manifold.ChartedSpaceHomeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

instance instChartedSpaceUnitAddCircle :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle (1 : ℝ)) :=
  (homeomorphCircle (T := (1 : ℝ)) (by norm_num)).symm.chartedSpace

instance instIsManifoldUnitAddCircle : IsManifold (𝓡 1) ∞ (AddCircle (1 : ℝ)) := by
  have hcirc : IsManifold (𝓡 1) ∞ Circle := IsManifold.of_le (le_top : (∞ : ℕ∞ω) ≤ ω)
  exact DifferentialGeometry.Manifold.isManifold_homeomorphChartedSpace (I := 𝓡 1) (n := ∞)
    (M := Circle) (f := (homeomorphCircle (T := (1 : ℝ)) (by norm_num)).symm)

noncomputable def euclideanSpaceFinOneContinuousLinearEquivReal :
    EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

noncomputable def euclideanSpaceFinOneHomeomorphReal : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
  euclideanSpaceFinOneContinuousLinearEquivReal.toHomeomorph

instance instChartedSpaceRealUnitAddCircle : ChartedSpace ℝ (AddCircle (1 : ℝ)) :=
  DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := AddCircle (1 : ℝ))
    euclideanSpaceFinOneHomeomorphReal

instance instIsManifoldRealUnitAddCircle : IsManifold 𝓘(ℝ, ℝ) ∞ (AddCircle (1 : ℝ)) :=
  DifferentialGeometry.Manifold.isManifold_transHomeomorph (I := 𝓡 1) (J := 𝓘(ℝ, ℝ))
    euclideanSpaceFinOneHomeomorphReal euclideanSpaceFinOneContinuousLinearEquivReal
    (fun _ => rfl)


private lemma homeomorphCircle_coe (t : ℝ) :
    homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ))
      = Circle.exp (2 * Real.pi * t) := by
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring

theorem contMDiff_coe :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => (t : AddCircle (1 : ℝ))) := by
  have hGt : ∀ t : ℝ,
      homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ))
        = Circle.exp (2 * Real.pi * t) := fun t => homeomorphCircle_coe t
  have hf : ContMDiff (𝓡 1) (𝓡 1) ∞
      ((homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm : Circle → AddCircle (1 : ℝ)) :=
    DifferentialGeometry.Manifold.contMDiff_homeomorphChartedSpace (𝓡 1)
      (homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
  have hcomp : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
      ((homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
        ∘ fun t : ℝ => Circle.exp (2 * Real.pi * t)) :=
    hf.comp (contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff)
  have heq : ((homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
        ∘ fun t : ℝ => Circle.exp (2 * Real.pi * t))
      = fun t : ℝ => (t : AddCircle (1 : ℝ)) := by
    funext t
    rw [Function.comp_apply, ← hGt t, Homeomorph.symm_apply_apply]
  have hsphere : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun t : ℝ => (t : AddCircle (1 : ℝ))) :=
    hcomp.congr fun t => (congrFun heq t).symm
  exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
    (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)) euclideanSpaceFinOneHomeomorphReal
    euclideanSpaceFinOneContinuousLinearEquivReal (fun _ => rfl) (I₀ := 𝓘(ℝ, ℝ))).mpr hsphere

private lemma bijective_mfderiv_circleExp [Fact (Module.finrank ℝ ℂ = 1 + 1)] (t : ℝ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t) := by
  set w : Metric.sphere (0 : ℂ) 1 := Circle.exp (2 * Real.pi * t) with hw
  set A := mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) w with hA
  set B := mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
    (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t with hB
  set c : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) with hcdef
  have hderiv : HasDerivAt (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) c t := by
    rw [hcdef]
    have hR : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
    exact ((hR.ofReal_comp).mul_const Complex.I).cexp
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (mul_ne_zero (by exact_mod_cast (by positivity : (2 : ℝ) * Real.pi ≠ 0)) Complex.I_ne_zero)
  have hCval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t
      = ContinuousLinearMap.toSpanSingleton ℝ c := by
    rw [mfderiv_eq_fderiv, hderiv.hasFDerivAt.fderiv]
  have hspan : Function.Injective (ContinuousLinearMap.toSpanSingleton ℝ c) := by
    intro x y hxy
    rw [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.toSpanSingleton_apply] at hxy
    have h : (x - y) • c = 0 := by rw [sub_smul, hxy, sub_self]
    rcases smul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc
  have hCwide : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t) := by
    intro x y hxy
    exact hspan (by rw [← hCval]; exact hxy)
  have hclosure : (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) ∘
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1))
      = fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
    funext s
    rfl
  have hgw : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) w :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hft : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t :=
    ((contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
        (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)))).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t = A.comp B := by
    rw [← hclosure, hA, hB]
    exact mfderiv_comp t hgw hft
  have hBinj : Function.Injective B := fun x y hxy => by
    apply hCwide
    rw [hchain]
    exact congrArg A hxy
  have hfin : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℝ) t)
      = Module.finrank ℝ (TangentSpace (𝓡 1) w) :=
    (Module.finrank_self ℝ).trans
      ((finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 1)).trans (Fintype.card_fin 1)).symm
  exact ⟨hBinj, (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank ℝ
    (TangentSpace 𝓘(ℝ, ℝ) t) _ _ _ (TangentSpace (𝓡 1) w) _ _
    (inferInstanceAs (FiniteDimensional ℝ ℝ))
    (inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1))))
    hfin (f := B.toLinearMap)).mp hBinj⟩

theorem bijective_mfderiv_coe (t : ℝ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) t) := by
  let _ := (Complex.finrank_real_complex_fact : Fact (Module.finrank ℝ ℂ = 1 + 1))
  let G : AddCircle (1 : ℝ) ≃ₜ Circle := homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hGt : ∀ s : ℝ, G (s : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * s) :=
    fun s => homeomorphCircle_coe s
  have hB : Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t) :=
    bijective_mfderiv_circleExp t
  have hGs : Function.Bijective (mfderiv (𝓡 1) (𝓡 1)
      (G.symm : Circle → AddCircle (1 : ℝ)) (Circle.exp (2 * Real.pi * t))) :=
    DifferentialGeometry.Manifold.bijective_mfderiv_homeomorphChartedSpace (𝓡 1) G.symm _
  have hfun : (G.symm : Circle → AddCircle (1 : ℝ)) ∘
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1))
      = fun s : ℝ => (s : AddCircle (1 : ℝ)) := by
    funext s
    rw [Function.comp_apply, ← hGt s]
    exact Homeomorph.symm_apply_apply G (s : AddCircle (1 : ℝ))
  have hg : MDifferentiableAt (𝓡 1) (𝓡 1)
      (G.symm : Circle → AddCircle (1 : ℝ)) (Circle.exp (2 * Real.pi * t)) :=
    (DifferentialGeometry.Manifold.contMDiff_homeomorphChartedSpace (𝓡 1) G.symm).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t :=
    ((contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
        (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)))).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hX : Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) t) := by
    rw [← hfun, mfderiv_comp t hg hf]
    exact hGs.comp hB
  exact (DifferentialGeometry.Manifold.bijective_mfderiv_chartedSpaceTransHomeomorph_iff
    (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)) euclideanSpaceFinOneHomeomorphReal
    euclideanSpaceFinOneContinuousLinearEquivReal (fun _ => rfl) (I₀ := 𝓘(ℝ, ℝ))
    (f := fun s : ℝ => (s : AddCircle (1 : ℝ))) (x := t)).mpr hX

end AddCircle

end
