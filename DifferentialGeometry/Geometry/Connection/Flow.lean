import DifferentialGeometry.Analysis.ODE.Flow.Complete
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PrescribedTangentInOpenSet
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.ChainRule
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem covDerivAlong_mfderiv_curveAt
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (fun y : M ↦ X y))
    (x : M) (v : TangentSpace I x) (t : ℝ) :
    covDerivAlong (I := I) g
      (fun s ↦ curveAt (fun y : M ↦ X y) hcomplete x s)
      (fun s ↦ mfderiv I I
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x v) t =
      (LeviCivita (I := I) g).toFun (fun y : M ↦ X y)
        (curveAt (fun y : M ↦ X y) hcomplete x t)
        (mfderiv I I (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x v) := by
  classical
  obtain ⟨η, hηsm, _hηmem, hη0, hηv⟩ :=
    exists_smooth_curve (I := I) x v Set.univ isOpen_univ (Set.mem_univ x)
  subst x
  let f : ℝ → ℝ → M := fun r s ↦
    curveAt (fun y : M ↦ X y) hcomplete (η r) s
  have hflow :
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M ↦
          curveAt (fun y : M ↦ X y) hcomplete p.2 p.1) :=
    contMDiff_curveAt (I := I) (fun y : M ↦ X y) X.contMDiff hcomplete
  have hf_smooth :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun p : ℝ × ℝ ↦ f p.1 p.2) := by
    have hin :
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
          (𝓘(ℝ, ℝ).prod I) ∞
          (fun p : ℝ × ℝ ↦ (p.2, η p.1)) :=
      contMDiff_snd.prodMk (hηsm.comp contMDiff_fst)
    simpa only [f, Function.comp_def] using hflow.comp hin
  have hf : IsSmoothVariation (I := I) f :=
    hf_smooth.of_le
      (WithTop.coe_le_coe.2 (le_top : (8 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have htime (r s : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f r u) s : ℝ →L[ℝ] _) (1 : ℝ) =
        X (f r s) := by
    have hc := curveAt_integralCurve
      (fun y : M ↦ X y) hcomplete (η r)
    change (mfderiv 𝓘(ℝ, ℝ) I
      (fun u ↦ curveAt (fun y : M ↦ X y) hcomplete (η r) u) s :
        ℝ →L[ℝ] _) (1 : ℝ) =
        X (curveAt (fun y : M ↦ X y) hcomplete (η r) s)
    rw [(hc s).mfderiv]
    change (1 : ℝ) • X
      (curveAt (fun y : M ↦ X y) hcomplete (η r) s) = _
    exact one_smul ℝ _
  have htime_fun :
      (fun r ↦ (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f r u) t : ℝ →L[ℝ] _)
        (1 : ℝ)) =
        fun r ↦ X (f r t) :=
    funext fun r ↦ htime r t
  have htransverse : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun r ↦ f r t) := by
    have hin :
        ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
          (fun r : ℝ ↦ (r, t)) :=
      contMDiff_id.prodMk contMDiff_const
    simpa only [Function.comp_def] using hf_smooth.comp hin
  have hXmd : MDiffAt (T% (fun y : M ↦ X y)) (f 0 t) :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hspace (s : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r s) 0 : ℝ →L[ℝ] _) (1 : ℝ) =
        mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) (η 0) v := by
    have hslice : ContMDiff I I ∞
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) := by
      have hin : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞
          (fun y : M ↦ (s, y)) :=
        contMDiff_const.prodMk contMDiff_id
      simpa only [Function.comp_def] using hflow.comp hin
    have hslice_md : MDifferentiableAt I I
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) (η 0) :=
      hslice.contMDiffAt.mdifferentiableAt (by simp)
    have hηmd : MDifferentiableAt 𝓘(ℝ, ℝ) I η 0 :=
      hηsm.contMDiffAt.mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp_apply
      (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := I)
      (f := η)
      (g := fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s)
      (x := (0 : ℝ)) hslice_md hηmd (1 : ℝ)
    rw [hηv] at hcomp
    simpa only [f, Function.comp_def] using hcomp
  have hspace_fun :
      (fun s ↦ (mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r s) 0 : ℝ →L[ℝ] _)
        (1 : ℝ)) =
        fun s ↦ mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) (η 0) v :=
    funext hspace
  have hcommute := commute_ds_dt_intrinsic (I := I) g f hf t
  rw [htime_fun, covDerivAlong_restrict_eq_leviCivita
    (I := I) g (fun r ↦ f r t) (fun y : M ↦ X y) 0 htransverse hXmd] at hcommute
  have hright := hcommute.symm
  rw [hspace_fun, hspace t] at hright
  exact hright

theorem covDerivAlong_mfderiv_curveAt_eq_zero_of_parallel
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (fun y : M ↦ X y))
    (hpar : ∀ x : M,
      (LeviCivita (I := I) g).toFun (fun y : M ↦ X y) x = 0)
    (x : M) (v : TangentSpace I x) (t : ℝ) :
    covDerivAlong (I := I) g
      (fun s ↦ curveAt (fun y : M ↦ X y) hcomplete x s)
      (fun s ↦ mfderiv I I
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x v) t = 0 := by
  rw [covDerivAlong_mfderiv_curveAt, hpar]
  rfl

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
