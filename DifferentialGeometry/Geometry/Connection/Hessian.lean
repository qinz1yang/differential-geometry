import DifferentialGeometry.Geometry.Connection.AlongCurveHom
import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

def hessian (cov : CovariantDerivative I F V)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    (σ : ∀ x, V x) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
    I M E (TangentSpace I) F V base cov (cov σ) x

theorem hessian_apply (cov : CovariantDerivative I F V)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    {σ : ∀ x, V x} {Y : ∀ x, TangentSpace I x} {x : M}
    (hDσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun y => (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] F)
        (fun y => TangentSpace I y →L[ℝ] V y))) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (X : TangentSpace I x) :
    cov.hessian base σ x X (Y x) =
      cov (fun y => cov σ y (Y y)) x X - cov σ x (base Y x X) := by
  let W := FiberBundle.extend E X
  have hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% W) x :=
    FiberBundle.mdifferentiableAt_extend ..
  have hWx : W x = X := by simp [W]
  rw [hessian, ← hWx]
  exact
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M E (TangentSpace I) F V base cov (cov σ) hDσ hW hY

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

theorem hessian_apply_of_contMDiffAt (cov : CovariantDerivative I F V)
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    {σ : ∀ x, V x} {Y : ∀ x, TangentSpace I x} {x : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (X : TangentSpace I x) :
    cov.hessian base σ x X (Y x) =
      cov (fun y => cov σ y (Y y)) x X - cov σ x (base Y x X) := by
  exact cov.hessian_apply base
    ((hcov.contMDiffAt (m := 1) hσ (by norm_num)).mdifferentiableAt (by simp)) hY X

theorem derivAlongWithin_derivAlongWithin_section
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {σ : ∀ x, V x} {J : Set ℝ} {t : ℝ}
    (hJ : J ∈ 𝓝 t)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) (γ t)) :
    let velocity := fun r => mfderivWithin 𝓘(ℝ, ℝ) I γ J r
      ((NormedSpace.fromTangentSpace r).symm 1)
    cov.derivAlongWithin γ
        (fun r => cov.derivAlongWithin γ (fun u => σ (γ u)) J r) J t =
      cov.hessian base σ (γ t) (velocity t) (velocity t) +
        cov σ (γ t) (base.derivAlongWithin γ velocity J t) := by
  dsimp only
  let velocity := fun r => mfderivWithin 𝓘(ℝ, ℝ) I γ J r
    ((NormedSpace.fromTangentSpace r).symm 1)
  have hDσ := (hcov.contMDiffAt (m := 1) hσ (by norm_num)).mdifferentiableAt (by simp)
  have hDγ := hγ.mdifferentiableAt (by norm_num)
  have hA : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun r => (⟨γ r, cov σ (γ r)⟩ : TotalSpace (E →L[ℝ] F)
        (fun x => TangentSpace I x →L[ℝ] V x))) J t :=
    (hDσ.comp t hDγ).mdifferentiableWithinAt
  have hv : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
      (fun r => (⟨γ r, velocity r⟩ : TangentBundle I M)) J t := by
    have h := hγ.time_mfderiv (m := 1) (by norm_num)
    apply MDifferentiableAt.mdifferentiableWithinAt
    apply (h.mdifferentiableAt (by simp)).congr_of_eventuallyEq
    filter_upwards [eventually_mem_nhds_iff.mpr hJ] with r hr
    simp only [velocity, mfderivWithin_of_mem_nhds hr]
  have hσnear : ∀ᶠ y in 𝓝 (γ t), MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hσ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))).mono
      (fun _ hy => hy.mdifferentiableAt (by simp))
  have hγnear : ∀ᶠ r in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hγ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))).mono
      (fun _ hr => hr.mdifferentiableAt (by simp))
  have heq : ∀ᶠ r in 𝓝 t,
      cov.derivAlongWithin γ (fun u => σ (γ u)) J r = cov σ (γ r) (velocity r) := by
    filter_upwards [hγ.continuousAt hσnear, hγnear] with r hσr hγr
    exact cov.derivAlongWithin_section hγr.mdifferentiableWithinAt hσr
  rw [cov.derivAlongWithin_congr_of_eventuallyEq
    (heq.filter_mono nhdsWithin_le_nhds)
    (cov.derivAlongWithin_section hDγ.mdifferentiableWithinAt
      (hσ.mdifferentiableAt (by norm_num)))]
  rw [derivAlongWithin_clm_apply base cov γ (fun r => cov σ (γ r)) velocity hA hv]
  rw [derivAlongWithin_section _ hDγ.mdifferentiableWithinAt hDσ]
  rfl

end CovariantDerivative
