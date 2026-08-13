import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import DifferentialGeometry.Geometry.Operator.Operators
import DifferentialGeometry.Geometry.Curvature.Realized.TimeInterval

noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem hasDerivAt_comp_mfderiv_along
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (gamma : ℝ → M) (t : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (gamma t))
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t) :
    HasDerivAt (fun s => f (gamma s))
      (NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I 𝓘(ℝ, ℝ) f (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)))) t := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have hcomp := hf.hasMFDerivAt.comp t hgamma.hasMFDerivAt
  have hcomp' := hcomp.hasFDerivAt
  convert hcomp' using 1
  change ContinuousLinearMap.toSpanSingleton Real
      (((mfderiv I 𝓘(ℝ, ℝ) f (gamma t)).comp
        (mfderiv 𝓘(ℝ, ℝ) I gamma t)) (1 : ℝ)) = _
  exact ContinuousLinearMap.toSpanSingleton_apply_map_one
    (R₁ := Real) (M₂ := Real) _

omit [FiniteDimensional ℝ E] in
theorem deriv_comp_mfderiv_along
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (gamma : ℝ → M) (t : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (gamma t))
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t) :
    deriv (fun s => f (gamma s)) t =
      NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I 𝓘(ℝ, ℝ) f (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) :=
  (hasDerivAt_comp_mfderiv_along I f gamma t hf hgamma).deriv

theorem deriv_along_curve_eq
    (g : SmoothRiemannianMetric I M)
    {F : ℝ → M → ℝ}
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => F p.1 p.2))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {t : ℝ} :
    deriv (fun s => F s (γ s)) t =
      deriv (fun s => F s (γ t)) t +
        g.inner (γ t) (gradientFun (I := I) g (F t) (γ t))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
  classical
  have hJ : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞ (fun s : ℝ => (s, γ s)) :=
    contMDiff_id.prodMk hγ
  have hFmd : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
      (fun p : ℝ × M => F p.1 p.2) (t, γ t) :=
    hF.mdifferentiableAt (x := (t, γ t)) (by norm_num)
  have hJmd : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
      (fun s : ℝ => (s, γ s)) t :=
    hJ.mdifferentiableAt (x := t) (by norm_num)
  have hJderiv0 : (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) (fun s : ℝ => (s, γ s)) t) (1 : ℝ) =
      ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
    have hid : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t :=
      (contMDiff_id (n := ∞) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s)).mdifferentiableAt
        (by norm_num)
    have hJhas : HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
        (fun s : ℝ => (s, γ s)) t
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t).prod
          (mfderiv 𝓘(ℝ, ℝ) I γ t)) := by
      exact HasMFDerivAt.prodMk hid.hasMFDerivAt
        (hγ.mdifferentiableAt (x := t) (by simp)).hasMFDerivAt
    have hJderiv := hJhas.mfderiv
    rw [hJderiv]
    simp [mfderiv_eq_fderiv]
    rfl
  have hcurve0 : HasDerivAt (fun s => F s (γ s))
      (NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) (fun s : ℝ => (s, γ s)) t (1 : ℝ)))) t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    have hcomp := hFmd.hasMFDerivAt.comp t hJmd.hasMFDerivAt
    have hcomp' := hcomp.hasFDerivAt
    convert hcomp' using 1
    change ContinuousLinearMap.toSpanSingleton Real
        (((mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) (fun s : ℝ => (s, γ s)) t)) (1 : ℝ)) = _
    exact ContinuousLinearMap.toSpanSingleton_apply_map_one (R₁ := Real) (M₂ := Real) _
  have hcurve : HasDerivAt (fun s => F s (γ s))
      (NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) t := by
    simpa [hJderiv0] using hcurve0
  have hmain' : deriv (fun s => F s (γ s)) t =
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) :=
    hcurve.deriv
  rw [hmain']
  have hdec := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (f := fun p : ℝ × M => F p.1 p.2) (p := (t, γ t))
    (v := ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
    (hF.mdifferentiableAt (x := (t, γ t)) (by simp))
  rw [hdec]
  have hlin : NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t (1 : ℝ) +
          mfderiv I 𝓘(ℝ, ℝ) (F t) (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) =
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t (1 : ℝ)) +
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv I 𝓘(ℝ, ℝ) (F t) (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) := by
    simp [NormedSpace.fromTangentSpace, map_add]
  rw [hlin]
  congr 1
  · have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t :=
      (hF.comp (contMDiff_id.prodMk (contMDiff_const (c := γ t)))).mdifferentiableAt
        (x := t) (by norm_num)
    have hd : deriv (fun s : ℝ => F s (γ t)) t =
        NormedSpace.fromTangentSpace (F t (γ t))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t (1 : ℝ)) := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun s : ℝ => F s (γ t)) t =
        (fderiv ℝ (fun s : ℝ => F s (γ t)) t) (1 : ℝ)
      rw [fderiv_apply_one_eq_deriv (f := fun s : ℝ => F s (γ t)) (x := t)]
    exact hd.symm
  · have hinner := inner_gradientFun (I := I) g (F t) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
    symm
    exact hinner

theorem deriv_along_curve_eq_on
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    {F : ℝ → M → ℝ}
    (hF : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => F p.1 p.2)
      (D.regular ×ˢ univ))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {t : ℝ} (ht : t ∈ D.regular) :
    deriv (fun s => F s (γ s)) t =
      deriv (fun s => F s (γ t)) t +
        g.inner (γ t) (gradientFun (I := I) g (F t) (γ t))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
  classical
  have hJ : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞ (fun s : ℝ => (s, γ s)) :=
    contMDiff_id.prodMk hγ
  have hFmd : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
      (fun p : ℝ × M => F p.1 p.2) (t, γ t) := by
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (t, γ t) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨ht, trivial⟩
    exact (hF.contMDiffAt hnh).mdifferentiableAt (by norm_num)
  have hJmd : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
      (fun s : ℝ => (s, γ s)) t :=
    hJ.mdifferentiableAt (x := t) (by norm_num)
  have hJderiv0 : (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) (fun s : ℝ => (s, γ s)) t) (1 : ℝ) =
      ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
    have hid : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t :=
      (contMDiff_id (n := ∞) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s)).mdifferentiableAt
        (by norm_num)
    have hJhas : HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
        (fun s : ℝ => (s, γ s)) t
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t).prod
          (mfderiv 𝓘(ℝ, ℝ) I γ t)) := by
      exact HasMFDerivAt.prodMk hid.hasMFDerivAt
        (hγ.mdifferentiableAt (x := t) (by simp)).hasMFDerivAt
    have hJderiv := hJhas.mfderiv
    rw [hJderiv]
    simp [mfderiv_eq_fderiv]
    rfl
  have hcurve0 : HasDerivAt (fun s => F s (γ s))
      (NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) (fun s : ℝ => (s, γ s)) t (1 : ℝ)))) t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    have hcomp := hFmd.hasMFDerivAt.comp t hJmd.hasMFDerivAt
    have hcomp' := hcomp.hasFDerivAt
    convert hcomp' using 1
    change ContinuousLinearMap.toSpanSingleton Real
        (((mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) (fun s : ℝ => (s, γ s)) t)) (1 : ℝ)) = _
    exact ContinuousLinearMap.toSpanSingleton_apply_map_one (R₁ := Real) (M₂ := Real) _
  have hcurve : HasDerivAt (fun s => F s (γ s))
      (NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) t := by
    simpa [hJderiv0] using hcurve0
  have hmain' : deriv (fun s => F s (γ s)) t =
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) :=
    hcurve.deriv
  rw [hmain']
  have hdec := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (f := fun p : ℝ × M => F p.1 p.2) (p := (t, γ t))
    (v := ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
    hFmd
  rw [hdec]
  have hlin : NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t (1 : ℝ) +
          mfderiv I 𝓘(ℝ, ℝ) (F t) (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) =
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t (1 : ℝ)) +
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv I 𝓘(ℝ, ℝ) (F t) (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) := by
    simp [NormedSpace.fromTangentSpace, map_add]
  rw [hlin]
  congr 1
  · have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t := by
      have hnh : D.regular ×ˢ univ ∈ 𝓝 (t, γ t) :=
        (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨ht, trivial⟩
      have hFat : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => F p.1 p.2) (t, γ t) := hF.contMDiffAt hnh
      have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => F s (γ t)) t :=
        hFat.comp (x := t) (contMDiffAt_id.prodMk contMDiffAt_const)
      exact ContMDiffAt.mdifferentiableAt hsliceAt (by norm_num)
    have hd : deriv (fun s : ℝ => F s (γ t)) t =
        NormedSpace.fromTangentSpace (F t (γ t))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t (1 : ℝ)) := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun s : ℝ => F s (γ t)) t =
        (fderiv ℝ (fun s : ℝ => F s (γ t)) t) (1 : ℝ)
      rw [fderiv_apply_one_eq_deriv (f := fun s : ℝ => F s (γ t)) (x := t)]
    exact hd.symm
  · have hinner := inner_gradientFun (I := I) g (F t) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
    symm
    exact hinner

end DifferentialGeometry.Analysis.Calculus

end
