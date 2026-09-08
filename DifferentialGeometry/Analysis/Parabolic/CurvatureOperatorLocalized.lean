import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.LogarithmicBarrier
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.TraceScalarization
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.EndomorphismReaction
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.LocalizedEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra

noncomputable section

open Bundle CovariantDerivative Filter Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology InnerProductSpace

open DifferentialGeometry.Geometry.Curvature.DimensionThree
namespace DifferentialGeometry.Analysis.Parabolic

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem curvatureOperatorReactionEndomorphism3_apply_of_least_eigenvector
    (hdim : Module.finrank ℝ V = 3) (A : V →L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) {v : V}
    (hv : A v = (⨅ w : {w : V // w ≠ 0}, A.rayleighQuotient w) • v) :
    curvatureOperatorReactionEndomorphism3 A.toLinearMap v =
      ((⨅ w : {w : V // w ≠ 0}, A.rayleighQuotient w) ^ 2 +
        hA.eigenvalues hdim 0 * hA.eigenvalues hdim 1) • v := by
  have hmin := hA.iInf_rayleighQuotient_eq_eigenvalues_last (n := 2) hdim
  have he : Fin.last 2 = (2 : Fin 3) := rfl
  rw [he] at hmin
  rw [hmin] at hv ⊢
  exact curvatureOperatorReactionEndomorphism3_apply_of_eigenvalues_last hdim A.toLinearMap hA hv

private theorem curvatureOperatorReactionEndomorphism3_inner_of_least_eigenvector
    (hdim : Module.finrank ℝ V = 3) (A : V →L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) {v : V} (hunit : ‖v‖ = 1)
    (hv : A v = (⨅ w : {w : V // w ≠ 0}, A.rayleighQuotient w) • v) :
    inner ℝ (curvatureOperatorReactionEndomorphism3 A.toLinearMap v) v =
      (⨅ w : {w : V // w ≠ 0}, A.rayleighQuotient w) ^ 2 +
        hA.eigenvalues hdim 0 * hA.eigenvalues hdim 1 := by
  rw [curvatureOperatorReactionEndomorphism3_apply_of_least_eigenvector hdim A hA hv]
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hunit, one_pow, mul_one]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem cutoff_negative_minimum_eigenvalue_reaction_inequality_at_spacetime_max
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {t : ℝ} (ht : 0 < t)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (x : M) (hx : I.IsInteriorPoint x)
    (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hdim : Module.finrank ℝ (V x) = 3)
    (hPDE : letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
      HasDerivWithinAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
            (fun y => A t y) x (X t x) +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap)
        (Icc 0 t) t)
    (hA : (A t x).toLinearMap.IsSymmetric)
    (hneg : (⨅ v : {v : V x // v ≠ 0}, (A t x).rayleighQuotient v) < 0)
    (χ φ : ℝ → M → ℝ)
    (hφχ : ∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x),
      0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ χ p.1 p.2)
    (hφeq : φ t x = χ t x)
    (hφtime : DifferentiableWithinAt ℝ (fun q => φ q x) (Icc 0 t) t)
    (hφspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hφgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (φ t) y) x)
    (hmax : IsLocalMaxOn (fun p : ℝ × M => χ p.1 p.2 *
      max (-(⨅ w : {w : V p.2 // w ≠ 0}, (A p.1 p.2).rayleighQuotient w)) 0)
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x)) :
    letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
    φ t x ^ 2 * (ν ^ 2 + hA.eigenvalues hdim 0 * hA.eigenvalues hdim 1) +
      ν * φ t x * parabolicOperatorWithDrift (I := I) G t X φ t x +
      2 * ν * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
        (gradientAt (I := I) G t (φ t) x) ≤ 0 := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  obtain ⟨v, _, hunit, heigen, hineq⟩ :=
    exists_cutoff_negative_minimum_eigenvalue_parabolic_inequality_at_spacetime_max
      (I := I) G cov hcov ht A x hx X hGconn hPDE.differentiableWithinAt hA hneg
      χ φ hφχ hφeq hφtime hφspace hφgrad hmax
  have hder := hPDE.derivWithin ((uniqueDiffOn_Icc ht).uniqueDiffWithinAt ⟨ht.le, le_rfl⟩)
  rw [hder] at hineq
  have hres :
      rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
            (fun y => A t y) x (X t x) +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap -
        rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x -
        HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
          (fun y => A t y) x (X t x) =
      (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap := by
    abel
  rw [hres] at hineq
  have hreact := curvatureOperatorReactionEndomorphism3_inner_of_least_eigenvector
    hdim (A t x) hA hunit.self_of_nhds heigen
  change inner ℝ
    ((curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap
      (v x)) (v x) = _ at hreact
  rw [hreact] at hineq
  exact hineq


theorem hamilton_ivey_scalar_reaction_ge_at_logarithmic_boundary
    [BoundarylessManifold I M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (v : Cₛ^∞⟮I; F, V⟯) (x : M)
    (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hdim : Module.finrank ℝ (V x) = 3)
    (hPDE : letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
      HasDerivWithinAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
            (fun y => A t y) x (X t x) +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap)
        (Icc 0 T) t)
    (hA : (A t x).toLinearMap.IsSymmetric)
    (heigen : A t x (v x) =
      (⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w) • v x)
    (hv : cov v x = 0) (hunit : ∀ᶠ y in 𝓝 x, ‖v y‖ = 1)
    (hneg : (⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w) < 0)
    {b : ℝ}
    (hboundary : LinearMap.trace ℝ (V x) (A t x).toLinearMap =
      (-(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w)) * (b - 1)) :
    (⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w) ^ 2 ≤
      parabolicOperatorWithDrift (I := I) G T X
        (fun s y => LinearMap.trace ℝ (V y) (A s y).toLinearMap) t x -
      b * parabolicOperatorWithDrift (I := I) G T X
        (fun s y => -inner ℝ (A s y (v y)) (v y)) t x := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let Q := (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap
  have hder := hPDE.derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)
  have hres : derivWithin (fun s => A s x) (Icc 0 T) t -
      rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x -
      HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
        (fun y => A t y) x (X t x) = Q := by
    rw [hder]
    change _ + _ + Q - _ - _ = Q
    abel
  have htrace := parabolicOperatorWithDrift_trace G cov hcov inferInstance hT ht A x X
    hGconn hPDE.differentiableWithinAt
  rw [hres] at htrace
  have hunit' : ∀ᶠ y in 𝓝 x, inner ℝ (v y) (v y) = 1 := by
    filter_upwards [hunit] with y hy
    simp only [real_inner_self_eq_norm_sq, hy, one_pow]
  have hinner := parabolicOperatorWithDrift_inner_endomorphism_apply_of_normal_eigenvector
    G cov hcov hT ht A v x BoundarylessManifold.isInteriorPoint X hGconn hPDE.differentiableWithinAt hA heigen hv hunit'
  rw [hres] at hinner
  have hutime : DifferentiableWithinAt ℝ
      (fun s => inner ℝ (A s x (v x)) (v x)) (Icc 0 T) t :=
    (hPDE.differentiableWithinAt.clm_apply (differentiableWithinAt_const (v x))).inner ℝ
      (differentiableWithinAt_const (v x))
  have huspace : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => inner ℝ (A t y (v y)) (v y)) :=
    (ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff v.contMDiff).inner_bundle v.contMDiff
  have hnegP := parabolic_neg G T X (fun s y => inner ℝ (A s y (v y)) (v y)) t x hutime
    (fun y => huspace.mdifferentiableAt (by simp))
    ((gradientFun_smooth (G.metric t) huspace).mdifferentiableAt (by simp))
  rw [htrace, hnegP, hinner]
  have hmin : (⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w) =
      hA.eigenvalues hdim 2 := hA.iInf_rayleighQuotient_eq_eigenvalues_last (n := 2) hdim
  have halg := hamilton_ivey_reaction_inner_ge_at_logarithmic_boundary
    hdim (A t x) hA hunit.self_of_nhds
      (hmin ▸ heigen) (hmin ▸ hneg) (hmin ▸ hboundary)
  rw [← hmin] at halg
  change _ ≤ LinearMap.trace ℝ (V x) Q.toLinearMap + b * inner ℝ (Q (v x)) (v x) at halg
  linarith


theorem cutoff_hamilton_ivey_bound_at_time_and_space_min
    [BoundarylessManifold I M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {t : ℝ} (ht : 0 < t)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (x : M) (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hdim : Module.finrank ℝ (V x) = 3)
    (hPDE : letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
      HasDerivWithinAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
            (fun y => A t y) x (X t x) +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap)
        (Icc 0 t) t)
    (hA : (A t x).toLinearMap.IsSymmetric)
    (hneg : (⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w) < 0)
    (χ φ : ℝ → M → ℝ) (c : ℝ → ℝ)
    (hφχ : ∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), φ p.1 p.2 ≤ χ p.1 p.2)
    (hφeq : φ t x = χ t x) (hχpos : 0 < χ t x)
    (hφtime : DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t)
    (hφspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hφgrad : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (φ t) y) x)
    (hctime : DifferentiableWithinAt ℝ c (Icc 0 t) t)
    (hslope : 0 < Real.log (χ t x * (-(⨅ w : {w : V x // w ≠ 0},
      (A t x).rayleighQuotient w))) + c t + 1)
    (hboundary : LinearMap.trace ℝ (V x) (A t x).toLinearMap =
      (-(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w)) *
        (Real.log (χ t x * (-(⨅ w : {w : V x // w ≠ 0},
          (A t x).rayleighQuotient w))) + c t))
    (htimemin : IsLocalMinOn (fun s =>
      χ s x * LinearMap.trace ℝ (V x) (A s x).toLinearMap -
      (χ s x * max (-(⨅ w : {w : V x // w ≠ 0}, (A s x).rayleighQuotient w)) 0) *
        (Real.log (χ s x * max (-(⨅ w : {w : V x // w ≠ 0},
          (A s x).rayleighQuotient w)) 0) + c s)) (Icc 0 t) t)
    (hspacemin : IsLocalMin (fun y =>
      χ t y * LinearMap.trace ℝ (V y) (A t y).toLinearMap -
      (χ t y * max (-(⨅ w : {w : V y // w ≠ 0}, (A t y).rayleighQuotient w)) 0) *
        (Real.log (χ t y * max (-(⨅ w : {w : V y // w ≠ 0},
          (A t y).rayleighQuotient w)) 0) + c t)) x)
    {δ ε : ℝ}
    (hφpar : parabolicOperatorWithDrift (I := I) G t X φ t x ≤ δ)
    (hφsq : (G.metric t).inner x
      (gradientAt (I := I) G t (φ t) x) (gradientAt (I := I) G t (φ t) x) ≤ ε * φ t x) :
    φ t x * (-(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w)) ≤
      δ + 2 * ε + φ t x * derivWithin c (Icc 0 t) t := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let r : ℝ → M → ℝ := fun s y => LinearMap.trace ℝ (V y) (A s y).toLinearMap
  let L₀ : (V x →L[ℝ] V x) →ₗ[ℝ] ℝ :=
    { toFun := fun B => LinearMap.trace ℝ (V x) B.toLinearMap
      map_add' := by intro B C; simp
      map_smul' := by intro a B; simp }
  let L : (V x →L[ℝ] V x) →L[ℝ] ℝ := L₀.toContinuousLinearMap
  have hrtime : DifferentiableWithinAt ℝ (fun s => r s x) (Icc 0 t) t :=
    (L.hasFDerivAt.comp_hasDerivWithinAt t hPDE).differentiableWithinAt
  have hrsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (r t) :=
    contMDiff_linearMap_trace (fun y => A t y) (A t).contMDiff
  obtain ⟨v, hv, hunit, heigen, heq, hsuptime, hsupspace⟩ :=
    exists_cutoff_logarithmic_minimum_eigenvalue_upper_support cov hcov
      (show t ∈ Icc 0 t from ⟨ht.le, le_rfl⟩) A x hPDE.continuousWithinAt hA hneg r χ φ c
      hrtime.continuousWithinAt hrsmooth.continuous.continuousAt hφtime.continuousWithinAt
      hφspace.self_of_nhds.continuousAt hctime.continuousWithinAt hφχ hφeq hχpos hslope hboundary
  let q : ℝ → M → ℝ := fun s y => -inner ℝ (A s y (v y)) (v y)
  have hqeq : q t x = -(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w) := by
    simp only [q, heigen, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hunit.self_of_nhds, one_pow, mul_one]
  have hqtime : DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 t) t :=
    ((hPDE.differentiableWithinAt.clm_apply (differentiableWithinAt_const (v x))).inner ℝ
      (differentiableWithinAt_const (v x))).neg
  have hqsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (q t) :=
    ((ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff v.contMDiff).inner_bundle v.contMDiff).neg
  have hφpos : 0 < φ t x := by rw [hφeq]; exact hχpos
  have hqpos : 0 < q t x := by rw [hqeq]; exact neg_pos.mpr hneg
  have hb : r t x = q t x * (Real.log (φ t x * q t x) + c t) := by
    rw [hqeq, hφeq]
    exact hboundary
  have htime : IsLocalMinOn
      (fun s => φ s x * r s x - (φ s x * q s x) * (Real.log (φ s x * q s x) + c s))
      (Icc 0 t) t := by
    filter_upwards [htimemin, hsuptime] with s hs hsup
    exact heq.trans_le (hs.trans hsup)
  have hspace : IsLocalMin
      (fun y => φ t y * r t y - (φ t y * q t y) * (Real.log (φ t y * q t y) + c t)) x := by
    filter_upwards [hspacemin, hsupspace] with y hy hsup
    exact heq.trans_le (hy.trans hsup)
  have hreact := hamilton_ivey_scalar_reaction_ge_at_logarithmic_boundary G cov hcov ht
    (show t ∈ Icc 0 t from ⟨ht.le, le_rfl⟩) A v x X hGconn hdim hPDE hA heigen hv hunit hneg
    (b := Real.log (φ t x * q t x) + c t + 1) (by rw [← hqeq]; dsimp only [r] at hb; linarith [hb])
  have hreaction : (1 : ℝ) * q t x ^ 2 ≤ parabolicOperatorWithDrift (I := I) G t X r t x -
      (Real.log (φ t x * q t x) + c t + 1) * parabolicOperatorWithDrift (I := I) G t X q t x := by
    change _ ≤ _ - _ * parabolicOperatorWithDrift (I := I) G t X q t x at hreact
    rw [hqeq] at hreact ⊢
    simpa only [one_mul, neg_sq] using hreact
  have hbound := cutoff_logarithmic_reaction_bound_at_time_and_space_min G X r q φ c ht x
    BoundarylessManifold.isInteriorPoint hrtime hqtime hφtime hctime
    (Eventually.of_forall fun y => hrsmooth.mdifferentiableAt (by simp))
    (Eventually.of_forall fun y => hqsmooth.mdifferentiableAt (by simp)) hφspace
    ((gradientFun_smooth (G.metric t) hrsmooth).mdifferentiableAt (by simp))
    ((gradientFun_smooth (G.metric t) hqsmooth).mdifferentiableAt (by simp)) hφgrad
    hφpos hqpos hb htime hspace hreaction hφpar hφsq
  simpa only [one_mul, hqeq] using hbound

end DifferentialGeometry.Analysis.Parabolic
