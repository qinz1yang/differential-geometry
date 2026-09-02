import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricFirstOrder
import DifferentialGeometry.Geometry.Comparison.DistanceExhaustion
import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Analysis.Elliptic.MetricBounds

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
    [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
private theorem differential_normSq_eq_gradient_sq
    (g : SmoothRiemannianMetric I M) (f : M → Real) (x : M) :
    normSq0S (I := I) g x 1 (differential1FormFun (I := I) f x) =
      g.inner x (gradientFun (I := I) g f x)
        (gradientFun (I := I) g f x) := by
  have hsharp :
      cotangentSharp (I := I) g x (differential1FormFun (I := I) f x) =
        gradientFun (I := I) g f x := by
    apply tangentFlatLinear_injective (I := I) g x
    ext v
    change g.inner x
        (cotangentSharp (I := I) g x (differential1FormFun (I := I) f x)) v =
      g.inner x (gradientFun (I := I) g f x) v
    rw [cotangentSharp_inner, cotangentToDual_apply]
    exact differential1FormFun_apply_eq_inner_gradientFun (I := I) g f x v
  rw [normSq0S_eq_inner, inner0S_one_eq_cotangent, cotangentInner_eq_sharp,
    hsharp]

omit [NeZero (Module.finrank Real E)] [IsManifold I 1 M] [SigmaCompactSpace M] in
private theorem support_bounds_of_metric_first_order
    (g0 gt : SmoothRiemannianMetric I M)
    {Lambda C0 C1 : Real}
    (hLambda : 1 ≤ Lambda)
    (hC0 : 0 ≤ C0)
    (hC1 : 0 ≤ C1)
    (hequiv : MetricUniformEquivalentOn (I := I) Set.univ g0 gt Lambda)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gt g0 C1)
    {f : M → Real} {U : Set M} {x : M}
    (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U)
    (hx : x ∈ U)
    (hgrad : g0.inner x (gradientFun (I := I) g0 f x)
        (gradientFun (I := I) g0 f x) ≤ C0)
    (hhess : ∀ v : TangentSpace I x,
      hessFun (I := I) g0 f x v v ≤ C0 * g0.inner x v v) :
    Real.sqrt (gt.inner x (gradientFun (I := I) gt f x)
        (gradientFun (I := I) gt f x)) ≤ Real.sqrt (Lambda * C0) ∧
      laplacian (I := I) (LeviCivita (I := I) gt) gt f x ≤
        (Module.finrank Real E : Real) *
          (C0 * Lambda + Real.sqrt C0 *
            ((3 / 2 : Real) * Lambda ^ 3 * C1 * Lambda)) := by
  classical
  have hLambda0 : 0 ≤ Lambda := le_trans zero_le_one hLambda
  have hgradient :
      Real.sqrt (gt.inner x (gradientFun (I := I) gt f x)
          (gradientFun (I := I) gt f x)) ≤ Real.sqrt (Lambda * C0) := by
    have hnorm := normSq0S_upper_le_of_equiv
      (I := I) g0 gt x 1 hLambda (hequiv.2 x (Set.mem_univ x))
      (differential1FormFun (I := I) f x)
    rw [differential_normSq_eq_gradient_sq (I := I) gt f x,
      differential_normSq_eq_gradient_sq (I := I) g0 f x, pow_one] at hnorm
    exact (Real.sqrt_le_sqrt hnorm).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hgrad hLambda0))
  refine ⟨hgradient, ?_⟩
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gt x
  have hinv : MetricInverseInBasisGen (I := I) gt x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) gt basis hON
  have hlap :
      laplacian (I := I) (LeviCivita (I := I) gt) gt f x =
        ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
          hessFun (I := I) gt f x (basis i) (basis i) := by
    rw [lap_eq_hess_on (I := I) gt hU hf hx,
      metricTracePair0SAt_eq_sum_basis (I := I) gt basis
        (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
        hinv (hessTensorAt (I := I) gt f x)]
    simp only [hessTensorAt_apply, identityInvMetric, diagonalInvMetric]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  rw [hlap]
  let A : Real := (3 / 2 : Real) * Lambda ^ 3 * C1
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hsymm : MetricUniformEquivalentOn (I := I) Set.univ gt g0 Lambda :=
    metricUniformEquivalentOn_symm (I := I) hequiv
  have hone (i : Fin (Module.finrank Real (TangentSpace I x))) :
      gt.inner x (basis i) (basis i) = 1 := by
    simpa using hON i i
  have hdiag : ∀ i : Fin (Module.finrank Real (TangentSpace I x)),
      hessFun (I := I) gt f x (basis i) (basis i) ≤
        C0 * Lambda + Real.sqrt C0 * (A * Lambda) := by
    intro i
    let e : TangentSpace I x := basis i
    let Dv : TangentSpace I x :=
      (CovariantDerivative.difference
        (LeviCivita (I := I) gt) (LeviCivita (I := I) g0) x e) e
    have he0 : 0 ≤ g0.inner x e e :=
      Geometry.Riemannian.Exponential.gInner_self_nonneg (I := I) g0 x e
    have he_le : g0.inner x e e ≤ Lambda := by
      have h := (hsymm.2 x (Set.mem_univ x) e).2
      rw [show gt.inner x e e = 1 by simpa [e] using hone i, mul_one] at h
      exact h
    have hD : Real.sqrt (g0.inner x Dv Dv) ≤ A * Lambda := by
      have h := connectionDifference_gJet_le (I := I) hequiv hjet
        (Set.mem_univ x) e e
      change Real.sqrt (g0.inner x Dv Dv) ≤ _ at h
      calc
        Real.sqrt (g0.inner x Dv Dv) ≤
            A * Real.sqrt (g0.inner x e e) * Real.sqrt (g0.inner x e e) := by
          simpa only [A] using h
        _ = A * g0.inner x e e := by
          rw [mul_assoc, ← pow_two, Real.sq_sqrt he0]
        _ ≤ A * Lambda := mul_le_mul_of_nonneg_left he_le hA0
    have hdf : |mvfderiv (I := I) f x Dv| ≤ Real.sqrt C0 * (A * Lambda) := by
      rw [← inner_gradientFun (I := I) g0 f x Dv]
      calc
        |g0.inner x (gradientFun (I := I) g0 f x) Dv| ≤
            Real.sqrt (g0.inner x (gradientFun (I := I) g0 f x)
              (gradientFun (I := I) g0 f x)) *
              Real.sqrt (g0.inner x Dv Dv) :=
          DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
            (I := I) (M := M) g0 x _ _
        _ ≤ Real.sqrt C0 * (A * Lambda) :=
          mul_le_mul (Real.sqrt_le_sqrt hgrad) hD (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
    have hdiff := hessFun_sub_eq_neg_mvfderiv_connectionDifference
      (I := I) gt g0 hU hf hx e e
    change hessFun (I := I) gt f x e e - hessFun (I := I) g0 f x e e =
      -mvfderiv (I := I) f x Dv at hdiff
    have hh0 : hessFun (I := I) g0 f x e e ≤ C0 * Lambda :=
      (hhess e).trans (mul_le_mul_of_nonneg_left he_le hC0)
    change hessFun (I := I) gt f x e e ≤
      C0 * Lambda + Real.sqrt C0 * (A * Lambda)
    linarith [neg_le_abs (mvfderiv (I := I) f x Dv)]
  calc
    ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
        hessFun (I := I) gt f x (basis i) (basis i) ≤
      ∑ _i : Fin (Module.finrank Real (TangentSpace I x)),
        (C0 * Lambda + Real.sqrt C0 * (A * Lambda)) :=
      Finset.sum_le_sum fun i _ ↦ hdiag i
    _ = (Module.finrank Real E : Real) *
        (C0 * Lambda + Real.sqrt C0 * (A * Lambda)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [show Module.finrank Real (TangentSpace I x) =
        Module.finrank Real E by rfl]
    _ = (Module.finrank Real E : Real) *
        (C0 * Lambda + Real.sqrt C0 *
          ((3 / 2 : Real) * Lambda ^ 3 * C1 * Lambda)) := by
      rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_proper_exhaustion_with_gradient_laplacian_bound_on_slab
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alphaMinus alpha b C : Real}
    (hbuffer : alphaMinus < alpha)
    (halphaB : alpha < b)
    (hslab : Set.Icc alphaMinus b ⊆ D.carrier)
    (hreg : Set.Ioc alphaMinus b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric alphaMinus))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Set.Icc alphaMinus b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hsec : ∀ x : M, metricRm04At (I := I) (S.base.metric alpha) x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    ∃ h : M → Real, Continuous h ∧ IsProperMap h ∧
      (∀ x, 1 ≤ h x) ∧
      ∃ Ch : Real, 1 ≤ Ch ∧ ∀ t ∈ Set.Icc alpha b, ∀ x : M,
        ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ hbar : M → Real,
          ContMDiffOn I 𝓘(Real, Real) ∞ hbar U ∧
          hbar x = h x ∧
          (∀ᶠ y in nhds x, h y ≤ hbar y) ∧
          Real.sqrt ((S.base.metric t).inner x
              (gradientFun (I := I) (S.base.metric t) hbar x)
              (gradientFun (I := I) (S.base.metric t) hbar x)) ≤ Ch * h x ∧
          laplacian (I := I) (LeviCivita (I := I) (S.base.metric t))
              (S.base.metric t) hbar x ≤ Ch * h x := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
      let _ : IsEmpty M := hEmpty
      let _ : CompactSpace M := ⟨by
        rw [show (Set.univ : Set M) = ∅ by
          ext x
          exact isEmptyElim x]
        exact isCompact_empty⟩
      refine ⟨fun _ ↦ 1, continuous_const, isProperMap_const 1, ?_, 1, le_rfl, ?_⟩
      · intro x
        exact isEmptyElim x
      · intro t ht x
        exact isEmptyElim x
  | inr hNonempty =>
      let _ : Nonempty M := hNonempty
      let K : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt C
      have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
      have hric : ∀ t ∈ Set.Icc alphaMinus b, ∀ x : M,
          ∀ v : TangentSpace I x,
            |ricciTensor (I := I) (S.base.metric t) x v v| ≤
              K * (S.base.metric t).inner x v v := by
        intro t ht x v
        exact ricci_quadratic_form_bound_of_solution_curvature_bound
          (I := I) S x v (hcurv t ht x)
      have hcompleteAlpha :
          RiemannianMetricComplete (I := I) (S.base.metric alpha) :=
        complete_of_ricBound (I := I) S hS hslab hreg hK hric hcomplete
          ⟨hbuffer.le, halphaB.le⟩
      obtain ⟨h, hcont, hproper, hh, C0, hC0, hsupport⟩ :=
        DifferentialGeometry.exists_proper_distance_exhaustion_with_hessian_bound
          (I := I) (S.base.metric alpha) hcompleteAlpha hsec
          (Classical.choice hNonempty)
      obtain ⟨Lambda, C1, hLambda, hC1, hequiv, hjet⟩ :=
        exists_uniform_metric_first_order_bound_on_slab
          (I := I) S hS hbuffer halphaB hslab hreg hcomplete hC hcurv
      let B : Real := (Module.finrank Real E : Real) *
        (C0 * Lambda + Real.sqrt C0 *
          ((3 / 2 : Real) * Lambda ^ 3 * C1 * Lambda))
      let Ch : Real := max 1 (max (Real.sqrt (Lambda * C0)) B)
      have hB0 : 0 ≤ B := by
        dsimp only [B]
        positivity
      have hCh : 1 ≤ Ch := le_max_left _ _
      have hCh0 : 0 ≤ Ch := le_trans zero_le_one hCh
      refine ⟨h, hcont, hproper, hh, Ch, hCh, ?_⟩
      intro t ht x
      obtain ⟨U, hU, hxU, hbar, hbarSmooth, hbarEq, hbarUpper,
          hbarGrad, hbarHess⟩ := hsupport x
      have htransfer := support_bounds_of_metric_first_order
        (I := I) (S.base.metric alpha) (S.base.metric t)
        hLambda (le_trans zero_le_one hC0) hC1 (hequiv t ht) (hjet t ht)
        hU hbarSmooth hxU hbarGrad hbarHess
      have hscale : Ch ≤ Ch * h x := by
        calc
          Ch = Ch * 1 := by ring
          _ ≤ Ch * h x := mul_le_mul_of_nonneg_left (hh x) hCh0
      have hgradCh : Real.sqrt (Lambda * C0) ≤ Ch :=
        (le_max_left (Real.sqrt (Lambda * C0)) B).trans
          (le_max_right 1 (max (Real.sqrt (Lambda * C0)) B))
      have hBCh : B ≤ Ch :=
        (le_max_right (Real.sqrt (Lambda * C0)) B).trans
          (le_max_right 1 (max (Real.sqrt (Lambda * C0)) B))
      refine ⟨U, hU, hxU, hbar, hbarSmooth, hbarEq, hbarUpper, ?_, ?_⟩
      · exact (htransfer.1.trans hgradCh).trans hscale
      · exact (htransfer.2.trans hBCh).trans hscale

end DifferentialGeometry.PDE.RicciFlow
