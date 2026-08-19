import DifferentialGeometry.Geometry.Connection.ParallelTransport.Radial
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]
variable [NeZero (Module.finrank ℝ E)]
variable [T2Space (TangentBundle I M)]
variable [I.Boundaryless]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
private theorem inner0S_four_orthonormalBasis_sq
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A B : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 A B =
      ∑ I0 : Fin 4 → Fin 3,
        A (fun a => basis (I0 a)) * B (fun a => basis (I0 a)) := by
  classical
  let gInv : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0
  have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
    intro i j
    constructor
    · calc
        (∑ k : Fin 3, gInv i k * g.inner x (basis k) (basis j))
            = g.inner x (basis i) (basis j) := by
              rw [Finset.sum_eq_single i]
              · simp [gInv]
              · intro k _ hk
                have hik : i ≠ k := Ne.symm hk
                simp [gInv, hik]
              · intro hi
                exact False.elim (hi (Finset.mem_univ i))
        _ = if i = j then 1 else 0 := by
              simpa [delta3] using horth i j
    · calc
        (∑ k : Fin 3, g.inner x (basis i) (basis k) * gInv k j)
            = g.inner x (basis i) (basis j) := by
              rw [Finset.sum_eq_single j]
              · simp [gInv]
              · intro k _ hk
                have hkj : k ≠ j := Ne.symm (Ne.symm hk)
                simp [gInv, hkj]
              · intro hj
                exact False.elim (hj (Finset.mem_univ j))
        _ = if i = j then 1 else 0 := by
              simpa [delta3] using horth i j
  have hdelta : ∀ I0 J0 : Fin 4 → Fin 3,
      (∏ a : Fin 4, gInv (I0 a) (J0 a)) = if I0 = J0 then 1 else 0 := by
    intro I0 J0
    by_cases hIJ : I0 = J0
    · subst J0
      simp [gInv]
    · have hne : ∃ a : Fin 4, I0 a ≠ J0 a := by
        by_contra h
        apply hIJ
        funext a
        by_contra hne'
        exact h ⟨a, hne'⟩
      rcases hne with ⟨a, hne⟩
      have hzero : gInv (I0 a) (J0 a) = 0 := by
        simp [gInv, hne]
      rw [Finset.prod_eq_zero (Finset.mem_univ a) hzero]
      rw [if_neg hIJ]
  calc
    inner0S (I := I) g x 4 A B
        = coordInner0S (I := I) (x := x) 4 gInv A B basis := by
            exact inner0S_eq_coord (I := I) g x 4 basis gInv hinv A B
    _ = ∑ I0 : Fin 4 → Fin 3, ∑ J0 : Fin 4 → Fin 3,
          (∏ a : Fin 4, gInv (I0 a) (J0 a)) * A (fun a => basis (I0 a)) *
            B (fun a => basis (J0 a)) := by
          unfold coordInner0S
          apply Finset.sum_congr rfl
          intro I0 _
          apply Finset.sum_congr rfl
          intro J0 _
          simp
    _ = ∑ I0 : Fin 4 → Fin 3, A (fun a => basis (I0 a)) * B (fun a => basis (I0 a)) := by
          apply Finset.sum_congr rfl
          intro I0 _
          simp_rw [hdelta I0]
          rw [Finset.sum_eq_single I0]
          · simp
          · intro J0 _ hJ0
            rw [if_neg (Ne.symm hJ0)]
            ring
          · intro hJ0
            exact False.elim (hJ0 (Finset.mem_univ I0))

section RadialTransportLinear

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialParallelTransportSection_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (u w : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    radialParallelTransportSection (I := I) g p hX (u + w) t =
      radialParallelTransportSection (I := I) g p hX u t +
        radialParallelTransportSection (I := I) g p hX w t := by
  classical
  let γ : ℝ → M := fun s => expMap (I := I) g p (s • X)
  let Puv : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX (u + w)
  let Pu : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX u
  let Pw : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX w
  let Y₁ : ℝ → E := chartRepAt (I := I) γ Puv 0
  let Y₂ : ℝ → E := chartRepAt (I := I) γ Pu 0 + chartRepAt (I := I) γ Pw 0
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 2 := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let U : Set ℝ := {s : ℝ | ‖s • (X : E)‖ < expMapC2Radius (I := I) g p}
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ U := by
    intro s hs
    exact norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX (hIcc_sub hs)
  have hcd : ContDiffOn ℝ 2 (chartCurve (I := I) p γ) U := by
    simpa [γ, U] using (radialCurve_chartCurve_contDiffOn (I := I) g p (v := X))
  have hcd1 : ContDiffOn ℝ 1 (chartCurve (I := I) p γ) U :=
    hcd.of_le (WithTop.coe_le_coe.2 (by norm_num : (1 : ℕ∞) ≤ (2 : ℕ∞)))
  have hu : ContinuousOn (fun τ : ℝ => deriv (chartCurve (I := I) p γ) τ) (Set.Icc 0 1) := by
    have hd : ContDiffOn ℝ 0 (deriv (chartCurve (I := I) p γ)) U :=
      hcd1.deriv_of_isOpen (radialCurve_domain_isOpen (I := I) g p X)
        (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
    exact (hd.continuousOn).mono hsub
  have hγ : ContinuousOn (chartCurve (I := I) p γ) (Set.Icc 0 1) := by
    have hφ : ContinuousOn (extChartAt I p) (extChartAt I p).source :=
      continuousOn_extChartAt (I := I) p
    have hmaps : Set.MapsTo γ (Set.Icc 0 1) (extChartAt I p).source := by
      intro s hs
      rw [extChartAt_source]
      exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc_sub hs)
    have hγcont : ContinuousOn γ U :=
      (radialCurve_contMDiffOn_two (I := I) g p (v := X)).continuousOn
    exact hφ.comp (hγcont.mono hsub) hmaps
  have hsrc : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ (chartAt H p).source := by
    intro τ hτ
    exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc_sub hτ)
  have hODE : ∀ (η₀ : TangentSpace I p), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX η₀) 0)
        (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ)
          (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX η₀) 0 τ)
          (chartCurve (I := I) p γ τ))
        (Set.Icc (0 : ℝ) 1) τ := by
    intro η₀ τ hτ
    have hd := radialParallelTransportSection_ode (I := I) g p hX η₀ (hIcc_sub hτ)
    exact hd.mono (by intro s hs; exact hIcc_sub hs)
  have hY₁ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Y₁
      (- chartChristoffelContraction (I := I) g p
        (deriv (chartCurve (I := I) p γ) τ) (Y₁ τ) (chartCurve (I := I) p γ τ))
      (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have hd := hODE (u + w) τ hτ
    simpa [Y₁, Puv] using hd
  have hY₂ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Y₂
      (- chartChristoffelContraction (I := I) g p
        (deriv (chartCurve (I := I) p γ) τ) (Y₂ τ) (chartCurve (I := I) p γ τ))
      (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have hdu := hODE u τ hτ
    have hdw := hODE w τ hτ
    have hsum := hdu.add hdw
    have hfun : (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 +
          chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0) = Y₂ := by
      rfl
    have hderiv : - chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ)
          (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 τ)
          (chartCurve (I := I) p γ τ) +
        - chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ)
          (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0 τ)
          (chartCurve (I := I) p γ τ) =
        - chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ) (Y₂ τ) (chartCurve (I := I) p γ τ) := by
        rw [show Y₂ τ = chartRepAt (I := I) γ Pu 0 τ + chartRepAt (I := I) γ Pw 0 τ by rfl]
        rw [show chartRepAt (I := I) γ Pu 0 τ = chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 τ by rfl]
        rw [show chartRepAt (I := I) γ Pw 0 τ = chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0 τ by rfl]
        rw [ChartChristoffel.contraction_add_right]
        abel
    convert hsum using 1
    · exact hderiv.symm
  have h0eq : Y₁ 0 = Y₂ 0 := by
    dsimp [Y₁, Y₂]
    have h1 : (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
        (radialParallelTransportSection (I := I) g p hX (u + w) 0) =
      (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0) u +
        (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0) w := by
      rw [radialParallelTransportSection_initial (I := I) g p hX (u + w)]
      exact map_add ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)) u w
    simpa [Puv, Pu, Pw, radialParallelTransportSection_initial] using h1
  have hEq01 : Set.EqOn Y₁ Y₂ (Set.Icc (0 : ℝ) 1) :=
    parallel_local_uniqueness_on_Icc (I := I) g p γ
      (fun τ => deriv (chartCurve (I := I) p γ) τ) (by norm_num) ⟨le_rfl, by norm_num⟩
      hu hγ hsrc hY₁ hY₂ h0eq
  have hEq_t : Y₁ t = Y₂ t := hEq01 ht
  have hchart : chartRepAt (I := I) γ Puv 0 t = chartRepAt (I := I) γ Pu 0 t + chartRepAt (I := I) γ Pw 0 t := by
    simpa [Y₁, Y₂] using hEq_t
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrc t ht
  have hsec : Puv t = Pu t + Pw t := by
    change (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Puv t) =
      (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Pu t) +
        (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Pw t) at hchart
    rw [show γ 0 = p from (radialCurve_zero (I := I) g p X)] at hchart
    have hround_l : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Puv t)) = Puv t :=
      (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Puv t)
    have hround_r : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Pu t) +
          (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Pw t)) = Pu t + Pw t := by
      rw [map_add]
      rw [(trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pu t)]
      rw [(trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pw t)]
    exact hround_l.symm.trans ((congrArg ((trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)) hchart).trans hround_r)
  simpa [Puv, Pu, Pw] using hsec

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialParallelTransportSection_smul [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (c : ℝ) (u : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    radialParallelTransportSection (I := I) g p hX (c • u) t =
      c • radialParallelTransportSection (I := I) g p hX u t := by
  classical
  by_cases hc : c = 0
  · subst c
    have hz : radialParallelTransportSection (I := I) g p hX 0 t = 0 := by
      have hadd : radialParallelTransportSection (I := I) g p hX (0 + 0) t =
          radialParallelTransportSection (I := I) g p hX 0 t + radialParallelTransportSection (I := I) g p hX 0 t :=
        radialParallelTransportSection_add (I := I) g p hX 0 0 ht
      have hleft : radialParallelTransportSection (I := I) g p hX (0 + 0) t =
          radialParallelTransportSection (I := I) g p hX 0 t := by
        congr 1
        abel
      exact add_left_cancel (a := radialParallelTransportSection (I := I) g p hX 0 t)
        (b := radialParallelTransportSection (I := I) g p hX 0 t)
        (c := (0 : TangentSpace I (expMap (I := I) g p (t • X)))) (by
          rw [add_zero]
          exact (hadd.symm.trans hleft))
    rw [show (0 : ℝ) • u = 0 by exact zero_smul ℝ u]
    rw [show (0 : ℝ) • radialParallelTransportSection (I := I) g p hX u t = 0 by
      exact zero_smul ℝ (radialParallelTransportSection (I := I) g p hX u t)]
    exact hz
  · let γ : ℝ → M := fun s => expMap (I := I) g p (s • X)
    let Pcu : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX (c • u)
    let Pu : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX u
    let Y₁ : ℝ → E := chartRepAt (I := I) γ Pcu 0
    let Y₂ : ℝ → E := c • chartRepAt (I := I) γ Pu 0
    have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 2 := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    let U : Set ℝ := {s : ℝ | ‖s • (X : E)‖ < expMapC2Radius (I := I) g p}
    have hsub : Set.Icc (0 : ℝ) 1 ⊆ U := by
      intro s hs
      exact norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX (hIcc_sub hs)
    have hcd : ContDiffOn ℝ 2 (chartCurve (I := I) p γ) U := by
      simpa [γ, U] using (radialCurve_chartCurve_contDiffOn (I := I) g p (v := X))
    have hcd1 : ContDiffOn ℝ 1 (chartCurve (I := I) p γ) U :=
      hcd.of_le (WithTop.coe_le_coe.2 (by norm_num : (1 : ℕ∞) ≤ (2 : ℕ∞)))
    have hu : ContinuousOn (fun τ : ℝ => deriv (chartCurve (I := I) p γ) τ) (Set.Icc 0 1) := by
      have hd : ContDiffOn ℝ 0 (deriv (chartCurve (I := I) p γ)) U :=
        hcd1.deriv_of_isOpen (radialCurve_domain_isOpen (I := I) g p X)
          (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
      exact (hd.continuousOn).mono hsub
    have hγ : ContinuousOn (chartCurve (I := I) p γ) (Set.Icc 0 1) := by
      have hφ : ContinuousOn (extChartAt I p) (extChartAt I p).source :=
        continuousOn_extChartAt (I := I) p
      have hmaps : Set.MapsTo γ (Set.Icc 0 1) (extChartAt I p).source := by
        intro s hs
        rw [extChartAt_source]
        exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc_sub hs)
      have hγcont : ContinuousOn γ U :=
        (radialCurve_contMDiffOn_two (I := I) g p (v := X)).continuousOn
      exact hφ.comp (hγcont.mono hsub) hmaps
    have hsrc : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ (chartAt H p).source := by
      intro τ hτ
      exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc_sub hτ)
    have hODE : ∀ (η₀ : TangentSpace I p), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX η₀) 0)
          (- chartChristoffelContraction (I := I) g p
            (deriv (chartCurve (I := I) p γ) τ)
            (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX η₀) 0 τ)
            (chartCurve (I := I) p γ τ))
          (Set.Icc (0 : ℝ) 1) τ := by
      intro η₀ τ hτ
      have hd := radialParallelTransportSection_ode (I := I) g p hX η₀ (hIcc_sub hτ)
      exact hd.mono (by intro s hs; exact hIcc_sub hs)
    have hY₁ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Y₁
        (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ) (Y₁ τ) (chartCurve (I := I) p γ τ))
        (Set.Icc (0 : ℝ) 1) τ := by
      intro τ hτ
      have hd := hODE (c • u) τ hτ
      simpa [Y₁, Pcu] using hd
    have hY₂ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Y₂
        (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) τ) (Y₂ τ) (chartCurve (I := I) p γ τ))
        (Set.Icc (0 : ℝ) 1) τ := by
      intro τ hτ
      have hdu := hODE u τ hτ
      have hsmul := hdu.const_smul c
      have hfun : (c • chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0) = Y₂ := by
        rfl
      have hderiv : c • (- chartChristoffelContraction (I := I) g p
            (deriv (chartCurve (I := I) p γ) τ)
            (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 τ)
            (chartCurve (I := I) p γ τ)) =
          - chartChristoffelContraction (I := I) g p
            (deriv (chartCurve (I := I) p γ) τ) (Y₂ τ) (chartCurve (I := I) p γ τ) := by
        rw [show Y₂ τ = c • chartRepAt (I := I) γ Pu 0 τ by rfl]
        rw [show chartRepAt (I := I) γ Pu 0 τ = chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 τ by rfl]
        rw [ChartChristoffel.contraction_smul_right]
        rw [smul_neg]
      convert hsmul using 1
      · exact hderiv.symm
    have h0eq : Y₁ 0 = Y₂ 0 := by
      dsimp [Y₁, Y₂]
      have h1 : (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
          (radialParallelTransportSection (I := I) g p hX (c • u) 0) =
          c • (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
            (radialParallelTransportSection (I := I) g p hX u 0) := by
        rw [radialParallelTransportSection_initial (I := I) g p hX (c • u)]
        rw [radialParallelTransportSection_initial (I := I) g p hX u]
        exact map_smul ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)) c u
      simpa [Pcu, Pu, radialParallelTransportSection_initial] using h1
    have hEq01 : Set.EqOn Y₁ Y₂ (Set.Icc (0 : ℝ) 1) :=
      parallel_local_uniqueness_on_Icc (I := I) g p γ
        (fun τ => deriv (chartCurve (I := I) p γ) τ) (by norm_num) ⟨le_rfl, by norm_num⟩
        hu hγ hsrc hY₁ hY₂ h0eq
    have hEq_t : Y₁ t = Y₂ t := hEq01 ht
    have hchart : chartRepAt (I := I) γ Pcu 0 t = c • chartRepAt (I := I) γ Pu 0 t := by
      simpa [Y₁, Y₂] using hEq_t
    have hmem : γ t ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrc t ht
    have hsec : Pcu t = c • Pu t := by
      change (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Pcu t) =
        c • (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ t) (Pu t) at hchart
      rw [show γ 0 = p from (radialCurve_zero (I := I) g p X)] at hchart
      have hround_l : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
          ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Pcu t)) = Pcu t :=
        (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pcu t)
      have hround_r : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
          (c • (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t) (Pu t)) = c • Pu t := by
        rw [map_smul]
        rw [(trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pu t)]
      exact hround_l.symm.trans ((congrArg ((trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)) hchart).trans hround_r)
    simpa [Pcu, Pu] using hsec

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialTransportSection_linear_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    (u w : TangentSpace I p) (y : M) :
    radialTransportSection g p (u + w) y =
      radialTransportSection g p u y + radialTransportSection g p w y := by
  classical
  by_cases hy : y ∈ radialTransportSectionDomain (I := I) g p
  · rw [radialTransportSection]
    have hcond : y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p := by
      simpa [radialTransportSectionDomain] using hy
    simp_rw [radialTransportSection, dif_pos hcond]
    exact radialParallelTransportSection_add (I := I) g p hcond.2 u w (t := 1)
      ⟨by norm_num, by norm_num⟩
  · have hnot : ¬(y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p) := by
      simpa [radialTransportSectionDomain] using hy
    simp_rw [radialTransportSection, dif_neg hnot]
    simp

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialTransportSection_linear_smul [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    (c : ℝ) (u : TangentSpace I p) (y : M) :
    radialTransportSection g p (c • u) y = c • radialTransportSection g p u y := by
  classical
  by_cases hy : y ∈ radialTransportSectionDomain (I := I) g p
  · rw [radialTransportSection]
    have hcond : y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p := by
      simpa [radialTransportSectionDomain] using hy
    simp_rw [radialTransportSection, dif_pos hcond]
    exact radialParallelTransportSection_smul (I := I) g p hcond.2 c u (t := 1)
      ⟨by norm_num, by norm_num⟩
  · have hnot : ¬(y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p) := by
      simpa [radialTransportSectionDomain] using hy
    simp_rw [radialTransportSection, dif_neg hnot]
    simp



set_option linter.unusedSectionVars false in
omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
lemma radialParallelTransportSection_chartGram_hasDerivAt_zero [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (u w : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 2) :
    HasDerivAt (fun τ : ℝ =>
      chartGramAlongCurve (I := I) g p (fun τ0 : ℝ => expMap (I := I) g p (τ0 • X))
        (chartRepAt (I := I) (fun τ0 : ℝ => expMap (I := I) g p (τ0 • X))
          (radialParallelTransportSection (I := I) g p hX u) 0)
        (chartRepAt (I := I) (fun τ0 : ℝ => expMap (I := I) g p (τ0 • X))
          (radialParallelTransportSection (I := I) g p hX w) 0) τ) 0 t := by
  classical
  let γ : ℝ → M := fun t0 => expMap (I := I) g p (t0 • X)
  let Pu : ∀ t0, TangentSpace I (γ t0) := radialParallelTransportSection (I := I) g p hX u
  let Pw : ∀ t0, TangentSpace I (γ t0) := radialParallelTransportSection (I := I) g p hX w
  let V : ℝ → E := chartRepAt (I := I) γ Pu 0
  let W : ℝ → E := chartRepAt (I := I) γ Pw 0
  let uPrime : ℝ → E := fun t0 => deriv (chartCurve (I := I) p γ) t0
  let o : Set ℝ := Set.Ioo (-1 : ℝ) 2
  have hdom : ∀ t0 : ℝ, t0 ∈ o → ‖t0 • (X : E)‖ < expMapC2Radius (I := I) g p := by
    intro t0 ht0
    exact norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX ⟨ht0.1.le, ht0.2.le⟩
  have hIcc : ∀ t0 : ℝ, t0 ∈ o → t0 ∈ Set.Icc (-1 : ℝ) 2 := by
    intro t0 ht0
    exact ⟨ht0.1.le, ht0.2.le⟩
  have hγdiff : ∀ t0 : ℝ, t0 ∈ o → DifferentiableAt ℝ (chartCurve (I := I) p γ) t0 := by
    intro t0 ht0
    let U : Set ℝ := {u0 : ℝ | ‖u0 • (X : E)‖ < expMapC2Radius (I := I) g p}
    have hcd : ContDiffOn ℝ 2 (chartCurve (I := I) p γ) U := by
      simpa [γ, U] using (radialCurve_chartCurve_contDiffOn (I := I) g p (v := X))
    have hUnhd : U ∈ 𝓝 t0 := (radialCurve_domain_isOpen (I := I) g p X).mem_nhds (hdom t0 ht0)
    exact (hcd.contDiffAt hUnhd).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hsrc_o : ∀ t0 ∈ o, γ t0 ∈ (chartAt H p).source := by
    intro t0 ht0
    exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX (hIcc t0 ht0)
  have hmem : ∀ t0 ∈ o, chartCurve (I := I) p γ t0 ∈ interior (extChartAt I p).target := by
    intro t0 ht0
    have hxsrc : γ t0 ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hsrc_o t0 ht0
    have hxtarget : chartCurve (I := I) p γ t0 ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hxsrc
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p hxtarget
  have hVpar : IsParallelChart (I := I) g p γ uPrime V o := by
    constructor
    · intro t0 ht0
      exact (hγdiff t0 ht0).hasDerivAt
    · intro t0 ht0
      have hd := radialParallelTransportSection_ode (I := I) g p hX u (hIcc t0 ht0)
      have hd' : HasDerivAt (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0)
          (- chartChristoffelContraction (I := I) g p (uPrime t0)
            (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX u) 0 t0)
            (chartCurve (I := I) p γ t0)) t0 :=
        hd.hasDerivAt (Icc_mem_nhds ht0.1 ht0.2)
      simpa [V, Pu] using hd'
  have hWpar : IsParallelChart (I := I) g p γ uPrime W o := by
    constructor
    · intro t0 ht0
      exact (hγdiff t0 ht0).hasDerivAt
    · intro t0 ht0
      have hd := radialParallelTransportSection_ode (I := I) g p hX w (hIcc t0 ht0)
      have hd' : HasDerivAt (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0)
          (- chartChristoffelContraction (I := I) g p (uPrime t0)
            (chartRepAt (I := I) γ (radialParallelTransportSection (I := I) g p hX w) 0 t0)
            (chartCurve (I := I) p γ t0)) t0 :=
        hd.hasDerivAt (Icc_mem_nhds ht0.1 ht0.2)
      simpa [W, Pw] using hd'
  have hderiv : ∀ t0 ∈ o, HasDerivAt
      (fun τ : ℝ => chartGramAlongCurve (I := I) g p γ V W τ) 0 t0 := by
    intro t0 ht0
    let Vprime : ℝ → E := fun _ => - chartChristoffelContraction (I := I) g p (uPrime t0) (V t0)
      (chartCurve (I := I) p γ t0)
    let Wprime : ℝ → E := fun _ => - chartChristoffelContraction (I := I) g p (uPrime t0) (W t0)
      (chartCurve (I := I) p γ t0)
    have hV : HasDerivAt V (Vprime t0) t0 := by
      simpa [Vprime] using (hVpar.hasDerivAt ht0)
    have hW : HasDerivAt W (Wprime t0) t0 := by
      simpa [Wprime] using (hWpar.hasDerivAt ht0)
    have hmain := chartGramAlongCurve_hasDerivAt_covariant (I := I) g p γ V W
      (uPrime := uPrime) (Vprime := Vprime) (Wprime := Wprime) (t := t0)
      ((hγdiff t0 ht0).hasDerivAt) (hmem t0 ht0) hV hW
    have hVzero : Vprime t0 + chartChristoffelContraction (I := I) g p (uPrime t0) (V t0)
        (chartCurve (I := I) p γ t0) = 0 := by
      simp [Vprime]
    have hWzero : Wprime t0 + chartChristoffelContraction (I := I) g p (uPrime t0) (W t0)
        (chartCurve (I := I) p γ t0) = 0 := by
      simp [Wprime]
    rw [hVzero, hWzero] at hmain
    simpa [hVzero, hWzero] using hmain
  have hgoal : HasDerivAt (fun τ : ℝ =>
      chartGramAlongCurve (I := I) g p γ V W τ) 0 t := hderiv t ht
  simpa [γ, Pu, Pw, V, W] using hgoal

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] in
lemma chartGramAlongCurve_eq_inner
    (g : SmoothRiemannianMetric I M) (p : M)
    (γ : ℝ → M) (V W : ℝ → E) (t : ℝ)
    (hsrc : γ t ∈ (chartAt H p).source) :
    chartGramAlongCurve (I := I) g p γ V W t =
      g.inner (γ t) ((trivializationAt E (TangentSpace I) p).symmL ℝ (γ t) (V t))
        ((trivializationAt E (TangentSpace I) p).symmL ℝ (γ t) (W t)) := by
  rw [chartGramAlongCurve_def]
  have hgram : ∀ i j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g p i j (chartCurve (I := I) p γ t) =
        chartGramMatrix (I := I) g p (γ t) i j := by
    intro i j
    rw [chartGramOnE_def]
    rw [chartCurve_def]
    rw [(extChartAt I p).left_inv (by rw [extChartAt_source]; exact hsrc)]
  simp_rw [hgram]
  have hmain := inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g p (x := γ t) (V t) (W t)
  exact hmain.symm


omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialParallelTransportSection_inner_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (u w : TangentSpace I p) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 2) :
    g.inner (expMap (I := I) g p (s • X))
      (radialParallelTransportSection (I := I) g p hX u s)
      (radialParallelTransportSection (I := I) g p hX w s) = g.inner p u w := by
  classical
  let γ : ℝ → M := fun t => expMap (I := I) g p (t • X)
  let Pu : ∀ t, TangentSpace I (γ t) := radialParallelTransportSection (I := I) g p hX u
  let Pw : ∀ t, TangentSpace I (γ t) := radialParallelTransportSection (I := I) g p hX w
  let V : ℝ → E := chartRepAt (I := I) γ Pu 0
  let W : ℝ → E := chartRepAt (I := I) γ Pw 0
  let f : ℝ → ℝ := fun t => chartGramAlongCurve (I := I) g p γ V W t
  let o : Set ℝ := Set.Ioo (-1 : ℝ) 2
  have hγ0 : γ 0 = p := by
    dsimp [γ]
    exact radialCurve_zero (I := I) g p X
  have hsrc_o : ∀ t ∈ o, γ t ∈ (chartAt H p).source := by
    intro t ht
    exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX ⟨ht.1.le, ht.2.le⟩
  have hderiv : ∀ t ∈ o, HasDerivAt f 0 t := by
    intro t ht
    have h := radialParallelTransportSection_chartGram_hasDerivAt_zero (I := I) g p hX u w ht
    simpa [f, γ, Pu, Pw, V, W] using h
  have hconst : f s = f 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hderiv t ht).deriv) hs ⟨by norm_num, by norm_num⟩
  have hfs : f s = g.inner (expMap (I := I) g p (s • X))
      (radialParallelTransportSection (I := I) g p hX u s)
      (radialParallelTransportSection (I := I) g p hX w s) := by
    have hb : (γ s) ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrc_o s hs
    have hV₀ : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ s) (V s) = radialParallelTransportSection (I := I) g p hX u s := by
      change (trivializationAt E (TangentSpace I) p).symmL ℝ (γ s)
          ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s)
            (radialParallelTransportSection (I := I) g p hX u s)) =
        radialParallelTransportSection (I := I) g p hX u s
      rw [hγ0]
      exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hb
        (radialParallelTransportSection (I := I) g p hX u s)
    have hW₀ : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ s) (W s) = radialParallelTransportSection (I := I) g p hX w s := by
      change (trivializationAt E (TangentSpace I) p).symmL ℝ (γ s)
          ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s)
            (radialParallelTransportSection (I := I) g p hX w s)) =
        radialParallelTransportSection (I := I) g p hX w s
      rw [hγ0]
      exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hb
        (radialParallelTransportSection (I := I) g p hX w s)
    unfold f
    rw [← hV₀, ← hW₀]
    exact chartGramAlongCurve_eq_inner (I := I) g p γ V W s (hsrc_o s hs)
  have hf0 : f 0 = g.inner p u w := by
    have hb : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H p
    have hV₀ : (trivializationAt E (TangentSpace I) p).symmL ℝ p (V 0) = u := by
      change (trivializationAt E (TangentSpace I) p).symmL ℝ p
          ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
            (radialParallelTransportSection (I := I) g p hX u 0)) = u
      rw [hγ0]
      rw [radialParallelTransportSection_initial (I := I) g p hX u]
      exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hb u
    have hW₀ : (trivializationAt E (TangentSpace I) p).symmL ℝ p (W 0) = w := by
      change (trivializationAt E (TangentSpace I) p).symmL ℝ p
          ((trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0)
            (radialParallelTransportSection (I := I) g p hX w 0)) = w
      rw [hγ0]
      rw [radialParallelTransportSection_initial (I := I) g p hX w]
      exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hb w
    unfold f
    rw [← hV₀, ← hW₀]
    have h := chartGramAlongCurve_eq_inner (I := I) g p γ V W 0 (hsrc_o 0 ⟨by norm_num, by norm_num⟩)
    rw [hγ0] at h
    exact h
  rw [← hfs, ← hf0]
  exact hconst

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialTransportSection_inner_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M) (u w : TangentSpace I p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    g.inner y (radialTransportSection g p u y) (radialTransportSection g p w y) = g.inner p u w := by
  classical
  have hcond : y ∈ (normalChartAt (I := I) g p).source ∧
      ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p := by
    simpa [radialTransportSectionDomain] using hy
  let x : E := normalChartAt (I := I) g p y
  have hEq : y = expMap (I := I) g p ((1 : ℝ) • x) := by
    have hsymm : (normalChartAt (I := I) g p).symm x = y := by
      rw [show x = normalChartAt (I := I) g p y by rfl]
      exact normalChartAt_left_inv (I := I) g p hcond.1
    have htgt : x ∈ (normalChartAt (I := I) g p).symm.source := by
      rw [show x = normalChartAt (I := I) g p y by rfl]
      have hmap : normalChartAt (I := I) g p y ∈ (normalChartAt (I := I) g p).target :=
        (normalChartAt (I := I) g p).map_source hcond.1
      simpa using hmap
    have hexp : (normalChartAt (I := I) g p).symm x = expMap (I := I) g p x :=
      normalChartAt_symm_apply (I := I) g p htgt
    rw [← hsymm, hexp]
    simp
  have hval_u : radialTransportSection g p u y = radialParallelTransportSection (I := I) g p hcond.2 u 1 := by
    simp_rw [radialTransportSection, dif_pos hcond]
  have hval_w : radialTransportSection g p w y = radialParallelTransportSection (I := I) g p hcond.2 w 1 := by
    simp_rw [radialTransportSection, dif_pos hcond]
  have hmain := radialParallelTransportSection_inner_eq (I := I) g p hcond.2 u w (s := 1)
    ⟨by norm_num, by norm_num⟩
  rw [hval_u, hval_w]
  have hbase : g.inner y (radialParallelTransportSection (I := I) g p hcond.2 u 1)
        (radialParallelTransportSection (I := I) g p hcond.2 w 1) =
      g.inner (expMap (I := I) g p ((1 : ℝ) • x))
        (radialParallelTransportSection (I := I) g p hcond.2 u 1)
        (radialParallelTransportSection (I := I) g p hcond.2 w 1) := by
    exact congrArg (fun z : M => g.inner z (radialParallelTransportSection (I := I) g p hcond.2 u 1)
      (radialParallelTransportSection (I := I) g p hcond.2 w 1)) hEq
  rw [hbase]
  simpa [x] using hmain

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem radialTransportSection_injective [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    Function.Injective (fun v : TangentSpace I p => radialTransportSection g p v y) := by
  intro v w hvw
  have hmain := radialTransportSection_inner_eq (I := I) g p (v - w) (v - w) y hy
  have hv : radialTransportSection g p (v - w) y = 0 := by
    have hlin : radialTransportSection g p (v - w) y = radialTransportSection g p v y - radialTransportSection g p w y := by
      have h1 := radialTransportSection_linear_add (I := I) g p v (-w) y
      have h2 := radialTransportSection_linear_smul (I := I) g p (-1) w y
      rw [show -w = (-1 : ℝ) • w by simp] at h1
      rw [h2] at h1
      simpa [sub_eq_add_neg] using h1
    simpa [sub_eq_add_neg, hvw] using hlin
  have hzero : g.inner p (v - w) (v - w) = 0 := by
    rw [← hmain]
    rw [hv]
    simp
  exact sub_eq_zero.mp (by
    by_contra hne
    have hpos' : 0 < g.inner p (v - w) (v - w) := g.pos p (v - w) hne
    linarith)


section TensorTransport

noncomputable def radialTransportLinearMapAt (g : SmoothRiemannianMetric I M) (p y : M) :
    E →ₗ[ℝ] E :=
  { toFun := fun v => radialTransportSection g p v y
    map_add' := by
      intro a b
      exact radialTransportSection_linear_add (I := I) g p a b y
    map_smul' := by
      intro a b
      exact radialTransportSection_linear_smul (I := I) g p a b y }

noncomputable def radialTransportInverseAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) : E →L[ℝ] E :=
  let T : E →ₗ[ℝ] E := radialTransportLinearMapAt g p y
  let hT : Function.Injective T := by
    intro a b hab
    exact radialTransportSection_injective (I := I) g p y hy (by simpa [radialTransportLinearMapAt] using hab)
  let hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective T ⟨hT, hsurj⟩
  (e.symm.toContinuousLinearEquiv).toContinuousLinearMap

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem radialTransportInverseAt_apply
    (g : SmoothRiemannianMetric I M) (p y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) (v : E) :
    radialTransportInverseAt g p y hy v =
      (LinearEquiv.ofBijective (radialTransportLinearMapAt g p y)
        (by
          have hT : Function.Injective (radialTransportLinearMapAt g p y) := by
            intro a b hab
            exact radialTransportSection_injective (I := I) g p y hy (by simpa [radialTransportLinearMapAt] using hab)
          have hsurj : Function.Surjective (radialTransportLinearMapAt g p y) :=
            (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
          exact ⟨hT, hsurj⟩)).symm v := by
  rfl

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportInverseAt_left_inverse
    (g : SmoothRiemannianMetric I M) (p y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) (v : E) :
    radialTransportInverseAt g p y hy (radialTransportLinearMapAt g p y v) = v := by
  rw [radialTransportInverseAt_apply]
  exact (LinearEquiv.ofBijective (radialTransportLinearMapAt g p y) (by
    have hT : Function.Injective (radialTransportLinearMapAt g p y) := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy (by simpa [radialTransportLinearMapAt] using hab)
    have hsurj : Function.Surjective (radialTransportLinearMapAt g p y) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
    exact ⟨hT, hsurj⟩)).symm_apply_apply v

noncomputable def radialTransportSectionTensor [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : Tensor04At (I := I) (M := M) p) : ∀ y : M, Tensor04At (I := I) (M := M) y := by
  classical
  exact fun y =>
    if h : y ∈ radialTransportSectionDomain (I := I) g p then
      η₀.compContinuousLinearMap (fun _ : Fin 4 => (radialTransportInverseAt g p y h : E →L[ℝ] E))
    else 0


set_option linter.unusedSectionVars false in
omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
lemma mem_radialTransportSectionDomain_expMap
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    expMap (I := I) g p (s • X) ∈ radialTransportSectionDomain (I := I) g p := by
  classical
  have hs_norm : ‖s • (X : E)‖ < expMapC2Radius (I := I) g p :=
    norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX ⟨hs.1.le, by linarith [hs.2]⟩
  have hs_rad : ‖s • (X : E)‖ < radialRadius (I := I) g p := by
    have hnorm : ‖s • (X : E)‖ ≤ ‖(X : E)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |s| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact (mul_le_mul_of_nonneg_right habs (norm_nonneg (X : E))).trans_eq (one_mul _)
    exact lt_of_le_of_lt hnorm hX
  unfold radialTransportSectionDomain
  constructor
  · exact expMap_mem_normalChartAt_source_of_norm_lt_radialRadius (I := I) g p hs_norm
  · have hv : normalChartAt (I := I) g p (expMap (I := I) g p (s • X)) = s • (X : E) :=
      normalChartAt_expMap_smul (I := I) g p (X : E) s (ball_subset_normalChartAt_target
        (I := I) g p hs_norm)
    rw [hv]
    exact hs_rad

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportInverseAt_transport_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1)
    (v : E) :
    radialTransportInverseAt g p (expMap (I := I) g p (s • X))
      (mem_radialTransportSectionDomain_expMap (I := I) g p hX hs)
      (radialParallelTransportSection (I := I) g p hX v s) = v := by
  classical
  let y : M := expMap (I := I) g p (s • X)
  have hmem : y ∈ radialTransportSectionDomain (I := I) g p :=
    mem_radialTransportSectionDomain_expMap (I := I) g p hX hs
  have h := radialTransportInverseAt_left_inverse (I := I) g p y hmem v
  have hval : radialTransportLinearMapAt g p y v = radialParallelTransportSection (I := I) g p hX v s := by
    dsimp [radialTransportLinearMapAt, y]
    exact radialTransportSection_pullback_eq (I := I) g p v hX hs
  rw [hval] at h
  exact h

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportSectionTensor_initial
    (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : Tensor04At (I := I) (M := M) p) :
    radialTransportSectionTensor g p η₀ p = η₀ := by
  classical
  have hmem : p ∈ radialTransportSectionDomain (I := I) g p :=
    mem_radialTransportSectionDomain_self (I := I) g p
  rw [radialTransportSectionTensor]
  rw [dif_pos hmem]
  have hid : (radialTransportInverseAt g p p hmem : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    ext v
    have hc : radialTransportSection g p v p = v :=
      radialTransportSection_center (I := I) g p v 0 (by
        rw [norm_zero]
        exact radialRadius_pos (I := I) g p)
    have hlin : radialTransportLinearMapAt g p p v = v := by
      simpa [radialTransportLinearMapAt] using hc
    have h := radialTransportInverseAt_left_inverse (I := I) g p p hmem v
    simpa [hlin] using h
  rw [hid]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] in
private theorem tensor04Field_sum_apply
    {ι : Type*} [Fintype ι]
    (A : ι → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) 4)
    (y : M) :
    (∑ i, A i) y = ∑ i, A i y := by
  let L :
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 4 →+
        ((z : M) → Tensor0SSpace 4 I z) :=
    { toFun := fun B z => B z
      map_zero' := by rfl
      map_add' := by intro B C; rfl }
  have h := congrFun (map_sum L A Finset.univ) y
  change (∑ i, A i) y = (∑ i, fun z => A i z) y at h
  rw [Finset.sum_apply] at h
  exact h

noncomputable def radialTransportTensorExtension
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (η₀ : Tensor04At (I := I) (M := M) p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 4 :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    η₀ (fun a => basis (slots4 i j k l a)) •
      metricFormSection (I := I) (M := M) g 4 (fun a => W (slots4 i j k l a))

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] in
theorem radialTransportTensorExtension_apply
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (η₀ : Tensor04At (I := I) (M := M) p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (y : M) (v : Fin 4 → TangentSpace I y) :
    radialTransportTensorExtension g p basis η₀ W y v =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        η₀ (fun a => basis (slots4 i j k l a)) *
          ∏ a : Fin 4, g.inner y (W (slots4 i j k l a) y) (v a) := by
  rw [radialTransportTensorExtension, tensor04Field_sum_apply, tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensor04Field_sum_apply, tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [tensor04Field_sum_apply, tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [tensor04Field_sum_apply, tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  change (η₀ (fun a => basis (slots4 i j k l a)) •
    metricFormSection (I := I) (M := M) g 4
      (fun a => W (slots4 i j k l a)) y) v = _
  rw [Tensor0SSpace.smul_apply]
  change η₀ (fun a => basis (slots4 i j k l a)) * Tensor0SSpace.toModel
    (metricFormSection (I := I) (M := M) g 4
      (fun a => W (slots4 i j k l a)) y) v = _
  rw [toModel_metricFormSection,
    DifferentialGeometry.Integral.L2.separableFormAt_apply]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportSectionTensor_apply_eq_sum
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p)
    (v : Fin 4 → TangentSpace I y) :
    radialTransportSectionTensor g p η₀ y v =
      ∑ J : Fin 4 → Fin 3,
        η₀ (fun a => basis (J a)) *
          ∏ a : Fin 4, g.inner y
            (radialTransportSection (I := I) g p (basis (J a)) y) (v a) := by
  classical
  let T : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (radialTransportLinearMapAt g p y) (by
    have hT : Function.Injective (radialTransportLinearMapAt g p y) := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy
        (by simpa [radialTransportLinearMapAt] using hab)
    have hsurj : Function.Surjective (radialTransportLinearMapAt g p y) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
    exact ⟨hT, hsurj⟩)
  let basisY : Module.Basis (Fin 3) ℝ (TangentSpace I y) := basis.map T
  have horthY : OrthonormalBasisAt (I := I) g y basisY := by
    intro a b
    have hinner := radialTransportSection_inner_eq (I := I) g p (basis a) (basis b) y hy
    have hTa : (basisY a : TangentSpace I y) =
        radialTransportSection (I := I) g p (basis a) y := by
      dsimp [basisY]
      change (T (basis a) : TangentSpace I y) = _
      rfl
    have hTb : (basisY b : TangentSpace I y) =
        radialTransportSection (I := I) g p (basis b) y := by
      dsimp [basisY]
      change (T (basis b) : TangentSpace I y) = _
      rfl
    rw [hTa, hTb]
    simpa [horth a b] using hinner
  rw [tensor0S_apply_eq_sum (I := I) basisY (radialTransportSectionTensor g p η₀ y) v]
  apply Finset.sum_congr rfl
  intro J _
  have hcoeff : radialTransportSectionTensor g p η₀ y (fun a => basisY (J a)) =
      η₀ (fun a => basis (J a)) := by
    rw [radialTransportSectionTensor, dif_pos hy]
    change η₀ (fun a => radialTransportInverseAt g p y hy (basisY (J a))) = _
    congr 1
    funext a
    change radialTransportInverseAt g p y hy
        (radialTransportLinearMapAt g p y (basis (J a))) = basis (J a)
    exact radialTransportInverseAt_left_inverse (I := I) g p y hy (basis (J a))
  rw [component0S_apply, hcoeff]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  have hinv : MetricInverseInBasis (I := I) g y basisY
      (identityInvMetric (Idx := Fin 3)) :=
    Tensor0SBundle.metricInverseInBasis_identity_of_orthonormal (I := I) g basisY
      (by simpa [delta3] using horthY)
  rw [DifferentialGeometry.Geometry.Curvature.basis_coord_eq_sum_inv_inner
    (I := I) g basisY (identityInvMetric (Idx := Fin 3)) hinv]
  rw [Finset.sum_eq_single (J a)]
  · rw [identityInvMetric_apply_self, one_mul]
    rfl
  · intro b _ hba
    rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hba.symm, zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ (J a)) ha

private def fin4SlotsEquiv : (Fin 4 → Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [slots4]

private lemma sum_fin_four_fun {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 → Fin 3) → α) :
    (∑ I0 : Fin 4 → Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) := by
  classical
  rw [Fintype.sum_equiv fin4SlotsEquiv F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) =>
      F (slots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [fin4SlotsEquiv, slots4]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportTensorExtension_eq_smul
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (y : M) :
    radialTransportTensorExtension g p basis η₀ W y =
      (χ y) ^ 4 • radialTransportSectionTensor g p η₀ y := by
  classical
  apply tensor0SSpace_ext
  intro v
  rw [radialTransportTensorExtension_apply, Tensor0SSpace.smul_apply]
  by_cases hχ : χ y = 0
  · simp_rw [hW]
    simp [hχ]
  · have hySupport : y ∈ Function.support (χ : M → ℝ) := hχ
    have hyTsupport : y ∈ tsupport (χ : M → ℝ) := subset_closure hySupport
    have hy : y ∈ radialTransportSectionDomain (I := I) g p := hsupport hyTsupport
    rw [radialTransportSectionTensor_apply_eq_sum g p basis horth η₀ y hy v]
    rw [sum_fin_four_fun]
    simp_rw [hW, map_smul (g.inner y), ContinuousLinearMap.smul_apply, smul_eq_mul,
      Fin.prod_univ_four]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportTensorExtension_eventually_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y) :
    ∀ᶠ y in 𝓝 p,
      radialTransportTensorExtension g p basis η₀ W y =
        radialTransportSectionTensor g p η₀ y := by
  filter_upwards [χ.eventuallyEq_one] with y hy
  rw [radialTransportTensorExtension_eq_smul g p basis horth η₀ χ W hsupport hW y]
  simp [hy]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportTensorExtension_initial
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y) :
    radialTransportTensorExtension g p basis η₀ W p = η₀ := by
  rw [radialTransportTensorExtension_eq_smul g p basis horth η₀ χ W hsupport hW p,
    χ.eq_one, one_pow, one_smul, radialTransportSectionTensor_initial]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportSectionTensor_inner_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    (hdim : Module.finrank Real (TangentSpace I p) = 3)
    (A B : Tensor04At (I := I) (M := M) p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    inner0S (I := I) g y 4 (radialTransportSectionTensor g p A y)
        (radialTransportSectionTensor g p B y) =
      inner0S (I := I) g p 4 A B := by
  classical
  let basis₀ : Module.Basis (Fin 3) Real (TangentSpace I p) :=
    Classical.choose (exists_orthonormalBasisAt (I := I) g p hdim)
  have horth₀ : OrthonormalBasisAt (I := I) g p basis₀ :=
    Classical.choose_spec (exists_orthonormalBasisAt (I := I) g p hdim)
  let T : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (radialTransportLinearMapAt g p y) (by
    have hT : Function.Injective (radialTransportLinearMapAt g p y) := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy (by simpa [radialTransportLinearMapAt] using hab)
    have hsurj : Function.Surjective (radialTransportLinearMapAt g p y) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl).mp hT
    exact ⟨hT, hsurj⟩)
  let basisY : Module.Basis (Fin 3) Real (TangentSpace I y) := basis₀.map T
  have horthY : OrthonormalBasisAt (I := I) g y basisY := by
    intro a b
    have hinner := radialTransportSection_inner_eq (I := I) g p (basis₀ a) (basis₀ b) y hy
    have hTa : (basisY a : TangentSpace I y) = radialTransportSection g p (basis₀ a) y := by
      dsimp [basisY]
      change (T (basis₀ a) : TangentSpace I y) = radialTransportSection g p (basis₀ a) y
      dsimp [T]
      rfl
    have hTb : (basisY b : TangentSpace I y) = radialTransportSection g p (basis₀ b) y := by
      dsimp [basisY]
      change (T (basis₀ b) : TangentSpace I y) = radialTransportSection g p (basis₀ b) y
      dsimp [T]
      rfl
    rw [hTa, hTb]
    simpa [horth₀ a b] using hinner
  have hcomponent : ∀ C : Tensor04At (I := I) (M := M) p, ∀ J : Fin 4 → Fin 3,
      (radialTransportSectionTensor g p C y) (fun a => basisY (J a)) =
        C (fun a => basis₀ (J a)) := by
    intro C J
    rw [radialTransportSectionTensor]
    rw [dif_pos hy]
    have hTval : ∀ a : Fin 4,
        (basisY (J a) : E) = radialTransportLinearMapAt g p y (basis₀ (J a)) := by
      intro a
      dsimp [basisY]
      change (T (basis₀ (J a)) : E) = radialTransportLinearMapAt g p y (basis₀ (J a))
      dsimp [T]
    change C (fun a => radialTransportInverseAt g p y hy (basisY (J a))) =
      C (fun a => basis₀ (J a))
    congr 1
    funext a
    rw [hTval a]
    exact radialTransportInverseAt_left_inverse (I := I) g p y hy (basis₀ (J a))
  rw [inner0S_four_orthonormalBasis_sq (I := I) g y basisY horthY
    (radialTransportSectionTensor g p A y) (radialTransportSectionTensor g p B y)]
  rw [inner0S_four_orthonormalBasis_sq (I := I) g p basis₀ horth₀ A B]
  apply Finset.sum_congr rfl
  intro J _
  rw [hcomponent A J, hcomponent B J]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportSectionTensor_isometry
    (g : SmoothRiemannianMetric I M) (p : M)
    (hdim : Module.finrank Real (TangentSpace I p) = 3)
    (η₀ : Tensor04At (I := I) (M := M) p) (y : M)
    (hy : y ∈ radialTransportSectionDomain (I := I) g p) :
    inner0S (I := I) g y 4 (radialTransportSectionTensor g p η₀ y)
        (radialTransportSectionTensor g p η₀ y) =
      inner0S (I := I) g p 4 η₀ η₀ :=
  radialTransportSectionTensor_inner_eq (I := I) g p hdim η₀ η₀ y hy

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem radialTransportTensorExtension_inner_self_le
    (g : SmoothRiemannianMetric I M) (p : M)
    (hdim : Module.finrank ℝ (TangentSpace I p) = 3)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (y : M) :
    inner0S (I := I) g y 4 (radialTransportTensorExtension g p basis η₀ W y)
        (radialTransportTensorExtension g p basis η₀ W y) ≤
      inner0S (I := I) g p 4 η₀ η₀ := by
  classical
  rw [radialTransportTensorExtension_eq_smul g p basis horth η₀ χ W hsupport hW y]
  by_cases hχ : χ y = 0
  · have hinner : 0 ≤ inner0S (I := I) g p 4 η₀ η₀ :=
      MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g p 4) η₀
    simpa [hχ, inner0S, MetricFiberData.inner] using hinner
  · have hySupport : y ∈ Function.support (χ : M → ℝ) := hχ
    have hyTsupport : y ∈ tsupport (χ : M → ℝ) := subset_closure hySupport
    have hy : y ∈ radialTransportSectionDomain (I := I) g p := hsupport hyTsupport
    let c : ℝ := (χ y) ^ 4
    have hscale : inner0S (I := I) g y 4
          (c • radialTransportSectionTensor g p η₀ y)
          (c • radialTransportSectionTensor g p η₀ y) =
        c * c * inner0S (I := I) g y 4
          (radialTransportSectionTensor g p η₀ y)
          (radialTransportSectionTensor g p η₀ y) := by
      unfold inner0S MetricFiberData.inner
      simp [map_smul, smul_eq_mul]
      ring
    rw [show (χ y) ^ 4 = c by rfl, hscale,
      radialTransportSectionTensor_isometry (I := I) g p hdim η₀ y hy]
    have hc0 : 0 ≤ c := pow_nonneg (χ.nonneg : 0 ≤ χ y) 4
    have hc1 : c ≤ 1 := by
      dsimp [c]
      exact pow_le_one₀ (χ.nonneg : 0 ≤ χ y) (χ.le_one : χ y ≤ 1)
    have hcc : c * c ≤ 1 := by nlinarith
    have hinner : 0 ≤ inner0S (I := I) g p 4 η₀ η₀ :=
      MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g p 4) η₀
    calc
      c * c * inner0S (I := I) g p 4 η₀ η₀ ≤
          1 * inner0S (I := I) g p 4 η₀ η₀ :=
        mul_le_mul_of_nonneg_right hcc hinner
      _ = inner0S (I := I) g p 4 η₀ η₀ := one_mul _

omit [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] in
private theorem localizedRadialTransportSection_nabla_center_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hW : (fun y => W y) =ᶠ[𝓝 p] radialTransportSection (I := I) g p v)
    (X : TangentSpace I p) :
    (LeviCivita (I := I) g).toFun (fun y => W y) p X = 0 := by
  have hWtotal : (T% fun y => W y) =ᶠ[𝓝 p]
      (T% fun y => radialTransportSection (I := I) g p v y) := by
    filter_upwards [hW] with y hy
    rw [hy]
  have hRsm : ContMDiffAt I I.tangent ∞
      (T% fun y => radialTransportSection (I := I) g p v y) p :=
    W.contMDiff.contMDiffAt.congr_of_eventuallyEq hWtotal.symm
  have hWmd : MDiffAt (T% fun y => W y) p :=
    W.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hRmd : MDiffAt (T% fun y => radialTransportSection (I := I) g p v y) p :=
    hRsm.mdifferentiableAt (by simp)
  have heq := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hWmd hRmd Filter.univ_mem hW
  rw [heq]
  exact radialTransportSection_nabla_center_zero (I := I) g p v X hRmd

omit [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] in
private theorem localizedRadialTransportSection_nabla2_center_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v w : TangentSpace I p)
    (W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hW : (fun y => W y) =ᶠ[𝓝 p] radialTransportSection (I := I) g p v) :
    (LeviCivita (I := I) g).toFun
      (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) p w)
        (fun y => W y)) p w = 0 := by
  let X := linearExtensionTangent (I := I) p w
  let R := radialTransportSection (I := I) g p v
  let D := covApply (LeviCivita (I := I) g) X (fun y => W y)
  let D0 := fun y => (LeviCivita (I := I) g).toFun R y
    (coordExtensionTangent (I := I) p w y)
  have hWtotal : (T% fun y => W y) =ᶠ[𝓝 p] (T% fun y => R y) := by
    filter_upwards [hW] with y hy
    rw [hy]
  have hRsm : ContMDiffAt I I.tangent ∞ (T% fun y => R y) p :=
    W.contMDiff.contMDiffAt.congr_of_eventuallyEq hWtotal.symm
  have hXsm : ContMDiff I I.tangent ∞ (T% X) :=
    linearExtensionTangent_smooth (I := I) p w
  have hDsm : ContMDiff I I.tangent ∞ (T% D) := by
    rw [← contMDiffOn_univ]
    apply covApply_contMDiffOn (cov := LeviCivita (I := I) g) hXsm
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ by rw [ENat.coe_top_add_one]]
    exact W.contMDiff
  have hXeq : X =ᶠ[𝓝 p] coordExtensionTangent (I := I) p w := by
    filter_upwards [(linExtBump (I := I) p).eventuallyEq_one] with y hy
    simp [X, linearExtensionTangent_apply, hy]
  have hEqSet : {y : M | W y = R y} ∈ 𝓝 p := by
    simpa only [R] using hW
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hEqSet
  have hUnhds : U ∈ 𝓝 p := hUopen.mem_nhds hpU
  have hD : D =ᶠ[𝓝 p] D0 := by
    filter_upwards [hUnhds, hXeq] with y hyU hXy
    have hWRy : (fun z => W z) =ᶠ[𝓝 y] R := by
      filter_upwards [hUopen.mem_nhds hyU] with z hz
      exact hUsub hz
    have hWRtotal_y : (T% fun z => W z) =ᶠ[𝓝 y] (T% fun z => R z) := by
      filter_upwards [hWRy] with z hz
      rw [hz]
    have hWmd_y : MDiffAt (T% fun z => W z) y :=
      W.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hRsm_y : ContMDiffAt I I.tangent ∞ (T% fun z => R z) y :=
      W.contMDiff.contMDiffAt.congr_of_eventuallyEq hWRtotal_y.symm
    have hRmd_y : MDiffAt (T% fun z => R z) y :=
      hRsm_y.mdifferentiableAt (by simp)
    have hcov_y := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hWmd_y hRmd_y Filter.univ_mem hWRy
    simp only [D, D0, covApply_apply]
    rw [hcov_y, hXy]
  have hDtotal : (T% D) =ᶠ[𝓝 p] (T% D0) := by
    filter_upwards [hD] with y hy
    rw [hy]
  have hD0sm : ContMDiffAt I I.tangent ∞ (T% D0) p :=
    hDsm.contMDiffAt.congr_of_eventuallyEq hDtotal.symm
  have hDmd : MDiffAt (T% D) p :=
    hDsm.contMDiffAt.mdifferentiableAt (by simp)
  have hD0md : MDiffAt (T% D0) p := hD0sm.mdifferentiableAt (by simp)
  have heq := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hDmd hD0md Filter.univ_mem hD
  change (LeviCivita (I := I) g).toFun D p w = 0
  rw [heq]
  exact radialTransportSection_nabla2_center_zero (I := I) g p v w hRsm

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem radialTransportTensorExtension_eval_eventually_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (J : Fin 4 → Fin 3) :
    (fun y => radialTransportTensorExtension g p basis η₀ W y
      (fun a => W (J a) y)) =ᶠ[𝓝 p]
      fun _ => η₀ (fun a => basis (J a)) := by
  have hA := radialTransportTensorExtension_eventually_eq
    (I := I) g p basis horth η₀ χ W hsupport hW
  have hD : radialTransportSectionDomain (I := I) g p ∈ 𝓝 p :=
    (radialTransportSectionDomain_isOpen (I := I) g p).mem_nhds
      (mem_radialTransportSectionDomain_self (I := I) g p)
  filter_upwards [hA, χ.eventuallyEq_one, hD] with y hAy hχy hy
  simp only [Pi.one_apply] at hχy
  rw [hAy, radialTransportSectionTensor, dif_pos hy]
  change η₀ (fun a => radialTransportInverseAt g p y hy (W (J a) y)) = _
  congr 1
  funext a
  rw [hW, hχy, one_smul]
  change radialTransportInverseAt g p y hy
      (radialTransportLinearMapAt g p y (basis (J a))) = basis (J a)
  exact radialTransportInverseAt_left_inverse (I := I) g p y hy (basis (J a))

omit [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem radialTransportTensorExtension_nabla_center_zero
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (d : CanonicalSpatialDerivs0S (I := I) (M := M) (LeviCivita (I := I) g)
      (radialTransportTensorExtension g p basis η₀ W)) :
    d.nablaA p = 0 := by
  apply ext0S_basis (I := I) basis
  intro idx
  change d.nablaA p (fun a => basis (idx a)) = 0
  let X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := W (idx 0)
  let V : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    fun a => W (idx a.succ)
  have hWp : ∀ i : Fin 3, W i p = basis i := by
    intro i
    rw [hW, χ.eq_one, one_smul]
    exact radialTransportSection_center (I := I) g p (basis i) 0 (by
      rw [norm_zero]
      exact radialRadius_pos (I := I) g p)
  have hslots : (fun a : Fin 5 => basis (idx a)) =
      Fin.cons (X p) (fun a : Fin 4 => V a p) := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp [X, hWp]
    · simp [V, hWp]
  have hfirst := d.first.eval_smooth_slots (I := I) X V p
  have hscalar := radialTransportTensorExtension_eval_eventually_eq
    (I := I) g p basis horth η₀ χ W hsupport hW (fun a => idx a.succ)
  have hderiv : extDerivFun (I := I)
      (fun y : M => radialTransportTensorExtension g p basis η₀ W y
        (fun a : Fin 4 => V a y)) p (X p) = 0 := by
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_congr_eventually
      (I := I) (v := X p) (by simpa [V] using hscalar)]
    simp [extDerivFun]
  have hconn : ∀ a : Fin 4,
      (LeviCivita (I := I) g).toFun (fun y => V a y) p (X p) = 0 := by
    intro a
    have hVi : (fun y => V a y) =ᶠ[𝓝 p]
        radialTransportSection (I := I) g p (basis (idx a.succ)) := by
      filter_upwards [χ.eventuallyEq_one] with y hy
      simp only [Pi.one_apply] at hy
      simp [V, hW, hy]
    exact localizedRadialTransportSection_nabla_center_zero
      (I := I) g p (basis (idx a.succ)) (V a) hVi (X p)
  rw [hslots, hfirst, hderiv]
  have hsum : (∑ a : Fin 4,
      radialTransportTensorExtension g p basis η₀ W p
        (Function.update (fun b : Fin 4 => V b p) a
          ((LeviCivita (I := I) g).toFun (fun y => V a y) p (X p)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [hconn a]
    exact (radialTransportTensorExtension g p basis η₀ W p).toMultilinearMap.map_update_zero
      (fun b => V b p) a
  rw [hsum, sub_zero]

omit [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem radialTransportTensorExtension_nabla2_diagonal_center_zero
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (d : CanonicalSpatialDerivs0S (I := I) (M := M) (LeviCivita (I := I) g)
      (radialTransportTensorExtension g p basis η₀ W))
    (a : Fin 3) (J : Fin 4 → Fin 3) :
    d.nabla2A p (Fin.cons (basis a) (Fin.cons (basis a) (fun j => basis (J j)))) = 0 := by
  let A := radialTransportTensorExtension g p basis η₀ W
  let X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨linearExtensionTangent (I := I) p (basis a),
      linearExtensionTangent_smooth (I := I) p (basis a)⟩
  let V : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    fun j => W (J j)
  have hXp : X p = basis a := by
    exact linearExtensionTangent_eq (I := I) p (basis a)
  have hWp : ∀ i : Fin 3, W i p = basis i := by
    intro i
    rw [hW, χ.eq_one, one_smul]
    exact radialTransportSection_center (I := I) g p (basis i) 0 (by
      rw [norm_zero]
      exact radialRadius_pos (I := I) g p)
  have hVp : ∀ j : Fin 4, V j p = basis (J j) := by
    intro j
    exact hWp (J j)
  have hVi : ∀ j : Fin 4, (fun y => V j y) =ᶠ[𝓝 p]
      radialTransportSection (I := I) g p (basis (J j)) := by
    intro j
    filter_upwards [χ.eventuallyEq_one] with y hy
    simp only [Pi.one_apply] at hy
    simp [V, hW, hy]
  let D : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := fun j =>
    ⟨covApply (LeviCivita (I := I) g) (fun y => X y) (fun y => V j y), by
      rw [← contMDiffOn_univ]
      apply covApply_contMDiffOn (cov := LeviCivita (I := I) g) X.contMDiff
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ by rw [ENat.coe_top_add_one]]
      exact (V j).contMDiff⟩
  have hD0 : ∀ j : Fin 4, D j p = 0 := by
    intro j
    change (LeviCivita (I := I) g).toFun (fun y => V j y) p (X p) = 0
    exact localizedRadialTransportSection_nabla_center_zero
      (I := I) g p (basis (J j)) (V j) (hVi j) (X p)
  have hD2 : ∀ j : Fin 4,
      (LeviCivita (I := I) g).toFun (fun y => D j y) p (X p) = 0 := by
    intro j
    have hmain := localizedRadialTransportSection_nabla2_center_zero
      (I := I) g p (basis (J j)) (basis a) (V j) (hVi j)
    change (LeviCivita (I := I) g).toFun
      (covApply (LeviCivita (I := I) g)
        (linearExtensionTangent (I := I) p (basis a)) (fun y => V j y)) p (X p) = 0
    rw [hXp]
    exact hmain
  have hnabla : d.nablaA p = 0 :=
    radialTransportTensorExtension_nabla_center_zero
      (I := I) g p basis horth η₀ χ W hsupport hW d
  let q : Fin 4 → M → ℝ := fun j y =>
    A y (fun b => (Function.update V j (D j)) b y)
  have hqsm : ∀ j : Fin 4, ContMDiff I 𝓘(ℝ, ℝ) ∞ (q j) := by
    intro j
    let Vj : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
      Function.update V j (D j)
    have hsm := DifferentialGeometry.TensorMultilinear.contMDiff_tensor0SField_apply
      (I := I) (M := M) A Vj
    simpa only [q, Vj] using hsm
  have hqderiv : ∀ j : Fin 4, extDerivFun (I := I) (q j) p (X p) = 0 := by
    intro j
    let Vj : Fin 4 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
      Function.update V j (D j)
    have hfirst := d.first.eval_smooth_slots (I := I) X Vj p
    have hsum : (∑ k : Fin 4, A p
        (Function.update (fun b : Fin 4 => Vj b p) k
          ((LeviCivita (I := I) g).toFun (fun y => Vj k y) p (X p)))) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hkj : k = j
      · subst k
        have hcov : (LeviCivita (I := I) g).toFun (fun y => Vj j y) p (X p) = 0 := by
          simpa [Vj] using hD2 j
        rw [hcov]
        exact (A p).map_update_zero (fun b => Vj b p) j
      · apply (A p).map_coord_zero j
        rw [Function.update_of_ne (Ne.symm hkj)]
        simp [Vj, hD0]
    rw [hnabla] at hfirst
    simp only [Tensor0SSpace.zero_apply] at hfirst
    rw [hsum, sub_zero] at hfirst
    simpa [q, Vj] using hfirst.symm
  let f : M → ℝ := fun y => A y (fun j => V j y)
  have hfconst : f =ᶠ[𝓝 p] fun _ => η₀ (fun j => basis (J j)) := by
    simpa [f, A, V] using radialTransportTensorExtension_eval_eventually_eq
      (I := I) g p basis horth η₀ χ W hsupport hW J
  have hEqSet : {y : M | f y = η₀ (fun j => basis (J j))} ∈ 𝓝 p := by
    simpa only [Filter.EventuallyEq, Pi.one_apply] using hfconst
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hEqSet
  have hzeroFirst : (fun y => extDerivFun (I := I) f y (X y)) =ᶠ[𝓝 p] 0 := by
    filter_upwards [hUopen.mem_nhds hpU] with y hy
    have hfy : f =ᶠ[𝓝 y] fun _ => η₀ (fun j => basis (J j)) := by
      filter_upwards [hUopen.mem_nhds hy] with z hz
      exact hUsub hz
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_congr_eventually
      (I := I) (v := X y) hfy]
    simp [extDerivFun]
  let V5 : Fin 5 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := Fin.cons X V
  let G : M → ℝ := fun y => d.nablaA y (fun j => V5 j y)
  have hG : G =ᶠ[𝓝 p] fun y => -(∑ j : Fin 4, q j y) := by
    filter_upwards [hzeroFirst] with y hy
    simp only [Pi.zero_apply] at hy
    have hfirst := d.first.eval_smooth_slots (I := I) X V y
    have hXV : (fun j : Fin 5 => V5 j y) =
        Fin.cons (X y) (fun j => V j y) := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j <;> rfl
    change d.nablaA y (fun j : Fin 5 => V5 j y) = _
    rw [hXV]
    rw [hfirst, hy, zero_sub]
    simp only [q, A]
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    funext b
    by_cases hbj : b = j
    · subst b
      simp [D, covApply_apply]
    · simp [Function.update_of_ne hbj]
  have hsumqmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ j : Fin 4, q j y) p := by
    change MDifferentiableAt I 𝓘(ℝ, ℝ) (Finset.univ.sum q) p
    apply DifferentialGeometry.Tensor.RicciIdentity.mdiffAt_finset_sum
    intro j _
    exact (hqsm j).contMDiffAt.mdifferentiableAt (by simp)
  have hGderiv : extDerivFun (I := I) G p (X p) = 0 := by
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_congr_eventually
      (I := I) (v := X p) hG]
    rw [DifferentialGeometry.Tensor.RicciIdentity.extDerivFun_neg_at
      (I := I) (x := p) (X p) hsumqmd]
    change -extDerivFun (I := I) (Finset.univ.sum q) p (X p) = 0
    rw [DifferentialGeometry.Tensor.RicciIdentity.extDerivFun_finset_sum_at
      (I := I) Finset.univ q (X p) (fun j _ =>
        (hqsm j).contMDiffAt.mdifferentiableAt (by simp))]
    simp [hqderiv]
  have hV5p : ∀ j : Fin 5,
      V5 j p = Fin.cases (basis a) (fun k => basis (J k)) j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [V5] using hXp
    · simpa [V5] using hVp k
  have hslots :
      (Fin.cons (basis a) (Fin.cons (basis a) (fun j => basis (J j))) :
        Fin 6 → TangentSpace I p) =
      (Fin.cons (X p) (fun j : Fin 5 => V5 j p) : Fin 6 → TangentSpace I p) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using hXp.symm
    · simpa using (hV5p k).symm
  have hsecond := d.second.eval_smooth_slots (I := I) X V5 p
  have hsum2 : (∑ k : Fin 5, d.nablaA p
      (Function.update (fun b : Fin 5 => V5 b p) k
        ((LeviCivita (I := I) g).toFun (fun y => V5 k y) p (X p)))) = 0 := by
    rw [hnabla]
    simp
  rw [hslots, hsecond]
  change extDerivFun (I := I) G p (X p) - _ = 0
  rw [hGderiv, hsum2, sub_zero]

omit [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem radialTransportTensorExtension_metricTrace_center_zero
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (d : CanonicalSpatialDerivs0S (I := I) (M := M) (LeviCivita (I := I) g)
      (radialTransportTensorExtension g p basis η₀ W)) :
    metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Fin 3)) (d.nabla2A p) = 0 := by
  apply ext0S_basis (I := I) basis
  intro J
  change metricTrace0S2TensorInBasis (I := I) basis
    (identityInvMetric (Idx := Fin 3)) (d.nabla2A p)
      (fun a => basis (J a)) = 0
  rw [metricTrace0S2TensorInBasis_apply]
  unfold metricTrace0S2InBasis
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [identityInvMetric_apply_self, one_mul]
    exact radialTransportTensorExtension_nabla2_diagonal_center_zero
      (I := I) g p basis horth η₀ χ W hsupport hW d i J
  · intro j _ hji
    rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hji.symm, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end TensorTransport
end RadialTransportLinear

end DifferentialGeometry.Geometry.Riemannian.Variation

end
