import DifferentialGeometry.Analysis.Calculus.FiniteDimension
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.Energy
import DifferentialGeometry.Geometry.Metric.Family.TimeDerivative
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def dirichletEnergyVariation
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t : ℝ)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, -deriv (fun s => (g s).inner x) t
      (gradientFun (I := I_half n) (g t) u.toFun x)
      (gradientFun (I := I_half n) (g t) v.toFun x) +
    (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
      (g t).inner x
        (gradientFun (I := I_half n) (g t) u.toFun x)
        (gradientFun (I := I_half n) (g t) v.toFun x)
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t))

theorem hasDerivAt_dirichletEnergy_self
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (u : SmoothScalarDirichlet q) :
    HasDerivAt (fun s => dirichletEnergy (G.metric s) u u)
      (dirichletEnergyVariation G.metric t u u) t := by
  have hgram := fun α i j => hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) α i j
  have hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (I_half n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u.toFun p.2) (D.regular ×ˢ (univ : Set M)) :=
    (u.smooth.comp contMDiff_snd).contMDiffOn
  have hgrad := gradSq_joint (I := I_half n) G.metric D.regular_isOpen hgram
    (fun _ x => u.toFun x) hu
  have hfirst := first_var_joint (I := I_half n) (M := M)
    (f := fun s x => (G.metric s).inner x
      (gradientFun (I := I_half n) (G.metric s) u.toFun x)
      (gradientFun (I := I_half n) (G.metric s) u.toFun x))
    D.regular_isOpen ht hgram hgrad
  change HasDerivAt (fun s => dirichletEnergy (G.metric s) u u) _ t at hfirst
  refine hfirst.congr_deriv ?_
  apply integral_congr_ae
  filter_upwards [] with x
  let Q : Tensor0SSpace 2 (I_half n) x :=
    (- (1 / 2 : ℝ)) •
      (((continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm.toContinuousLinearMap).comp
        (deriv (fun s => (G.metric s).inner x) t)).uncurryLeft
  have hmetric (v w : TangentSpace (I_half n) x) :
      HasDerivAt (fun s => (G.metric s).inner x v w)
        (-2 * Q (fun i : Fin 2 => if i = 0 then v else w)) t := by
    convert hG.hasDerivAt_inner ht x v w using 1
    change -2 * (- (1 / 2 : ℝ) * (deriv (fun s => (G.metric s).inner x) t v w)) = _
    ring
  have hdf (v : TangentSpace (I_half n) x) :
      HasDerivAt (fun _ : ℝ => mvfderiv (I := I_half n) u.toFun x v)
        (mvfderiv (I := I_half n) (fun _ : M => (0 : ℝ)) x v) t := by
    simpa only [mvfderiv_const, zero_apply] using
      hasDerivAt_const t (mvfderiv (I := I_half n) u.toFun x v)
  have hd := normGradSq_time (I := I_half n) G.metric
    (fun _ x => u.toFun x) (fun _ => 0) Q hmetric hdf
  rw [hd.deriv, gradientFun_const, map_zero, zero_apply, mul_zero, add_zero]
  change 2 * (- (1 / 2 : ℝ) *
    deriv (fun s => (G.metric s).inner x) t
      (gradientFun (I := I_half n) (G.metric t) u.toFun x)
      (gradientFun (I := I_half n) (G.metric t) u.toFun x)) + _ = _
  ring

theorem abs_dirichletEnergyVariation_self_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t C B : ℝ)
    (hmetric : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      |deriv (fun s => (g s).inner x) t v v| ≤ C * (g t).inner x v v)
    (htrace : ∀ x : M, |traceTimeDerivMetric (I := I_half n) g t x| ≤ B)
    (u : SmoothScalarDirichlet q) :
    |dirichletEnergyVariation g t u u| ≤ (C + (1 / 2) * B) * dirichletEnergy (g t) u u := by
  let e : M → ℝ := fun x => (g t).inner x
    (gradientFun (I := I_half n) (g t) u.toFun x)
    (gradientFun (I := I_half n) (g t) u.toFun x)
  have hint : Integrable (fun x => (C + (1 / 2) * B) * e x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) :=
    (dirichletEnergy_integrable (g t) u u).const_mul _
  have hb := norm_integral_le_of_norm_le hint (f := fun x =>
    -deriv (fun s => (g s).inner x) t
      (gradientFun (I := I_half n) (g t) u.toFun x)
      (gradientFun (I := I_half n) (g t) u.toFun x) +
    (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x * e x) ?_
  · rw [Real.norm_eq_abs, integral_const_mul] at hb
    exact hb
  · filter_upwards [] with x
    have hpos : 0 ≤ e x := metric_inner_self_nonneg (g t) x _
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |deriv (fun s => (g s).inner x) t
          (gradientFun (I := I_half n) (g t) u.toFun x)
          (gradientFun (I := I_half n) (g t) u.toFun x)| +
          (1 / 2) * |traceTimeDerivMetric (I := I_half n) g t x| * e x := by
        simpa only [abs_neg, abs_mul, abs_of_nonneg hpos,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using abs_add_le
          (-deriv (fun s => (g s).inner x) t
            (gradientFun (I := I_half n) (g t) u.toFun x)
            (gradientFun (I := I_half n) (g t) u.toFun x))
          ((1 / 2) * traceTimeDerivMetric (I := I_half n) g t x * e x)
      _ ≤ C * e x + (1 / 2) * B * e x := by
        gcongr
        · exact hmetric x _
        · exact htrace x
      _ = _ := by ring

theorem exists_dirichletEnergyVariation_bound
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {K : Set ℝ} (hK : IsCompact K) (hreg : K ⊆ D.regular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ u : SmoothScalarDirichlet q,
      |dirichletEnergyVariation G.metric t u u| ≤ C * dirichletEnergy (G.metric t) u u := by
  obtain ⟨C, hC, hmetric⟩ := hG.exists_inner_time_deriv_bound hK hreg
  have htrace := (continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
    D.regular_isOpen (fun α i j => hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) α i j)).mono
      (Set.prod_mono hreg Set.Subset.rfl)
  obtain ⟨B, hB⟩ := (hK.prod isCompact_univ).exists_bound_of_continuousOn htrace
  refine ⟨C + (1 / 2) * max B 0,
    add_nonneg hC (mul_nonneg (by norm_num) (le_max_right _ _)), fun t ht u => ?_⟩
  apply abs_dirichletEnergyVariation_self_le G.metric t C (max B 0) (hmetric t ht) _ u
  intro x
  have h := hB (t, x) ⟨ht, mem_univ x⟩
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

section Finite

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

local instance dualNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (E := V) (F := ℝ)

local instance dualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance bilinearNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (E := V) (F := V →L[ℝ] ℝ)

local instance bilinearNormedSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem differentiableAt_dirichletFinEnergy
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    DifferentiableAt ℝ (fun s => dirichletFinEnergy (G.metric s) J) t := by
  apply differentiableAt_clm_apply.mpr
  intro v
  apply differentiableAt_clm_apply.mpr
  intro w
  have hvw := (hasDerivAt_dirichletEnergy_self hG ht (J (v + w))).differentiableAt
  have hv := (hasDerivAt_dirichletEnergy_self hG ht (J v)).differentiableAt
  have hw := (hasDerivAt_dirichletEnergy_self hG ht (J w)).differentiableAt
  have hp := ((hvw.sub hv).sub hw).div_const 2
  apply hp.congr_of_eventuallyEq
  filter_upwards [] with s
  change dirichletEnergy (G.metric s) (J v) (J w) = _
  simp only [Pi.sub_apply]
  rw [map_add, dirichletEnergy_add_left, dirichletEnergy_add_right,
    dirichletEnergy_add_right, dirichletEnergy_symm (G.metric s) (J w) (J v)]
  ring

theorem hasDerivWithinAt_dirichletFinEnergy
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    {γ : ℝ → V} {v : V} {S : Set ℝ} (hγ : HasDerivWithinAt γ v S t) :
    HasDerivWithinAt
      (fun s => dirichletEnergy (G.metric s) (J (γ s)) (J (γ s)))
      (2 * dirichletEnergy (G.metric t) (J v) (J (γ t)) +
        dirichletEnergyVariation G.metric t (J (γ t)) (J (γ t))) S t := by
  let L : ℝ → V →L[ℝ] V →L[ℝ] ℝ := fun s => dirichletFinEnergy (G.metric s) J
  have hL : HasDerivAt L (deriv L t) t :=
    (differentiableAt_dirichletFinEnergy hG ht J).hasDerivAt
  have hstatic : HasDerivAt
      (fun s => dirichletEnergy (G.metric s) (J (γ t)) (J (γ t)))
      (deriv L t (γ t) (γ t)) t := by
    simpa only [L, dirichletFinEnergy_apply, map_zero, zero_apply, add_zero] using
      (hL.clm_apply (hasDerivAt_const t (γ t))).clm_apply (hasDerivAt_const t (γ t))
  have hident := hstatic.unique (hasDerivAt_dirichletEnergy_self hG ht (J (γ t)))
  have hcurve := (hL.hasDerivWithinAt.clm_apply hγ).clm_apply hγ
  apply hcurve.congr_deriv
  simp only [add_apply]
  rw [hident]
  change _ + dirichletEnergy (G.metric t) (J v) (J (γ t)) +
    dirichletEnergy (G.metric t) (J (γ t)) (J v) = _
  rw [dirichletEnergy_symm (G.metric t) (J (γ t)) (J v)]
  ring

theorem hasDerivWithinAt_dirichletGalerkin_energy
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) (a : ℝ)
    {γ : ℝ → V} {v : V} {S : Set ℝ} (hγ : HasDerivWithinAt γ v S t)
    (hweak : dirichletFinMass (G.metric t) J v =
      dirichletFinWeakForm (G.metric t) X a J (γ t)) :
    HasDerivWithinAt
      (fun s => dirichletEnergy (G.metric s) (J (γ s)) (J (γ s)))
      (-2 * dirichletMass (G.metric t) (J v) (J v) +
        2 * dirichletDrift (G.metric t) X (J (γ t)) (J v) -
        2 * a * dirichletMass (G.metric t) (J (γ t)) (J v) +
        dirichletEnergyVariation G.metric t (J (γ t)) (J (γ t))) S t := by
  have hderiv := hasDerivWithinAt_dirichletFinEnergy hG ht J hγ
  have heval := congrArg (fun L : V →L[ℝ] ℝ => L v) hweak
  change dirichletMass (G.metric t) (J v) (J v) =
    -dirichletEnergy (G.metric t) (J (γ t)) (J v) +
      dirichletDrift (G.metric t) X (J (γ t)) (J v) -
      a * dirichletMass (G.metric t) (J (γ t)) (J v) at heval
  apply hderiv.congr_deriv
  rw [dirichletEnergy_symm (G.metric t) (J v) (J (γ t))]
  linarith

end Finite

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
