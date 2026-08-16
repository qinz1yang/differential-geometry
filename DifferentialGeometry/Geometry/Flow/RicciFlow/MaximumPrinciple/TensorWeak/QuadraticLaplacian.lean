import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.Certification
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.FirstNull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]

omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem laplacianAt_quad_eq_metricTraceFirstTwo_of_covZero_null
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := ∞) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := ∞) 4}
    {t : Real} {x : M} {v : TangentSpace I x}
    (hreal1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (G.connection t) B nablaB)
    (hreal2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 (G.connection t) nablaB nabla2B)
    (V : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _))
    (hV : V x = v)
    (hcovV : ∀ W : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _),
      ((G.connection t) (fun p : M => V p) x) (W x) = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (G.connection t) (1 : WithTop ℕ∞))
    (hcovInf : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (G.connection t) ∞)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (G.metric t) x basis) :
    laplacianAt (I := I) G t (fun y : M => B y (vec2 (I := I) (V y) (V y))) x =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) (nabla2B x)
        (vec2 (I := I) v v) := by
  classical
  let phi : M -> Real := fun p : M => B p (vec2 (I := I) (V p) (V p))
  have hphi : ContMDiff I 𝓘(Real, Real) ∞ phi := by
    let Slots : Fin 2 -> ContMDiffSection I E ∞ (TangentSpace I : M -> Type _) :=
      fun _ => V
    have hraw := TensorMultilinear.contMDiff_tensor0SField_apply (I := I) (M := M) B Slots
    simpa [phi, Slots, vec2_self_eq_const] using hraw
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible_gen (I := I)
      (G.connection t) (G.metric t) := by
    exact (G.metricCompatible t)
  let du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1 :=
    duSec (I := I) phi hphi
  let Hess : (y : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y :=
    fun y => hessianSec (I := I) (G.connection t) hcovInf phi hphi y
  have hdu : DuFieldRealizes (I := I) phi du := by
    simpa [du] using duSec_realizes (I := I) phi hphi
  have hHess : HessianRealizesNablaDuAt (I := I) (G.connection t) du Hess x := by
    simpa [du, Hess] using hessianSec_realizesAt (I := I) (G.connection t) hcovInf phi hphi x
  have hAreg : ∀ Y : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _),
      ContMDiffAt I (I.prod 𝓘(Real, E)) 1
        (fun p : M => (⟨p, ((G.connection t) (fun q : M => V q) p) (Y p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x := by
    intro Y
    simpa using CovariantDerivative.smoothSections_cov_contMDiffAt_one
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (G.connection t) hcov1 Y V x
  have hhess : ∀ U W : TangentSpace I x,
      nabla2B x (metricTraceInput (I := I) U W (vec2 (I := I) v v)) =
        Hess x (vec2 (I := I) U W) := by
    exact nabla2Eval_hess_slots (I := I) (M := M)
      (cov := G.connection t) (B := B) (nablaB := nablaB) (nabla2B := nabla2B)
      (du := du) (Hess := Hess) hreal1 hreal2 V hV hcovV hkerL hkerR
      hdu hHess hAreg
  have hlap : ScalarLaplacianRealizesTraceAt (I := I) (G.connection t) (G.metric t)
      phi (Hess x) := by
    simpa [Hess] using scalarLap_smooth (I := I) (M := M)
      (cov := G.connection t) hcovInf (G.metric t) hmc phi hphi
  have hlap' : laplacianAt (I := I) G t phi x =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) (Hess x) Fin.elim0 := by
    simpa [laplacianAt, ScalarLaplacianRealizesTraceAt] using hlap
  rw [hlap']
  have hinv : MetricInverseInBasis_gen (I := I) (G.metric t) x basis
      DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (G.metric t) basis horth
  have htraceH := metricTraceFirstTwo0SAt_eq_sum_basis (I := I) (G.metric t)
    basis DifferentialGeometry.Geometry.Curvature.delta3 hinv (Hess x) Fin.elim0
  have htraceN := metricTraceFirstTwo0SAt_eq_sum_basis (I := I) (G.metric t)
    basis DifferentialGeometry.Geometry.Curvature.delta3 hinv (nabla2B x)
    (vec2 (I := I) v v)
  rw [htraceH, htraceN]
  unfold metricTrace0S2InBasis
  simp only [Fin.sum_univ_three, DifferentialGeometry.Geometry.Curvature.delta3, Fin.isValue,
    Fin.reduceEq, ↓reduceIte, one_mul, zero_mul, add_zero]
  have hinput : ∀ U W : TangentSpace I x,
      vec2 (I := I) U W = metricTraceInput (I := I) U W Fin.elim0 := by
    intro U W
    funext q
    fin_cases q <;> rfl
  have hhess' : ∀ U W : TangentSpace I x,
      (nabla2B x) (metricTraceInput (I := I) U W
          (metricTraceInput (I := I) v v Fin.elim0)) =
        (Hess x) (metricTraceInput (I := I) U W Fin.elim0) := by
    intro U W
    simpa [hinput] using hhess U W
  rw [hinput v v]
  rw [hhess' (basis 0) (basis 0), hhess' (basis 1) (basis 1),
    hhess' (basis 2) (basis 2)]

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [T2Space M] [SigmaCompactSpace M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)]
  [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I] in
theorem derivWithin_nonpos_of_nonneg_left
    {phi : Real -> Real} {a b t d : Real}
    (hat : a < t) (htb : t ≤ b)
    (hnonneg : ∀ s : Real, s ∈ Set.Icc a t -> 0 ≤ phi s)
    (hzero : phi t = 0)
    (hderiv : HasDerivWithinAt phi d (Set.Ioc a b) t) :
    d ≤ 0 := by
  let m : Real := (a + t) / 2
  have ham : a < m := by
    dsimp [m]
    linarith
  have hmt : m < t := by
    dsimp [m]
    linarith
  have hsubset : Set.Icc m t ⊆ Set.Ioc a b := by
    intro y hy
    exact ⟨lt_of_lt_of_le ham hy.1, hy.2.trans htb⟩
  have hderiv_m : HasDerivWithinAt phi d (Set.Icc m t) t :=
    hderiv.mono hsubset
  have hmin : IsMinOn phi (Set.Icc m t) t := by
    intro y hy
    rw [hzero]
    exact hnonneg y ⟨(le_of_lt ham).trans hy.1, hy.2⟩
  have hlocal : IsLocalMinOn phi (Set.Icc m t) t := hmin.localize
  have hdir : m - t ∈ posTangentConeAt (Set.Icc m t) t := by
    have hseg : segment Real t m ⊆ Set.Icc m t := by
      rw [segment_symm, segment_eq_Icc (le_of_lt hmt)]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg_deriv :
      0 ≤ (fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real) (m - t) :=
    hlocal.fderivWithin_nonneg hdir
  have huniq : UniqueDiffWithinAt Real (Set.Icc m t) t :=
    (uniqueDiffOn_Icc hmt).uniqueDiffWithinAt ⟨le_of_lt hmt, le_rfl⟩
  have hderiv_eq : derivWithin phi (Set.Icc m t) t = d :=
    hderiv_m.derivWithin huniq
  have hlin :
      (fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real) (m - t) =
        (m - t) * derivWithin phi (Set.Icc m t) t := by
    rw [← fderivWithin_derivWithin (𝕜 := Real) (f := phi)
      (s := Set.Icc m t) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real).map_smul
        (m - t) (1 : Real))
  rw [hlin, hderiv_eq] at hnonneg_deriv
  exact nonpos_of_mul_nonneg_right hnonneg_deriv (sub_neg.mpr hmt)


omit [SigmaCompactSpace M] in
theorem tensorParabolic_no_null_of_positive_reaction_at_min
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real} {t : Real} {x : M} {v : TangentSpace I x}
    (ht : t ∈ Set.Ioc 0 T)
    (hSderivs : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S)
    (hmc : ∀ s : Real,
      DifferentialGeometry.Geometry.Connection.IsMetricCompatible_gen (I := I) (cov s) (G s))
    (hcov1 : ∀ s : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally (cov s) 1)
    (hcovInf : ∀ s : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally (cov s) ∞)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S)
      (fun _t x => (0 : TangentSpace I x)) N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T)
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hpsd : ∀ s : Real, s ∈ Set.Icc 0 t -> ∀ y : M,
      TwoTensorNonnegativeAt (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S s) y)
    (hnull : twoTensorSecToFamily (I := I) (M := M) S t x v v = 0)
    (V : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _))
    (hV : V x = v)
    (hcovV : ∀ W : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _),
      ((cov t) (fun p : M => V p) x) (W x) = 0)
    (hreaction_pos : 0 < N t (G t)
      (twoTensorSecToFamily (I := I) (M := M) S t) x v v)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (G t) x basis) :
    False := by
  classical
  let Sraw : TwoTensorFamily (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) S
  let phi : M -> Real := fun y => S t y (vec2 (I := I) (V y) (V y))
  have hphi_smooth : ContMDiff I 𝓘(Real, Real) ∞ phi := by
    let Slots : Fin 2 -> ContMDiffSection I E ∞ (TangentSpace I : M -> Type _) :=
      fun _ => V
    have hraw := TensorMultilinear.contMDiff_tensor0SField_apply (I := I) (M := M) (S t) Slots
    simpa [phi, Slots, vec2_self_eq_const] using hraw
  have hphi_min : IsMinOn phi Set.univ x := by
    intro y _
    have hpsdt := hpsd t (by exact ⟨le_of_lt ht.1, le_rfl⟩) y
    calc
      phi x = Sraw t x v v := by
        simp [phi, Sraw, hV]
      _ = 0 := hnull
      _ ≤ Sraw t y (V y) (V y) := hpsdt (V y)
      _ = phi y := by simp [phi, Sraw]
  let Gt : MetricConnectionFamily (I := I) (M := M) Real :=
    { metric := fun _ => G t
      connection := fun _ => cov t
      metricCompatible := fun _ => hmc t }
  have hlap_eq := laplacianAt_quad_eq_metricTraceFirstTwo_of_covZero_null
    (I := I) (M := M) (G := Gt) (B := S t) (nablaB := nablaS t)
    (nabla2B := nabla2S t) (t := t) (x := x) (v := v)
    (hSderivs.first t) (hSderivs.second t) V hV hcovV
  have hkerL : ∀ w : TangentSpace I x, (S t x) (vec2 (I := I) v w) = 0 := by
    intro w
    have hsymt := hsym t (by exact ⟨le_of_lt ht.1, ht.2⟩) x
    have hpsdt := hpsd t (by exact ⟨le_of_lt ht.1, le_rfl⟩) x
    exact psd_null_left_raw (I := I) (M := M) hsymt
      (twoTensorSecToFamily_bilin (I := I) (M := M) S t x)
      hpsdt (by simpa [Sraw, twoTensorSecToFamily_apply] using hnull) w
  have hkerR : ∀ w : TangentSpace I x, (S t x) (vec2 (I := I) w v) = 0 := by
    intro w
    have hsymt := hsym t (by exact ⟨le_of_lt ht.1, ht.2⟩) x
    have hpsdt := hpsd t (by exact ⟨le_of_lt ht.1, le_rfl⟩) x
    exact psd_null_right_raw (I := I) (M := M) hsymt
      (twoTensorSecToFamily_bilin (I := I) (M := M) S t x)
      hpsdt (by simpa [Sraw, twoTensorSecToFamily_apply] using hnull) w
  have hlap_eq' := hlap_eq hkerL hkerR (hcov1 t) (hcovInf t) basis horth
  have hlap_nonneg : 0 ≤ laplacianAt (I := I) Gt t phi x := by
    rw [laplacianAt]
    have hmin : IsLocalMin phi x := (isLocalMinOn_univ_iff).1 hphi_min.localize
    exact laplacian_nonneg_at_spatial_min_of_metricCompatible
      (I := I) (cov := cov t) (G t) (hmc t)
      hmin (hphi_smooth.mdifferentiable (by simp) x)
      (by filter_upwards with y using hphi_smooth.mdifferentiable (by simp) y)
      (gradientFun_mdiffAt (I := I) (G t) hphi_smooth x)
  rcases hparabolic.evaluatedInequality with ⟨timeDeriv, htime, hineq⟩
  have htime_deriv : HasDerivWithinAt (fun s : Real => Sraw s x v v)
      (timeDeriv t x v) (Set.Ioc 0 T) t := by
    have h := htime t ht x v
    exact h.mono (by intro s hs; exact ⟨le_of_lt hs.1, hs.2⟩)
  have htime_nonpos : timeDeriv t x v ≤ 0 := by
    apply derivWithin_nonpos_of_nonneg_left
      (a := 0) (b := T) (t := t) (d := timeDeriv t x v)
      ht.1 ht.2
    · intro s hs
      exact hpsd s hs x v
    · exact hnull
    · exact htime_deriv
  have hheat_eq : tensorHeatWithDrift2QuadMetricAt (I := I) (G t)
      (fun _y : M => 0) (nabla2S t x) (nablaS t x) v =
      laplacianAt (I := I) Gt t phi x := by
    rw [tensorHeatWithDrift2QuadMetricAt_zero_drift]
    rw [hlap_eq']
  have hineq' : tensorHeatWithDrift2QuadMetricAt (I := I) (G t)
      (fun _y : M => 0) (nabla2S t x) (nablaS t x) v +
        N t (G t) (Sraw t) x v v ≤ timeDeriv t x v := by
    exact hineq t ht x v
  have htime_pos : 0 < timeDeriv t x v := by
    nlinarith [hlap_nonneg, hreaction_pos, hheat_eq, hineq']
  nlinarith

end DifferentialGeometry.PDE.RicciFlow
