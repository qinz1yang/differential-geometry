import DifferentialGeometry.Analysis.Elliptic.WithBoundary.Neumann.Unrestricted.H1
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorH1Compl
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorSmoothScalarPreH1
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.GreenWithBoundary
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Green
open DifferentialGeometry.Geometry.Operator


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Operator.WithBoundary

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [CompactSpace M]

private theorem boundaryFaceSum_smoothSmul_grad_eq_zero_of_h_interior_support
    (g : SmoothRiemannianMetric (I_half n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ (I_half n).interior M) :
    boundaryFaceSum (I := I_half n) g
        (smoothSmul (I := I_half n) f hf
          (gradGWithBoundarySection (I := I_half n) g hh hh_int)) = 0 := by
  classical
  set X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯ :=
    gradGWithBoundarySection (I := I_half n) g hh hh_int with hX_def
  set Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯ :=
    smoothSmul (I := I_half n) f hf X with hY_def
  have hY_cs : HasCompactSupport Y := HasCompactSupport.of_compactSpace _
  have hX_int : tsupport (X : ∀ x, TangentSpace (I_half n) x) ⊆
      (I_half n).interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior
      (I := I_half n) g hh hh_int
  have hY_int : tsupport (Y : ∀ x, TangentSpace (I_half n) x) ⊆
      (I_half n).interior M :=
    tsupport_smoothSmul_subset_interior (I := I_half n) hf X hX_int
  have h_div_Y_zero :
      ∫ x, divergenceGWithBoundary (I := I_half n) g Y x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) = 0 :=
    integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
      (I := I_half n) g Y hY_cs hY_int
  have h_stokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I_half n) g Y
  rw [h_div_Y_zero] at h_stokes
  exact h_stokes.symm

omit [CompactSpace M] in
lemma UnrestrictedSmoothScalar.oneSubLap_continuous_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M} (u : UnrestrictedSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    Continuous (fun x : M =>
      u.toFun x - ΔGWithBoundary (I := I_half n) g u.smooth hu_int x) :=
  u.smooth.continuous.sub
    (Δ_g_with_boundary_continuous (I := I_half n) g u.smooth hu_int)

lemma UnrestrictedSmoothScalar.oneSubLap_memLp_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M} (u : UnrestrictedSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    MemLp (fun x : M =>
        u.toFun x - ΔGWithBoundary (I := I_half n) g u.smooth hu_int x)
      2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  exact (u.oneSubLap_continuous_of_interior_support hu_int).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def UnrestrictedSmoothScalar.oneSubLapInteriorSupportLp
    {g : SmoothRiemannianMetric (I_half n) M} (u : UnrestrictedSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (u.oneSubLap_memLp_of_interior_support hu_int).toLp _

theorem unrestrictedSmoothScalarH1Inner_eq_integral_oneSubLap_mul_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : UnrestrictedSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    unrestrictedSmoothScalarH1Inner u v =
      ∫ x, (u.toFun x -
              ΔGWithBoundary (I := I_half n) g u.smooth hu_int x) *
            v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  classical
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  have h_green : ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g u.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) +
        ∫ x, v.toFun x *
            ΔGWithBoundary (I := I_half n) g u.smooth hu_int x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
      boundaryFaceSum (I := I_half n) g
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (gradGWithBoundarySection (I := I_half n) g u.smooth hu_int)) :=
    green_first_with_boundary (I := I_half n) g v.smooth u.smooth hu_int
  have h_face : boundaryFaceSum (I := I_half n) g
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (gradGWithBoundarySection (I := I_half n) g u.smooth hu_int)) = 0 :=
    boundaryFaceSum_smoothSmul_grad_eq_zero_of_h_interior_support
      (g := g) v.smooth u.smooth hu_int
  rw [h_face] at h_green
  have h_symm : ∀ x : M,
      g.inner x (gradFun (I := I_half n) g v.toFun x)
        (gradFun (I := I_half n) g u.toFun x) =
        g.inner x (gradFun (I := I_half n) g u.toFun x)
          (gradFun (I := I_half n) g v.toFun x) := by
    intro x; exact g.symm x _ _
  have h_int_symm :
      ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g u.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        ∫ x, g.inner x (gradFun (I := I_half n) g u.toFun x)
              (gradFun (I := I_half n) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall h_symm)
  rw [h_int_symm] at h_green
  have h_grad_eq :
      ∫ x, g.inner x (gradFun (I := I_half n) g u.toFun x)
            (gradFun (I := I_half n) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        -∫ x, v.toFun x *
              ΔGWithBoundary (I := I_half n) g u.smooth hu_int x
            ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
    linarith
  unfold unrestrictedSmoothScalarH1Inner
  have hΔu_cont : Continuous
      (ΔGWithBoundary (I := I_half n) g u.smooth hu_int) :=
    Δ_g_with_boundary_continuous (I := I_half n) g u.smooth hu_int
  have hu_cont : Continuous u.toFun := u.smooth.continuous
  have hv_cont : Continuous v.toFun := v.smooth.continuous
  have h_uv_int : Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    (hu_cont.mul hv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_vΔu_int : Integrable
      (fun x : M => v.toFun x *
        ΔGWithBoundary (I := I_half n) g u.smooth hu_int x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    (hv_cont.mul hΔu_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x : M,
      (u.toFun x -
          ΔGWithBoundary (I := I_half n) g u.smooth hu_int x) *
          v.toFun x =
        u.toFun x * v.toFun x -
          v.toFun x *
            ΔGWithBoundary (I := I_half n) g u.smooth hu_int x := by
    intro x; ring
  rw [show (fun x : M =>
        (u.toFun x -
          ΔGWithBoundary (I := I_half n) g u.smooth hu_int x) *
          v.toFun x) =
      (fun x : M =>
          u.toFun x * v.toFun x -
            v.toFun x *
              ΔGWithBoundary (I := I_half n) g u.smooth hu_int x)
      from funext hpt]
  rw [integral_sub h_uv_int h_vΔu_int]
  rw [h_grad_eq]
  ring

theorem unrestrictedSmoothScalarH1Inner_eq_lpInner_oneSubLap_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : UnrestrictedSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    unrestrictedSmoothScalarH1Inner u v =
      ⟪u.oneSubLapInteriorSupportLp hu_int, smoothToLpUnrestricted g v⟫_ℝ := by
  rw [unrestrictedSmoothScalarH1Inner_eq_integral_oneSubLap_mul_of_interior_support
    (u := u) (v := v) hu_int]
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)]
  have hae_lhs :
      (u.oneSubLapInteriorSupportLp hu_int :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
        (fun x : M =>
          u.toFun x -
            ΔGWithBoundary (I := I_half n) g u.smooth hu_int x) :=
    MemLp.coeFn_toLp (u.oneSubLap_memLp_of_interior_support hu_int)
  have hae_rhs : (smoothToLpUnrestricted g v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
        v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine integral_congr_ae ?_
  filter_upwards [hae_lhs, hae_rhs] with x hl hr
  rw [hl, hr]
  show (u.toFun x -
        ΔGWithBoundary (I := I_half n) g u.smooth hu_int x) * v.toFun x = _
  rw [show @inner ℝ _ _
        (u.toFun x -
            ΔGWithBoundary (I := I_half n) g u.smooth hu_int x)
        (v.toFun x) =
      v.toFun x *
        (u.toFun x -
            ΔGWithBoundary (I := I_half n) g u.smooth hu_int x)
      from RCLike.inner_apply _ _]
  ring

lemma inner_smoothToUnrestrictedH1Compl_smoothToUnrestrictedH1Compl
    {g : SmoothRiemannianMetric (I_half n) M} (u v : UnrestrictedSmoothScalar g) :
    ⟪smoothToUnrestrictedH1Compl g u, smoothToUnrestrictedH1Compl g v⟫_ℝ =
      unrestrictedSmoothScalarH1Inner u v := by
  unfold smoothToUnrestrictedH1Compl
  change ⟪((u : UnrestrictedH1Compl g) : UnrestrictedH1Compl g),
        ((v : UnrestrictedH1Compl g) : UnrestrictedH1Compl g)⟫_ℝ =
      unrestrictedSmoothScalarH1Inner u v
  rw [UniformSpace.Completion.inner_coe (𝕜 := ℝ) u v]
  rfl

lemma unrestrictedH1ComplBilin_smoothToUnrestrictedH1Compl_smoothToUnrestrictedH1Compl
    {g : SmoothRiemannianMetric (I_half n) M} (u v : UnrestrictedSmoothScalar g) :
    unrestrictedH1ComplBilin g
        (smoothToUnrestrictedH1Compl g u)
        (smoothToUnrestrictedH1Compl g v) =
      unrestrictedSmoothScalarH1Inner u v := by
  rw [unrestrictedH1ComplBilin_apply]
  exact inner_smoothToUnrestrictedH1Compl_smoothToUnrestrictedH1Compl u v

theorem unrestrictedSmoothScalar_bilin_eq_lpFunctional_smooth_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : UnrestrictedSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    unrestrictedH1ComplBilin g
        (smoothToUnrestrictedH1Compl g u)
        (smoothToUnrestrictedH1Compl g v) =
      lpFunctionalCLMUnrestricted g (u.oneSubLapInteriorSupportLp hu_int)
        (smoothToUnrestrictedH1Compl g v) := by
  rw [unrestrictedH1ComplBilin_smoothToUnrestrictedH1Compl_smoothToUnrestrictedH1Compl,
    unrestrictedSmoothScalarH1Inner_eq_lpInner_oneSubLap_of_interior_support
      (u := u) (v := v) hu_int]
  rw [lpFunctionalCLMUnrestricted_apply,
    unrestrictedH1ComplToLp_smoothToUnrestrictedH1Compl]
  exact real_inner_comm _ _

theorem denseRange_smoothToUnrestrictedH1Compl
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (smoothToUnrestrictedH1Compl g) := by
  unfold smoothToUnrestrictedH1Compl
  rw [show (UniformSpace.Completion.toComplL :
      UnrestrictedSmoothScalar g → UnrestrictedH1Compl g) =
      ((↑) : UnrestrictedSmoothScalar g →
        UniformSpace.Completion (UnrestrictedSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

theorem smoothToUnrestrictedH1Compl_bilin_eq_lpFunctional_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : UnrestrictedSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M)
    (w : UnrestrictedH1Compl g) :
    unrestrictedH1ComplBilin g (smoothToUnrestrictedH1Compl g u) w =
      lpFunctionalCLMUnrestricted g (u.oneSubLapInteriorSupportLp hu_int) w := by
  let L : UnrestrictedH1Compl g → ℝ := fun w =>
    unrestrictedH1ComplBilin g (smoothToUnrestrictedH1Compl g u) w
  let R : UnrestrictedH1Compl g → ℝ := fun w =>
    lpFunctionalCLMUnrestricted g (u.oneSubLapInteriorSupportLp hu_int) w
  change L w = R w
  have hL_cont : Continuous L :=
    (unrestrictedH1ComplBilin g (smoothToUnrestrictedH1Compl g u)).continuous
  have hR_cont : Continuous R :=
    (lpFunctionalCLMUnrestricted g
      (u.oneSubLapInteriorSupportLp hu_int)).continuous
  have hLR_smooth :
      L ∘ (smoothToUnrestrictedH1Compl g) = R ∘ (smoothToUnrestrictedH1Compl g) := by
    funext v
    exact unrestrictedSmoothScalar_bilin_eq_lpFunctional_smooth_of_interior_support
      u v hu_int
  exact congrFun
    ((denseRange_smoothToUnrestrictedH1Compl g).equalizer hL_cont hR_cont
      hLR_smooth) w

theorem smoothToUnrestrictedH1Compl_eq_unrestrictedNeumannResolvent_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : UnrestrictedSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    smoothToUnrestrictedH1Compl g u =
      unrestrictedNeumannResolvent g (u.oneSubLapInteriorSupportLp hu_int) := by
  apply ext_inner_right ℝ
  intro w
  rw [show ⟪smoothToUnrestrictedH1Compl g u, w⟫_ℝ =
        unrestrictedH1ComplBilin g (smoothToUnrestrictedH1Compl g u) w from rfl]
  rw [smoothToUnrestrictedH1Compl_bilin_eq_lpFunctional_of_interior_support
    u hu_int w]
  rw [unrestrictedNeumannResolvent_inner_eq_lpFunctional]
  rw [lpFunctionalCLMUnrestricted_apply]

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
