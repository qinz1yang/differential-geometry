import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Topology.FiberBundleT2

set_option autoImplicit false

/-!
# Agreement of the chart-fixed and intrinsic exponentials on the C2 ball

The chart-fixed exponential is only a local realization of the complete
intrinsic exponential.  This file proves that the two realizations agree on the
named `expMapC2Radius` ball and packages the corresponding map germ.  The latter
is the compatibility boundary needed by raw radial Jacobi consumers.
-/

noncomputable section

open Bundle Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- On the named `C²` ball, the chart-fixed exponential agrees with the
complete intrinsic exponential. -/
theorem exp_eq_intr_of_c2
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {u : E}
    (hu : ‖u‖ < expMapC2Radius (I := I) g p) :
    expMap (I := I) g p (show TangentSpace I p from u) =
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from u) := by
  classical
  let γR : Real → M := fun s =>
    expMap (I := I) g p (show TangentSpace I p from s • u)
  let γI : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from u)
  have hlocal : γR =ᶠ[𝓝 (0 : Real)] γI := by
    simpa only [γR, γI] using
      exp_radial_eq_intr (I := I) g hEnorm p u
  have hlocal_mem : {s : Real | γR s = γI s} ∈ 𝓝 (0 : Real) := hlocal
  obtain ⟨U, hUsub, hUopen, h0U⟩ := mem_nhds_iff.mp hlocal_mem
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hUopen 0 h0U
  let δ : Real := min ε 1
  let s₀ : Real := δ / 2
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have hs₀ : 0 < s₀ := div_pos hδ (by norm_num)
  have hs₀_lt_ε : s₀ < ε := by
    dsimp only [s₀]
    have hδε : δ ≤ ε := min_le_left _ _
    linarith
  have hs₀_lt_one : s₀ < 1 := by
    dsimp only [s₀]
    have hδone : δ ≤ 1 := min_le_right _ _
    linarith
  have hs₀U : s₀ ∈ U := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos hs₀] using hs₀_lt_ε
  have hlocal_s₀ : γR =ᶠ[𝓝 s₀] γI :=
    Filter.mem_of_superset (hUopen.mem_nhds hs₀U) hUsub
  have hnorm (s : Real) (hs : s ∈ Set.Icc (0 : Real) 1) :
      ‖s • u‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc
      s * ‖u‖ ≤ 1 * ‖u‖ :=
        mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = ‖u‖ := one_mul _
      _ < expMapC2Radius (I := I) g p := hu
  have hγR_cont : ContinuousOn γR (Set.Icc (0 : Real) 1) := by
    intro s hs
    exact
      (radialCurve_contMDiffAt2 (I := I) g p u s
          (hnorm s hs)).continuousAt.continuousWithinAt
  have hγI_cont : ContinuousOn γI (Set.Icc (0 : Real) 1) :=
    (intrinsicGeodesic_continuous (I := I) g hEnorm p
      (show TangentSpace I p from u)).continuousOn
  have hγR_geo : Geodesic.IsGeodesicOn (I := I) g γR
      (Set.Ioo (0 : Real) 1) := by
    intro s hs
    simpa only [γR] using
      radial_geo_at (I := I) g p u hu s hs
  have hγI_geo : Geodesic.IsGeodesicOn (I := I) g γI
      (Set.Ioo (0 : Real) 1) := by
    exact
      (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u)).isGeodesicOn _
  let O : Set Real := Set.Ioo (-s₀) (1 - s₀)
  let γRs : Real → M := fun r => γR (r + s₀)
  let γIs : Real → M := fun r => γI (r + s₀)
  have hmaps (r : Real) (hr : r ∈ O) :
      r + s₀ ∈ Set.Ioo (0 : Real) 1 := by
    dsimp only [O] at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hγRs_geo : Geodesic.IsGeodesicOn (I := I) g γRs O := by
    intro r hr
    have hgeo := hγR_geo (r + s₀) (hmaps r hr)
    have hgeo' : Geodesic.HasGeodesicEquationAt (I := I) g γR
        ((1 : Real) * r + s₀) := by
      simpa only [one_mul] using hgeo
    change Geodesic.HasGeodesicEquationAt (I := I) g
      (fun s : Real => γR (s + s₀)) r
    simpa only [one_mul] using
      (Geodesic.hasGeodesicEquationAt_comp_affine
        (I := I) (g := g) (γ := γR)
        (c := (1 : Real)) (d := s₀) (t := r) hgeo')
  have hγIs_geo : Geodesic.IsGeodesicOn (I := I) g γIs O := by
    intro r hr
    have hgeo := hγI_geo (r + s₀) (hmaps r hr)
    have hgeo' : Geodesic.HasGeodesicEquationAt (I := I) g γI
        ((1 : Real) * r + s₀) := by
      simpa only [one_mul] using hgeo
    change Geodesic.HasGeodesicEquationAt (I := I) g
      (fun s : Real => γI (s + s₀)) r
    simpa only [one_mul] using
      (Geodesic.hasGeodesicEquationAt_comp_affine
        (I := I) (g := g) (γ := γI)
        (c := (1 : Real)) (d := s₀) (t := r) hgeo')
  have hmapO : Set.MapsTo (fun r : Real => r + s₀) O
      (Set.Ioo (0 : Real) 1) := fun r hr => hmaps r hr
  have hγRs_cont : ContinuousOn γRs O := by
    exact
      hγR_cont.mono Set.Ioo_subset_Icc_self |>.comp
        (continuous_id.add continuous_const).continuousOn hmapO
  have hγIs_cont : ContinuousOn γIs O := by
    exact
      (intrinsicGeodesic_continuous (I := I) g hEnorm p
        (show TangentSpace I p from u)).comp
        (continuous_id.add continuous_const) |>.continuousOn
  have hshift : γRs =ᶠ[𝓝 (0 : Real)] γIs := by
    have hadd : Tendsto (fun r : Real => r + s₀)
        (𝓝 (0 : Real)) (𝓝 s₀) := by
      have hc : ContinuousAt (fun r : Real => r + s₀) 0 :=
        (continuousAt_id : ContinuousAt (fun r : Real => r) 0).add
          continuousAt_const
      simpa only [ContinuousAt, zero_add] using hc
    exact hadd.eventually hlocal_s₀
  have h0O : (0 : Real) ∈ O := by
    dsimp only [O]
    constructor <;> linarith
  have hEqShift : Set.EqOn γRs γIs O := by
    apply geo_eqOn_of_init (I := I) g isOpen_Ioo isPreconnected_Ioo h0O
      hγRs_geo hγIs_geo hγRs_cont hγIs_cont
    · exact hshift.eq_of_nhds
    · have hmfd :
          mfderiv 𝓘(Real, Real) I γRs 0 =
            mfderiv 𝓘(Real, Real) I γIs 0 :=
        hshift.mfderiv_eq
      exact congrArg (fun L => (L (1 : Real) : E)) hmfd
  have hEqOpen : Set.EqOn γR γI (Set.Ioo (0 : Real) 1) := by
    intro s hs
    have hr : s - s₀ ∈ O := by
      dsimp only [O]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa only [γRs, γIs, sub_add_cancel] using hEqShift hr
  have hEqClosed : Set.EqOn γR γI (Set.Icc (0 : Real) 1) := by
    apply hEqOpen.of_subset_closure hγR_cont hγI_cont
      Set.Ioo_subset_Icc_self
    intro s hs
    rw [closure_Ioo (by norm_num : (0 : Real) ≠ 1)]
    exact hs
  simpa only [γR, γI, one_smul, expMapIntrinsic_def] using
    hEqClosed (by norm_num : (1 : Real) ∈ Set.Icc (0 : Real) 1)

/-- The chart-fixed and intrinsic fixed-base exponential maps have the same
germ at every vector in the named `C²` ball. -/
theorem exp_germ_eq_intr
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {u : E}
    (hu : ‖u‖ < expMapC2Radius (I := I) g p) :
    (fun w : E =>
      expMap (I := I) g p (show TangentSpace I p from w)) =ᶠ[𝓝 u]
    (fun w : E =>
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from w)) := by
  have huball : u ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  filter_upwards
    [(Metric.isOpen_ball.mem_nhds huball)] with w hw
  apply exp_eq_intr_of_c2 (I := I) g hEnorm p
  simpa only [Metric.mem_ball, dist_zero_right] using hw

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
