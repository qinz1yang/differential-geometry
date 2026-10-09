import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicPrimitiveMain

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Hyperbolic
  GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1

/-- **Cusp-level content of `PrescribedCuspMeridian` (fields `loop` … `short`).** For every
hyperbolic cusp `H` there is one embedded smooth primitive loop of the torus that is, for every
sufficiently large depth `b`, a geodesic of the depth-`b` cross-section `deepCusp_CPA H b` and
has `deepCusp_CPA H b`-speed at most `L < 1`. -/
theorem exists_meridian_deepCusp_CPA2 (H : HyperbolicCusp) :
    ∃ loop : freeLoop Torus,
      _root_.Topology.IsEmbedding loop ∧
      ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop) ∧
      (∃ e : FundamentalGroup Torus (loop 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1)) ∧
      ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
        DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
          (deepCusp_CPA H b).torusMetric (loopLift loop) ∧
        ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ s : ℝ,
          let v := mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1;
          (deepCusp_CPA H b).torusMetric.inner (loopLift loop s) v v ≤ L ^ 2 := by
  obtain ⟨loop, hemb, hsm, hgeo, hprim⟩ :=
    exists_primitive_closed_geodesic_CPA2 H.torusMetric H.torus_flat
  obtain ⟨c₀, hc₀, hc⟩ := exists_scale_short_geodesic_CPA H.torusMetric loop hsm hgeo
  refine ⟨loop, hemb, hsm, hprim, -Real.log c₀, fun b hb => ?_⟩
  have hle : Real.exp (-b) ≤ c₀ := by
    calc Real.exp (-b) ≤ Real.exp (Real.log c₀) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = c₀ := Real.exp_log hc₀
  exact hc (Real.exp (-b)) (Real.exp_pos _) hle

end GC.LongTime.CuspP1
