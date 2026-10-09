import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Geodesic
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Connection
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianMetric
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section

open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contMDiff_geodesicLine {n : ℕ∞ω} (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n (geodesicLine x v hv ho) := by
  have h : ContDiff ℝ n (fun t : ℝ => Real.cosh t • x.space + Real.sinh t • v.2) :=
    (Real.contDiff_cosh.smul contDiff_const).add (Real.contDiff_sinh.smul contDiff_const)
  have he : geodesicLine x v hv ho =
      ofSpace ∘ (fun t : ℝ => Real.cosh t • x.space + Real.sinh t • v.2) := by
    funext t
    ext
    rfl
  rw [he]
  exact contMDiff_ofSpace.comp h.contMDiff

theorem mfderiv_space_geodesicLine_apply_one (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (t : ℝ) :
    NormedSpace.fromTangentSpace (𝕜 := ℝ) (geodesicLine x v hv ho t).space
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph (geodesicLine x v hv ho t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicLine x v hv ho) t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1))) =
      Real.sinh t • x.space + Real.cosh t • v.2 := by
  have hc := (contMDiff_geodesicLine (n := ∞) x v hv ho).mdifferentiableAt (x := t) (by simp)
  have hs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph
      (geodesicLine x v hv ho t) :=
    (contMDiff_space (E := E) (n := ∞)).mdifferentiableAt (by simp)
  rw [← mfderiv_comp_apply t hs hc, mfderiv_eq_fderiv]
  change (fderiv ℝ (fun s : ℝ => Real.cosh s • x.space + Real.sinh s • v.2) t) 1 = _
  rw [fderiv_apply_one_eq_deriv]
  exact ((Real.hasDerivAt_cosh t).smul_const x.space |>.add
    ((Real.hasDerivAt_sinh t).smul_const v.2)).deriv

theorem geodesicLine_unit_speed (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (t : ℝ) :
    riemannianMetric.inner (geodesicLine x v hv ho t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicLine x v hv ho) t
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicLine x v hv ho) t
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)) = 1 := by
  let c := geodesicLine x v hv ho t
  let w : ℝ × E := Real.sinh t • (x.time, x.space) + Real.cosh t • v
  have hx : lorentzForm E (x.time, x.space) (x.time, x.space) = -1 := by
    rw [lorentzForm_apply]
    nlinarith [x.time_sq_sub_inner_self]
  have ho' : lorentzForm E v (x.time, x.space) = 0 := by
    have hsym : lorentzForm E v (x.time, x.space) =
        lorentzForm E (x.time, x.space) v := by
      simpa using (lorentzForm_isSymm E).eq v (x.time, x.space)
    exact hsym.trans ho
  have hw : lorentzForm E w w = 1 := by
    simp only [w, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hx, hv, ho, ho']
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hc : lorentzForm E (c.time, c.space) w = 0 := by
    change lorentzForm E (Real.cosh t • (x.time, x.space) + Real.sinh t • v)
      (Real.sinh t • (x.time, x.space) + Real.cosh t • v) = 0
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hx, hv, ho, ho']
    ring
  have hi : inner ℝ c.space w.2 = c.time * w.1 := sub_eq_zero.mp hc
  rw [riemannianMetric_inner]
  simp only [mfderiv_space_geodesicLine_apply_one]
  change inner ℝ w.2 w.2 - inner ℝ c.space w.2 * inner ℝ c.space w.2 /
    (1 + ‖c.space‖ ^ 2) = 1
  rw [← c.time_sq, hi]
  have hcancel : c.time * w.1 * (c.time * w.1) / c.time ^ 2 = w.1 * w.1 := by
    field_simp [c.time_pos.ne']
  rw [hcancel]
  exact hw

theorem isGeodesic_geodesicLine [FiniteDimensional ℝ E] (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    Geometry.Riemannian.Geodesic.IsGeodesic (I := 𝓘(ℝ, E))
      riemannianMetric (geodesicLine x v hv ho) := by
  intro t
  let c := geodesicLine x v hv ho
  let u : ℝ → E := fun s => Real.sinh s • x.space + Real.cosh s • v.2
  have hchart : Geometry.Riemannian.Geodesic.chartLocalCurve (I := 𝓘(ℝ, E)) c t =
      fun s => Real.cosh s • x.space + Real.sinh s • v.2 := by
    funext s
    rw [Geometry.Riemannian.Geodesic.chartLocalCurve_def, extChartAt_coe,
      chartAt_eq_spaceHomeomorph]
    rfl
  have hd (s : ℝ) : HasDerivAt
      (Geometry.Riemannian.Geodesic.chartLocalCurve (I := 𝓘(ℝ, E)) c t) (u s) s := by
    rw [hchart]
    exact ((Real.hasDerivAt_cosh s).smul_const x.space).add
      ((Real.hasDerivAt_sinh s).smul_const v.2)
  have hderiv : deriv
      (Geometry.Riemannian.Geodesic.chartLocalCurve (I := 𝓘(ℝ, E)) c t) = u :=
    funext fun s => (hd s).deriv
  refine ⟨u t, (c t).space, hd t, Filter.Eventually.of_forall (fun s => ?_), ?_, ?_⟩
  · rw [hderiv]
    exact hd s
  · rw [hderiv]
    exact ((Real.hasDerivAt_sinh t).smul_const x.space).add
      ((Real.hasDerivAt_cosh t).smul_const v.2)
  · have hext : extChartAt 𝓘(ℝ, E) (c t) (c t) = (c t).space := by
      rw [extChartAt_coe, chartAt_eq_spaceHomeomorph]
      rfl
    rw [hext, chartChristoffelContraction_eq]
    have hvel : spaceVectorField (u t) (c t) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) := by
      have h := mfderiv_space_geodesicLine_apply_one x v hv ho t
      rw [mfderiv_spaceDiffeomorph] at h
      exact h.symm
    rw [hvel, geodesicLine_unit_speed]
    rw [neg_one_smul]
    exact add_neg_cancel ((c t).space)

end DifferentialGeometry.Hyperboloid
