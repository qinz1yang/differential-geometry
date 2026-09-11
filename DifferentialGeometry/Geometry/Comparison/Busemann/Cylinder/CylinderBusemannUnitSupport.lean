import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannUnitSupport
import DifferentialGeometry.Geometry.Comparison.Busemann.Cylinder.CylinderBusemann

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Metric

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Sphere3 := Metric.sphere (0 : E3) 1
private abbrev C := Sphere3 × ℝ
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

private local instance : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_busemann_unit_upper_supports_on_cylinder
    (g : SmoothRiemannianMetric IC C) (hcomplete : RiemannianMetricComplete g)
    (hRic : ∀ x : C, ∀ v : TangentSpace IC x, 0 ≤ ricciTensor g x v v) :
    ∃ gamma : ℝ → C,
      ContMDiff 𝓘(ℝ, ℝ) IC ∞ gamma ∧ IsGeodesic g gamma ∧
      (gamma 0).2 = 0 ∧
      (∀ s t : ℝ, riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) ∧
      let bplus : C → ℝ := fun y ↦ ⨅ t : ℝ,
        (riemannianEDistOf g y (gamma t)).toReal - t
      let bminus : C → ℝ := fun y ↦ ⨅ t : ℝ,
        (riemannianEDistOf g y (gamma (-t))).toReal - t
      Continuous bplus ∧ Continuous bminus ∧
      (∀ s : ℝ, bplus (gamma s) = -s ∧ bminus (gamma s) = s) ∧
      ∀ x : C, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ (phiPlus phiMinus : C → ℝ) (U : Set C),
          IsOpen U ∧ x ∈ U ∧
          ContMDiffOn IC 𝓘(ℝ, ℝ) ∞ phiPlus U ∧
          ContMDiffOn IC 𝓘(ℝ, ℝ) ∞ phiMinus U ∧
          phiPlus x = bplus x ∧ phiMinus x = bminus x ∧
          (∀ y ∈ U, bplus y ≤ phiPlus y) ∧
          (∀ y ∈ U, bminus y ≤ phiMinus y) ∧
          laplacian (LeviCivita g) g phiPlus x ≤ epsilon ∧
          laplacian (LeviCivita g) g phiMinus x ≤ epsilon ∧
          g.inner x (gradientFun g phiPlus x) (gradientFun g phiPlus x) = 1 ∧
          g.inner x (gradientFun g phiMinus x) (gradientFun g phiMinus x) = 1 := by
  have hsphereConnected : IsConnected (Metric.sphere (0 : E3) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace Sphere3 := Subtype.connectedSpace hsphereConnected
  let : ConnectedSpace C := inferInstance
  obtain ⟨gamma, hsmooth, hgeo, hzero, hline, hdata⟩ :=
    exists_busemann_functions_on_cylinder g hcomplete
  rcases hdata with ⟨hp, hm, _hpLip, _hmLip, _hpLimit, _hmLimit, hsigned, _hsum⟩
  have hreverse (s t : ℝ) :
      riemannianEDistOf g (gamma (-s)) (gamma (-t)) = ENNReal.ofReal |s - t| := by
    rw [hline]
    have hneg : -s - -t = -(s - t) := by ring
    rw [hneg, abs_neg]
  refine ⟨gamma, hsmooth, hgeo, hzero, hline, hp, hm, hsigned, ?_⟩
  intro x epsilon hepsilon
  obtain ⟨phiPlus, Uplus, hpOpen, hpMem, hpSmooth, hpEq, hpUpper, hpLap, hpUnit⟩ :=
    busemannFunction_exists_smooth_unit_upper_support g hcomplete hRic
      gamma hline x epsilon hepsilon
  obtain ⟨phiMinus, Uminus, hmOpen, hmMem, hmSmooth, hmEq, hmUpper, hmLap, hmUnit⟩ :=
    busemannFunction_exists_smooth_unit_upper_support g hcomplete hRic
      (fun t : ℝ ↦ gamma (-t)) hreverse x epsilon hepsilon
  exact ⟨phiPlus, phiMinus, Uplus ∩ Uminus, hpOpen.inter hmOpen, ⟨hpMem, hmMem⟩,
    hpSmooth.mono inter_subset_left, hmSmooth.mono inter_subset_right,
    hpEq, hmEq, (fun y hy ↦ hpUpper y hy.1), (fun y hy ↦ hmUpper y hy.2),
    hpLap, hmLap, hpUnit, hmUnit⟩

end DifferentialGeometry.Geometry.Metric

end
