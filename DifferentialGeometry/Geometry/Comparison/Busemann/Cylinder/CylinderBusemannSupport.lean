import DifferentialGeometry.Geometry.Operator.LocalLaplacian
import DifferentialGeometry.Geometry.Comparison.Busemann.Cylinder.CylinderBusemann
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannUpperSupport
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Metric

private abbrev Sphere3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Cyl3 := Sphere3 × ℝ
private abbrev ICyl3 := (𝓡 2).prod 𝓘(ℝ)

private local instance : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_opposite_busemann_sum_upper_supports_on_cylinder
    (g : SmoothRiemannianMetric ICyl3 Cyl3)
    (hcomplete : RiemannianMetricComplete g)
    (hRic : ∀ y : Cyl3, ∀ v : TangentSpace ICyl3 y, 0 ≤ ricciTensor g y v v) :
    ∃ gamma : ℝ → Cyl3,
      ContMDiff 𝓘(ℝ, ℝ) ICyl3 ∞ gamma ∧ IsGeodesic g gamma ∧
      (gamma 0).2 = 0 ∧
      (∀ s t : ℝ,
        riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) ∧
      let bplus : Cyl3 → ℝ := fun x ↦
        ⨅ t : ℝ, (riemannianEDistOf g x (gamma t)).toReal - t
      let bminus : Cyl3 → ℝ := fun x ↦
        ⨅ t : ℝ, (riemannianEDistOf g x (gamma (-t))).toReal - t
      let u : Cyl3 → ℝ := fun x ↦ bplus x + bminus x
      Continuous bplus ∧ Continuous bminus ∧
      (∀ s : ℝ, bplus (gamma s) = -s ∧ bminus (gamma s) = s) ∧
      Continuous u ∧ (∀ x, 0 ≤ u x) ∧ (∀ s : ℝ, u (gamma s) = 0) ∧
      ∀ x : Cyl3, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ (U : Set Cyl3) (phi : Cyl3 → ℝ),
          IsOpen U ∧ x ∈ U ∧ ContMDiffOn ICyl3 𝓘(ℝ, ℝ) ∞ phi U ∧
          phi x = u x ∧ (∀ y ∈ U, u y ≤ phi y) ∧
          laplacian (LeviCivita g) g phi x ≤ epsilon := by
  have hsphereConnected : IsConnected
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace Sphere3 := Subtype.connectedSpace hsphereConnected
  let : ConnectedSpace Cyl3 := inferInstance
  obtain ⟨gamma, hsmooth, hgeo, hzero, hline, hdata⟩ :=
    exists_busemann_functions_on_cylinder g hcomplete
  let bplus : Cyl3 → ℝ := fun y ↦
    ⨅ t : ℝ, (riemannianEDistOf g y (gamma t)).toReal - t
  let bminus : Cyl3 → ℝ := fun y ↦
    ⨅ t : ℝ, (riemannianEDistOf g y (gamma (-t))).toReal - t
  rcases hdata with ⟨hplusCont, hminusCont, _hplusLip, _hminusLip,
    _hplusLimit, _hminusLimit, hsigned, hnonneg⟩
  have hreverse : ∀ s t : ℝ,
      riemannianEDistOf g (gamma (-s)) (gamma (-t)) = ENNReal.ofReal |s - t| := by
    intro s t
    rw [hline]
    congr 1
    have hneg : -s - -t = -(s - t) := by ring
    rw [hneg, abs_neg]
  refine ⟨gamma, hsmooth, hgeo, hzero, hline, hplusCont, hminusCont, hsigned,
    hplusCont.add hminusCont, hnonneg, ?_, ?_⟩
  · intro s
    change bplus (gamma s) + bminus (gamma s) = 0
    exact (congrArg₂ (fun a b : ℝ => a + b) (hsigned s).1 (hsigned s).2).trans
      (neg_add_cancel s)
  · intro x epsilon hepsilon
    obtain ⟨phip, Up, hUp, hxUp, hphip, heqp, hupperp, hlapp⟩ :=
      busemannFunction_exists_smooth_upper_support g hcomplete hRic gamma hline
        x (epsilon / 2) (half_pos hepsilon)
    obtain ⟨phim, Um, hUm, hxUm, hphim, heqm, hupperm, hlapm⟩ :=
      busemannFunction_exists_smooth_upper_support g hcomplete hRic
        (fun t : ℝ ↦ gamma (-t)) hreverse x (epsilon / 2) (half_pos hepsilon)
    have hboth : {y : Cyl3 | bplus y ≤ phip y ∧ bminus y ≤ phim y} ∈ 𝓝 x :=
      hupperp.and hupperm
    obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hboth
    let U : Set Cyl3 := (Up ∩ Um) ∩ V
    have hU : IsOpen U := (hUp.inter hUm).inter hVopen
    have hxU : x ∈ U := ⟨⟨hxUp, hxUm⟩, hxV⟩
    have hpU : ContMDiffOn ICyl3 𝓘(ℝ, ℝ) ∞ phip U :=
      hphip.mono (by intro y hy; exact hy.1.1)
    have hmU : ContMDiffOn ICyl3 𝓘(ℝ, ℝ) ∞ phim U :=
      hphim.mono (by intro y hy; exact hy.1.2)
    refine ⟨U, (fun y ↦ phip y + phim y), hU, hxU, hpU.add hmU, ?_, ?_, ?_⟩
    · exact congrArg₂ (fun a b : ℝ ↦ a + b) heqp heqm
    · intro y hy
      have hyy := hVsub hy.2
      exact add_le_add hyy.1 hyy.2
    · have hdp : ∀ᶠ y in 𝓝 x, MDifferentiableAt ICyl3 𝓘(ℝ, ℝ) phip y := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        exact ((hpU y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
      have hdm : ∀ᶠ y in 𝓝 x, MDifferentiableAt ICyl3 𝓘(ℝ, ℝ) phim y := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        exact ((hmU y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
      have hgp := gradientFun_mdiffOn g hU hpU hxU
      have hgm := gradientFun_mdiffOn g hU hmU hxU
      rw [DifferentialGeometry.Geometry.Operator.laplacian_add_of_local_regularity
        (LeviCivita g) g phip phim x hdp hdm hgp hgm]
      linarith only [hlapp, hlapm]

end DifferentialGeometry.Geometry.Metric

end
