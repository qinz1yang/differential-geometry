import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleChart
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Bundle.Orientation.Transport
import DifferentialGeometry.Bundle.Orientation.Cover

/-!
# An orientation of the flat torus (O-FIXTURE-C1, G9 file 2)

The quotient charts of `Topology/Manifold/Quotient.lean` are private, so the orientation is not
read off an atlas: it is PUSHED from `ℝ³` along the covering map `π : ℝ³ → T³`.

* `torPiDeriv_OFC z = dπ_z` as a linear isomorphism; `torPiDeriv_add_OFC`: `dπ_{z+v} = dπ_z` for
  lattice vectors `v` (`π ∘ (· + v) = π`).
* `torOrientationVal_OFC y = dπ_{ỹ}(o₀)` (`ỹ = torLift y`, `o₀` the standard orientation of `ℝ³`).
* `torChartDeriv_OFC p z = D(φ_p ∘ π)(z)` (`φ_p` the extended chart at `p`) for `π z` in the chart
  source; it is continuous in `z` there (`continuousOn_torChartDeriv_OFC`), and
  `torOrientationVal_chart_OFC`: in the chart of `p`, the pushed orientation at `π z` is
  `D(φ_p ∘ π)(z)(o₀)` for ANY lift `z`.
* `torSmoothOrientation_OFC : SmoothOrientation`: local constancy in every chart (continuity of the
  chart-composed derivative, orientations discrete, `π` open).
* `torOrientation_OFC Λ : ManifoldOrientation 𝓘(ℝ, E3) (Tor_FXC1 Λ) 3` — removes the orientation
  PARAMETER of the C1 packets and of the orientation-quantified rows (GAF07 strong, ZSP02 strong).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable (Λ : TorusPeriods_FXC1)

/-- The standard orientation of `ℝ³`. -/
def e3Orientation_OFC : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)) :=
  (Module.finBasis ℝ E3).orientation

/-- The derivative of the covering map at a point, as a linear isomorphism of `ℝ³`. -/
def torPiDeriv_OFC (z : E3) : E3 ≃L[ℝ] E3 :=
  (torPi_isLocalDiffeomorph_FXC1 Λ).mfderivToContinuousLinearEquiv (by simp) z

theorem torPiDeriv_coe_OFC (z : E3) :
    (torPiDeriv_OFC Λ z : E3 →L[ℝ] E3) = mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) z :=
  (torPi_isLocalDiffeomorph_FXC1 Λ).mfderivToContinuousLinearEquiv_coe (by simp) z

/-- The derivative of the covering map is invariant under lattice translations. -/
theorem torPiDeriv_add_OFC (z : E3) (n : TorusGroup_FXC1 Λ) :
    torPiDeriv_OFC Λ (z + latticeVec_FXC1 Λ n) = torPiDeriv_OFC Λ z := by
  apply ContinuousLinearEquiv.coe_inj.mp
  rw [torPiDeriv_coe_OFC, torPiDeriv_coe_OFC]
  have hcomp : torPi_FXC1 Λ ∘ (fun w : E3 => w + latticeVec_FXC1 Λ n) = torPi_FXC1 Λ := by
    funext w
    exact (torPi_eq_iff_FXC1.mpr ⟨n, rfl⟩).symm
  have hd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) (z + latticeVec_FXC1 Λ n) :=
    ((torPi_isLocalDiffeomorph_FXC1 Λ).contMDiff.mdifferentiable (by simp)) _
  have ht : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (fun w : E3 => w + latticeVec_FXC1 Λ n) z :=
    (differentiableAt_id.add_const _).mdifferentiableAt
  have h := mfderiv_comp z hd ht
  rw [hcomp] at h
  have hτ : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (fun w : E3 => w + latticeVec_FXC1 Λ n) z =
      ContinuousLinearMap.id ℝ E3 := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id z).add_const _).fderiv
  rw [h, hτ]
  rfl


open scoped Classical in
/-- The chart-composed derivative `D(φ_p ∘ π)(z)` at points over the chart of `p`. -/
def torChartDeriv_OFC (p : Tor_FXC1 Λ) (z : E3) : E3 ≃L[ℝ] E3 :=
  if hz : torPi_FXC1 Λ z ∈ (chartAt E3 p).source then
    (torPiDeriv_OFC Λ z).trans (preferredChartTangentEquiv 𝓘(ℝ, E3) p (torPi_FXC1 Λ z) hz)
  else ContinuousLinearEquiv.refl ℝ E3

theorem torChartDeriv_eq_OFC (p : Tor_FXC1 Λ) {z : E3}
    (hz : torPi_FXC1 Λ z ∈ (chartAt E3 p).source) :
    (torChartDeriv_OFC Λ p z : E3 →L[ℝ] E3) =
      fderiv ℝ (extChartAt 𝓘(ℝ, E3) p ∘ torPi_FXC1 Λ) z := by
  have hc : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p) (torPi_FXC1 Λ z) :=
    mdifferentiableAt_extChartAt hz
  have hpi : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) z :=
    ((contMDiff_torPi_FXC1 Λ) z).mdifferentiableAt (by simp)
  have h := mfderiv_comp z hc hpi
  ext v
  have h1 : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p ∘ torPi_FXC1 Λ) z v =
      fderiv ℝ (extChartAt 𝓘(ℝ, E3) p ∘ torPi_FXC1 Λ) z v := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [← h1, h]
  simp only [torChartDeriv_OFC, hz, ↓reduceDIte]
  rfl

theorem isOpen_torChartPre_OFC (p : Tor_FXC1 Λ) :
    IsOpen (torPi_FXC1 Λ ⁻¹' (chartAt E3 p).source) :=
  (chartAt E3 p).open_source.preimage (contMDiff_torPi_FXC1 Λ).continuous

theorem continuousOn_torChartDeriv_OFC (p : Tor_FXC1 Λ) :
    ContinuousOn (fun z => (torChartDeriv_OFC Λ p z : E3 →L[ℝ] E3))
      (torPi_FXC1 Λ ⁻¹' (chartAt E3 p).source) := by
  have hφ : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (extChartAt 𝓘(ℝ, E3) p ∘ torPi_FXC1 Λ)
      (torPi_FXC1 Λ ⁻¹' (chartAt E3 p).source) :=
    (contMDiffOn_extChartAt).comp (contMDiff_torPi_FXC1 Λ).contMDiffOn (fun _ hz => hz)
  have hd := (contMDiffOn_iff_contDiffOn.mp hφ).continuousOn_fderiv_of_isOpen
    (isOpen_torChartPre_OFC Λ p) (by simp)
  exact hd.congr fun z hz => torChartDeriv_eq_OFC Λ p hz


/-- The orientation of `T³` pushed from `ℝ³` along the covering map at the chosen lift. -/
def torOrientationVal_OFC (y : Tor_FXC1 Λ) : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)) :=
  Orientation.map _ (torPiDeriv_OFC Λ (torLift_FXC1 Λ y)).toLinearEquiv e3Orientation_OFC

/-- In the chart of `p`, the pushed orientation at `π z` is the chart-composed derivative at ANY
lift `z` applied to the standard orientation (lattice translations do not change `dπ`). -/
theorem torOrientationVal_chart_OFC (p : Tor_FXC1 Λ) (z : E3)
    (hz : torPi_FXC1 Λ z ∈ (chartAt E3 p).source) :
    Orientation.map (Fin (Module.finrank ℝ E3))
        (preferredChartTangentEquiv 𝓘(ℝ, E3) p (torPi_FXC1 Λ z) hz).toLinearEquiv
        (torOrientationVal_OFC Λ (torPi_FXC1 Λ z)) =
      Orientation.map (Fin (Module.finrank ℝ E3)) (torChartDeriv_OFC Λ p z).toLinearEquiv
        e3Orientation_OFC := by
  obtain ⟨m, hm⟩ := torPi_eq_iff_FXC1.mp (torPi_torLift_FXC1 Λ (torPi_FXC1 Λ z)).symm
  rw [torOrientationVal_OFC, hm, torPiDeriv_add_OFC,
    DifferentialGeometry.VectorBundle.map_orientation_trans]
  congr 1
  ext v
  simp only [torChartDeriv_OFC, hz, ↓reduceDIte]
  rfl

attribute [local instance] DifferentialGeometry.VectorBundle.orientationTopology

/-- The orientations are discrete (local instance for the transport lemma). -/
local instance instDiscreteOrientation_OFC :
    DiscreteTopology (Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) := ⟨rfl⟩

/-- **The pushed orientation of the flat torus is smooth** (locally constant in every chart). -/
def torSmoothOrientation_OFC : SmoothOrientation 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
  ⟨torOrientationVal_OFC Λ, fun p => by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨x, hx⟩ := x
    have hxtπ : torPi_FXC1 Λ (torLift_FXC1 Λ x) = x := torPi_torLift_FXC1 Λ x
    have hxO : torLift_FXC1 Λ x ∈ torPi_FXC1 Λ ⁻¹' (chartAt E3 p).source := by
      rw [Set.mem_preimage, hxtπ]
      exact hx
    let o₁ := Orientation.map (Fin (Module.finrank ℝ E3))
      (torChartDeriv_OFC Λ p (torLift_FXC1 Λ x)).toLinearEquiv e3Orientation_OFC
    have hG := (DifferentialGeometry.VectorBundle.continuousOn_orientation_transport
      (n := Module.finrank ℝ E3) rfl (torChartDeriv_OFC Λ p)
      (continuousOn_torChartDeriv_OFC Λ p)).comp
      (continuousOn_id.prodMk continuousOn_const)
      (fun z hz => ⟨hz, mem_univ e3Orientation_OFC⟩)
    have hGx := (hG.continuousAt ((isOpen_torChartPre_OFC Λ p).mem_nhds hxO))
      ((isOpen_discrete {o₁}).mem_nhds rfl)
    have hW : {z | Orientation.map (Fin (Module.finrank ℝ E3))
        (torChartDeriv_OFC Λ p z).toLinearEquiv e3Orientation_OFC = o₁} ∩
        torPi_FXC1 Λ ⁻¹' (chartAt E3 p).source ∈ 𝓝 (torLift_FXC1 Λ x) :=
      Filter.inter_mem hGx ((isOpen_torChartPre_OFC Λ p).mem_nhds hxO)
    have himg := (torPi_isLocalDiffeomorph_FXC1 Λ).isOpenMap.image_mem_nhds hW
    rw [hxtπ] at himg
    filter_upwards [(continuous_subtype_val.tendsto ⟨x, hx⟩) himg] with y hy
    obtain ⟨z, ⟨hzG, hzO⟩, hzy⟩ := hy
    have h1 := torOrientationVal_chart_OFC Λ p z hzO
    have h2 := torOrientationVal_chart_OFC Λ p (torLift_FXC1 Λ x) hxO
    simp only [hzy, hxtπ] at h1 h2
    rw [h1, h2]
    exact hzG⟩

/-- **A `ManifoldOrientation` of the flat torus** (from the smooth orientation pushed along the
covering map; `dim = 3`). -/
def torOrientation_OFC : ManifoldOrientation 𝓘(ℝ, E3) (Tor_FXC1 Λ) 3 :=
  cast (congrArg (fun n : ℕ => ManifoldOrientation 𝓘(ℝ, E3) (Tor_FXC1 Λ) n)
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)))
    (exists_manifoldOrientation_eq_of_smoothOrientation 𝓘(ℝ, E3)
      (torSmoothOrientation_OFC Λ)).choose

end DifferentialGeometry.Geometry.Collapse
