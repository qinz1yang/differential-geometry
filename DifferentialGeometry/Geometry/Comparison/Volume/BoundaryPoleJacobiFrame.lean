import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryFlowJacobiDerivative
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseJacobiLinearFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleFlowFamily

/-!
The actual pole-family velocity derivative has zero initial value and identity covariant jet.
The same linear derivative yields smooth Jacobi directions on every existing pole-ray time.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

noncomputable def boundaryPoleJacobiLinear (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (y v : E) (t : ℝ) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun u => boundaryPoleFlowFamily G y u t) v

theorem boundaryPoleJacobiLinear_fiber (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (y v w : E) (t : ℝ)
    (ht : ((⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain) :
    boundaryPoleJacobiLinear G y v t w =
      boundaryFlowJacobiField G
        (fun s : ℝ => (⟨y, v + s • w⟩ : TangentBundle 𝓘(ℝ, E) E)) t := by
  let σ : E → TangentBundle 𝓘(ℝ, E) E := fun u => ⟨y, u⟩
  have hσ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ :=
    DifferentialGeometry.contMDiff_tangentFiber (I := 𝓘(ℝ, E)) y
  have hpoint := boundaryPhasePoint_smoothAt G ⟨univ, isOpen_univ⟩ σ hσ.contMDiffOn
    v t (mem_univ v) ht
  have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hlineMF := hline.hasFDerivAt.hasMFDerivAt
  have hlineApplied : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun s : ℝ => v + s • w)
      0 (1 : ℝ) : E) = w := by
    have hh := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hlineMF.mfderiv
    change (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun s : ℝ => v + s • w)
      0 (1 : ℝ) : E) = (1 : ℝ) • w at hh
    exact hh.trans (one_smul ℝ w)
  have hchain := mfderiv_comp_apply_of_eq (0 : ℝ)
    (hpoint.mdifferentiableAt (by simp)) hlineMF.mdifferentiableAt
    (show v + (0 : ℝ) • w = v by simp only [zero_smul, add_zero]) (1 : ℝ)
  rw [hlineApplied] at hchain
  exact hchain.symm

theorem boundaryPoleJacobiLinear_initial (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (y v w : E) :
    boundaryPoleJacobiLinear G y v 0 w = 0 ∧
      covDerivAlong G (boundaryPoleFlowFamily G y v)
        (fun t => boundaryPoleJacobiLinear G y v t w) 0 = w := by
  have hzero := G.mem_geodesicFlowDomain_zero (r := ⊤) le_top
    (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E)
  refine ⟨(boundaryPoleJacobiLinear_fiber G y v w 0 hzero).trans
    (boundaryFlowJacobi_fiber_zero G y v w), ?_⟩
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),
      ((⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain :=
    ((G.isOpen_geodesicFlowDomain (r := ⊤) le_top).preimage
      (continuous_const.prodMk continuous_id)).mem_nhds hzero
  have hfield : ∀ᶠ t in 𝓝 (0 : ℝ), boundaryPoleJacobiLinear G y v t w =
      boundaryFlowJacobiField G
        (fun s : ℝ => (⟨y, v + s • w⟩ : TangentBundle 𝓘(ℝ, E) E)) t := by
    filter_upwards [hnear] with t ht
    exact boundaryPoleJacobiLinear_fiber G y v w t ht
  have hcov := covDerivAlong_congr_of_eventuallyEq G (boundaryPoleFlowFamily G y v) hfield
  have hjet := boundaryFlowJacobi_fiber_derivative G y v w
  have hcurve : (fun t => boundaryFlowVariation G
      (fun s : ℝ => (⟨y, v + s • w⟩ : TangentBundle 𝓘(ℝ, E) E)) 0 t) =ᶠ[𝓝 (0 : ℝ)]
      boundaryPoleFlowFamily G y v := by
    apply Eventually.of_forall
    intro t
    change (G.geodesicFlow (⟨y, v + (0 : ℝ) • w⟩ : TangentBundle 𝓘(ℝ, E) E) t).proj =
      (G.geodesicFlow (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E) t).proj
    rw [zero_smul, add_zero]
  have htransport := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve G
    (γ' := boundaryPoleFlowFamily G y v)
    (boundaryFlowJacobiField G
      (fun s : ℝ => (⟨y, v + s • w⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (fun t => boundaryFlowJacobiField G
      (fun s : ℝ => (⟨y, v + s • w⟩ : TangentBundle 𝓘(ℝ, E) E)) t)
    hcurve (Eventually.of_forall fun _t => rfl)
  have hjetPole := htransport.symm.trans hjet
  exact hcov.trans hjetPole

theorem boundaryPoleJacobiLinear_jacobi (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (y v : E) :
    ∀ w : E, ∀ t : ℝ,
      ((⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain →
      IsJacobiAt G (boundaryPoleFlowFamily G y v)
        (fun s => boundaryPoleJacobiLinear G y v s w) t ∧
      ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun s => (⟨boundaryPoleFlowFamily G y v s,
          boundaryPoleJacobiLinear G y v s w⟩ : TangentBundle 𝓘(ℝ, E) E)) t := by
  let σ : E → TangentBundle 𝓘(ℝ, E) E := fun u => ⟨y, u⟩
  have hσ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ :=
    DifferentialGeometry.contMDiff_tangentFiber (I := 𝓘(ℝ, E)) y
  exact boundaryPhaseJacobiLinear_jacobi G ⟨univ, isOpen_univ⟩ σ hσ.contMDiffOn v
    (mem_univ v)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
