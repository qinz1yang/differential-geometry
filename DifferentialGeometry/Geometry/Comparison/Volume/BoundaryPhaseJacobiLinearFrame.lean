import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseJacobiVariation

/-!
The actual velocity derivative of a native phase-flow point map is a linear Jacobi family.
Each direction field is smooth and Jacobi along the same existing central ray.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundaryless : I.Boundaryless]
  {N : Type*} [interiorTopology : TopologicalSpace N] [interiorCharts : ChartedSpace H N]
  [interiorSmooth : IsManifold I ∞ N] [interiorT2 : T2Space N]

noncomputable def boundaryPhasePoint (g : SmoothRiemannianMetric I N)
    (σ : E → TangentBundle I N) (v : E) (t : ℝ) : N := (g.geodesicFlow (σ v) t).proj

noncomputable def boundaryPhaseJacobiLinear (g : SmoothRiemannianMetric I N)
    (σ : E → TangentBundle I N) (v₀ : E) (t : ℝ) :
    E →L[ℝ] TangentSpace I (boundaryPhasePoint g σ v₀ t) :=
  mfderiv 𝓘(ℝ, E) I (fun v => boundaryPhasePoint g σ v t) v₀

theorem boundaryPhasePoint_smooth (g : SmoothRiemannianMetric I N)
    (W : Opens E) (σ : E → TangentBundle I N)
    (hσ : ContMDiffOn 𝓘(ℝ, E) I.tangent ∞ σ W) :
    let D := {q : E × ℝ | q.1 ∈ W ∧ (σ q.1, q.2) ∈ g.geodesicFlowDomain}
    IsOpen D ∧ ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞
      (fun q : E × ℝ => boundaryPhasePoint g σ q.1 q.2) D := by
  let D : Set (E × ℝ) := {q | q.1 ∈ W ∧ (σ q.1, q.2) ∈ g.geodesicFlowDomain}
  let P : Set (E × ℝ) := (W : Set E) ×ˢ univ
  let phase : E × ℝ → TangentBundle I N × ℝ := fun q => (σ q.1, q.2)
  have hphase : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) (I.tangent.prod 𝓘(ℝ)) ∞ phase P :=
    (hσ.comp contMDiff_fst.contMDiffOn (fun q hq => hq.1)).prodMk
      contMDiff_snd.contMDiffOn
  have hD : D = P ∩ phase ⁻¹' g.geodesicFlowDomain := by
    ext q
    change (q.1 ∈ W ∧ (σ q.1, q.2) ∈ g.geodesicFlowDomain) ↔
      ((q.1 ∈ W ∧ q.2 ∈ univ) ∧ (σ q.1, q.2) ∈ g.geodesicFlowDomain)
    simp only [mem_univ, and_true]
  have hPopen : IsOpen P := W.isOpen.prod isOpen_univ
  have hopen : IsOpen D := by
    rw [hD]
    exact hphase.continuousOn.isOpen_inter_preimage hPopen
      (g.isOpen_geodesicFlowDomain (r := ⊤) le_top)
  have hproj : ContMDiff I.tangent I ∞ (TotalSpace.proj : TangentBundle I N → N) :=
    contMDiff_proj (TangentSpace I : N → Type _)
  have hfoot := hproj.comp_contMDiffOn (g.contMDiffOn_geodesicFlow (r := ⊤) le_top)
  refine ⟨hopen, ?_⟩
  exact hfoot.comp (hphase.mono (fun q hq => ⟨hq.1, mem_univ q.2⟩)) (fun q hq => hq.2)

theorem boundaryPhasePoint_smoothAt (g : SmoothRiemannianMetric I N)
    (W : Opens E) (σ : E → TangentBundle I N)
    (hσ : ContMDiffOn 𝓘(ℝ, E) I.tangent ∞ σ W) (v₀ : E) (t : ℝ)
    (hv₀ : v₀ ∈ W) (ht : (σ v₀, t) ∈ g.geodesicFlowDomain) :
    ContMDiffAt 𝓘(ℝ, E) I ∞ (fun v => boundaryPhasePoint g σ v t) v₀ := by
  obtain ⟨hopen, hpoint⟩ := boundaryPhasePoint_smooth g W σ hσ
  have hp : (v₀, t) ∈ {q : E × ℝ | q.1 ∈ W ∧ (σ q.1, q.2) ∈ g.geodesicFlowDomain} :=
    ⟨hv₀, ht⟩
  exact (hpoint.contMDiffAt (hopen.mem_nhds hp)).comp
    (f := fun v : E => (v, t)) v₀ (contMDiffAt_id.prodMk contMDiffAt_const)

private theorem phaseLinear_angular_derivative (g : SmoothRiemannianMetric I N)
    (W : Opens E) (σ : E → TangentBundle I N)
    (hσ : ContMDiffOn 𝓘(ℝ, E) I.tangent ∞ σ W) (v₀ w : E) (hv₀ : v₀ ∈ W)
    (ζ : ℝ → TangentBundle I N)
    (hζ : ζ =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => σ (v₀ + s • w)))
    (t : ℝ) (ht : (σ v₀, t) ∈ g.geodesicFlowDomain) :
    (boundaryFlowJacobiField g ζ t : E) = boundaryPhaseJacobiLinear g σ v₀ t w := by
  have hpoint := boundaryPhasePoint_smoothAt g W σ hσ v₀ t hv₀ ht
  have hline : HasDerivAt (fun s : ℝ => v₀ + s • w) w 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v₀
  have hlineMF := hline.hasFDerivAt.hasMFDerivAt
  have hlineApplied : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun s : ℝ => v₀ + s • w)
      0 (1 : ℝ) : E) = w := by
    have hh := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hlineMF.mfderiv
    change (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun s : ℝ => v₀ + s • w)
      0 (1 : ℝ) : E) = (1 : ℝ) • w at hh
    exact hh.trans (one_smul ℝ w)
  have hchain := mfderiv_comp_apply_of_eq (0 : ℝ)
    (hpoint.mdifferentiableAt (by simp)) hlineMF.mdifferentiableAt
    (show v₀ + (0 : ℝ) • w = v₀ by simp only [zero_smul, add_zero]) (1 : ℝ)
  rw [hlineApplied] at hchain
  have hev : (fun s => boundaryFlowVariation g ζ s t) =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ => boundaryPhasePoint g σ (v₀ + s • w) t) := by
    filter_upwards [hζ] with s hs
    change (g.geodesicFlow (ζ s) t).proj = (g.geodesicFlow (σ (v₀ + s • w)) t).proj
    rw [hs]
  have hder : mfderiv 𝓘(ℝ) I (fun s => boundaryFlowVariation g ζ s t) 0 =
      mfderiv 𝓘(ℝ) I (fun s : ℝ => boundaryPhasePoint g σ (v₀ + s • w) t) 0 :=
    hev.mfderiv_eq
  have happ := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hder
  exact happ.trans hchain

theorem boundaryPhaseJacobiLinear_jacobi (g : SmoothRiemannianMetric I N)
    (W : Opens E) (σ : E → TangentBundle I N)
    (hσ : ContMDiffOn 𝓘(ℝ, E) I.tangent ∞ σ W) (v₀ : E) (hv₀ : v₀ ∈ W) :
    ∀ w : E, ∀ t : ℝ, (σ v₀, t) ∈ g.geodesicFlowDomain →
      IsJacobiAt g (fun s => boundaryPhasePoint g σ v₀ s)
        (fun s => boundaryPhaseJacobiLinear g σ v₀ s w) t ∧
      ContMDiffAt 𝓘(ℝ) I.tangent ∞
        (fun s => (⟨boundaryPhasePoint g σ v₀ s,
          boundaryPhaseJacobiLinear g σ v₀ s w⟩ : TangentBundle I N)) t := by
  intro w t ht
  obtain ⟨ζ, hζ, hzero, hgerm, hJac⟩ :=
    boundary_phase_local_variation_jacobi g W σ hσ v₀ w hv₀
  have hdom : (ζ 0, t) ∈ g.geodesicFlowDomain := hzero.symm ▸ ht
  have hnear : ∀ᶠ s in 𝓝 t, (σ v₀, s) ∈ g.geodesicFlowDomain :=
    ((g.isOpen_geodesicFlowDomain (r := ⊤) le_top).preimage
      (continuous_const.prodMk continuous_id)).mem_nhds ht
  have hfield : (fun s => (⟨boundaryFlowVariation g ζ 0 s,
      boundaryFlowJacobiField g ζ s⟩ : TangentBundle I N)) =ᶠ[𝓝 t]
      (fun s => (⟨boundaryPhasePoint g σ v₀ s,
        boundaryPhaseJacobiLinear g σ v₀ s w⟩ : TangentBundle I N)) := by
    filter_upwards [hnear] with s hs
    apply TotalSpace.ext
    · exact congrArg (fun z : TangentBundle I N => (g.geodesicFlow z s).proj) hzero
    · exact heq_of_eq (phaseLinear_angular_derivative g W σ hσ v₀ w hv₀ ζ hgerm s hs)
  exact ⟨(hJac t hdom).1.congr_of_eventuallyEq hfield,
    (hJac t hdom).2.congr_of_eventuallyEq hfield.symm⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
