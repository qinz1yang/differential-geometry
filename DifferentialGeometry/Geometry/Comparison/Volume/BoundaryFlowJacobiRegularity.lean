import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryFlowJacobi

/-!
Actual incomplete-flow seed variation fields are smooth in the native tangent bundle.
The field is the slice derivative of the actual joint flow map on its open phase domain.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundaryless : I.Boundaryless]
  {N : Type*} [interiorTopology : TopologicalSpace N] [interiorCharts : ChartedSpace H N]
  [interiorSmooth : IsManifold I ∞ N] [interiorT2 : T2Space N]

theorem boundaryFlowJacobi_smooth (g : SmoothRiemannianMetric I N)
    (σ : ℝ → TangentBundle I N) (hσ : ContMDiff 𝓘(ℝ) I.tangent ∞ σ)
    (t₀ : ℝ) (ht₀ : (σ 0, t₀) ∈ g.geodesicFlowDomain) :
    ContMDiffAt 𝓘(ℝ) I.tangent ∞
      (fun t => (⟨boundaryFlowVariation g σ 0 t,
        boundaryFlowJacobiField g σ t⟩ : TangentBundle I N)) t₀ := by
  let K := 𝓘(ℝ).prod 𝓘(ℝ)
  let F : ℝ × ℝ → N := fun q => boundaryFlowVariation g σ q.1 q.2
  let D : Set (ℝ × ℝ) := {q | (σ q.1, q.2) ∈ g.geodesicFlowDomain}
  have hphase : ContMDiff K (I.tangent.prod 𝓘(ℝ)) ∞
      (fun q : ℝ × ℝ => (σ q.1, q.2)) :=
    (hσ.comp contMDiff_fst).prodMk contMDiff_snd
  have hopen := g.isOpen_geodesicFlowDomain (r := ⊤) le_top
  have hDopen : IsOpen D := hopen.preimage hphase.continuous
  have hproj : ContMDiff I.tangent I ∞ (TotalSpace.proj : TangentBundle I N → N) :=
    contMDiff_proj (TangentSpace I : N → Type _)
  have hF : ContMDiffOn K I ∞ F D :=
    (hproj.comp_contMDiffOn (g.contMDiffOn_geodesicFlow (r := ⊤) le_top)).comp
      hphase.contMDiffOn (fun q hq => hq)
  let L : ℝ → TangentBundle K (ℝ × ℝ) := fun t => ⟨(0, t), (1, 0)⟩
  have hL : ContMDiff 𝓘(ℝ) K.tangent ∞ L := by
    have hzero : ContMDiff 𝓘(ℝ) (𝓘(ℝ)).tangent ∞
        (fun t : ℝ => (⟨t, 0⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
      Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ) : ℝ → Type _)
    have hpair : ContMDiff 𝓘(ℝ) ((𝓘(ℝ)).tangent.prod (𝓘(ℝ)).tangent) ∞
        (fun t : ℝ => ((⟨(0 : ℝ), (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ) ℝ),
          (⟨t, 0⟩ : TangentBundle 𝓘(ℝ) ℝ))) :=
      contMDiff_const.prodMk hzero
    exact (contMDiff_equivTangentBundleProd_symm
      (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (M := ℝ) (M' := ℝ)).comp hpair
  have hmap : ContMDiffOn K.tangent I.tangent ∞ (tangentMapWithin K I F D)
      ((TotalSpace.proj : TangentBundle K (ℝ × ℝ) → ℝ × ℝ) ⁻¹' D) :=
    hF.contMDiffOn_tangentMapWithin (by simp) hDopen.uniqueMDiffOn
  have hsource : IsOpen ((TotalSpace.proj : TangentBundle K (ℝ × ℝ) → ℝ × ℝ) ⁻¹' D) :=
    hDopen.preimage
      (contMDiff_proj (n := ∞) (IB := K) (TangentSpace K : (ℝ × ℝ) → Type _)).continuous
  have hLtime : L t₀ ∈ (TotalSpace.proj ⁻¹' D) := ht₀
  have hQ : ContMDiffAt 𝓘(ℝ) I.tangent ∞
      (fun t => tangentMapWithin K I F D (L t)) t₀ :=
    (hmap.contMDiffAt (hsource.mem_nhds hLtime)).comp (f := L) t₀ hL.contMDiffAt
  have htime : {t : ℝ | (0, t) ∈ D} ∈ 𝓝 t₀ :=
    (hDopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds ht₀
  have hev : (fun t => tangentMapWithin K I F D (L t)) =ᶠ[𝓝 t₀]
      (fun t => (⟨boundaryFlowVariation g σ 0 t,
        boundaryFlowJacobiField g σ t⟩ : TangentBundle I N)) := by
    filter_upwards [htime] with t ht
    have hfull : MDifferentiableAt K I F (0, t) :=
      (hF.contMDiffAt (hDopen.mem_nhds ht)).mdifferentiableAt (by simp)
    have hwithin := tangentMapWithin_eq_tangentMap (p := L t)
      (hDopen.uniqueMDiffOn (0, t) ht) hfull
    rw [hwithin]
    have hincl : HasMFDerivAt 𝓘(ℝ) K (fun s : ℝ => (s, t)) (0 : ℝ)
        ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) :=
      (hasMFDerivAt_id (0 : ℝ)).prodMk (hasMFDerivAt_const t (0 : ℝ))
    have hcomp := mfderiv_comp (0 : ℝ) hfull hincl.mdifferentiableAt
    rw [hincl.mfderiv] at hcomp
    have happ := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hcomp
    have hvalue : (mfderiv 𝓘(ℝ) I (fun s : ℝ => boundaryFlowVariation g σ s t)
        0 (1 : ℝ) : E) = mfderiv K I F (0, t) (1, 0) := happ
    apply TotalSpace.ext
    · rfl
    · exact heq_of_eq hvalue.symm
  exact hQ.congr_of_eventuallyEq hev.symm

theorem boundaryFlowJacobi_fiber_smooth (g : SmoothRiemannianMetric I N) (p : N)
    (u w : TangentSpace I p) (t₀ : ℝ)
    (ht₀ : ((⟨p, u⟩ : TangentBundle I N), t₀) ∈ g.geodesicFlowDomain) :
    ContMDiffAt 𝓘(ℝ) I.tangent ∞
      (fun t => (⟨boundaryFlowVariation g
        (fun s : ℝ => (⟨p, u + s • w⟩ : TangentBundle I N)) 0 t,
        boundaryFlowJacobiField g
          (fun s : ℝ => (⟨p, u + s • w⟩ : TangentBundle I N)) t⟩ : TangentBundle I N)) t₀ := by
  let σ : ℝ → TangentBundle I N := fun s => ⟨p, u + s • w⟩
  have hσ : ContMDiff 𝓘(ℝ) I.tangent ∞ σ :=
    (DifferentialGeometry.contMDiff_tangentFiber (I := I) p).comp
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff)
  have hdom : (σ 0, t₀) ∈ g.geodesicFlowDomain := by
    simpa only [σ, zero_smul, add_zero] using ht₀
  exact boundaryFlowJacobi_smooth g σ hσ t₀ hdom

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
