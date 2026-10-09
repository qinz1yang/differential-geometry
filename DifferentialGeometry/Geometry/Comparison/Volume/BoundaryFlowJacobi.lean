import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorRicci
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Variation
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth

/-!
Actual smooth seed variations of incomplete geodesic flow construct Jacobi fields.
The equation holds at each existing base-flow time, with no completeness or Jacobi input.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundaryless : I.Boundaryless]
  {N : Type*} [interiorTopology : TopologicalSpace N] [interiorCharts : ChartedSpace H N]
  [interiorSmooth : IsManifold I ∞ N] [interiorT2 : T2Space N]

def boundaryFlowVariation (g : SmoothRiemannianMetric I N)
    (σ : ℝ → TangentBundle I N) (s t : ℝ) : N := (g.geodesicFlow (σ s) t).proj

noncomputable def boundaryFlowJacobiField (g : SmoothRiemannianMetric I N)
    (σ : ℝ → TangentBundle I N) (t : ℝ) : TangentSpace I (boundaryFlowVariation g σ 0 t) :=
  mfderiv 𝓘(ℝ) I (fun s => boundaryFlowVariation g σ s t) 0 1

theorem boundaryFlowJacobiAt (g : SmoothRiemannianMetric I N)
    (σ : ℝ → TangentBundle I N) (hσ : ContMDiff 𝓘(ℝ) I.tangent ∞ σ)
    (t₀ : ℝ) (ht₀ : (σ 0, t₀) ∈ g.geodesicFlowDomain) :
    IsJacobiAt g (fun t => boundaryFlowVariation g σ 0 t)
      (boundaryFlowJacobiField g σ) t₀ := by
  let F := boundaryFlowVariation g σ
  let D : Set (ℝ × ℝ) := {q | (σ q.1, q.2) ∈ g.geodesicFlowDomain}
  have hphase : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (I.tangent.prod 𝓘(ℝ)) ∞
      (fun q : ℝ × ℝ => (σ q.1, q.2)) :=
    (hσ.comp contMDiff_fst).prodMk contMDiff_snd
  have hopen := g.isOpen_geodesicFlowDomain (r := ⊤) le_top
  have hDopen : IsOpen D := hopen.preimage hphase.continuous
  have hDzero : (0, t₀) ∈ D := ht₀
  obtain ⟨φ, ψ, hφ, hψ, hφid, hψid, hrange⟩ :=
    DifferentialGeometry.exists_contDiff_prodMap_range_subset (hDopen.mem_nhds hDzero)
  let Fhat : ℝ → ℝ → N := fun s t => F (φ s) (ψ t)
  have hψtime : ψ t₀ = t₀ := hψid.eq_of_nhds
  have hphaseHat : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (I.tangent.prod 𝓘(ℝ)) ∞
      (fun q : ℝ × ℝ => (σ (φ q.1), ψ q.2)) :=
    (hσ.comp (hφ.contMDiff.comp contMDiff_fst)).prodMk
      (hψ.contMDiff.comp contMDiff_snd)
  have hproj : ContMDiff I.tangent I ∞ (TotalSpace.proj : TangentBundle I N → N) :=
    contMDiff_proj (TangentSpace I : N → Type _)
  have hfoot := hproj.comp_contMDiffOn (g.contMDiffOn_geodesicFlow (r := ⊤) le_top)
  have hFhat : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) I ∞
      (fun q : ℝ × ℝ => Fhat q.1 q.2) := by
    intro q
    have hq : (σ (φ q.1), ψ q.2) ∈ g.geodesicFlowDomain := hrange ⟨q, rfl⟩
    exact (hfoot.contMDiffAt (hopen.mem_nhds hq)).comp
      (f := fun z : ℝ × ℝ => (σ (φ z.1), ψ z.2)) q hphaseHat.contMDiffAt
  have hvariation : IsSmoothVariation Fhat := hFhat.of_le ENat.LEInfty.out
  have hzero : ∀ s : ℝ, covDerivAlong g (fun t => Fhat s t)
      (fun t => mfderiv 𝓘(ℝ) I (fun u => Fhat s u) t 1) t₀ = 0 := by
    intro s
    have hdom : (σ (φ s), t₀) ∈ g.geodesicFlowDomain := by
      have hd : (σ (φ s), ψ t₀) ∈ g.geodesicFlowDomain := hrange ⟨(s, t₀), rfl⟩
      rwa [hψtime] at hd
    have hnative : HasGeodesicEquationAt g
        (fun t => (g.geodesicFlow (σ (φ s)) t).proj) t₀ := by
      let z := σ (φ s)
      have hi := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow
        g z.proj z.snd
      exact (hi.isGeodesicAt
        (isOpen_maximalIntegralCurveInterval.mem_nhds hdom)).hasGeodesicEquationAt
    have hev : (fun t => Fhat s t) =ᶠ[𝓝 t₀]
        (fun t => (g.geodesicFlow (σ (φ s)) t).proj) := by
      filter_upwards [hψid] with t ht
      simp only [Fhat, F, boundaryFlowVariation, ht, id_eq]
    have hgeo := HasGeodesicEquationAt.congr_of_eventuallyEq_at
      hev.eq_of_nhds hev hnative
    have hslice : ContMDiffAt 𝓘(ℝ) I 2 (fun t => Fhat s t) t₀ :=
      (hFhat.comp (contMDiff_const.prodMk contMDiff_id)).contMDiffAt.of_le (by norm_num)
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g _ t₀ hslice hgeo
  have hjac := isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero
    g Fhat hvariation t₀ hzero
  have hfield : (fun t => (⟨Fhat 0 t,
      mfderiv 𝓘(ℝ) I (fun s => Fhat s t) 0 1⟩ : TangentBundle I N)) =ᶠ[𝓝 t₀]
      (fun t => (⟨F 0 t, boundaryFlowJacobiField g σ t⟩ : TangentBundle I N)) := by
    filter_upwards [hψid] with t ht
    have hspatial : (fun s => Fhat s t) =ᶠ[𝓝 (0 : ℝ)] (fun s => F s t) := by
      filter_upwards [hφid] with s hs
      simp only [Fhat, hs, ht, id_eq]
    have hder : mfderiv 𝓘(ℝ) I (fun s => Fhat s t) 0 =
        mfderiv 𝓘(ℝ) I (fun s => F s t) 0 := hspatial.mfderiv_eq
    have happ := congrArg (fun A : ℝ →L[ℝ] E => A 1) hder
    apply TotalSpace.ext
    · exact hspatial.eq_of_nhds
    · exact heq_of_eq happ
  exact hjac.congr_of_eventuallyEq hfield

theorem boundaryFlowJacobi_fiber (g : SmoothRiemannianMetric I N) (p : N)
    (u w : TangentSpace I p) (t₀ : ℝ)
    (ht₀ : ((⟨p, u⟩ : TangentBundle I N), t₀) ∈ g.geodesicFlowDomain) :
    IsJacobiAt g
      (fun t => boundaryFlowVariation g (fun s : ℝ => (⟨p, u + s • w⟩ : TangentBundle I N)) 0 t)
      (boundaryFlowJacobiField g (fun s : ℝ => (⟨p, u + s • w⟩ : TangentBundle I N))) t₀ := by
  let σ : ℝ → TangentBundle I N := fun s => ⟨p, u + s • w⟩
  have hσ : ContMDiff 𝓘(ℝ) I.tangent ∞ σ :=
    (DifferentialGeometry.contMDiff_tangentFiber (I := I) p).comp
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff)
  have hdom : (σ 0, t₀) ∈ g.geodesicFlowDomain := by
    simpa only [σ, zero_smul, add_zero] using ht₀
  have hjac := boundaryFlowJacobiAt g σ hσ t₀ hdom
  exact hjac

omit interiorT2 in
theorem boundaryFlowJacobi_fiber_zero (g : SmoothRiemannianMetric I N) (p : N)
    (u w : TangentSpace I p) :
    (boundaryFlowJacobiField g (fun s : ℝ => (⟨p, u + s • w⟩ : TangentBundle I N)) 0 : E) = 0 := by
  have hcurve : (fun s : ℝ => (g.geodesicFlow (⟨p, u + s • w⟩ : TangentBundle I N) 0).proj) =
      fun _s : ℝ => p := by
    funext s
    exact congrArg (fun z : TangentBundle I N => z.proj)
      (g.geodesicFlow_zero (r := ⊤) le_top (⟨p, u + s • w⟩ : TangentBundle I N))
  have hvalue := congrArg (fun f : ℝ → N => (mfderiv 𝓘(ℝ) I f 0 (1 : ℝ) : E)) hcurve
  have hconstant : (mfderiv 𝓘(ℝ) I (fun _s : ℝ => p) 0 (1 : ℝ) : E) = 0 := by
    rw [mfderiv_const]
    rfl
  exact hvalue.trans hconstant

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
