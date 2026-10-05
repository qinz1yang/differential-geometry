import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryFlowJacobiRegularity
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic

/-!
Actual incomplete-flow fiber variations have the prescribed initial covariant derivative.
Local smooth clamps permit the native variation commutation without global completeness.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundaryless : I.Boundaryless]
  {N : Type*} [interiorTopology : TopologicalSpace N] [interiorCharts : ChartedSpace H N]
  [interiorSmooth : IsManifold I ∞ N] [interiorT2 : T2Space N]

theorem boundaryFlowJacobi_fiber_derivative (g : SmoothRiemannianMetric I N) (p : N)
    (u w : TangentSpace I p) :
    (covDerivAlong g
      (fun t => boundaryFlowVariation g
        (fun s : ℝ => (⟨p, u + s • w⟩ : TangentBundle I N)) 0 t)
      (boundaryFlowJacobiField g
        (fun s : ℝ => (⟨p, u + s • w⟩ : TangentBundle I N))) 0 : E) = w := by
  let σ : ℝ → TangentBundle I N := fun s => ⟨p, u + s • w⟩
  let F := boundaryFlowVariation g σ
  let D : Set (ℝ × ℝ) := {q | (σ q.1, q.2) ∈ g.geodesicFlowDomain}
  have hσ : ContMDiff 𝓘(ℝ) I.tangent ∞ σ :=
    (DifferentialGeometry.contMDiff_tangentFiber (I := I) p).comp
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff)
  have hphase : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (I.tangent.prod 𝓘(ℝ)) ∞
      (fun q : ℝ × ℝ => (σ q.1, q.2)) :=
    (hσ.comp contMDiff_fst).prodMk contMDiff_snd
  have hopen := g.isOpen_geodesicFlowDomain (r := ⊤) le_top
  have hDopen : IsOpen D := hopen.preimage hphase.continuous
  have hDzero : (0, 0) ∈ D := g.mem_geodesicFlowDomain_zero (r := ⊤) le_top (σ 0)
  obtain ⟨φ, ψ, hφ, hψ, hφid, hψid, hrange⟩ :=
    DifferentialGeometry.exists_contDiff_prodMap_range_subset (hDopen.mem_nhds hDzero)
  let Fhat : ℝ → ℝ → N := fun s t => F (φ s) (ψ t)
  have hψzero : ψ 0 = 0 := hψid.eq_of_nhds
  have hφzero : φ 0 = 0 := hφid.eq_of_nhds
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
  have hFzero : ∀ s : ℝ, Fhat s 0 = p := by
    intro s
    change (g.geodesicFlow (σ (φ s)) (ψ 0)).proj = p
    rw [hψzero]
    exact congrArg (fun z : TangentBundle I N => z.proj)
      (g.geodesicFlow_zero (r := ⊤) le_top (σ (φ s)))
  have hlaunch : ∀ s : ℝ,
      (mfderiv 𝓘(ℝ) I (fun t => Fhat s t) 0 (1 : ℝ) : E) = u + φ s • w := by
    intro s
    have hev : (fun t => Fhat s t) =ᶠ[𝓝 (0 : ℝ)]
        (fun t => (g.geodesicFlow (σ (φ s)) t).proj) := by
      filter_upwards [hψid] with t ht
      simp only [Fhat, F, boundaryFlowVariation, ht, id_eq]
    have hnative := g.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top
      (g.mem_geodesicFlowDomain_zero (r := ⊤) le_top (σ (φ s)))
    have hder : mfderiv 𝓘(ℝ) I (fun t => Fhat s t) 0 =
        mfderiv 𝓘(ℝ) I (fun t => (g.geodesicFlow (σ (φ s)) t).proj) 0 :=
      hev.mfderiv_eq
    have happ := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hder
    have hn : (mfderiv 𝓘(ℝ) I
        (fun t => (g.geodesicFlow (σ (φ s)) t).proj) 0 (1 : ℝ) : E) =
        u + φ s • w := by
      have hv := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hnative.mfderiv
      have hz := congrArg (fun z : TangentBundle I N => (z.snd : E))
        (g.geodesicFlow_zero (r := ⊤) le_top (σ (φ s)))
      have hvApplied : (mfderiv 𝓘(ℝ) I
          (fun t => (g.geodesicFlow (σ (φ s)) t).proj) 0 (1 : ℝ) : E) =
          (g.geodesicFlow (σ (φ s)) 0).snd := by
        change (mfderiv 𝓘(ℝ) I
          (fun t => (g.geodesicFlow (σ (φ s)) t).proj) 0 (1 : ℝ) : E) =
            (1 : ℝ) • (g.geodesicFlow (σ (φ s)) 0).snd at hv
        simpa only [one_smul] using hv
      exact hvApplied.trans hz
    exact happ.trans hn
  have hFzeroEv : (fun s => Fhat s 0) =ᶠ[𝓝 (0 : ℝ)] (fun _ => p) :=
    Eventually.of_forall hFzero
  have hlaunchEv : ∀ᶠ s in 𝓝 (0 : ℝ),
      (mfderiv 𝓘(ℝ) I (fun t => Fhat s t) 0 (1 : ℝ) : E) = u + s • w := by
    filter_upwards [hφid] with s hs
    rw [hlaunch, hs, id_eq]
  have hderiv : HasDerivAt (fun s : ℝ => (u + s • w : E)) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (w : E)).const_add (u : E)
  have hleft := covDerivAlong_congr_curve g
    (fun s => mfderiv 𝓘(ℝ) I (fun t => Fhat s t) 0 (1 : ℝ))
    (fun s => (show TangentSpace I p from u + s • w)) hFzeroEv hlaunchEv
  have hconst := covDerivAlong_const g p
    (fun s => (show TangentSpace I p from u + s • w)) 0 hderiv.differentiableAt
  have hcomm := commute_ds_dt_intrinsic g Fhat hvariation 0
  have hvalue : (covDerivAlong g (fun t => Fhat 0 t)
      (fun t => mfderiv 𝓘(ℝ) I (fun s => Fhat s t) 0 (1 : ℝ)) 0 : E) = w :=
    hcomm.symm.trans (hleft.trans (hconst.trans hderiv.deriv))
  have hcentral : (fun t => Fhat 0 t) =ᶠ[𝓝 (0 : ℝ)] (fun t => F 0 t) := by
    filter_upwards [hψid] with t ht
    simp only [Fhat, hφzero, ht, id_eq]
  have hfield : ∀ᶠ t in 𝓝 (0 : ℝ),
      (mfderiv 𝓘(ℝ) I (fun s => Fhat s t) 0 (1 : ℝ) : E) =
        boundaryFlowJacobiField g σ t := by
    filter_upwards [hψid] with t ht
    have hev : (fun s => Fhat s t) =ᶠ[𝓝 (0 : ℝ)] (fun s => F s t) := by
      filter_upwards [hφid] with s hs
      simp only [Fhat, hs, ht, id_eq]
    have hd : mfderiv 𝓘(ℝ) I (fun s => Fhat s t) 0 =
        mfderiv 𝓘(ℝ) I (fun s => F s t) 0 := hev.mfderiv_eq
    exact congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hd
  have hcongr := covDerivAlong_congr_curve g
    (fun t => mfderiv 𝓘(ℝ) I (fun s => Fhat s t) 0 (1 : ℝ))
    (boundaryFlowJacobiField g σ) hcentral hfield
  exact hcongr.symm.trans hvalue

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
