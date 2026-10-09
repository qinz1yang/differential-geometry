import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleFlowFamily
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorLift

/-!
A jointly smooth original interior phase family constructs actual smooth native flow seeds.
Each seed is the time tangent of its genuine interior-atlas lift, with the original base point.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M]

private theorem phaseSeed_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundary_original_phase_seed (V : Opens (E × ℝ)) (R : E × ℝ → M)
    (hR : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ R V)
    (henter : ∀ q ∈ V, I.IsInteriorPoint (R q)) (v₀ : E) (a : ℝ) (hva : (v₀, a) ∈ V) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      phaseSeed_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    ∃ ρ : E × ℝ → U, ∃ σ : E → TangentBundle 𝓘(ℝ, E) U,
      (∀ q ∈ V, (ρ q : M) = R q) ∧
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ {v : E | (v, a) ∈ V} ∧
      ∀ v : E, (v, a) ∈ V → (σ v).proj = ρ (v, a) ∧
        ((σ v).snd : E) = mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun t => ρ (v, t)) a (1 : ℝ) := by
  classical
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    phaseSeed_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  let p : U := ⟨R (v₀, a), henter (v₀, a) hva⟩
  let ρ : E × ℝ → U := fun q => if hq : I.IsInteriorPoint (R q) then ⟨R q, hq⟩ else p
  have hρval (q : E × ℝ) (hq : q ∈ V) : (ρ q : M) = R q := by
    dsimp only [ρ]
    rw [dite_eq_left (henter q hq)]
  let K := 𝓘(ℝ, E).prod 𝓘(ℝ)
  have hρ : ContMDiffOn K 𝓘(ℝ, E) ∞ ρ V := by
    intro q hq
    have hev : (fun z => (ρ z : M)) =ᶠ[𝓝 q] R :=
      eventually_of_mem (V.isOpen.mem_nhds hq) (fun z hz => hρval z hz)
    have hold : ContMDiffAt K I ∞ ρ q :=
      (ContMDiffAt.subtypeVal_comp_iff U ρ q).mp
        ((hR.contMDiffAt (V.isOpen.mem_nhds hq)).congr_of_eventuallyEq hev)
    exact (Φ.contMDiff.contMDiffAt.comp q hold).contMDiffWithinAt
  let L : E → TangentBundle K (E × ℝ) := fun v => ⟨(v, a), (0, 1)⟩
  have hL : ContMDiff 𝓘(ℝ, E) K.tangent ∞ L := by
    have hzero : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun v : E => (⟨v, 0⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
      Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E) : E → Type _)
    have hpair : ContMDiff 𝓘(ℝ, E) ((𝓘(ℝ, E)).tangent.prod (𝓘(ℝ)).tangent) ∞
        (fun v : E => ((⟨v, 0⟩ : TangentBundle 𝓘(ℝ, E) E),
          (⟨a, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ) ℝ))) :=
      hzero.prodMk contMDiff_const
    exact (contMDiff_equivTangentBundleProd_symm
      (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ)) (M := E) (M' := ℝ)).comp hpair
  let σ : E → TangentBundle 𝓘(ℝ, E) U := fun v => tangentMapWithin K 𝓘(ℝ, E) ρ V (L v)
  have hmap : ContMDiffOn K.tangent (𝓘(ℝ, E)).tangent ∞
      (tangentMapWithin K 𝓘(ℝ, E) ρ V)
      ((TotalSpace.proj : TangentBundle K (E × ℝ) → E × ℝ) ⁻¹' V) :=
    hρ.contMDiffOn_tangentMapWithin (by simp) V.isOpen.uniqueMDiffOn
  have hσ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ {v : E | (v, a) ∈ V} :=
    hmap.comp hL.contMDiffOn (fun v hv => hv)
  refine ⟨ρ, σ, hρval, hρ, hσ, ?_⟩
  intro v hv
  have hfull : MDifferentiableAt K 𝓘(ℝ, E) ρ (v, a) :=
    (hρ.contMDiffAt (V.isOpen.mem_nhds hv)).mdifferentiableAt (by simp)
  have hwithin := tangentMapWithin_eq_tangentMap (p := L v)
    (V.isOpen.uniqueMDiffOn (v, a) hv) hfull
  have hseed : ((σ v).snd : E) = mfderiv K 𝓘(ℝ, E) ρ (v, a) (0, 1) :=
    congrArg (fun z : TangentBundle 𝓘(ℝ, E) U => (z.snd : E)) hwithin
  have hincl : HasMFDerivAt 𝓘(ℝ) K (fun t : ℝ => (v, t)) a
      ((0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const v a).prodMk (hasMFDerivAt_id a)
  have hcomp := mfderiv_comp a hfull hincl.mdifferentiableAt
  rw [hincl.mfderiv] at hcomp
  have happ := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hcomp
  have hvalue : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun t => ρ (v, t)) a (1 : ℝ) : E) =
      mfderiv K 𝓘(ℝ, E) ρ (v, a) (0, 1) := happ
  exact ⟨rfl, hseed.trans hvalue.symm⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
