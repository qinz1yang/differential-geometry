import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPhaseSeed

/-!
Actual original joint geodesic families agree uniformly with their constructed native seeds.
A common velocity neighborhood and time interval are derived from genuine open phase domains.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem phaseMatching_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundary_original_phase_flow_matches (g : SmoothRiemannianMetric I M)
    (V : Opens (E × ℝ)) (R : E × ℝ → M)
    (hR : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ R V)
    (henter : ∀ q ∈ V, I.IsInteriorPoint (R q))
    (hgeo : ∀ q ∈ V, HasGeodesicEquationAt g (fun t => R (q.1, t)) q.2)
    (v₀ : E) (a : ℝ) (hva : (v₀, a) ∈ V) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      phaseMatching_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ σ : E → TangentBundle 𝓘(ℝ, E) U, ∃ W : Opens E, ∃ ε : ℝ,
      v₀ ∈ W ∧ 0 < ε ∧ ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
      (∀ v ∈ W, ((σ v).proj : M) = R (v, a)) ∧
      ∀ v ∈ W, ∀ s ∈ Metric.ball (0 : ℝ) ε,
        (σ v, s) ∈ k.geodesicFlowDomain ∧
        ((k.geodesicFlow (σ v) s).proj : M) = R (v, s + a) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    phaseMatching_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨ρ, σ, hρval, hρ, hσ, hseed⟩ :=
    boundary_original_phase_seed V R hR henter v₀ a hva
  let W : Set E := {v | (v, a) ∈ V}
  have hWopen : IsOpen W := V.isOpen.preimage (continuous_id.prodMk continuous_const)
  let K := 𝓘(ℝ, E).prod 𝓘(ℝ)
  let P : Set (E × ℝ) := W ×ˢ univ
  let phase : E × ℝ → TangentBundle 𝓘(ℝ, E) U × ℝ := fun q => (σ q.1, q.2)
  have hphase : ContMDiffOn K ((𝓘(ℝ, E)).tangent.prod 𝓘(ℝ)) ∞ phase P :=
    (hσ.comp contMDiff_fst.contMDiffOn (fun q hq => hq.1)).prodMk
      contMDiff_snd.contMDiffOn
  have hPopen : IsOpen P := hWopen.prod isOpen_univ
  have kopen := k.isOpen_geodesicFlowDomain (r := ⊤) le_top
  let S : Set (E × ℝ) := (P ∩ phase ⁻¹' k.geodesicFlowDomain) ∩
    (fun q : E × ℝ => (q.1, q.2 + a)) ⁻¹' V
  have hSopen : IsOpen S :=
    (hphase.continuousOn.isOpen_inter_preimage hPopen kopen).inter
      (V.isOpen.preimage (continuous_fst.prodMk (continuous_snd.add continuous_const)))
  have hSzero : (v₀, 0) ∈ S :=
    ⟨⟨⟨hva, mem_univ 0⟩, k.mem_geodesicFlowDomain_zero (r := ⊤) le_top (σ v₀)⟩,
      by
        change (v₀, 0 + a) ∈ V
        simpa only [zero_add] using hva⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (hSopen.mem_nhds hSzero)
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp hB
  let Z : Opens E := ⟨interior A, isOpen_interior⟩
  have hZzero : v₀ ∈ Z := mem_interior_iff_mem_nhds.mpr hA
  have hcommon (v : E) (hv : v ∈ Z) (s : ℝ) (hs : s ∈ Metric.ball 0 ε) :
      (σ v, s) ∈ k.geodesicFlowDomain ∧ (v, s + a) ∈ V := by
    have hq : (v, s) ∈ S := hAB ⟨interior_subset hv, hεB hs⟩
    exact ⟨hq.1.2, hq.2⟩
  have hZsub : (Z : Set E) ⊆ W := by
    intro v hv
    have hq : (v, (0 : ℝ)) ∈ S :=
      hAB ⟨interior_subset hv, hεB (Metric.mem_ball_self hε)⟩
    exact hq.1.1.1
  refine ⟨σ, Z, ε, hZzero, hε, hσ.mono hZsub, ?_, ?_⟩
  · intro v hv
    exact (congrArg (fun x : U => (x : M)) (hseed v (hZsub hv)).1).trans
      (hρval (v, a) (hZsub hv))
  · intro v hv
    let γ : ℝ → U := fun s => ρ (v, s + a)
    let η : ℝ → U := fun s => (k.geodesicFlow (σ v) s).proj
    have hflow (s : ℝ) (hs : s ∈ Metric.ball 0 ε) :
        (σ v, s) ∈ k.geodesicFlowDomain := (hcommon v hv s hs).1
    have hγsmooth : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ (Metric.ball 0 ε) := by
      intro s hs
      have hρat : ContMDiffAt K 𝓘(ℝ, E) ∞ ρ (v, s + a) :=
        hρ.contMDiffAt (V.isOpen.mem_nhds (hcommon v hv s hs).2)
      have hh : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ s :=
        hρat.comp (f := fun t : ℝ => (v, t + a)) s
          (contMDiff_const.prodMk (contMDiff_id.add contMDiff_const)).contMDiffAt
      exact hh.contMDiffWithinAt
    have hγval (s : ℝ) (hs : s ∈ Metric.ball 0 ε) : (γ s : M) = R (v, s + a) :=
      hρval (v, s + a) (hcommon v hv s hs).2
    have hγgeo : IsGeodesicOn k γ (Metric.ball 0 ε) := by
      intro s hs
      have hev : (fun t => (γ t : M)) =ᶠ[𝓝 s] (fun t => R (v, t + a)) :=
        eventually_of_mem (Metric.isOpen_ball.mem_nhds hs) (fun t ht => hγval t ht)
      have hshift : HasGeodesicEquationAt g (fun t => R (v, t + a)) s := by
        simpa only [one_mul] using hasGeodesicEquationAt_comp_affine
          (c := 1) (d := a) (t := s)
          (by simpa only [one_mul] using hgeo (v, s + a) (hcommon v hv s hs).2)
      have horig := HasGeodesicEquationAt.congr_of_eventuallyEq_at
        hev.eq_of_nhds hev hshift
      exact (boundaryInteriorAtlas_geodesicEquation_iff g γ s
        (hγsmooth.contMDiffAt (Metric.isOpen_ball.mem_nhds hs))).mpr horig
    have hηgeo : IsGeodesicOn k η (Metric.ball 0 ε) := by
      intro s hs
      have hi := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow
        k (σ v).proj (σ v).snd
      exact (hi.isGeodesicAt
        (isOpen_maximalIntegralCurveInterval.mem_nhds (hflow s hs))).hasGeodesicEquationAt
    have hηcont : ContinuousOn η (Metric.ball 0 ε) := by
      intro s hs
      exact (k.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top
        (hflow s hs)).continuousAt.continuousWithinAt
    have hinitial : η 0 = γ 0 := by
      have hn := congrArg (fun q : TangentBundle 𝓘(ℝ, E) U => q.proj)
        (k.geodesicFlow_zero (r := ⊤) le_top (σ v))
      exact hn.trans (by simpa only [γ, zero_add] using (hseed v (hZsub hv)).1)
    have hvη : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η 0 (1 : ℝ) : E) = (σ v).snd := by
      have hn := (k.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top
        (hflow 0 (Metric.mem_ball_self hε))).mfderiv
      have happ := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hn
      have ha : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η 0 (1 : ℝ) : E) =
          (k.geodesicFlow (σ v) 0).snd := by
        change (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η 0 (1 : ℝ) : E) =
          (1 : ℝ) • (k.geodesicFlow (σ v) 0).snd at happ
        simpa only [one_smul] using happ
      exact ha.trans (congrArg (fun q : TangentBundle 𝓘(ℝ, E) U => (q.snd : E))
        (k.geodesicFlow_zero (r := ⊤) le_top (σ v)))
    have hρslice : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) (fun t => ρ (v, t)) a :=
      ((hρ.contMDiffAt (V.isOpen.mem_nhds (hZsub hv))).comp
        (f := fun t : ℝ => (v, t)) a
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt).mdifferentiableAt (by simp)
    have hshift : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => t + a) 0
        (ContinuousLinearMap.id ℝ ℝ) := by
      have hadd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => t + a) 0
          (ContinuousLinearMap.id ℝ ℝ + (0 : ℝ →L[ℝ] ℝ)) :=
        (hasMFDerivAt_id (0 : ℝ)).add (hasMFDerivAt_const a (0 : ℝ))
      simpa only [add_zero] using hadd
    have hρshift : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) (fun t => ρ (v, t)) (0 + a) := by
      simpa only [zero_add] using hρslice
    have hcomp := mfderiv_comp (0 : ℝ) hρshift hshift.mdifferentiableAt
    rw [hshift.mfderiv] at hcomp
    have happ := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hcomp
    have hvγ : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ) : E) =
        mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun t => ρ (v, t)) a (1 : ℝ) := by
      change (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ) : E) =
        mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun t => ρ (v, t)) (0 + a) (1 : ℝ) at happ
      have hpoint := congrArg
        (fun t : ℝ => (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun r => ρ (v, r)) t (1 : ℝ) : E))
        (zero_add a)
      exact happ.trans hpoint
    have hvelocity : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η 0 (1 : ℝ) : E) =
        mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ) :=
      hvη.trans ((hseed v (hZsub hv)).2.trans hvγ.symm)
    have heq := geo_eqOn_of_initial k Metric.isOpen_ball
      (convex_ball (0 : ℝ) ε).isPreconnected (Metric.mem_ball_self hε)
      hηgeo hγgeo hηcont hγsmooth.continuousOn hinitial hvelocity
    intro s hs
    exact ⟨hflow s hs, (congrArg (fun x : U => (x : M)) (heq hs)).trans (hγval s hs)⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
