import DifferentialGeometry.Geometry.HarmonicMap.TangentGraphGerms
import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphDifference
import DifferentialGeometry.Analysis.Calculus.Inverse.GraphTransversality
import DifferentialGeometry.Analysis.Elliptic.Planar.RegularZeros
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Maps.CoincidentGerms
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryTraceInjectivity

/-!
# Conditional embedding of the original regular Morrey disk

The local image-germ theorem needs rank only at the two interior collision
points. The conditional embedding theorem additionally retains full closed-disk
rank. Both use the actual target metric, prescribed loop, disk and explicit
exclusion of transverse regular collisions. Private graph-contact and
neighborhood-transport mechanics combine existing geometric suppliers;
boundary singleton fibers use the boundary-rank supplier. This file does not
construct the no-transverse input.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval

namespace DifferentialGeometry.Geometry

set_option maxHeartbeats 800000 in
-- The full graph-jet and scalar-PDE tuple exceeds the default elaboration budget.
/-- The unchanged Morrey disk supplies a smooth elliptic height-difference
equation at any distinct regular nontransverse collision, with no assumption
that the two source points share a small branch neighborhood. -/
private theorem morrey_regular_collision_elliptic_height_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hd3 : Module.finrank ℝ E = 3)
    {a b : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hb : b ∈ ball (0 : ℂ) 1)
    (hab : a ≠ b) (hvalue : diskExtension u a = diskExtension u b)
    (hDa : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a))
    (hDb : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b))
    (hnot : ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b)))) :
    let U : ℂ → M := diskExtension u
    let p := U a
    let s := ball (0 : ℂ) 1 ∩ U ⁻¹' (chartAt E p).source
    let ξ : Fin (Module.finrank ℝ E) → ℂ := fun i => chartComplexGradient p U i a
    let Q := chartGramBilin g p p
    let proj := chartLeadingPlaneProjection g p p ξ
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * ξ i).re)
    ∃ (N : E) (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
      Q N N = 1 ∧ proj N = 0 ∧
      (∀ v : E, v = lift (proj v) + (Q N v) • N) ∧
      a ∈ e₁.source ∧ b ∈ e₂.source ∧
      e₁.source ⊆ s ∧ e₂.source ⊆ s ∧ Disjoint e₁.source e₂.source ∧
      (e₁ : ℂ → ℂ) = F ∧ (e₂ : ℂ → ℂ) = F ∧
      ContDiffOn ℝ ∞ e₁.symm e₁.target ∧
      ContDiffOn ℝ ∞ e₂.symm e₂.target ∧
      IsOpen O ∧ F a ∈ O ∧ O ⊆ e₁.target ∩ e₂.target ∧
      let h₁ : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a)
      let h₂ : ℂ → ℝ := fun y => Q N (X (e₂.symm y) - X a)
      let w : ℂ → ℝ := fun y => h₁ y - h₂ y
      ContDiffOn ℝ ∞ h₁ O ∧ ContDiffOn ℝ ∞ h₂ O ∧ ContDiffOn ℝ ∞ w O ∧
      (∀ y ∈ O,
        X (e₁.symm y) = X a + lift (y - F a) + h₁ y • N ∧
        X (e₂.symm y) = X a + lift (y - F a) + h₂ y • N) ∧
      ∃ (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
        (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
        (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun y => A y i j) O) ∧
        (∀ i : Fin 2, ContDiffOn ℝ ∞ (fun y => beta y i) O) ∧
        ContDiffOn ℝ ∞ c O ∧
        ∀ y ∈ O,
          (A y).PosDef ∧
          (∑ i : Fin 2, ∑ j : Fin 2,
            A y i j * fderiv ℝ (fderiv ℝ w) y
              ((![1, Complex.I] : Fin 2 → ℂ) i)
              ((![1, Complex.I] : Fin 2 → ℂ) j)) +
            (∑ i : Fin 2, beta y i * fderiv ℝ w y
              ((![1, Complex.I] : Fin 2 → ℂ) i)) + c y * w y = 0 := by
  classical
  intro U p s ξ Q proj X F lift
  change U a = U b at hvalue
  have hs : IsOpen s := hu.smoothInterior.continuousOn.isOpen_inter_preimage
    isOpen_ball (chartAt E p).open_source
  have haS : a ∈ s := ⟨ha, mem_chart_source E p⟩
  have hbS : b ∈ s := by
    refine ⟨hb, ?_⟩
    change U b ∈ (chartAt E p).source
    rw [← hvalue]
    exact mem_chart_source E p
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s :=
    hu.smoothInterior.mono inter_subset_left
  have hconf : ∀ z ∈ s, DiskMapConformalAt g U z := fun z hz => hu.conformal z hz.1
  have htension : ∀ z ∈ s, diskMapTension g U z = 0 := fun z hz => hu.harmonic z hz.1
  have hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source := fun _ hz => hz.2
  with_reducible
    obtain ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      hdisj, he₁, he₂, hei₁, hei₂, hOo, haO, hOsub, hsegment⟩ :=
      chartLeadingPlaneProjection_exists_tangent_collision_germs g hd3 hs hU hconf
        haS hbS hab hvalue hchart hDa hDb hnot
  have hO₁ : O ⊆ e₁.target := hOsub.trans inter_subset_left
  have hO₂ : O ⊆ e₂.target := hOsub.trans inter_subset_right
  with_reducible
    have hdata := chartLeadingPlaneProjection_two_graphs_height_difference g
      hs hU hconf htension (a := a) (p := p) hchart (b := ξ) N hNN hPN hsplit
      e₁ e₂ he₁s he₂s he₁ he₂ hei₁ hei₂ hOo
      hO₁ hO₂ hsegment
  let h₁ : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a)
  let h₂ : ℂ → ℝ := fun y => Q N (X (e₂.symm y) - X a)
  let w : ℂ → ℝ := fun y => h₁ y - h₂ y
  let dirs : Fin 2 → ℂ := ![1, Complex.I]
  let duals : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]
  let Jet := ℝ × (ℂ →L[ℝ] ℝ)
  let J₁ : ℂ → Jet := fun y => (h₁ y, fderiv ℝ h₁ y)
  let J₂ : ℂ → Jet := fun y => (h₂ y, fderiv ℝ h₂ y)
  let J : ℂ → ℝ → Jet := fun y t => (1 - t) • J₂ y + t • J₁ y
  let Y : ℂ → Jet → E := fun y q => X a + lift (y - F a) + q.1 • N
  let V : (ℂ →L[ℝ] ℝ) → Fin 2 → E := fun l i => lift (dirs i) + l (dirs i) • N
  let H : ℂ → Jet → Matrix (Fin 2) (Fin 2) ℝ := fun y q i j =>
    chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y y q)) (V q.2 i) (V q.2 j)
  let A : ℂ → Jet → Matrix (Fin 2) (Fin 2) ℝ := fun y q =>
    Analysis.planarConductivity (H y q 0 0) (H y q 1 1) (H y q 0 1)
  let theta : (ℂ →L[ℝ] ℝ) → E →L[ℝ] ℝ := fun l => Q N - l.comp proj
  let P : ℂ → Jet → (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) → ℝ := fun y q K =>
    ∑ i : Fin 2, ∑ j : Fin 2,
      A y q i j * (K (dirs i) (dirs j) +
        theta q.2 (chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y y q)))
  let R : ℂ → Jet → ℝ := fun y q => P y q (fderiv ℝ (fderiv ℝ h₂) y)
  let beta : ℂ → Fin 2 → ℝ := fun y i =>
    ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (0, duals i)
  let c : ℂ → ℝ := fun y =>
    ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (1, 0)
  with_reducible
    obtain ⟨hh₁, hh₂, hw, hrecon, _, hA, hbeta, hc, hpde⟩ := hdata
  refine ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
    hdisj, he₁, he₂, hei₁, hei₂, hOo, haO, hOsub, hh₁, hh₂, hw, ?_,
    fun y => A y (J₁ y), beta, c, fun i j => (hA i j).1, hbeta, hc, ?_⟩
  · intro y hy
    exact ⟨(hrecon y hy).1.symm, (hrecon y hy).2.1.symm⟩
  · intro y hy
    obtain ⟨_, _, hpos, _, _, _, _, _, hEq⟩ := hpde y hy
    exact ⟨hpos, hEq⟩

private theorem transverse_regular_pair_of_graph_height_derivatives_ne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    (proj : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ) (N : E) (lift : ℂ → E)
    (hsplit : ∀ v : E, v = lift (proj v) + height v • N)
    (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ)
    (he₁s : e₁.source ⊆ s) (he₂s : e₂.source ⊆ s)
    (hdisj : Disjoint e₁.source e₂.source)
    (he₁ : (e₁ : ℂ → ℂ) = fun z => proj (extChartAt 𝓘(ℝ, E) p (U z)))
    (he₂ : (e₂ : ℂ → ℂ) = fun z => proj (extChartAt 𝓘(ℝ, E) p (U z)))
    (hei₁ : ContDiffOn ℝ ∞ e₁.symm e₁.target)
    (hei₂ : ContDiffOn ℝ ∞ e₂.symm e₂.target)
    (x₀ : E) {y : ℂ} (hy₁ : y ∈ e₁.target) (hy₂ : y ∈ e₂.target)
    (hheight : height (extChartAt 𝓘(ℝ, E) p (U (e₁.symm y)) - x₀) =
      height (extChartAt 𝓘(ℝ, E) p (U (e₂.symm y)) - x₀))
    (hderiv : fderiv ℝ (fun w => height (extChartAt 𝓘(ℝ, E) p (U (e₁.symm w)) - x₀)) y ≠
      fderiv ℝ (fun w => height (extChartAt 𝓘(ℝ, E) p (U (e₂.symm w)) - x₀)) y) :
    e₁.symm y ≠ e₂.symm y ∧ U (e₁.symm y) = U (e₂.symm y) ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₁.symm y)) ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₂.symm y)) ∧
      Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₁.symm y)).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₂.symm y)))) := by
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let F : ℂ → ℂ := fun z => proj (X z)
  change (e₁ : ℂ → ℂ) = F at he₁
  change (e₂ : ℂ → ℂ) = F at he₂
  let h₁ : ℂ → ℝ := fun w => height (X (e₁.symm w) - x₀)
  let h₂ : ℂ → ℝ := fun w => height (X (e₂.symm w) - x₀)
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hchain (z : ℂ) (hz : z ∈ s) :
      fderiv ℝ X z =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U z)).comp
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart z hz)
    have hh := mfderiv_comp z (hc.mdifferentiableAt (by simp))
      ((hU.contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hcalc (e : OpenPartialHomeomorph ℂ ℂ) (hes : e.source ⊆ s)
      (he : (e : ℂ → ℂ) = F) (hei : ContDiffOn ℝ ∞ e.symm e.target)
      (hye : y ∈ e.target) :
      proj.comp ((fderiv ℝ X (e.symm y)).comp (fderiv ℝ e.symm y)) =
        ContinuousLinearMap.id ℝ ℂ ∧
      fderiv ℝ (fun w => height (X (e.symm w) - x₀)) y =
        height.comp ((fderiv ℝ X (e.symm y)).comp (fderiv ℝ e.symm y)) ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm y)) := by
    let x := e.symm y
    have hx : x ∈ s := hes (e.map_target hye)
    have hdx := (hX.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
    have hde := (hei.contDiffAt (e.open_target.mem_nhds hye)).differentiableAt (by simp)
    have hdF : DifferentiableAt ℝ F x := proj.differentiableAt.comp x hdx
    have hDF : fderiv ℝ F x = proj.comp (fderiv ℝ X x) :=
      (proj.hasFDerivAt.comp x hdx.hasFDerivAt).fderiv
    have heq : (fun w => F (e.symm w)) =ᶠ[𝓝 y] id := by
      filter_upwards [e.open_target.mem_nhds hye] with w hw
      rw [← he]
      exact e.right_inv hw
    have hFR : (fderiv ℝ F x).comp (fderiv ℝ e.symm y) =
        ContinuousLinearMap.id ℝ ℂ :=
      ((hdF.hasFDerivAt.comp y hde.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique
        (hasFDerivAt_id y)
    have hproj : proj.comp ((fderiv ℝ X x).comp (fderiv ℝ e.symm y)) =
        ContinuousLinearMap.id ℝ ℂ := by
      rw [← ContinuousLinearMap.comp_assoc, ← hDF]
      exact hFR
    have hheightD : fderiv ℝ (fun w => height (X (e.symm w) - x₀)) y =
        height.comp ((fderiv ℝ X x).comp (fderiv ℝ e.symm y)) :=
      (height.hasFDerivAt.comp y
        ((hdx.hasFDerivAt.comp y hde.hasFDerivAt).sub_const x₀)).fderiv
    have hDFsurj : Function.Surjective (fderiv ℝ F x) := by
      intro v
      exact ⟨fderiv ℝ e.symm y v, congrArg (fun K : ℂ →L[ℝ] ℂ => K v) hFR⟩
    have hDFinj : Function.Injective (fderiv ℝ F x) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hDFsurj
    have hDXinj : Function.Injective (fderiv ℝ X x) := by
      intro v w hvw
      apply hDFinj
      rw [hDF]
      exact congrArg proj hvw
    refine ⟨hproj, hheightD, ?_⟩
    intro v w hvw
    apply hDXinj
    rw [hchain x hx]
    exact congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) p) (U x)) hvw
  obtain ⟨hproj₁, hell₁, hmi₁⟩ := hcalc e₁ he₁s he₁ hei₁ hy₁
  obtain ⟨hproj₂, hell₂, hmi₂⟩ := hcalc e₂ he₂s he₂ hei₂ hy₂
  let x₁ := e₁.symm y
  let x₂ := e₂.symm y
  let R₁ := fderiv ℝ e₁.symm y
  let R₂ := fderiv ℝ e₂.symm y
  let T₁ := (fderiv ℝ X x₁).comp R₁
  let T₂ := (fderiv ℝ X x₂).comp R₂
  let ell₁ := fderiv ℝ h₁ y
  let ell₂ := fderiv ℝ h₂ y
  let L : ℂ →L[ℝ] E := T₁ - ell₁.smulRight N
  have hT₁ (v : ℂ) : T₁ v = lift v + ell₁ v • N := by
    have hp := congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hproj₁
    have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) hell₁
    have h := hsplit (T₁ v)
    change proj (T₁ v) = v at hp
    change ell₁ v = height (T₁ v) at he
    rwa [hp, ← he] at h
  have hT₂ (v : ℂ) : T₂ v = lift v + ell₂ v • N := by
    have hp := congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hproj₂
    have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) hell₂
    have h := hsplit (T₂ v)
    change proj (T₂ v) = v at hp
    change ell₂ v = height (T₂ v) at he
    rwa [hp, ← he] at h
  have hL (v : ℂ) : L v = lift v := by
    change T₁ v - ell₁ v • N = lift v
    rw [hT₁, add_sub_cancel_right]
  have hspan : ∀ v : E, ∃ (w : ℂ) (t : ℝ), v = L w + t • N := by
    intro v
    refine ⟨proj v, height v, ?_⟩
    rw [hL]
    exact hsplit v
  have hTL₁ : L + ell₁.smulRight N = T₁ :=
    ContinuousLinearMap.ext fun v => by
      change L v + ell₁ v • N = T₁ v
      rw [hL, hT₁]
  have hTL₂ : L + ell₂.smulRight N = T₂ :=
    ContinuousLinearMap.ext fun v => by
      change L v + ell₂ v • N = T₂ v
      rw [hL, hT₂]
  have htransT := Analysis.surjective_coprod_graphs_of_ne L N ell₁ ell₂ hspan hderiv
  rw [hTL₁, hTL₂] at htransT
  have htransX : Function.Surjective
      ((fderiv ℝ X x₁).coprod (-(fderiv ℝ X x₂))) := by
    intro v
    obtain ⟨z, hz⟩ := htransT v
    exact ⟨(R₁ z.1, R₂ z.2), hz⟩
  have hx₁s : x₁ ∈ s := he₁s (e₁.map_target hy₁)
  have hx₂s : x₂ ∈ s := he₂s (e₂.map_target hy₂)
  have hP₁ : proj (X x₁) = y := by
    change F (e₁.symm y) = y
    rw [← he₁]
    exact e₁.right_inv hy₁
  have hP₂ : proj (X x₂) = y := by
    change F (e₂.symm y) = y
    rw [← he₂]
    exact e₂.right_inv hy₂
  have hh : height (X x₁) = height (X x₂) := by
    change height (X x₁ - x₀) = height (X x₂ - x₀) at hheight
    rw [map_sub, map_sub] at hheight
    linarith
  have hXeq : X x₁ = X x₂ := by
    calc
      X x₁ = lift y + height (X x₁) • N := by rw [← hP₁]; exact hsplit _
      _ = lift y + height (X x₂) • N := by rw [hh]
      _ = X x₂ := by rw [← hP₂]; exact (hsplit _).symm
  have hUeq : U x₁ = U x₂ :=
    (extChartAt 𝓘(ℝ, E) p).injOn
      (by simpa only [extChartAt_source] using hchart x₁ hx₁s)
      (by simpa only [extChartAt_source] using hchart x₂ hx₂s) hXeq
  have hne : x₁ ≠ x₂ := by
    intro h
    have hx₁ := e₁.map_target hy₁
    have hx₂ := e₂.map_target hy₂
    change x₁ ∈ e₁.source at hx₁
    change x₂ ∈ e₂.source at hx₂
    rw [h] at hx₁
    exact disjoint_left.mp hdisj hx₁ hx₂
  let C : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U x₁)
  let D₁ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x₁
  let D₂ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x₂
  have hC : Function.Injective C :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
      (show U x₁ ∈ (extChartAt 𝓘(ℝ, E) p).source by
        simpa only [extChartAt_source] using hchart x₁ hx₁s)).injective
  have hD₁ : fderiv ℝ X x₁ = C.comp D₁ := hchain x₁ hx₁s
  have hD₂ : fderiv ℝ X x₂ = C.comp D₂ := by
    have h := hchain x₂ hx₂s
    rw [← hUeq] at h
    exact h
  refine ⟨hne, hUeq, hmi₁, hmi₂, ?_⟩
  intro v
  obtain ⟨z, hz⟩ := htransX (C v)
  refine ⟨z, hC ?_⟩
  change C (D₁ z.1 + -(D₂ z.2)) = C v
  change fderiv ℝ X x₁ z.1 + -(fderiv ℝ X x₂ z.2) = C v at hz
  rw [hD₁, hD₂] at hz
  simpa only [map_add, map_neg, ContinuousLinearMap.comp_apply] using hz

/-- Once transverse regular self-intersections have been excluded for the
original disk, every regular collision has coincident actual graph germs.
The exclusion hypothesis is retained; the scalar PDE is supplied by the exact
original Morrey disk through the accepted two-graph difference theorem. -/
private theorem morrey_regular_collision_graph_germs_of_no_transverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hd3 : Module.finrank ℝ E = 3)
    (hNoTransverse : ∀ x ∈ ball (0 : ℂ) 1, ∀ y ∈ ball (0 : ℂ) 1,
      x ≠ y → diskExtension u x = diskExtension u y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) y))))
    {a b : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hb : b ∈ ball (0 : ℂ) 1)
    (hab : a ≠ b) (hvalue : diskExtension u a = diskExtension u b)
    (hDa : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a))
    (hDb : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b)) :
    let U : ℂ → M := diskExtension u
    let p := U a
    let s := ball (0 : ℂ) 1 ∩ U ⁻¹' (chartAt E p).source
    let ξ : Fin (Module.finrank ℝ E) → ℂ := fun i => chartComplexGradient p U i a
    let Q := chartGramBilin g p p
    let proj := chartLeadingPlaneProjection g p p ξ
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * ξ i).re)
    ∃ (N : E) (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
      Q N N = 1 ∧ proj N = 0 ∧
      (∀ v : E, v = lift (proj v) + (Q N v) • N) ∧
      a ∈ e₁.source ∧ b ∈ e₂.source ∧
      e₁.source ⊆ s ∧ e₂.source ⊆ s ∧ Disjoint e₁.source e₂.source ∧
      (e₁ : ℂ → ℂ) = F ∧ (e₂ : ℂ → ℂ) = F ∧
      ContDiffOn ℝ ∞ e₁.symm e₁.target ∧
      ContDiffOn ℝ ∞ e₂.symm e₂.target ∧
      IsOpen O ∧ F a ∈ O ∧ O ⊆ e₁.target ∩ e₂.target ∧
      let h₁ : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a)
      let h₂ : ℂ → ℝ := fun y => Q N (X (e₂.symm y) - X a)
      h₁ =ᶠ[𝓝 (F a)] h₂ := by
  classical
  intro U p s ξ Q proj X F lift
  with_reducible
    obtain ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      hdisj, he₁, he₂, hei₁, hei₂, hOo, haO, hOsub, hh₁, hh₂, hw, _,
      A, beta, c, hA, hbeta, hc, hpde⟩ :=
      morrey_regular_collision_elliptic_height_difference
        hu hd3 ha hb hab hvalue hDa hDb (hNoTransverse a ha b hb hab hvalue hDa hDb)
  let h₁ : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a)
  let h₂ : ℂ → ℝ := fun y => Q N (X (e₂.symm y) - X a)
  let w : ℂ → ℝ := fun y => h₁ y - h₂ y
  change ContDiffOn ℝ ∞ h₁ O at hh₁
  change ContDiffOn ℝ ∞ h₂ O at hh₂
  change ContDiffOn ℝ ∞ w O at hw
  change (e₁ : ℂ → ℂ) = F at he₁
  change (e₂ : ℂ → ℂ) = F at he₂
  refine ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
    hdisj, he₁, he₂, hei₁, hei₂, hOo, haO, hOsub, ?_⟩
  change h₁ =ᶠ[𝓝 (F a)] h₂
  by_contra hgerm
  have hnonzero : F a ∈ closure {x : ℂ | w x ≠ 0} := by
    by_contra hn
    apply hgerm
    filter_upwards [isClosed_closure.compl_mem_nhds hn] with z hz
    have hwz : w z = 0 := by
      by_contra h
      exact hz (subset_closure h)
    exact sub_eq_zero.mp hwz
  have hFvalue : F a = F b := congrArg proj (congrArg (extChartAt 𝓘(ℝ, E) p) hvalue)
  have he₁a : e₁.symm (F a) = a := by rw [← he₁]; exact e₁.left_inv hae₁
  have he₂b : e₂.symm (F a) = b := by rw [hFvalue, ← he₂]; exact e₂.left_inv hbe₂
  have hXvalue : X b = X a := congrArg (extChartAt 𝓘(ℝ, E) p) hvalue.symm
  have hzero : w (F a) = 0 := by
    change Q N (X (e₁.symm (F a)) - X a) - Q N (X (e₂.symm (F a)) - X a) = 0
    simp only [he₁a, he₂b, hXvalue, sub_self, map_zero]
  obtain ⟨q, hqO, _, hwq, hDwq⟩ :=
    Analysis.exists_regular_zero_near_of_elliptic_eq_zero hOo
      (A := A) (beta := beta) (c := c) (w := w)
      (fun i j => (hA i j).continuousOn) (fun i => (hbeta i).continuousOn)
      hc.continuousOn (fun y hy => (hpde y hy).1) (hw.of_le (by norm_num))
      (fun y hy => (hpde y hy).2) haO hzero hnonzero 1 (by norm_num)
  have hheight : h₁ q = h₂ q := sub_eq_zero.mp hwq
  have hderiv : fderiv ℝ h₁ q ≠ fderiv ℝ h₂ q := by
    intro hequal
    apply hDwq
    have hd : fderiv ℝ w q = fderiv ℝ h₁ q - fderiv ℝ h₂ q :=
      fderiv_fun_sub
        ((hh₁.contDiffAt (hOo.mem_nhds hqO)).differentiableAt (by simp))
        ((hh₂.contDiffAt (hOo.mem_nhds hqO)).differentiableAt (by simp))
    rw [hd, hequal, sub_self]
  have hs : IsOpen s := hu.smoothInterior.continuousOn.isOpen_inter_preimage
    isOpen_ball (chartAt E p).open_source
  obtain ⟨hne, hUeq, hmi₁, hmi₂, hsurj⟩ :=
    transverse_regular_pair_of_graph_height_derivatives_ne hs
      (hu.smoothInterior.mono inter_subset_left) (fun _ hz => hz.2)
      proj (Q N) N lift hsplit e₁ e₂ he₁s he₂s hdisj he₁ he₂ hei₁ hei₂
      (X a) (hOsub hqO).1 (hOsub hqO).2 hheight hderiv
  exact hNoTransverse _ (he₁s (e₁.map_target (hOsub hqO).1)).1
    _ (he₂s (e₂.map_target (hOsub hqO).2)).1 hne hUeq hmi₁ hmi₂ hsurj

/-- Closed-disk rank of the same smooth extension gives local source sheets
also at boundary points. The target can be the actual open manifold in which
the minimizing disk was constructed. -/
private theorem isLocallyInjective_disk_of_injective_mfderiv
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (q : C(closedDisk, M)) {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    IsLocallyInjective q := by
  obtain ⟨hQeq, S, hS, hDS, hQs⟩ := hQ
  let Sopen : TopologicalSpace.Opens ℂ := ⟨S, hS⟩
  let F : Sopen → M := fun z => Q z
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F :=
    hQs.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  let ι : closedDisk → Sopen := fun z => ⟨z, hDS z.property⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk (fun z => hDS z.property)
  have hFq (z : closedDisk) : F (ι z) = q z := hQeq z
  have hloc : IsLocallyInjective q := by
    intro x
    have hDF : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (ι x)) := by
      change Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : Sopen => Q z) (ι x) : ℂ →L[ℝ] E)
      rw [DifferentialGeometry.mfderiv_restrict_open]
      exact hrank x x.property
    have hImm := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
      (by simp : (∞ : ℕ∞ω) ≠ 0) hF (ι x) hDF
    have hnormal (z : Sopen) (hz : z ∈ hImm.domChart.source) :
        (hImm.codChart.extend 𝓘(ℝ, E)) (F z) =
          hImm.equiv ((hImm.domChart.extend 𝓘(ℝ, ℂ)) z, 0) := by
      have hz' : z ∈ (hImm.domChart.extend 𝓘(ℝ, ℂ)).source := by
        rwa [OpenPartialHomeomorph.extend_source]
      have hh := hImm.writtenInCharts ((hImm.domChart.extend 𝓘(ℝ, ℂ)).map_source hz')
      simpa only [Function.comp_apply,
        (hImm.domChart.extend 𝓘(ℝ, ℂ)).left_inv hz'] using hh
    have hinj : Set.InjOn F hImm.domChart.source := by
      intro z hz w hw hzw
      have hh := (hnormal z hz).symm.trans
        ((congrArg (hImm.codChart.extend 𝓘(ℝ, E)) hzw).trans (hnormal w hw))
      apply (hImm.domChart.extend 𝓘(ℝ, ℂ)).injOn
      · rwa [OpenPartialHomeomorph.extend_source]
      · rwa [OpenPartialHomeomorph.extend_source]
      · exact congrArg Prod.fst (hImm.equiv.injective hh)
    refine ⟨ι ⁻¹' hImm.domChart.source, hImm.domChart.open_source.preimage hι,
      hImm.mem_domChart_source, ?_⟩
    intro z hz w hw hzw
    exact Subtype.ext (congrArg (fun t : Sopen => (t : ℂ))
      (hinj hz hw ((hFq z).trans (hzw.trans (hFq w).symm))))
  exact hloc

/-- Equality of the scalar heights of the supplied actual graph germs gives
equality of the original disk's pushed neighborhood filters. The extension,
metric projection, normal splitting, inverse germs, and disk restriction are
all retained. This does not produce height equality or handle boundary germs.
-/
private theorem actual_disk_image_germs_of_height_germ_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : C(closedDisk, M)) {U : ℂ → M}
    (hUq : ∀ z : closedDisk, U z = q z)
    {a b : closedDisk}
    (ha : (a : ℂ) ∈ Metric.ball (0 : ℂ) 1)
    (hb : (b : ℂ) ∈ Metric.ball (0 : ℂ) 1)
    (hvalue : q a = q b) {p : M} {s : Set ℂ}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source) :
    let B : Fin (Module.finrank ℝ E) → ℂ := fun i => chartComplexGradient p U i a
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) B
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B i).re)
    ∀ (N : E) (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ),
      (∀ v : E, v = lift (proj v) + (Q N v) • N) →
      (a : ℂ) ∈ e₁.source → (b : ℂ) ∈ e₂.source →
      e₁.source ⊆ s → e₂.source ⊆ s →
      (e₁ : ℂ → ℂ) = F → (e₂ : ℂ → ℂ) = F →
      (fun y => Q N (X (e₁.symm y) - X a)) =ᶠ[𝓝 (F a)]
        (fun y => Q N (X (e₂.symm y) - X a)) →
      Filter.map q (𝓝 a) = Filter.map q (𝓝 b) := by
  intro B Q proj X F lift N e₁ e₂ hsplit hae₁ hbe₂ he₁s he₂s he₁ he₂ hheight
  have hUvalue : U a = U b := (hUq a).trans (hvalue.trans (hUq b).symm)
  have hFvalue : F a = F b := congrArg proj
    (congrArg (extChartAt 𝓘(ℝ, E) p) hUvalue)
  have ht₁ : F a ∈ e₁.target := by
    rw [← he₁]
    exact e₁.map_source hae₁
  have ht₂ : F a ∈ e₂.target := by
    rw [hFvalue, ← he₂]
    exact e₂.map_source hbe₂
  have hgraphs : (U ∘ e₁.symm) =ᶠ[𝓝 (F a)] (U ∘ e₂.symm) := by
    filter_upwards [hheight, e₁.open_target.mem_nhds ht₁,
      e₂.open_target.mem_nhds ht₂] with y hhy hy₁ hy₂
    have hproj₁ : proj (X (e₁.symm y)) = y := by
      change F (e₁.symm y) = y
      rw [← he₁]
      exact e₁.right_inv hy₁
    have hproj₂ : proj (X (e₂.symm y)) = y := by
      change F (e₂.symm y) = y
      rw [← he₂]
      exact e₂.right_inv hy₂
    have hnormal : Q N (X (e₁.symm y)) = Q N (X (e₂.symm y)) := by
      simpa only [map_sub, sub_left_inj] using hhy
    apply (extChartAt 𝓘(ℝ, E) p).injOn
    · simpa only [Function.comp_def, extChartAt_source] using
        hchart _ (he₁s (e₁.map_target hy₁))
    · simpa only [Function.comp_def, extChartAt_source] using
        hchart _ (he₂s (e₂.map_target hy₂))
    · change X (e₁.symm y) = X (e₂.symm y)
      calc
        X (e₁.symm y) = lift (proj (X (e₁.symm y))) +
            (Q N (X (e₁.symm y))) • N := hsplit _
        _ = lift (proj (X (e₂.symm y))) + (Q N (X (e₂.symm y))) • N := by
          rw [hproj₁, hproj₂, hnormal]
        _ = X (e₂.symm y) := (hsplit _).symm
  have hmap₁ : Filter.map e₁.symm (𝓝 (F a)) = 𝓝 (a : ℂ) := by
    rw [← he₁]
    exact e₁.symm_map_nhds_eq hae₁
  have hmap₂ : Filter.map e₂.symm (𝓝 (F a)) = 𝓝 (b : ℂ) := by
    rw [hFvalue, ← he₂]
    exact e₂.symm_map_nhds_eq hbe₂
  have hUmap : Filter.map U (𝓝 (a : ℂ)) = Filter.map U (𝓝 (b : ℂ)) := by
    rw [← hmap₁, ← hmap₂, Filter.map_map, Filter.map_map]
    exact Filter.map_congr hgraphs
  have hrestriction : U ∘ (Subtype.val : closedDisk → ℂ) = (q : closedDisk → M) :=
    funext hUq
  have hdisk (z : closedDisk) (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
      Filter.map q (𝓝 z) = Filter.map U (𝓝 (z : ℂ)) := by
    rw [← hrestriction, ← Filter.map_map, map_nhds_subtype_val]
    rw [nhdsWithin_eq_nhds.2
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)]
  exact (hdisk a ha).trans (hUmap.trans (hdisk b hb).symm)

/-- Under the supplied exclusion of transverse regular collisions, two distinct
regular interior points of the same Morrey disk have the same actual image
germ. Only the derivatives at these two points are assumed injective; no
closed-disk rank or regularity at other source points is used. -/
theorem IsMorreyDisk.image_germs_eq_of_regular_interior_collision_of_no_transverse
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk G γ q) (hd3 : Module.finrank ℝ E = 3)
    (hNoTransverse : ∀ x ∈ ball (0 : ℂ) 1, ∀ y ∈ ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y))))
    {a b : closedDisk}
    (ha : (a : ℂ) ∈ ball (0 : ℂ) 1) (hb : (b : ℂ) ∈ ball (0 : ℂ) 1)
    (hab : a ≠ b) (hvalue : q a = q b)
    (hDa : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (a : ℂ)))
    (hDb : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (b : ℂ))) :
    Filter.map q (𝓝 a) = Filter.map q (𝓝 b) := by
  classical
  have hne : (a : ℂ) ≠ (b : ℂ) := fun h => hab (Subtype.ext h)
  have hUvalue : diskExtension q a = diskExtension q b := by
    simpa only [diskExtension_coe] using hvalue
  with_reducible
    obtain ⟨N, e₁, e₂, O, _hNN, _hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      _hdisj, he₁, he₂, _hei₁, _hei₂, _hOo, _haO, _hOsub, hheight⟩ :=
      morrey_regular_collision_graph_germs_of_no_transverse hq hd3 hNoTransverse
        ha hb hne hUvalue hDa hDb
  have hchart (z : ℂ)
      (hz : z ∈ ball (0 : ℂ) 1 ∩
        (diskExtension q) ⁻¹' (chartAt E (diskExtension q a)).source) :
      diskExtension q z ∈ (chartAt E (diskExtension q a)).source := by
    change z ∈ ball (0 : ℂ) 1 ∧
      diskExtension q z ∈ (chartAt E (diskExtension q a)).source at hz
    exact hz.2
  with_reducible
    exact actual_disk_image_germs_of_height_germ_eq G q (diskExtension_coe q)
      ha hb hvalue
      (p := diskExtension q a)
      (s := ball (0 : ℂ) 1 ∩ (diskExtension q) ⁻¹' (chartAt E (diskExtension q a)).source)
      hchart N e₁ e₂ hsplit hae₁ hbe₂ he₁s he₂s he₁ he₂ hheight

/-- Conditional embedding of the supplied Morrey disk in its actual target.
Full closed-disk rank is used only at this final global stage. The exclusion
of transverse regular collisions remains an explicit hypothesis, and boundary
singleton fibers are supplied by the existing boundary-rank/phase theorem.
Instantiate the target with the actual open manifold and its complete metric;
no ambient-global minimality for another metric is asserted.
-/
theorem IsMorreyDisk.isEmbedding_of_no_transverse
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk G γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hd3 : Module.finrank ℝ E = 3)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ∀ θ : loopCircle, q z ≠ γ θ)
    (hNoTransverse : ∀ x ∈ ball (0 : ℂ) 1, ∀ y ∈ ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y)))) :
    IsEmbedding q := by
  classical
  obtain ⟨σ, hσ, htrace⟩ := hq.trace
  have hrankBoundary (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) :=
    hrank z (sphere_subset_closedBall hz)
  have hboundary := hQ.boundary_fiber_eq hγ hσ htrace hrankBoundary hseparate
  have hloc : IsLocallyInjective q :=
    isLocallyInjective_disk_of_injective_mfderiv q hQ hrank
  have hrankInterior (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z) := by
    have hder :
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) =
          (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z) := by
      ext v
      exact congrArg (fun L => L v)
        ((hQ.eventuallyEq_diskExtension hz).mfderiv_eq
          (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)))
    have hQrank : Function.Injective
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) :=
      hrank z (ball_subset_closedBall hz)
    change Function.Injective
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)
    intro v w hvw
    apply hQrank
    exact (congrArg (fun L : ℂ →L[ℝ] E => L v) hder).trans
      (hvw.trans (congrArg (fun L : ℂ →L[ℝ] E => L w) hder).symm)
  have hinterior (x y : closedDisk) (hne : x ≠ y) (hxy : q x = q y) :
      (x : ℂ) ∈ ball (0 : ℂ) 1 := by
    by_contra hx
    have hnorm : ‖(x : ℂ)‖ = 1 := by
      have hle : ‖(x : ℂ)‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right] using x.property
      have hnotlt : ¬ ‖(x : ℂ)‖ < 1 := by
        simpa only [mem_ball, dist_zero_right] using hx
      exact le_antisymm hle (le_of_not_gt hnotlt)
    let c : Circle := ⟨(x : ℂ), mem_sphere_zero_iff_norm.mpr hnorm⟩
    obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
    have hbx : diskBoundary θ = x := by
      apply Subtype.ext
      have hc := congrArg (fun w : Circle => (w : ℂ)) hθ
      simpa only [AddCircle.homeomorphCircle_apply] using! hc
    have hyx : y = x := (hboundary θ y
      (hxy.symm.trans (congrArg q hbx).symm)).trans hbx
    exact hne hyx.symm
  have hgerm : ∀ x y : closedDisk, q x = q y →
      Filter.map q (𝓝 x) = Filter.map q (𝓝 y) := by
    intro x y hxy
    by_cases heq : x = y
    · subst y
      rfl
    have hx := hinterior x y heq hxy
    have hy := hinterior y x (Ne.symm heq) hxy.symm
    exact hq.image_germs_eq_of_regular_interior_collision_of_no_transverse hd3
      hNoTransverse hx hy heq hxy (hrankInterior x hx) (hrankInterior y hy)
  exact (q.continuous.isClosedEmbedding
    (injective_of_isLocallyInjective_of_coincident_germs q.continuous hloc hgerm
      ⟨diskBoundary 0, hboundary 0⟩)).isEmbedding

end DifferentialGeometry.Geometry
