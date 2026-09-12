import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.OpenConnection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ComponentDisk


noncomputable section
open Bundle Manifold Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width
section Germ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem covDerivAlong_congr_germ (g : SmoothRiemannianMetric I M)
    (gamma eta : ℝ → M)
    (V : ∀ s, TangentSpace I (gamma s)) (W : ∀ s, TangentSpace I (eta s)) (t : ℝ)
    (hcurve : gamma =ᶠ[𝓝 t] eta)
    (hfield : (fun s => (V s : E)) =ᶠ[𝓝 t] (fun s => (W s : E))) :
    (covDerivAlong g gamma V t : E) = (covDerivAlong g eta W t : E) := by
  let rep (p q : M) (v : E) : E :=
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ q
      (show TangentSpace I q from v)
  let out (p : M) (v : E) : E :=
    (trivializationAt E (TangentSpace I) p).symmL ℝ p v
  let conn (p : M) (u v w : E) : E := Geodesic.chartChristoffelContraction g p u v w
  have hpoint : gamma t = eta t := hcurve.eq_of_nhds
  have hrep : chartRepAt (I := I) gamma V t =ᶠ[𝓝 t]
      chartRepAt (I := I) eta W t := by
    filter_upwards [hcurve, hfield] with s hs hVs
    change rep (gamma t) (gamma s) (V s) = rep (eta t) (eta s) (W s)
    exact (congrArg₂ (fun p q => rep p q (V s : E)) hpoint hs).trans
      (congrArg (rep (eta t) (eta s)) hVs)
  have hchart : chartCurve (I := I) (gamma t) gamma =ᶠ[𝓝 t]
      chartCurve (I := I) (eta t) eta := by
    filter_upwards [hcurve] with s hs
    exact congrArg₂ (fun p q => extChartAt I p q) hpoint hs
  change out (gamma t) (deriv (chartRepAt (I := I) gamma V t) t +
      conn (gamma t) (deriv (chartCurve (I := I) (gamma t) gamma) t)
        (chartRepAt (I := I) gamma V t t) (chartCurve (I := I) (gamma t) gamma t)) =
    out (eta t) (deriv (chartRepAt (I := I) eta W t) t +
      conn (eta t) (deriv (chartCurve (I := I) (eta t) eta) t)
        (chartRepAt (I := I) eta W t t) (chartCurve (I := I) (eta t) eta t))
  rw [hrep.deriv_eq, hrep.eq_of_nhds, hchart.deriv_eq, hchart.eq_of_nhds]
  exact congrArg (fun p => out p (deriv (chartRepAt (I := I) eta W t) t +
    conn p (deriv (chartCurve (I := I) (eta t) eta) t)
      (chartRepAt (I := I) eta W t t) (chartCurve (I := I) (eta t) eta t))) hpoint

theorem diskLocalTension_congr_germ (g : SmoothRiemannianMetric I M)
    (F G : ℂ → M) (z : ℂ) (h : F =ᶠ[𝓝 z] G) :
    (diskLocalTension g F z : E) = (diskLocalTension g G z : E) := by
  have hline (v : ℂ) : Tendsto (fun t : ℝ => z + t • v) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ => z + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  have hd (v : ℂ) : (fun y : ℂ => (mfderiv 𝓘(ℝ, ℂ) I F y v : E)) =ᶠ[𝓝 z]
      (fun y : ℂ => (mfderiv 𝓘(ℝ, ℂ) I G y v : E)) := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact DFunLike.congr_fun (hy.mfderiv_eq (I := 𝓘(ℝ, ℂ)) (I' := I)) v
  have heq (v : ℂ) :
      (covDerivAlong g (fun t : ℝ => F (z + t • v))
        (fun t => mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) 0 : E) =
      (covDerivAlong g (fun t : ℝ => G (z + t • v))
        (fun t => mfderiv 𝓘(ℝ, ℂ) I G (z + t • v) v) 0 : E) := by
    apply covDerivAlong_congr_germ
    · exact h.comp_tendsto (hline v)
    · exact (hd v).comp_tendsto (hline v)
  change _ + _ = _ + _
  exact congrArg₂ (fun x y : E => x + y) (heq 1) (heq Complex.I)

theorem diskLocalTension_congr_of_eqOn (g : SmoothRiemannianMetric I M)
    {F G : ℂ → M} {U : Set ℂ} (hU : IsOpen U) (h : EqOn F G U) {z : ℂ} (hz : z ∈ U) :
    (diskLocalTension g F z : E) = (diskLocalTension g G z : E) :=
  diskLocalTension_congr_germ g F G z (eventuallyEq_of_mem (hU.mem_nhds hz) h)
end Germ

section OpenTarget
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ Q] [T2Space Q] in
theorem mfderiv_subtypeVal (U : TopologicalSpace.Opens Q) (F : ℂ → U) (z : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) I (Subtype.val ∘ F) z : ℂ →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, ℂ) I F z : ℂ →L[ℝ] E) := by
  have hi : MDifferentiableAt 𝓘(ℝ, ℂ) I (Subtype.val ∘ F) z ↔
      MDifferentiableAt 𝓘(ℝ, ℂ) I F z := by
    simpa only [mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_subtypeVal_iff U F univ z
  by_cases hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z
  · have hd := mfderiv_comp z (hasMFDerivAt_subtype_val (I := I) U (F z)).mdifferentiableAt hF
    rw [mfderiv_subtype_val] at hd
    exact hd.trans (by ext v; rfl)
  · rw [mfderiv_zero_of_not_mdifferentiableAt hF,
      mfderiv_zero_of_not_mdifferentiableAt (fun h => hF (hi.mp h))]
    rfl


theorem tension_subtypeVal (g : SmoothRiemannianMetric I Q)
    (U : TopologicalSpace.Opens Q) (F : ℂ → U) (z : ℂ) (hF : ContinuousAt F z) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    (diskLocalTension (g.restrictOpen U) F z : E) =
      (diskLocalTension g (Subtype.val ∘ F) z : E) := by
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  have hd := mfderiv_subtypeVal (I := I) U F
  have heq (v : ℂ) :
      (covDerivAlong (g.restrictOpen U) (fun t : ℝ => F (z + t • v))
        (fun t => mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) 0 : E) =
      (covDerivAlong g (fun t : ℝ => (F (z + t • v) : Q))
        (fun t => mfderiv 𝓘(ℝ, ℂ) I (Subtype.val ∘ F) (z + t • v) v) 0 : E) := by
    have hc : ContinuousAt (fun t : ℝ => F (z + t • v)) 0 := by
      have hline : ContinuousAt (fun t : ℝ => z + t • v) 0 :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      have hF0 : ContinuousAt F (z + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using hF
      exact hF0.comp (f := fun t : ℝ => z + t • v) hline
    have hh := covDerivAlong_restrictOpen g U (fun t : ℝ => F (z + t • v))
      (fun t => mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) 0 hc
    change @Eq E _ _ at hh
    change @Eq E _ _
    simpa only [hd] using! hh
  change _ + _ = _ + _
  exact congrArg₂ (fun x y : E => x + y) (heq 1) (heq Complex.I)

theorem harmonic_subtypeVal (g : SmoothRiemannianMetric I Q)
    (U : TopologicalSpace.Opens Q)
    (v : SmoothDisk (I := I) (Q := U)) (u : SmoothDisk (I := I) (Q := Q))
    (hmap : ∀ z, u.map z = (v.map z : Q)) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    v.IsHarmonic (g.restrictOpen U) ↔ u.IsHarmonic g := by
  classical
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  have hext : diskExtension u.map = Subtype.val ∘ diskExtension v.map := by
    rw [show (u.map : Disk → Q) = (fun z => (v.map z : Q)) from funext hmap]
    exact diskExtension_subtypeVal U v.map
  constructor
  · intro hv z F
    let S := F.domain ∩ F.map ⁻¹' (U : Set Q)
    have hS : IsOpen S := F.smooth.continuousOn.isOpen_inter_preimage F.isOpen_domain U.isOpen
    have hFz : F.map z = (v.map z : Q) := by
      calc
        F.map z = diskExtension u.map z := F.agrees ⟨F.mem_domain, z.property⟩
        _ = u.map z := diskExtension_coe u.map z
        _ = (v.map z : Q) := hmap z
    have hzS : (z : ℂ) ∈ S := ⟨F.mem_domain, by
      change F.map (z : ℂ) ∈ U
      rw [hFz]
      exact (v.map z).property⟩
    let F0 : ℂ → U := fun y => if h : F.map y ∈ U then ⟨F.map y, h⟩ else v.map diskCenter
    have hF0 : EqOn (Subtype.val ∘ F0) F.map S := by
      intro y hy
      have hyU : F.map y ∈ U := hy.2
      simp only [Function.comp_apply, F0, dif_pos hyU]
    have hF0smooth : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ F0 S := by
      have hcompose : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ (Subtype.val ∘ F0) S :=
        (F.smooth.mono inter_subset_left).congr hF0
      intro y hy
      exact (ContMDiffWithinAt.subtypeVal_comp_iff U F0 S y).mp (hcompose y hy)
    let G : DiskLocalExtension (I := I) v.map z := {
      map := F0
      domain := S
      isOpen_domain := hS
      mem_domain := hzS
      smooth := hF0smooth
      agrees := by
        intro y hy
        apply Subtype.ext
        have hyF : F.map y = diskExtension u.map y := F.agrees ⟨hy.1.1, hy.2⟩
        have hy0 : (F0 y : Q) = F.map y := hF0 hy.1
        rw [hy0, hyF, hext]
        rfl }
    have hzero := hv z G
    change (diskLocalTension (g.restrictOpen U) F0 z : E) = 0 at hzero
    have hn := tension_subtypeVal g U F0 z
      ((hF0smooth z hzS).contMDiffAt (hS.mem_nhds hzS)).continuousAt
    have hgerm : Subtype.val ∘ F0 =ᶠ[𝓝 (z : ℂ)] F.map :=
      Filter.eventuallyEq_of_mem (hS.mem_nhds hzS) hF0
    have ht := diskLocalTension_congr_germ g (Subtype.val ∘ F0) F.map z hgerm
    exact ht.symm.trans (hn.symm.trans hzero)
  · intro hu z G
    let F : DiskLocalExtension (I := I) u.map z := {
      map := Subtype.val ∘ G.map
      domain := G.domain
      isOpen_domain := G.isOpen_domain
      mem_domain := G.mem_domain
      smooth := (contMDiff_subtype_val (I := I) (U := U)).comp_contMDiffOn G.smooth
      agrees := by
        intro y hy
        have hh := congrArg (fun q : U => (q : Q)) (G.agrees hy)
        rw [hext]
        exact hh }
    have hzero := hu z F
    change (diskLocalTension g (Subtype.val ∘ G.map) z : E) = 0 at hzero
    have hn := tension_subtypeVal g U G.map z
      ((G.smooth z G.mem_domain).contMDiffAt
        (G.isOpen_domain.mem_nhds G.mem_domain)).continuousAt
    exact hn.trans hzero
end OpenTarget
end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
