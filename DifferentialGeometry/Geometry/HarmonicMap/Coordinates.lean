import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.TaylorIntegral

noncomputable section

open Set Filter Bundle Manifold InnerProductSpace
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry
open Riemannian.Geodesic Riemannian.AlongCurve Riemannian.CovariantDerivativeAlong

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem chart_partial_general {U : ℂ → M} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) I U z) (a : M)
    (hsrc : U z ∈ (chartAt H a).source) (v : ℂ) :
    (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (U z)
        (mfderiv 𝓘(ℝ, ℂ) I U z v) = fderiv ℝ ((extChartAt I a) ∘ U) z v := by
  have hh : ((trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (U z)).comp
      (mfderiv 𝓘(ℝ, ℂ) I U z) = fderiv ℝ ((extChartAt I a) ∘ U) z := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hsrc]
    exact (mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := I) (I'' := 𝓘(ℝ, E)) z
      (mdifferentiableAt_extChartAt hsrc) hU).symm.trans mfderiv_eq_fderiv
  exact congrArg (fun L => L v) hh

omit [FiniteDimensional ℝ E] in
private theorem chartRep_partial_eventually
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) I 2 U s)
    {a : M} (hsrc : ∀ z ∈ s, U z ∈ (chartAt H a).source)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    chartRepAtBase a (fun t : ℝ => U (z + t • v))
        (fun t => mfderiv 𝓘(ℝ, ℂ) I U (z + t • v) w) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => fderiv ℝ ((extChartAt I a) ∘ U) (z + t • v) w) := by
  have hline : ContinuousAt (fun t : ℝ => z + t • v) 0 := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, z + t • v ∈ s :=
    hline.preimage_mem_nhds (by simpa using hs.mem_nhds hz)
  filter_upwards [hnear] with t ht
  rw [chartRepAtBase_apply]
  exact chart_partial_general ((hU.contMDiffAt (hs.mem_nhds ht)).mdifferentiableAt (by simp))
    a (hsrc _ ht) w

private theorem covariant_partial_chart_general [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) I 2 U s)
    {a : M} (hsrc : ∀ z ∈ s, U z ∈ (chartAt H a).source)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    let γ : ℝ → M := fun t => U (z + t • v)
    let V : ∀ t, TangentSpace I (γ t) := fun t => mfderiv 𝓘(ℝ, ℂ) I U (z + t • v) w
    let X : ℂ → E := (extChartAt I a) ∘ U
    (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (γ 0)
        (covDerivAlong g γ V 0) =
      fderiv ℝ (fun q => fderiv ℝ X q w) z v +
        chartChristoffelContraction g a (fderiv ℝ X z v) (fderiv ℝ X z w) (X z) := by
  let γ : ℝ → M := fun t => U (z + t • v)
  let V : ∀ t, TangentSpace I (γ t) := fun t => mfderiv 𝓘(ℝ, ℂ) I U (z + t • v) w
  let X : ℂ → E := (extChartAt I a) ∘ U
  have hγ0 : γ 0 = U z := by simp [γ]
  have hline : ContDiffAt ℝ 2 (fun t : ℝ => z + t • v) 0 := by fun_prop
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 := by
    have hu : ContMDiffAt 𝓘(ℝ, ℂ) I 2 U (z + (0 : ℝ) • v) := by
      simpa using hU.contMDiffAt (hs.mem_nhds hz)
    exact (hu.comp 0 hline.contMDiffAt).mdifferentiableAt (by simp)
  have hX : ContDiffAt ℝ 2 X z :=
    ((contMDiffAt_extChartAt' (I := I) (n := 2) (hsrc z hz)).comp z
      (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt
  have hrep := chartRep_partial_eventually hs hU hsrc hz v w
  have hderrep : deriv (chartRepAtBase a γ V) 0 =
      fderiv ℝ (fun q => fderiv ℝ X q w) z v := by
    rw [hrep.deriv_eq]
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ X q w) (z + (0 : ℝ) • v) := by
      simpa only [zero_smul, add_zero] using
        (((hX.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by simp))
    simpa only [zero_smul, add_zero] using hd.deriv_comp_add_smul
  have hdercurve : deriv (chartCurve (I := I) a γ) 0 = fderiv ℝ X z v := by
    have hd : DifferentiableAt ℝ X (z + (0 : ℝ) • v) := by
      simpa only [zero_smul, add_zero] using hX.differentiableAt (by simp)
    change deriv (fun t : ℝ => X (z + t • v)) 0 = _
    simpa only [zero_smul, add_zero] using hd.deriv_comp_add_smul
  have hrep0 : chartRepAtBase a γ V 0 = fderiv ℝ X z w := by
    have hh := hrep.eq_of_nhds
    change chartRepAtBase a γ V 0 = fderiv ℝ X (z + (0 : ℝ) • v) w at hh
    simpa only [zero_smul, add_zero] using hh
  have hcurve0 : chartCurve (I := I) a γ 0 = X z := by
    change extChartAt I a (γ 0) = X z
    rw [hγ0]
    rfl
  have hVdiff : DifferentiableAt ℝ (chartRepAt γ V 0) 0 := by
    let b := γ 0
    let s' := s ∩ U ⁻¹' (chartAt H b).source
    have hs' : IsOpen s' := hU.continuousOn.isOpen_inter_preimage hs (chartAt H b).open_source
    have hz' : z ∈ s' := ⟨hz, by
      change U z ∈ (chartAt H b).source
      rw [← hγ0]
      exact mem_chart_source H b⟩
    have hrep' := chartRep_partial_eventually hs' (hU.mono inter_subset_left)
      (a := b) (fun _ ht => ht.2) hz' v w
    have hY : ContDiffAt ℝ 2 ((extChartAt I b) ∘ U) z :=
      ((contMDiffAt_extChartAt' (I := I) (n := 2) hz'.2).comp z
        (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt
    have hD : DifferentiableAt ℝ (fun q => fderiv ℝ ((extChartAt I b) ∘ U) q w) z :=
      ((hY.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hh : DifferentiableAt ℝ
        (fun t : ℝ => fderiv ℝ ((extChartAt I b) ∘ U) (z + t • v) w) 0 := by
      have hd : DifferentiableAt ℝ (fun q => fderiv ℝ ((extChartAt I b) ∘ U) q w)
          (z + (0 : ℝ) • v) := by simpa using hD
      exact hd.comp 0 (hline.differentiableAt (by simp))
    exact hh.congr_of_eventuallyEq hrep'
  have hβ : γ 0 ∈ (chartAt H a).source := by rw [hγ0]; exact hsrc z hz
  have hb : γ 0 ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hβ
  have hcov := covDeriv_chartAt g γ V 0 a hγ hβ hVdiff
  change (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (γ 0)
    (covDerivAlong g γ V 0) = _
  rw [← hcov, (trivializationAt E (TangentSpace I) a).continuousLinearMapAt_symmL (R := ℝ) hb,
    chartCovDerivAlong_def, hderrep, hdercurve, hrep0, hcurve0]


private def planarCovariantPartial (g : SmoothRiemannianMetric I M) (U : ℂ → M)
    (z v w : ℂ) : TangentSpace I (U z) := by
  simpa only [zero_smul, add_zero] using covDerivAlong g (fun t : ℝ => U (z + t • v))
    (fun t => mfderiv 𝓘(ℝ, ℂ) I U (z + t • v) w) 0

private def planarTension (g : SmoothRiemannianMetric I M) (U : ℂ → M) (z : ℂ) :
    TangentSpace I (U z) :=
  planarCovariantPartial g U z 1 1 + planarCovariantPartial g U z Complex.I Complex.I

private theorem laplacian_chart_eq_of_tension_general [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) I 2 U s)
    {a : M} (hsrc : ∀ z ∈ s, U z ∈ (chartAt H a).source)
    {z : ℂ} (hz : z ∈ s) (hτ : planarTension g U z = 0) :
    let X : ℂ → E := (extChartAt I a) ∘ U
    Laplacian.laplacian X z =
      -(chartChristoffelContraction g a (fderiv ℝ X z 1) (fderiv ℝ X z 1) (X z) +
        chartChristoffelContraction g a (fderiv ℝ X z Complex.I)
          (fderiv ℝ X z Complex.I) (X z)) := by
  let X : ℂ → E := (extChartAt I a) ∘ U
  have hX : ContDiffAt ℝ 2 X z :=
    ((contMDiffAt_extChartAt' (I := I) (n := 2) (hsrc z hz)).comp z
      (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt
  have hpartial (v w : ℂ) : fderiv ℝ (fun q => fderiv ℝ X q w) z v =
      fderiv ℝ (fderiv ℝ X) z v w := by
    rw [fderiv_clm_apply ((hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp))
      (differentiableAt_const w)]
    simp
  have hzero := congrArg
    ((trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (U z)) hτ
  rw [planarTension, map_add, map_zero] at hzero
  have hpair (v : ℂ) := covariant_partial_chart_general g hs hU hsrc hz v v
  dsimp only at hpair
  have hpair' (v : ℂ) :
      (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (U z)
        (planarCovariantPartial g U z v v) =
        fderiv ℝ (fun q => fderiv ℝ X q v) z v +
          chartChristoffelContraction g a (fderiv ℝ X z v) (fderiv ℝ X z v) (X z) := by
    have hh := hpair v
    erw [zero_smul, add_zero] at hh
    exact hh
  rw [hpair' 1, hpair' Complex.I, hpartial, hpartial] at hzero
  change Laplacian.laplacian X z = _
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply]
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_add_add_comm] at hzero
  exact hzero


private def harmonicCoordinateForcing (g : SmoothRiemannianMetric I M) (a : M)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (p : E × (ℂ →L[ℝ] E)) : E :=
  -(fderiv ℝ e.symm (e p.1)
    (chartChristoffelContraction g a (fderiv ℝ e p.1 (p.2 1)) (fderiv ℝ e p.1 (p.2 1)) (e p.1) +
      chartChristoffelContraction g a (fderiv ℝ e p.1 (p.2 Complex.I))
        (fderiv ℝ e p.1 (p.2 Complex.I)) (e p.1))) +
    ∑ i : Fin (Module.finrank ℝ ℂ), fderiv ℝ (fderiv ℝ e.symm) (e p.1)
      (fderiv ℝ e p.1 (p.2 (stdOrthonormalBasis ℝ ℂ i)))
      (fderiv ℝ e p.1 (p.2 (stdOrthonormalBasis ℝ ℂ i)))

private theorem laplacian_coordinates_of_tension_eq_zero [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (a : M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) I 2 U s)
    (hsrc : MapsTo U s (Φ.target ∩ (extChartAt I a).source))
    {z : ℂ} (hz : z ∈ s) (hτ : planarTension g U z = 0) :
    let e := Φ.trans (extChartAtPartialDiffeomorph I ∞ a)
    let X := Φ.symm ∘ U
    Laplacian.laplacian X z = harmonicCoordinateForcing g a e (X z, fderiv ℝ X z) := by
  let e := Φ.trans (extChartAtPartialDiffeomorph I ∞ a)
  let X := Φ.symm ∘ U
  let Z := (extChartAt I a) ∘ U
  have hXZ (q : ℂ) (hq : q ∈ s) : e (X q) = Z q := by
    change extChartAt I a (Φ (Φ.symm (U q))) = extChartAt I a (U q)
    exact congrArg (extChartAt I a) (Φ.toOpenPartialHomeomorph.right_inv (hsrc hq).1)
  have hZX (q : ℂ) (hq : q ∈ s) : e.symm (Z q) = X q := by
    change Φ.symm ((extChartAt I a).symm (extChartAt I a (U q))) = Φ.symm (U q)
    rw [(extChartAt I a).left_inv (hsrc hq).2]
  have hx (q : ℂ) (hq : q ∈ s) : X q ∈ e.source := by
    refine ⟨Φ.toOpenPartialHomeomorph.map_target (hsrc hq).1, ?_⟩
    change Φ (Φ.symm (U q)) ∈ (extChartAt I a).source
    have hr : Φ (Φ.symm (U q)) = U q := Φ.toOpenPartialHomeomorph.right_inv (hsrc hq).1
    rw [hr]
    exact (hsrc hq).2
  have hz' : Z z ∈ e.target := hXZ z hz ▸ e.toOpenPartialHomeomorph.map_source (hx z hz)
  have hX : ContDiffAt ℝ 2 X z := contMDiffAt_iff_contDiffAt.mp
    (((Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds (hsrc hz).1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp z
      (hU.contMDiffAt (hs.mem_nhds hz)))
  have hZ : ContDiffAt ℝ 2 Z z :=
    ((contMDiffAt_extChartAt' (I := I) (n := 2) (show U z ∈ (chartAt H a).source by simpa only [extChartAt_source] using (hsrc hz).2)).comp z
      (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt
  have he : ContDiffAt ℝ ∞ e (X z) := contMDiffAt_iff_contDiffAt.mp
    (e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds (hx z hz)))
  have hei : ContDiffAt ℝ ∞ e.symm (Z z) := contMDiffAt_iff_contDiffAt.mp
    (e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hz'))
  have hnear : Z =ᶠ[𝓝 z] e ∘ X := by
    filter_upwards [hs.mem_nhds hz] with q hq
    exact (hXZ q hq).symm
  have hneari : X =ᶠ[𝓝 z] e.symm ∘ Z := by
    filter_upwards [hs.mem_nhds hz] with q hq
    exact (hZX q hq).symm
  have hDZ : fderiv ℝ Z z = (fderiv ℝ e (X z)).comp (fderiv ℝ X z) := by
    rw [hnear.fderiv_eq]
    exact fderiv_comp z (he.differentiableAt (by simp)) (hX.differentiableAt (by simp))
  have hΔZ := laplacian_chart_eq_of_tension_general g hs hU (fun q hq => (show U q ∈ (chartAt H a).source by simpa only [extChartAt_source] using (hsrc hq).2)) hz hτ
  change Laplacian.laplacian Z z = _ at hΔZ
  have hcomp := hZ.laplacian_comp
    (hei.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change Laplacian.laplacian X z = harmonicCoordinateForcing g a e (X z, fderiv ℝ X z)
  rw [(laplacian_congr_nhds hneari).eq_of_nhds, hcomp, hΔZ, hDZ]
  simp only [harmonicCoordinateForcing, ContinuousLinearMap.comp_apply, map_neg, hXZ z hz]
  rfl


private theorem harmonicCoordinateForcing_smul (g : SmoothRiemannianMetric I M) (a : M)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (x : E) (D : ℂ →L[ℝ] E) (r : ℝ) :
    harmonicCoordinateForcing g a e (x, r • D) =
      (r * r) • harmonicCoordinateForcing g a e (x, D) := by
  simp only [harmonicCoordinateForcing, smul_apply, map_smul,
    chartChristoffelContraction_smul_smul, ← smul_add, smul_smul]
  simp only [smul_add, Finset.smul_sum, smul_neg]

private theorem contDiffOn_harmonicCoordinateForcing
    (g : SmoothRiemannianMetric I M) (a : M)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (het : MapsTo e e.source (interior (extChartAt I a).target)) :
    ContDiffOn ℝ ∞ (harmonicCoordinateForcing g a e) (e.source ×ˢ Set.univ) := by
  have he : ContDiffOn ℝ ∞ e e.source := e.contMDiffOn_toFun.contDiffOn
  have hi : ContDiffOn ℝ ∞ e.symm e.target := e.contMDiffOn_invFun.contDiffOn
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source := he.fderiv_of_isOpen e.open_source (by simp)
  have hdi : ContDiffOn ℝ ∞ (fderiv ℝ e.symm) e.target := hi.fderiv_of_isOpen e.open_target (by simp)
  have hddi : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ e.symm)) e.target :=
    hdi.fderiv_of_isOpen e.open_target (by simp)
  intro p hp
  have hD : ContDiffAt ℝ ∞ (fun q : E × (ℂ →L[ℝ] E) => fderiv ℝ e q.1) p :=
    (hd.contDiffAt (e.open_source.mem_nhds hp.1)).comp p contDiffAt_fst
  have hY : ContDiffAt ℝ ∞ (fun q : E × (ℂ →L[ℝ] E) => e q.1) p :=
    (he.contDiffAt (e.open_source.mem_nhds hp.1)).comp p contDiffAt_fst
  have hDX (v : ℂ) : ContDiffAt ℝ ∞
      (fun q : E × (ℂ →L[ℝ] E) => fderiv ℝ e q.1 (q.2 v)) p :=
    hD.clm_apply (contDiffAt_snd.clm_apply contDiffAt_const)
  have hΓ (v : ℂ) : ContDiffAt ℝ ∞ (fun q : E × (ℂ →L[ℝ] E) =>
      chartChristoffelContraction g a (fderiv ℝ e q.1 (q.2 v))
        (fderiv ℝ e q.1 (q.2 v)) (e q.1)) p :=
    (contDiffAt_chartChristoffelContraction g a _ _ _ (het hp.1)).comp
      (x := p) (g := fun q : E × E × E => chartChristoffelContraction g a q.1 q.2.1 q.2.2)
      (f := fun q : E × (ℂ →L[ℝ] E) =>
        (fderiv ℝ e q.1 (q.2 v), fderiv ℝ e q.1 (q.2 v), e q.1))
      ((hDX v).prodMk ((hDX v).prodMk hY))
  have hz : e p.1 ∈ e.target := e.toOpenPartialHomeomorph.map_source hp.1
  have hInv : ContDiffAt ℝ ∞ (fun q : E × (ℂ →L[ℝ] E) => fderiv ℝ e.symm (e q.1)) p :=
    (hdi.contDiffAt (e.open_target.mem_nhds hz)).comp p hY
  have hInv2 : ContDiffAt ℝ ∞
      (fun q : E × (ℂ →L[ℝ] E) => fderiv ℝ (fderiv ℝ e.symm) (e q.1)) p :=
    (hddi.contDiffAt (e.open_target.mem_nhds hz)).comp p hY
  exact (((hInv.clm_apply ((hΓ 1).add (hΓ Complex.I))).neg).add
    (ContDiffAt.sum (fun i _ => (hInv2.clm_apply (hDX (stdOrthonormalBasis ℝ ℂ i))).clm_apply
      (hDX (stdOrthonormalBasis ℝ ℂ i))))).contDiffWithinAt

private theorem exists_bound_harmonicCoordinateForcing
    (g : SmoothRiemannianMetric I M) (a : M)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (het : MapsTo e e.source (interior (extChartAt I a).target))
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ D : ℂ →L[ℝ] E,
      ‖harmonicCoordinateForcing g a e (x, D)‖ ≤ C * ‖D‖ ^ 2 := by
  have hc := (contDiffOn_harmonicCoordinateForcing g a e het).continuousOn.mono
    (Set.prod_mono hKs (Set.subset_univ (Metric.closedBall (0 : ℂ →L[ℝ] E) 1)))
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : ℂ →L[ℝ] E) 1)).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun x hx D => ?_⟩
  by_cases hD : D = 0
  · have hzero := harmonicCoordinateForcing_smul g a e x 0 0
    simp only [zero_smul, zero_mul] at hzero
    simpa only [hD, hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using (le_refl (0 : ℝ))
  have hn : ‖(‖D‖⁻¹ : ℝ) • D‖ = 1 := norm_smul_inv_norm hD
  have hunit : (‖D‖⁻¹ : ℝ) • D ∈ Metric.closedBall (0 : ℂ →L[ℝ] E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hn] using (le_refl (1 : ℝ))
  have hb := (hC (x, (‖D‖⁻¹ : ℝ) • D) ⟨hx, hunit⟩).trans (le_max_left C 0)
  have hrestore : ‖D‖ • ((‖D‖⁻¹ : ℝ) • D) = D := by
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD), one_smul]
  have hh := harmonicCoordinateForcing_smul g a e x ((‖D‖⁻¹ : ℝ) • D) ‖D‖
  rw [hrestore] at hh
  rw [hh, norm_smul, Real.norm_of_nonneg (mul_self_nonneg _)]
  exact (mul_le_mul_of_nonneg_left hb (mul_self_nonneg _)).trans_eq (by ring)


theorem exists_quadratic_laplacian_coordinates [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (a : M) :
    let Ω := (Φ.trans (extChartAtPartialDiffeomorph I ∞ a)).source
    ∃ Q : E × (ℂ →L[ℝ] E) → E,
      ContDiffOn ℝ ∞ Q (Ω ×ˢ Set.univ) ∧
      (∀ x D (r : ℝ), Q (x, r • D) = (r * r) • Q (x, D)) ∧
      (∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ K, ∀ D : ℂ →L[ℝ] E, ‖Q (x, D)‖ ≤ C * ‖D‖ ^ 2) ∧
      ∀ (U : ℂ → M) (s : Set ℂ), IsOpen s → ContMDiffOn 𝓘(ℝ, ℂ) I 2 U s →
        MapsTo U s (Φ.target ∩ (extChartAt I a).source) → ∀ z ∈ s,
        let τ₁ : TangentSpace I (U z) := by
          simpa only [zero_smul, add_zero] using
            covDerivAlong g (fun t : ℝ => U (z + t • (1 : ℂ)))
              (fun t => mfderiv 𝓘(ℝ, ℂ) I U (z + t • (1 : ℂ)) (1 : ℂ)) 0
        let τ₂ : TangentSpace I (U z) := by
          simpa only [zero_smul, add_zero] using
            covDerivAlong g (fun t : ℝ => U (z + t • Complex.I))
              (fun t => mfderiv 𝓘(ℝ, ℂ) I U (z + t • Complex.I) Complex.I) 0
        let τ := τ₁ + τ₂
        τ = 0 → Laplacian.laplacian (Φ.symm ∘ U) z =
          Q ((Φ.symm ∘ U) z, fderiv ℝ (Φ.symm ∘ U) z) := by
  let e := Φ.trans (extChartAtPartialDiffeomorph I ∞ a)
  have het : MapsTo e e.source (interior (extChartAt I a).target) := by
    intro x hx
    change e x ∈ interior (extChartAtPartialDiffeomorph I ∞ a).target
    rw [(extChartAtPartialDiffeomorph I ∞ a).open_target.interior_eq]
    exact (e.toOpenPartialHomeomorph.map_source hx).1
  refine ⟨harmonicCoordinateForcing g a e, contDiffOn_harmonicCoordinateForcing g a e het,
    harmonicCoordinateForcing_smul g a e, ?_, ?_⟩
  · intro K hK hKs
    exact exists_bound_harmonicCoordinateForcing g a e het hK hKs
  · intro U s hs hU hsrc z hz
    dsimp only
    intro hτ
    apply laplacian_coordinates_of_tension_eq_zero g Φ a hs hU hsrc hz
    exact hτ

end DifferentialGeometry.Geometry
