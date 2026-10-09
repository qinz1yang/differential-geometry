import DifferentialGeometry.Geometry.Connection.SectionAlongRegularity
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionAtBasepoint



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def sourceSectionCovariantDerivative (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : A → M) (W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)) (z v : A) :
    TangentSpace 𝓘(ℝ, E) (U z) :=
  covDerivAlong g (fun t : ℝ => U (z + t • v)) (fun t => W (z + t • v)) 0

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] in
theorem contDiffOn_sourceSectionPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : A → M} {s : Set A}
    (hU : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ U s)
    {W Z : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s)
    (hZ : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (Z z)) s) :
    ContDiffOn ℝ ∞ (fun z => g.inner (U z) (W z) (Z z)) s := by
  intro z hz
  have h : ContMDiffWithinAt 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U q)
        (g.inner (U q) (W q) (Z q))) s z := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact g.contMDiff.contMDiffAt.comp_contMDiffWithinAt z (hU z hz)
    · exact hW z hz
    · exact hZ z hz
  exact (contMDiffWithinAt_totalSpace.mp h).2.contDiffWithinAt



theorem fderiv_sourceSectionPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : A → M} {s : Set A}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ U s)
    {W Z : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s)
    (hZ : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (Z z)) s)
    {z : A} (hz : z ∈ s) (v : A) :
    fderiv ℝ (fun q => g.inner (U q) (W q) (Z q)) z v =
      g.inner (U z) (sourceSectionCovariantDerivative g U W z v) (Z z) +
      g.inner (U z) (W z) (sourceSectionCovariantDerivative g U Z z v) := by
  let line : ℝ → A := fun t => z + t • v
  have hl : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hl0 : line 0 = z := by simp [line]
  have hlz : line 0 ∈ s := by rwa [hl0]
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (U ∘ line) 0 :=
    ((hU _ hlz).contMDiffAt (hs.mem_nhds hlz)).comp 0 hl.contMDiff.contMDiffAt
  have hWl := ((hW _ hlz).contMDiffAt (hs.mem_nhds hlz)).comp 0 hl.contMDiff.contMDiffAt
  have hZl := ((hZ _ hlz).contMDiffAt (hs.mem_nhds hlz)).comp 0 hl.contMDiff.contMDiffAt
  have hrepW : DifferentiableAt ℝ (chartRepAt (U ∘ line) (fun t => W (line t)) 0) 0 :=
    (contDiffAt_chartRepAt_of_section hWl).differentiableAt (by simp)
  have hrepZ : DifferentiableAt ℝ (chartRepAt (U ∘ line) (fun t => Z (line t)) 0) 0 :=
    (contDiffAt_chartRepAt_of_section hZl).differentiableAt (by simp)
  have hinner := inner_deriv_at (by simp : (1 : WithTop ℕ∞) ≤ ∞) g (U ∘ line)
    (fun t => W (line t)) (fun t => Z (line t)) 0 hγ hrepW hrepZ
  have hscalar := ((contDiffOn_sourceSectionPairing g hU hW hZ z hz).contDiffAt
    (hs.mem_nhds hz)).differentiableAt (by simp)
  have hline : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have heq := (hscalar.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hline hl0.symm).unique hinner
  simp only [Function.comp_apply] at heq
  erw [hl0] at heq
  exact heq

end DifferentialGeometry.Geometry

end

section

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem sourceSectionCovariantDerivative_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : A → M} {s : Set A}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ U s)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s)
    {z : A} (hz : z ∈ s) (v : A) :
    let F := (extChartAt 𝓘(ℝ, E) (U z)) ∘ U
    let R := fun q => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ (U q) (W q)
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ (U z)
      (sourceSectionCovariantDerivative g U W z v) =
      fderiv ℝ R z v + chartChristoffelContraction g (U z) (fderiv ℝ F z v) (R z) (F z) := by
  let line : ℝ → A := fun t => z + t • v
  have hl0 : line 0 = z := by simp [line]
  have hl : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hUz := (hU z hz).contMDiffAt (hs.mem_nhds hz)
  let F := (extChartAt 𝓘(ℝ, E) (U z)) ∘ U
  let R := fun q => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ (U q) (W q)
  have hF : ContDiffAt ℝ 2 F z :=
    ((contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := U z)).comp z hUz).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hR : ContDiffAt ℝ ∞ R z := by
    have hWz := contMDiffAt_totalSpace.mp ((hW z hz).contMDiffAt (hs.mem_nhds hz))
    have hb : U z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)
    have heq : R =ᶠ[𝓝 z] (fun q =>
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)
          (TotalSpace.mk' E (U q) (W q))).2) := by
      filter_upwards [hUz.continuousAt
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).open_baseSet.mem_nhds hb)] with q hmem
      simp only [R]
      rw [(trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt_apply (R := ℝ),
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).coe_linearMapAt_of_mem hmem]
    exact hWz.2.contDiffAt.congr_of_eventuallyEq heq
  have hrep : chartRepAt (U ∘ line) (fun t => W (line t)) 0 =ᶠ[𝓝 0] R ∘ line := by
    filter_upwards [] with t
    simp only [chartRepAt_apply, Function.comp_apply, hl0, R]
  have hd := ((hR.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    (x := 0) hl hl0.symm).congr_of_eventuallyEq hrep
  have hcurve : HasDerivAt (chartCurve (I := 𝓘(ℝ, E)) (U z) (U ∘ line))
      (fderiv ℝ F z v) 0 :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq
      (x := 0) hl hl0.symm
  have hcov := covDerivAlong_chartCoord g (U ∘ line) (fun t => W (line t)) 0
  have hself (p : M) (X : TangentSpace 𝓘(ℝ, E) p) :
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ p X = X :=
    (trivToE_basepoint p X).trans (tangentSpaceModelContinuousLinearEquiv_apply p X)
  rw [hself] at hcov ⊢
  refine hcov.trans ?_
  rw [chartCovDerivAlong_def, hd.deriv, hrep.eq_of_nhds]
  simp only [Function.comp_apply, hl0]
  rw [hcurve.deriv]
  simp only [chartCurve_def, Function.comp_apply, hl0]
  rfl

end DifferentialGeometry.Geometry

end

end
