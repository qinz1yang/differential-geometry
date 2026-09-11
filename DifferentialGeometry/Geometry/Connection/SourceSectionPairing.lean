import DifferentialGeometry.Geometry.Connection.SectionAlongRegularity
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic



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
