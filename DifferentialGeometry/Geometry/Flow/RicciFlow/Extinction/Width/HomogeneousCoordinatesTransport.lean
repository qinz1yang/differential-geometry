import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauClassical

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]

def HomogeneousCoordinates.postcomposeDiffeomorph
    (g : SmoothRiemannianMetric I Q) {n : ℕ} (h : HomogeneousCoordinates g n)
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) :
    HomogeneousCoordinates (Diffeomorph.pullbackMetricCross g Φ.symm) n := by
  let V := EuclideanSpace ℝ (Fin n)
  let ψ : A → CubeChart (I := I) (Q := Q) n := fun p => h.atPoint (Φ.symm p)
  let chart : A → OpenPartialHomeomorph V A := fun p =>
    (ψ p).chart.trans Φ.toHomeomorph.toOpenPartialHomeomorph
  have hsource (p : A) : (chart p).source = (ψ p).chart.source := by
    simp only [chart, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  have hmap (p : A) : (chart p : V → A) = Φ ∘ (ψ p).chart :=
    OpenPartialHomeomorph.coe_trans _ _
  have hsrc (p : A) : closedCube n ⊆ (chart p).source := by
    rw [hsource p]
    exact (ψ p).closedCube_subset_source
  have hsm (p : A) : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (chart p) (chart p).source := by
    rw [hsource p, hmap p]
    exact Φ.contMDiff.comp_contMDiffOn (ψ p).smooth
  have hsymm (p : A) : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞
      (chart p).symm (chart p).target := by
    have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ ((ψ p).chart.symm ∘ (Φ.symm : A → Q))
        (Φ.symm ⁻¹' (ψ p).chart.target) :=
      (ψ p).smooth_inverse.comp Φ.symm.contMDiff.contMDiffOn (fun _ hy => hy)
    have heq : ((chart p).symm : A → V) = (ψ p).chart.symm ∘ (Φ.symm : A → Q) := by
      dsimp only [chart]
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.coe_trans]
      rfl
    rw [heq]
    have htarget : (chart p).target = Φ '' (ψ p).chart.target := by
      dsimp only [chart]
      rw [OpenPartialHomeomorph.trans_target]
      simp only [Homeomorph.toOpenPartialHomeomorph_target, univ_inter]
      exact (Φ.toHomeomorph.image_eq_preimage_symm _).symm
    have hpre : Φ.symm ⁻¹' (ψ p).chart.target = (chart p).target := by
      rw [htarget]
      ext x
      constructor
      · intro hx
        exact ⟨Φ.symm x, hx, Φ.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        change Φ.symm (Φ y) ∈ (ψ p).chart.target
        simpa only [Φ.symm_apply_apply] using hy
    exact hpre ▸ h1
  let atPoint : A → CubeChart (I := 𝓘(ℝ, E)) (Q := A) n := fun p =>
    { chart := chart p
      closedCube_subset_source := hsrc p
      smooth := hsm p
      smooth_inverse := hsymm p }
  have hident (p : A) {y : V} (hy : y ∈ (chart p).source) (v w : V) :
      (atPoint p).pullMetric (Diffeomorph.pullbackMetricCross g Φ.symm) y v w =
        (ψ p).pullMetric g y v w := by
    have hys : y ∈ (ψ p).chart.source := (hsource p) ▸ hy
    have hψ : MDifferentiableAt 𝓘(ℝ, V) I (ψ p).chart y :=
      ((ψ p).smooth.contMDiffAt ((ψ p).chart.open_source.mem_nhds hys)).mdifferentiableAt
        (by simp)
    have hderiv : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (chart p) y =
        (mfderiv I 𝓘(ℝ, E) Φ ((ψ p).chart y)).comp (mfderiv 𝓘(ℝ, V) I (ψ p).chart y) := by
      rw [hmap p]
      exact mfderiv_comp y (Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hψ
    have happly (v : V) : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (chart p) y v =
        mfderiv I 𝓘(ℝ, E) Φ ((ψ p).chart y) (mfderiv 𝓘(ℝ, V) I (ψ p).chart y v) := by
      rw [hderiv]
      rfl
    change (Diffeomorph.pullbackMetricCross g Φ.symm).inner ((chart p) y)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (chart p) y v)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (chart p) y w) = _
    rw [happly v, happly w, hmap p]
    exact DifferentialGeometry.Diffeomorph.inner_pullbackMetricCross_comp g Φ ((ψ p).chart y)
      (mfderiv 𝓘(ℝ, V) I (ψ p).chart y v) (mfderiv 𝓘(ℝ, V) I (ψ p).chart y w)
  refine {
    atPoint := atPoint
    centered := ?_
    lowerBound := h.lowerBound
    upperBound := h.upperBound
    lower_pos := h.lower_pos
    lower_le_upper := h.lower_le_upper
    ellipticity := ?_
    derivative_bounds := ?_ }
  · intro p
    change (chart p) 0 = p
    rw [hmap p]
    change Φ ((h.atPoint (Φ.symm p)).chart 0) = p
    rw [h.centered, Φ.apply_symm_apply]
  · intro p y hy v
    have hyc : y ∈ closedCube n := fun i => (hy i).le
    rw [hident p (hsrc p hyc) v v]
    exact h.ellipticity (Φ.symm p) y hy v
  · intro k
    obtain ⟨C, hC, hbound⟩ := h.derivative_bounds k
    refine ⟨C, hC, fun p y hy i j => ?_⟩
    have heq : (fun z => (atPoint p).pullMetric (Diffeomorph.pullbackMetricCross g Φ.symm)
        z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =ᶠ[𝓝 y]
        (fun z => (ψ p).pullMetric g z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
      filter_upwards [(chart p).open_source.mem_nhds (hsrc p hy)] with z hz
      exact hident p hz _ _
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) heq k).eq_of_nhds]
    exact hbound (Φ.symm p) y hy i j

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
