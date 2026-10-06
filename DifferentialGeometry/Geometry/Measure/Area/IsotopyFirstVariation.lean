import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskFirstVariation
import DifferentialGeometry.Geometry.Connection.SourceCovariantPartial
import DifferentialGeometry.Geometry.Connection.SourceSectionRestriction
import DifferentialGeometry.Geometry.Metric.ParameterTangentMap

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

private theorem hasDerivAt_pullback_gramCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΦ₀ : Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hvelocity : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = X x)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    HasDerivAt (fun t => (Diffeomorph.pullbackMetric g (Φ t)).inner (U z)
        (diskMapPartial U z v) (diskMapPartial U z w))
      (g.inner (U z) (sourceSectionCovariantDerivative g U (fun q => X (U q)) z v)
          (diskMapPartial U z w) +
        g.inner (U z) (diskMapPartial U z v)
          (sourceSectionCovariantDerivative g U (fun q => X (U q)) z w)) 0 := by
  let F : ℝ × ℂ → M := fun p => Φ p.1 (U p.2)
  let P (a : ℝ × ℂ) (p : ℝ × ℂ) : TangentSpace 𝓘(ℝ, E) (F p) :=
    mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F p a
  let V : Set (ℝ × ℂ) := univ ×ˢ s
  have hV : IsOpen V := isOpen_univ.prod hs
  have hzV : (0, z) ∈ V := ⟨mem_univ _, hz⟩
  have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (fun p : ℝ × ℂ => (p.1, U p.2)) V :=
    contMDiffOn_fst.prodMk (hU.comp contMDiffOn_snd (fun _ hp => hp.2))
  have hFprod : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) ∞ F V := by
    exact hΦ.comp_contMDiffOn hmap
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ F V := by
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hFprod
  have hFd (t : ℝ) (q : ℂ) (hq : q ∈ s) :
      MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) F (t, q) :=
    ((hFprod (t, q) ⟨mem_univ _, hq⟩).contMDiffAt
      (hV.mem_nhds ⟨mem_univ _, hq⟩)).mdifferentiableAt (by simp)
  have hP (a : ℝ × ℂ) : ContMDiffOn 𝓘(ℝ, ℝ × ℂ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E (F p) (P a p)) V :=
    contMDiffOn_source_partial hV hF (m := ∞) (by simp) a
  have hpair : ContDiffAt ℝ ∞
      (fun p => g.inner (F p) (P (0, v) p) (P (0, w) p)) (0, z) :=
    ((contDiffOn_sourceSectionPairing g hF (hP (0, v)) (hP (0, w)))
      (0, z) hzV).contDiffAt (hV.mem_nhds hzV)
  have hpair_deriv :
      fderiv ℝ (fun p => g.inner (F p) (P (0, v) p) (P (0, w) p)) (0, z) (1, 0) =
        g.inner (F (0, z)) (sourceCovariantPartial g F (0, z) (1, 0) (0, v))
          (P (0, w) (0, z)) +
        g.inner (F (0, z)) (P (0, v) (0, z))
          (sourceCovariantPartial g F (0, z) (1, 0) (0, w)) :=
    fderiv_sourceSectionPairing g hV hF (hP (0, v)) (hP (0, w)) hzV (1, 0)
  have hspace (t : ℝ) (a : ℂ) :
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => F (t, q)) z a = P (0, a) (t, z) := by
    have h := mfderiv_parameter_slice (hFd t z hz) a
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  have hcentral : (fun q => F (0, q)) = U := by
    funext q
    simp [F, hΦ₀]
  have hP₀ (a : ℂ) : P (0, a) (0, z) = diskMapPartial U z a := by
    rw [← hspace, hcentral]
    rfl
  have hW : (fun q => P (1, 0) (0, q)) =ᶠ[𝓝 z] fun q => X (U q) := by
    filter_upwards [hs.mem_nhds hz] with q hq
    have h := mfderiv_parameter_time (hFd 0 q hq) 1
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.symm.trans (hvelocity (U q))
  have hcov (a : ℂ) : sourceCovariantPartial g F (0, z) (0, a) (1, 0) =
      sourceSectionCovariantDerivative g U (fun q => X (U q)) z a := by
    unfold sourceCovariantPartial
    rw [sourceSectionCovariantDerivative_parameter_slice, hcentral]
    exact sourceSectionCovariantDerivative_congr g U hW a
  have htime : HasDerivAt (fun t : ℝ => (t, z)) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 z)
  have hd := (hpair.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 htime
  rw [hpair_deriv,
    sourceCovariantPartial_symm g hV hF hzV (1, 0) (0, v),
    sourceCovariantPartial_symm g hV hF hzV (1, 0) (0, w),
    hcov, hcov, hP₀, hP₀, congrFun hcentral z] at hd
  have hUz := ((hU z hz).contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp)
  have hPcomp (t : ℝ) (a : ℂ) : P (0, a) (t, z) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ t) (U z) (diskMapPartial U z a) := by
    rw [← hspace]
    have h := mfderiv_comp z ((Φ t).contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hUz
    change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => F (t, q)) z = _ at h
    rw [h]
    rfl
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => by
    change (Diffeomorph.pullbackMetric g (Φ t)).inner (U z)
      (diskMapPartial U z v) (diskMapPartial U z w) =
      g.inner (F (t, z)) (P (0, v) (t, z)) (P (0, w) (t, z))
    rw [Diffeomorph.pullbackMetric_inner, hPcomp, hPcomp])

/-- The actual first Gram area variation of the supplied ambient isotopy is
its tangential covariant trace in the original independent coordinate frame.
The same initial velocity is used at every ambient point. No normality,
conformality, or minimality is assumed. -/
theorem diskMapGramMetricVariationDensity_pullback_eq_tangentTrace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΦ₀ : Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hvelocity : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = X x)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s)
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    let v := diskMapPartial (E := E) U z 1
    let w := diskMapPartial (E := E) U z Complex.I
    let D := fun a => sourceSectionCovariantDerivative g U (fun q => X (U q)) z a
    diskMapGramMetricVariationDensity (fun t => Diffeomorph.pullbackMetric g (Φ t)) 0 U z =
      (g.inner (U z) w w * g.inner (U z) (D 1) v +
        g.inner (U z) v v * g.inner (U z) (D Complex.I) w -
        g.inner (U z) v w *
          (g.inner (U z) (D 1) w + g.inner (U z) (D Complex.I) v)) /
        riemannianAreaDensity g U z := by
  dsimp only
  have hcoef := hasDerivAt_pullback_gramCoefficient g Φ hΦ hΦ₀ X hvelocity hs hU hz
  have hJ : riemannianAreaDensity g U z ≠ 0 :=
    (riemannianAreaDensity_pos_of_injective_mfderiv g hi).ne'
  dsimp only [diskMapGramMetricVariationDensity]
  rw [(hcoef 1 1).deriv, (hcoef 1 Complex.I).deriv, (hcoef Complex.I Complex.I).deriv,
    hΦ₀, Diffeomorph.pullbackMetric_refl]
  rw [g.symm (U z) (diskMapPartial U z 1)
      (sourceSectionCovariantDerivative g U (fun q => X (U q)) z 1),
    g.symm (U z) (diskMapPartial U z Complex.I)
      (sourceSectionCovariantDerivative g U (fun q => X (U q)) z Complex.I),
    g.symm (U z) (diskMapPartial U z 1)
      (sourceSectionCovariantDerivative g U (fun q => X (U q)) z Complex.I)]
  field_simp [hJ]
  ring

end DifferentialGeometry.Geometry
