import DifferentialGeometry.Geometry.Metric.FamilySectionPairing
import DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import DifferentialGeometry.Analysis.Calculus.Derivative.Diagonal



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem hasDerivAt_metricFamilySourcePairing
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {U : A → M} {s : Set A} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ U s)
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)}
    (hW : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) s)
    (hZ : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (Z q)) s)
    {c : ℝ → A} (hc : ContDiffAt ℝ ∞ c t) (hcs : c t ∈ s) :
    HasDerivAt (fun r => (G r).inner (U (c r)) (W (c r)) (Z (c r)))
      (deriv (fun r => (G r).inner (U (c t)) (W (c t)) (Z (c t))) t +
        (G t).inner (U (c t))
          (sourceSectionCovariantDerivative (G t) U W (c t) (deriv c t)) (Z (c t)) +
        (G t).inner (U (c t)) (W (c t))
          (sourceSectionCovariantDerivative (G t) U Z (c t) (deriv c t))) t := by
  let F : ℝ × ℝ → ℝ := fun q => (G q.1).inner (U (c q.2)) (W (c q.2)) (Z (c q.2))
  have hc' := hc.contMDiffAt
  have hUc := ((hU _ hcs).contMDiffAt (hs.mem_nhds hcs)).comp t hc'
  have hWc := ((hW _ hcs).contMDiffAt (hs.mem_nhds hcs)).comp t hc'
  have hZc := ((hZ _ hcs).contMDiffAt (hs.mem_nhds hcs)).comp t hc'
  have hF : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F (t, t) :=
    contMDiffAt_metricFamilySectionPairing hG contMDiffAt_fst
      (hUc.comp (t, t) contMDiffAt_snd) ht
      (hWc.comp (t, t) contMDiffAt_snd) (hZc.comp (t, t) contMDiffAt_snd)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hF
  have hFd := hF.contDiffAt.differentiableAt (by simp)
  have hdiag := hFd.comp (f := fun r : ℝ => (r, r)) t
    (differentiableAt_id.prodMk differentiableAt_id)
  have hscalar := ((contDiffOn_sourceSectionPairing (G t) hU hW hZ _ hcs).contDiffAt
    (hs.mem_nhds hcs)).differentiableAt (by simp)
  have hfixed := hscalar.hasFDerivAt.comp_hasDerivAt t
    (hc.differentiableAt (by simp)).hasDerivAt
  have he := DifferentialGeometry.Analysis.deriv_diagonal hFd
  dsimp only [F] at he hdiag
  dsimp only [Function.comp_def] at hfixed hdiag
  rw [hfixed.deriv, fderiv_sourceSectionPairing (G t) hs hU hW hZ hcs] at he
  rw [← add_assoc] at he
  rw [← he]
  exact hdiag.hasDerivAt

end DifferentialGeometry.Geometry

end

section

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem derivWithin_metricFamilyPairing
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {T : Set ℝ} (hT : UniqueDiffWithinAt ℝ T t) (htT : t ∈ T)
    {γ : ℝ → M} (hγ : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ T t)
    {W Z : ∀ r, TangentSpace 𝓘(ℝ, E) (γ r)}
    (hW : ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun r => TotalSpace.mk' E (γ r) (W r)) T t)
    (hZ : ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun r => TotalSpace.mk' E (γ r) (Z r)) T t) :
    derivWithin (fun r => (G r).inner (γ r) (W r) (Z r)) T t =
      deriv (fun r => (G r).inner (γ t) (W t) (Z t)) t +
        derivWithin (fun r => (G t).inner (γ r) (W r) (Z r)) T t := by
  let F : ℝ × ℝ → ℝ := fun p => (G p.1).inner (γ p.2) (W p.2) (Z p.2)
  have hγsnd : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ => γ p.2) (T ×ˢ T) (t, t) := hγ.comp (s := T ×ˢ T) (f := fun p : ℝ × ℝ => p.2) (t, t) contMDiffWithinAt_snd
    (fun (q : ℝ × ℝ) hp => hp.2)
  have hWsnd : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun p : ℝ × ℝ =>
        TotalSpace.mk' E (γ p.2) (W p.2)) (T ×ˢ T) (t, t) := hW.comp (s := T ×ˢ T) (f := fun p : ℝ × ℝ => p.2) (t, t) contMDiffWithinAt_snd
    (fun (q : ℝ × ℝ) hp => hp.2)
  have hZsnd : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun p : ℝ × ℝ =>
        TotalSpace.mk' E (γ p.2) (Z p.2)) (T ×ˢ T) (t, t) := hZ.comp (s := T ×ˢ T) (f := fun p : ℝ × ℝ => p.2) (t, t) contMDiffWithinAt_snd
    (fun (q : ℝ × ℝ) hp => hp.2)
  have hF : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F (T ×ˢ T) (t, t) :=
    contMDiffWithinAt_metricFamilySectionPairing hG contMDiffWithinAt_fst hγsnd ht hWsnd hZsnd
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hF
  have he := DifferentialGeometry.Analysis.derivWithin_diagonal hT htT
    (hF.contDiffWithinAt.differentiableWithinAt (by simp))
  have hfixed : DifferentiableAt ℝ (fun r => (G r).inner (γ t) (W t) (Z t)) t := by
    have h : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun r => (G r).inner (γ t) (W t) (Z t)) t :=
      contMDiffAt_metricFamilySectionPairing hG contMDiffAt_id contMDiffAt_const ht
        contMDiffAt_const contMDiffAt_const
    exact h.contDiffAt.differentiableAt (by simp)
  dsimp only [F] at he
  rwa [hfixed.derivWithin hT] at he

end DifferentialGeometry.Geometry

end

end
