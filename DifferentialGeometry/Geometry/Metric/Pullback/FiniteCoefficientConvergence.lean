import DifferentialGeometry.Analysis.Calculus.MapConvergence.FinitePullback
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.UniformConvergence

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.CheegerGromovCompactness

theorem pullbackMetricCoefficients_mapCP_convergence_of_chart_convergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)]
    {U V K : Set E} {p : ℕ}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) I E (M i) ∞)
    (hsource : ∀ i, (Φ i).source = V)
    (P : ∀ i, E → M i)
    (hP : ∀ i, ContMDiffOn 𝓘(ℝ, E) I (p + 1 : ℕ) (P i) U)
    (hcapture : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ i in atTop, MapsTo (P i) L (Φ i).target)
    (hcoord : MapCPConvergenceOn K (p + 1) (fun i => (Φ i).symm ∘ P i) id)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ S : Set E, IsCompact S → S ⊆ V →
      MapCPConvergenceOn S p (fun i => pullbackMetricCoefficients (g i) (Φ i)) B)
    (hBC : ContDiffOn ℝ p B V) (hK : IsCompact K) (hKU : K ⊆ U) :
    MapCPConvergenceOn K p (fun i => pullbackMetricCoefficients (g i) (P i)) B := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  let A : ℕ → E → E := fun i => (Φ i).symm ∘ P i
  have hlocal : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∃ W : Set E, IsOpen W ∧ L ⊆ W ∧ W ⊆ U ∧
        ∀ᶠ i in atTop, ContDiffOn ℝ (p + 1 : ℕ) (A i) W ∧ MapsTo (A i) W V := by
    intro L hL hLU
    obtain ⟨W, hW, hLW, hWU, hcompact⟩ :=
      exists_open_between_and_isCompact_closure hL hU hLU
    have hWU' : W ⊆ U := subset_closure.trans hWU
    refine ⟨W, hW, hLW, hWU', ?_⟩
    filter_upwards [hcapture (closure W) hcompact hWU] with i hi
    have hmap : MapsTo (P i) W (Φ i).target := hi.mono_left subset_closure
    have hΦinv : ContMDiffOn I 𝓘(ℝ, E) (p + 1 : ℕ) (Φ i).symm (Φ i).target :=
      (Φ i).contMDiffOn_invFun.of_le (by exact_mod_cast le_top)
    refine ⟨(hΦinv.comp ((hP i).mono hWU') hmap).contDiffOn, ?_⟩
    intro x hx
    rw [← hsource i]
    exact (Φ i).toOpenPartialHomeomorph.map_target (hmap hx)
  have hBc : ∀ i, ContDiffOn ℝ p (pullbackMetricCoefficients (g i) (Φ i)) V := by
    intro i
    exact (contDiffOn_pullback_metric_coefficients (g i) hV
      (by simpa only [hsource i] using (Φ i).contMDiffOn_toFun)).of_le
        (by exact_mod_cast le_top)
  have hconv := mapCPConvergenceOn_pullbackForm_comp_fderiv_locally
    hV hK hcoord hB (hlocal K hK hKU) contDiffOn_id hBc hBC hUV
  obtain ⟨W, hW, hKW, hWU, hcompact⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  have hWU' : W ⊆ U := subset_closure.trans hWU
  apply hconv.congr_eventually hW hKW ?_ ?_
  · filter_upwards [hcapture (closure W) hcompact hWU] with i hi
    intro x hx
    ext v w
    exact (pullbackMetricCoefficients_fderiv_symm (g i) (Φ i)
      (((hP i).contMDiffAt (hU.mem_nhds (hWU' hx))).mdifferentiableAt
        (by simp))
      (hi (subset_closure hx)) v w).symm
  · intro x _
    ext v w
    simp

theorem pullbackMetricCoefficients_comp_mapCP_convergence_of_chart_convergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E H'}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
    {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)]
    {W : Set X} {V K : Set E} {p : ℕ}
    (hW : IsOpen W) (hV : IsOpen V)
    (ψ : PartialDiffeomorph 𝓘(ℝ, E) J E X (p + 1 : ℕ))
    (hUV : ψ.source ∩ ψ ⁻¹' W ⊆ V)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) I E (M i) ∞)
    (hsource : ∀ i, V ⊆ (Φ i).source)
    (F : ∀ i, X → M i)
    (hF : ∀ᶠ i in atTop, ContMDiffOn J I (p + 1 : ℕ) (F i) W)
    (hcapture : ∀ L : Set E, IsCompact L → L ⊆ ψ.source ∩ ψ ⁻¹' W →
      ∀ᶠ i in atTop, MapsTo (F i ∘ ψ) L (Φ i).target)
    (hcoord : ∀ L : Set E, IsCompact L → L ⊆ ψ.source ∩ ψ ⁻¹' W →
      MapCPConvergenceOn L (p + 1) (fun i => (Φ i).symm ∘ F i ∘ ψ) id)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ S : Set E, IsCompact S → S ⊆ V →
      MapCPConvergenceOn S p (fun i => pullbackMetricCoefficients (g i) (Φ i)) B)
    (hBC : ContDiffOn ℝ p B V) (hK : IsCompact K)
    (hKU : K ⊆ ψ.source ∩ ψ ⁻¹' W) :
    MapCPConvergenceOn K p (fun i => pullbackMetricCoefficients (g i) (F i ∘ ψ)) B := by
  classical
  let U : Set E := ψ.source ∩ ψ ⁻¹' W
  have hU : IsOpen U := ψ.toOpenPartialHomeomorph.isOpen_inter_preimage hW
  let Ψ : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) I E (M i) ∞ := fun i =>
    DifferentialGeometry.Topology.PartialDiffeomorph.restrict (Φ i) V hV
  have hΨsource : ∀ i, (Ψ i).source = V := by
    intro i
    change (Φ i).source ∩ V = V
    exact inter_eq_right.mpr (hsource i)
  let P : ∀ i, E → M i := fun i =>
    if ContMDiffOn J I (p + 1 : ℕ) (F i) W then F i ∘ ψ else Φ i
  have hPeq : ∀ᶠ i in atTop, P i = F i ∘ ψ :=
    hF.mono fun i hi => by simp only [P, ite_eq_left hi]
  have hP : ∀ i, ContMDiffOn 𝓘(ℝ, E) I (p + 1 : ℕ) (P i) U := by
    intro i
    by_cases hi : ContMDiffOn J I (p + 1 : ℕ) (F i) W
    · simp only [P, ite_eq_left hi]
      exact hi.comp (ψ.contMDiffOn_toFun.mono inter_subset_left) (fun _ hx => hx.2)
    · simp only [P, ite_eq_right hi]
      exact ((Φ i).contMDiffOn_toFun.of_le (by exact_mod_cast le_top)).mono
        (hUV.trans (hsource i))
  have hcapture' : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ i in atTop, MapsTo (P i) L (Ψ i).target := by
    intro L hL hLU
    have hzero := tendstoUniformlyOn_of_cPConvergence
      ((hcoord L hL hLU).mono_order (Nat.zero_le (p + 1)))
    have hcoordV := hzero.eventually_mapsTo_of_isCompact hL continuousOn_id hV
      (hLU.trans hUV)
    filter_upwards [hPeq, hcapture L hL hLU, hcoordV] with i hi hcap hmap x hx
    rw [hi]
    change F i (ψ x) ∈ (Φ i).target ∩ (Φ i).symm ⁻¹' V
    exact ⟨hcap hx, hmap hx⟩
  have hcoord' : MapCPConvergenceOn K (p + 1) (fun i => (Ψ i).symm ∘ P i) id := by
    apply (hcoord K hK hKU).congr_eventually hU hKU ?_ (Set.eqOn_refl _ _)
    filter_upwards [hPeq] with i hi x _
    rw [hi]
    rfl
  have hconv := pullbackMetricCoefficients_mapCP_convergence_of_chart_convergence
    hU hV hUV g Ψ hΨsource P hP hcapture' hcoord' hB hBC hK hKU
  apply hconv.congr_eventually hU hKU ?_ (Set.eqOn_refl _ _)
  filter_upwards [hPeq] with i hi x _
  rw [hi]


end DifferentialGeometry.Geometry
