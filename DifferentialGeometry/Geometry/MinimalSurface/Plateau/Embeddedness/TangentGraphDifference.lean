import DifferentialGeometry.Geometry.HarmonicMap.TangentGraphGerms
import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphDifference

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval

set_option maxHeartbeats 800000 in
-- The full graph-jet and scalar-PDE tuple exceeds the default elaboration budget.
/-- The unchanged Morrey disk supplies a smooth elliptic height-difference
equation at any distinct regular nontransverse collision, with no assumption
that the two source points share a small branch neighborhood. -/
theorem CuspIncompressibility.ConsumerAudit.morrey_regular_collision_elliptic_height_difference
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
