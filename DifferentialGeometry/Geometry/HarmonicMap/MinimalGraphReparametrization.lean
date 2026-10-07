import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphEquation

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem exists_inverse_germ_of_smooth_rightInverse
    {f r : ℂ → ℂ} {s O : Set ℂ} (hs : IsOpen s) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f s) (hr : ContDiffOn ℝ ∞ r O)
    (hmaps : MapsTo r O s) (hright : ∀ y ∈ O, f (r y) = y)
    {y : ℂ} (hy : y ∈ O) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      r y ∈ e.source ∧ e.source ⊆ s ∧ (e : ℂ → ℂ) = f ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ y ∈ e.target ∧ e.symm =ᶠ[𝓝 y] r := by
  have hfd := (hf.contDiffAt (hs.mem_nhds (hmaps hy))).differentiableAt (by simp)
  have hrd := (hr.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)
  have hnear : f ∘ r =ᶠ[𝓝 y] id := by
    filter_upwards [hO.mem_nhds hy] with q hq using hright q hq
  have hder : (fderiv ℝ f (r y)).comp (fderiv ℝ r y) =
      ContinuousLinearMap.id ℝ ℂ := by
    rw [← fderiv_comp y hfd hrd, hnear.fderiv_eq, fderiv_id]
  have hsurj : Function.Surjective (fderiv ℝ f (r y)) := by
    intro v
    exact ⟨fderiv ℝ r y v, congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hder⟩
  have hbij : Function.Bijective (fderiv ℝ f (r y)) :=
    ⟨(LinearMap.injective_iff_surjective (f := (fderiv ℝ f (r y)).toLinearMap)).mpr hsurj,
      hsurj⟩
  let L : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ f (r y)).toLinearMap hbij).toContinuousLinearEquiv
  have hL : (L : ℂ →L[ℝ] ℂ) = fderiv ℝ f (r y) := by ext v; rfl
  obtain ⟨e, hre, hes, he, hei⟩ := Analysis.exists_smooth_localInverse hs hf (hmaps hy) L
    (by rw [hL]; exact hfd.hasFDerivAt)
  have hyTarget : y ∈ e.target := by
    rw [← hright y hy, ← he]
    exact e.map_source hre
  have hnearSource : ∀ᶠ q in 𝓝 y, r q ∈ e.source :=
    hrd.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hre)
  refine ⟨e, hre, hes, he, hei, hyTarget, ?_⟩
  filter_upwards [hO.mem_nhds hy, hnearSource] with q hq hqs
  have h := e.left_inv hqs
  rw [he, hright q hq] at h
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The scalar graph equation is invariant under the actual smooth source
section of an original harmonic conformal map. The section is a right inverse
of its projected original map; the local inverse and its rank are derived.
Neither the section nor the resulting parametrized sheet is assumed conformal.
The equation holds only on the open domain mapped into the original harmonic
source, and the supplied height remains the literal same function. -/
theorem chartLeadingPlaneProjection_graph_equation_of_source_section
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    (htension : ∀ z ∈ s, diskMapTension g U z = 0)
    {a : ℂ} {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (N : E)
    (hunit : chartGramBilin g p (U a) N N = 1)
    (hprojN : chartLeadingPlaneProjection g p (U a) b N = 0)
    (hsplit : ∀ v : E,
      v = (chartModelBasis E).equivFunL.symm
          (fun i => (2 : ℝ) *
            (chartLeadingPlaneProjection g p (U a) b v * b i).re) +
        (chartGramBilin g p (U a) N v) • N)
    {O : Set ℂ} (hO : IsOpen O) (r : ℂ → ℂ) (hr : ContDiffOn ℝ ∞ r O)
    (hmaps : MapsTo r O s) (h : ℂ → ℝ)
    (hright : ∀ y ∈ O, chartLeadingPlaneProjection g p (U a) b
      (extChartAt 𝓘(ℝ, E) p (U (r y))) = y)
    (hheight : ∀ y ∈ O, h y = chartGramBilin g p (U a) N
      (extChartAt 𝓘(ℝ, E) p (U (r y)) - extChartAt 𝓘(ℝ, E) p (U a))) :
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) b
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    let Y : ℂ → E := fun y => X a + lift (y - proj (X a)) + h y • N
    let dirs : Fin 2 → ℂ := ![1, Complex.I]
    let W : ℂ → Fin 2 → E := fun y i => lift (dirs i) + fderiv ℝ h y (dirs i) • N
    let H : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun y i j =>
      chartGramBilin g p (U (r y)) (W y i) (W y j)
    let A : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
      Analysis.planarConductivity (H y 0 0) (H y 1 1) (H y 0 1)
    let theta : ℂ → E →L[ℝ] ℝ := fun y => Q N - (fderiv ℝ h y).comp proj
    ContDiffOn ℝ ∞ h O ∧ ∀ y ∈ O,
      X (r y) = Y y ∧ (H y).PosDef ∧ (A y).PosDef ∧
      A y = Real.sqrt (H y).det • (H y)⁻¹ ∧
      (∑ i : Fin 2, ∑ j : Fin 2,
        A y i j * (fderiv ℝ (fderiv ℝ h) y (dirs i) (dirs j) +
          theta y (chartChristoffelContraction g p (W y i) (W y j) (Y y)))) = 0 := by
  intro Q proj X lift Y dirs W H A theta
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart z hz)).comp z
      (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  let f : ℂ → ℂ := fun z => proj (X z)
  have hf : ContDiffOn ℝ ∞ f s := proj.contDiff.comp_contDiffOn hX
  have hh : ContDiffOn ℝ ∞ h O :=
    ((Q N).contDiff.comp_contDiffOn ((hX.comp hr hmaps).sub contDiffOn_const)).congr
      (fun y hy => hheight y hy)
  refine ⟨hh, ?_⟩
  intro y hy
  obtain ⟨e, _, hes, he, hei, hye, hnear⟩ :=
    exists_inverse_germ_of_smooth_rightInverse hs hO hf hr hmaps hright hy
  let h₀ : ℂ → ℝ := fun q => Q N (X (e.symm q) - X a)
  have hheightNear : h₀ =ᶠ[𝓝 y] h := by
    filter_upwards [hO.mem_nhds hy, hnear] with q hq heq
    change Q N (X (e.symm q) - X a) = h q
    rw [heq]
    exact (hheight q hq).symm
  have hval : h₀ y = h y := hheightNear.eq_of_nhds
  have hD : fderiv ℝ h₀ y = fderiv ℝ h y := hheightNear.fderiv_eq
  have hD₂ : fderiv ℝ (fderiv ℝ h₀) y = fderiv ℝ (fderiv ℝ h) y :=
    hheightNear.fderiv.fderiv_eq
  obtain ⟨_, hgraph, _, _, hH, _, hP⟩ :=
    chartLeadingPlaneProjection_graph_equation g hs hU hconformal htension
      hchart N hunit hprojN hsplit e hes he hei
  have hGraphAt := hgraph y hye
  have hHAt := hH y hye
  have hPAt := hP y hye
  change Matrix.PosDef (fun i j : Fin 2 => chartGramBilin g p (U (e.symm y))
    (lift (dirs i) + fderiv ℝ h₀ y (dirs i) • N)
    (lift (dirs j) + fderiv ℝ h₀ y (dirs j) • N)) at hHAt
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := fun i j => chartGramBilin g p (U (e.symm y))
    (lift (dirs i) + fderiv ℝ h₀ y (dirs i) • N)
    (lift (dirs j) + fderiv ℝ h₀ y (dirs j) • N)
  let A₀ := Analysis.planarConductivity (H₀ 0 0) (H₀ 1 1) (H₀ 0 1)
  change A₀.PosDef ∧ A₀ = Real.sqrt H₀.det • H₀⁻¹ ∧
    (∑ i : Fin 2, ∑ j : Fin 2, A₀ i j *
      (fderiv ℝ (fderiv ℝ h₀) y (dirs i) (dirs j) +
        (Q N - (fderiv ℝ h₀ y).comp proj)
          (chartChristoffelContraction g p
            (lift (dirs i) + fderiv ℝ h₀ y (dirs i) • N)
            (lift (dirs j) + fderiv ℝ h₀ y (dirs j) • N)
            (X a + lift (y - proj (X a)) + h₀ y • N)))) = 0 at hPAt
  have hinv : e.symm y = r y := hnear.eq_of_nhds
  change X (e.symm y) = X a + lift (y - proj (X a)) + h₀ y • N at hGraphAt
  rw [hinv, hval] at hGraphAt
  refine ⟨hGraphAt, ?_, ?_⟩
  · simpa only [W, H, hD, hinv] using hHAt
  · simpa only [A₀, H₀, A, H, W, theta, Y, hval, hD, hD₂, hinv] using hPAt

end DifferentialGeometry.Geometry
