import DifferentialGeometry.Geometry.Boundary.ModelCollarCoordinates
import DifferentialGeometry.Geometry.Boundary.ChartTangent
import DifferentialGeometry.Geometry.Boundary.Normal.Outward
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Boundary

private theorem exists_open_initial_strip
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X × ℝ → Y} {B : Set X} {x : X} {τ : ℝ} {A : Set Y}
    (hB : IsOpen B) (hx : x ∈ B) (hτ : 0 < τ)
    (hf : ContinuousWithinAt f (B ×ˢ Icc 0 τ) (x, 0))
    (hA : IsOpen A) (hfx : f (x, 0) ∈ A) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ B ∧
      ∃ ρ > 0, ρ < τ ∧ MapsTo f (W ×ˢ Icc 0 ρ) A := by
  have hn := hf.preimage_mem_nhdsWithin (hA.mem_nhds hfx)
  obtain ⟨C, hC, hCA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hn
  rw [nhds_prod_eq] at hC
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_prod_iff.mp hC
  obtain ⟨W, hWP, hW, hxW⟩ := mem_nhds_iff.mp (inter_mem hP (hB.mem_nhds hx))
  obtain ⟨δ, hδ, hδQ⟩ := Metric.mem_nhds_iff.mp hQ
  let ρ := min (τ / 2) (δ / 2)
  have hρ : 0 < ρ := lt_min (half_pos hτ) (half_pos hδ)
  have hρτ : ρ < τ := (min_le_left _ _).trans_lt (half_lt_self hτ)
  refine ⟨W, hW, hxW, (fun y hy ↦ (hWP hy).2), ρ, hρ, hρτ, ?_⟩
  intro z hz
  apply hCA
  refine ⟨hPQ ⟨(hWP hz.1).1, hδQ ?_⟩, (hWP hz.1).2, hz.2.1, hz.2.2.trans hρτ.le⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hz.2.1]
  exact (hz.2.2.trans (min_le_right _ _)).trans_lt (half_lt_self hδ)

open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_collar_coordinates_of_one_sided
    {φ : BoundaryManifold I M × ℝ → M} {B : Set (BoundaryManifold I M)}
    {x : BoundaryManifold I M} {τ : ℝ} {v : TangentSpace I x.1}
    (hB : IsOpen B) (hx : x ∈ B) (hτ : 0 < τ)
    (hφ : ContMDiffOn (hI.boundaryI.prod 𝓘(ℝ)) I ∞ φ (B ×ˢ Icc 0 τ))
    (hzero : ∀ y ∈ B, φ (y, 0) = y.1)
    (hderiv : HasMFDerivWithinAt 𝓘(ℝ) I (fun t ↦ φ (x, t)) (Icc 0 τ) 0
      (ContinuousLinearMap.toSpanSingleton ℝ v))
    (hinward : ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
      v = boundaryInclusionMfderiv x w + c • inwardCoord x) :
    ∃ d : OpenPartialHomeomorph (BoundaryManifold I M × EuclideanHalfSpace 1) M,
      (x, 0) ∈ d.source ∧
      d.source ⊆ B ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < τ} ∧
      ContMDiffOn (hI.boundaryI.prod (𝓡∂ 1)) I ∞ d d.source ∧
      ContMDiffOn I (hI.boundaryI.prod (𝓡∂ 1)) ∞ d.symm d.target ∧
      ∀ z ∈ d.source, d z = φ (z.1, z.2.1 0) := by
  let c := chartAt H x.1
  have hφ0 : φ (x, 0) = x.1 := hzero x hx
  obtain ⟨W, hW, hxW, hWB, ρ, hρ, hρτ, hφW⟩ := exists_open_initial_strip hB hx hτ
    (hφ.continuousOn (x, 0) ⟨hx, le_rfl, hτ.le⟩) c.open_source
    (by rw [hφ0]; exact mem_chart_source H x.1)
  let k : OpenPartialHomeomorph (BoundaryManifold I M) hI.boundaryE :=
    { toPartialEquiv := extChartAt hI.boundaryI x
      open_source := isOpen_extChartAt_source x
      open_target := isOpen_extChartAt_target x
      continuousOn_toFun := continuousOn_extChartAt x
      continuousOn_invFun := continuousOn_extChartAt_symm x }
  let p := k x
  have hxk : x ∈ k.source := mem_extChartAt_source x
  let V := k.target ∩ k.symm ⁻¹' W
  have hV : IsOpen V := k.isOpen_inter_preimage_symm hW
  have hpV : p ∈ V := ⟨k.map_source hxk, by change k.symm (k x) ∈ W; rwa [k.left_inv hxk]⟩
  have htime : Icc (0 : ℝ) ρ ⊆ Icc 0 τ := fun t ht ↦ ⟨ht.1, ht.2.trans hρτ.le⟩
  let f : hI.boundaryE × ℝ → E := fun z ↦ extChartAt I x.1 (φ (k.symm z.1, z.2))
  have hk : ContMDiffOn hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞ k k.source :=
    (contMDiffOn_extChartAt (I := hI.boundaryI) (x := x)).mono
      (fun y hy ↦ by simpa only [k, extChartAt_source] using hy)
  have hki : ContMDiffOn 𝓘(ℝ, hI.boundaryE) hI.boundaryI ∞ k.symm k.target :=
    contMDiffOn_extChartAt_symm x
  have hf : ContDiffOn ℝ ∞ f (V ×ˢ Icc 0 ρ) := by
    have hparam : ContMDiffOn 𝓘(ℝ, hI.boundaryE × ℝ) (hI.boundaryI.prod 𝓘(ℝ)) ∞
        (fun z ↦ (k.symm z.1, z.2)) (V ×ˢ Icc 0 ρ) :=
      (hki.comp contDiff_fst.contMDiff.contMDiffOn (fun z hz ↦ hz.1.1)).prodMk
        contDiff_snd.contMDiff.contMDiffOn
    have hfamily := hφ.comp hparam (fun z hz ↦ ⟨hWB hz.1.2, htime hz.2⟩)
    exact ((contMDiffOn_extChartAt (I := I) (x := x.1)).comp hfamily
      (fun z hz ↦ hφW ⟨hz.1.2, hz.2⟩)).contDiffOn
  have hfzero : ∀ q ∈ V, f (q, 0) = modelBoundaryParam I q := by
    intro q hq
    have hqW : k.symm q ∈ W := hq.2
    have hqC : (k.symm q).1 ∈ c.source := by
      have hh := hφW (show (k.symm q, (0 : ℝ)) ∈ W ×ˢ Icc 0 ρ from ⟨hqW, le_rfl, hρ.le⟩)
      rwa [hzero _ (hWB hqW)] at hh
    have hh := modelBoundaryParam_extChartAt_boundary x (k.symm q) hqC
    change modelBoundaryParam I (k (k.symm q)) = _ at hh
    rw [k.right_inv hq.1] at hh
    dsimp only [f]
    rw [hzero _ (hWB hqW)]
    exact hh.symm
  let vE : E := tangentSpaceModelContinuousLinearEquiv (I := I) x.1 v
  have hfd : HasDerivWithinAt (fun t ↦ f (p, t)) vE (Icc 0 ρ) 0 := by
    have hc : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x.1) (φ (x, 0)) := by
      rw [hφ0]
      exact mdifferentiableAt_extChartAt (mem_chart_source H x.1)
    have hh := hc.hasMFDerivAt.comp_hasMFDerivWithinAt 0 (hderiv.mono htime)
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hh
    have hh' : HasDerivWithinAt (fun t ↦ extChartAt I x.1 (φ (x, t))) vE (Icc 0 ρ) 0 := by
      apply hh.congr_fderiv
      apply ContinuousLinearMap.ext
      intro a
      change ℝ at a
      change mfderiv I 𝓘(ℝ, E) (extChartAt I x.1) (φ (x, 0)) (a • v) = a • vE
      rw [hφ0, mfderiv_extChartAt_self]
      rfl
    simpa only [f, p, k.left_inv hxk] using hh'
  have hvin : ∃ (w : hI.boundaryE) (r : ℝ), 0 < r ∧
      vE = fderiv ℝ (modelBoundaryParam I) p w + r • hI.inwardCoordE := by
    obtain ⟨w, r, hr, hvw⟩ := hinward
    refine ⟨tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x w, r, hr, ?_⟩
    dsimp only [vE]
    rw [hvw, map_add, map_smul, boundaryInclusionMfderiv_model]
    have hh := inwardCoord_eq x
    change inwardCoord x = hI.inwardCoordE at hh
    change _ + r • inwardCoord x = _
    rw [hh]
    rfl
  obtain ⟨d₀, hpd₀, hd₀V, hd₀, hd₀i, hd₀zero, hd₀eq⟩ :=
    exists_modelBoundary_collar_coordinates I hV hpV hρ hf hfzero hfd hvin
  let C := k.prod (OpenPartialHomeomorph.refl (EuclideanHalfSpace 1))
  have hC : ContMDiffOn (hI.boundaryI.prod (𝓡∂ 1))
      ((𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)) ∞ C C.source :=
    (hk.comp contMDiffOn_fst (fun z hz ↦ hz.1)).prodMk contMDiffOn_snd
  have hCi : ContMDiffOn ((𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1))
      (hI.boundaryI.prod (𝓡∂ 1)) ∞ C.symm C.target :=
    (hki.comp contMDiffOn_fst (fun z hz ↦ hz.1)).prodMk contMDiffOn_snd
  let C' : PartialDiffeomorph (hI.boundaryI.prod (𝓡∂ 1))
      ((𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)) (BoundaryManifold I M × EuclideanHalfSpace 1)
      (hI.boundaryE × EuclideanHalfSpace 1) ∞ :=
    { toPartialEquiv := C.toPartialEquiv
      open_source := C.open_source
      open_target := C.open_target
      contMDiffOn_toFun := hC
      contMDiffOn_invFun := hCi }
  let D' : PartialDiffeomorph ((𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)) I
      (hI.boundaryE × EuclideanHalfSpace 1) H ∞ :=
    { toPartialEquiv := d₀.toPartialEquiv
      open_source := d₀.open_source
      open_target := d₀.open_target
      contMDiffOn_toFun := hd₀
      contMDiffOn_invFun := hd₀i }
  let A' : PartialDiffeomorph I I M H ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let d := (C'.trans D').trans A'.symm
  have hpH : hI.inclH (hI.boundaryI.symm p) = c x.1 := by
    apply I.injective
    exact modelBoundaryParam_extChartAt_boundary x x (mem_chart_source H x.1)
  have hxd : (x, (0 : EuclideanHalfSpace 1)) ∈ d.source := by
    refine ⟨⟨⟨hxk, mem_univ _⟩, hpd₀⟩, ?_⟩
    change d₀ (p, 0) ∈ c.target
    rw [hd₀zero, hpH]
    exact c.map_source (mem_chart_source H x.1)
  have hWtime : ∀ z ∈ d.source, z.1 ∈ W ∧ z.2.1 0 < ρ := by
    intro z hz
    have hh := hd₀V hz.1.2
    have hW' : k.symm (k z.1) ∈ W := hh.1.2
    rw [k.left_inv hz.1.1.1] at hW'
    exact ⟨hW', hh.2⟩
  refine ⟨d.toOpenPartialHomeomorph, hxd,
    (fun z hz ↦ ⟨hWB (hWtime z hz).1, (hWtime z hz).2.trans hρτ⟩),
    d.contMDiffOn, d.symm.contMDiffOn, ?_⟩
  intro z hz
  have hqC : φ (z.1, z.2.1 0) ∈ c.source :=
    hφW ⟨(hWtime z hz).1, z.2.2, (hWtime z hz).2.le⟩
  have hh := hd₀eq (k z.1, z.2) hz.1.2
  dsimp only [f] at hh
  rw [k.left_inv hz.1.1.1] at hh
  have heq : d₀ (k z.1, z.2) = c (φ (z.1, z.2.1 0)) := I.injective hh
  change c.symm (d₀ (k z.1, z.2)) = φ (z.1, z.2.1 0)
  rw [heq, c.left_inv hqC]

end Poincare.Geometry.Boundary
