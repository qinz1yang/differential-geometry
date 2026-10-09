import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphAreaRegularity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Puncture

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open scoped Topology ContDiff Manifold Matrix

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The finite nonempty fibers supplied by the retained tuple cover the full
closed half-radius target, including the original center. -/
private theorem closedHalfTarget_subset_range
    (F : ℂ → ℂ) (a : ℂ) (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ) (m : ℕ)
    (hcard : ∀ y ∈ ball (F a) δ \ {F a},
      ((fun z : closedBall a r => F z.val) ⁻¹' {y}).encard = ((m + 1 : ℕ) : ℕ∞)) :
    closedBall (F a) (δ / 2) ⊆ range (fun z : closedBall a r => F z.val) := by
  intro y hy
  by_cases heq : y = F a
  · exact ⟨⟨a, mem_closedBall_self hr⟩, heq.symm⟩
  · have hyS : y ∈ ball (F a) δ \ {F a} :=
      ⟨(closedBall_subset_ball (half_lt_self hδ)) hy, heq⟩
    have hpos : 0 < ((fun z : closedBall a r => F z.val) ⁻¹' {y}).encard := by
      rw [hcard y hyS]
      exact_mod_cast Nat.succ_pos m
    exact Set.encard_pos.mp hpos

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Chart reconstruction for the retained closed factor uses its exact source
fibers. It holds at the center as well as on the punctured graph. -/
private theorem closedFactor_chart_graph
    (U : ℂ → M) (p : M) (a : ℂ) (r R : ℝ)
    (proj : E →L[ℝ] ℂ) (L : ℂ →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) (N : E)
    (hsplit : ∀ v : E, v = L (proj v) + (Q N v) • N)
    (hchart : ∀ z ∈ closedBall a r, U z ∈ (chartAt E p).source)
    (V : C(closedBall (proj (extChartAt 𝓘(ℝ, E) p (U a))) R, M)) (H : ℂ → ℝ)
    (hcover : closedBall (proj (extChartAt 𝓘(ℝ, E) p (U a))) R ⊆
      range (fun z : closedBall a r => proj (extChartAt 𝓘(ℝ, E) p (U z.val))))
    (hV : ∀ (z : closedBall a r)
      (hz : proj (extChartAt 𝓘(ℝ, E) p (U z.val)) ∈
        closedBall (proj (extChartAt 𝓘(ℝ, E) p (U a))) R),
      V ⟨proj (extChartAt 𝓘(ℝ, E) p (U z.val)), hz⟩ = U z.val)
    (hH : ∀ y, H y.val = Q N
      (extChartAt 𝓘(ℝ, E) p (V y) - extChartAt 𝓘(ℝ, E) p (U a))) :
    let X := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let c := proj (X a)
    let Y := fun y => X a + L (y - c) + H y • N
    ∀ y : closedBall c R,
      V y ∈ (chartAt E p).source ∧
      extChartAt 𝓘(ℝ, E) p (V y) = Y y.val ∧
      Y y.val ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
      (extChartAt 𝓘(ℝ, E) p).symm (Y y.val) = V y := by
  dsimp only
  intro y
  obtain ⟨z, hz⟩ := hcover y.property
  change proj (extChartAt 𝓘(ℝ, E) p (U z.val)) = y.val at hz
  have hzV : V y = U z.val := by
    have hzy : proj (extChartAt 𝓘(ℝ, E) p (U z.val)) ∈
        closedBall (proj (extChartAt 𝓘(ℝ, E) p (U a))) R := by
      rw [hz]
      exact y.property
    simpa only [hz] using hV z hzy
  have hsrc : V y ∈ (chartAt E p).source := by
    rw [hzV]
    exact hchart z.val z.property
  have hproj : proj (extChartAt 𝓘(ℝ, E) p (V y)) = y.val := by
    rw [hzV]
    exact hz
  have hgraph : extChartAt 𝓘(ℝ, E) p (V y) =
      extChartAt 𝓘(ℝ, E) p (U a) +
        L (y.val - proj (extChartAt 𝓘(ℝ, E) p (U a))) + H y.val • N := by
    have h := hsplit (extChartAt 𝓘(ℝ, E) p (V y) - extChartAt 𝓘(ℝ, E) p (U a))
    rw [map_sub, hproj, ← hH y] at h
    rw [sub_eq_iff_eq_add] at h
    simpa only [add_assoc, add_comm, add_left_comm] using h
  have hsrc' : V y ∈ (extChartAt 𝓘(ℝ, E) p).source := by
    simpa only [extChartAt_source] using hsrc
  refine ⟨hsrc, hgraph, ?_, ?_⟩
  · rw [← hgraph]
    exact (extChartAt 𝓘(ℝ, E) p).map_source hsrc'
  · rw [← hgraph]
    exact (extChartAt 𝓘(ℝ, E) p).left_inv hsrc'

/-- The retained closed factor and retained height satisfy the original metric's
weak graph-area equation. Every inverse is one of the supplied germs of the same
leading projection; no new disk, factor, or height is selected. -/
theorem IsMorreyDisk.closed_factor_graph_weak_stationarity
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {a : ℂ} {m : ℕ} {B : ℂ → Fin (Module.finrank ℝ E) → ℂ} :
    let U := diskExtension u
    let p := U a
    let Q := chartGramBilin g p p
    let proj := chartLeadingPlaneProjection g p p (B a)
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B a i).re)
    ∀ r δ : ℝ, 0 < r → 0 < δ →
      closedBall a r ⊆ ball (0 : ℂ) 1 →
      (∀ z ∈ closedBall a r, U z ∈ (chartAt E p).source) →
      (∀ y ∈ ball (F a) δ \ {F a},
        ((fun z : closedBall a r => F z.val) ⁻¹' {y}).encard = ((m + 1 : ℕ) : ℕ∞)) →
      ∀ N : E, Q N N = 1 → proj N = 0 →
      (∀ v : E, v = lift (proj v) + Q N v • N) →
      ∀ V : C(closedBall (F a) (δ / 2), M),
      (∀ (z : closedBall a r) (hz : F z.val ∈ closedBall (F a) (δ / 2)),
        V ⟨F z.val, hz⟩ = U z.val) →
      ∀ H : ℂ → ℝ,
      (∀ y : closedBall (F a) (δ / 2),
        H y.val = Q N (extChartAt 𝓘(ℝ, E) p (V y) - X a)) →
      ContDiffOn ℝ ∞ H (ball (F a) (δ / 2) \ {F a}) →
      ContDiffOn ℝ 1 H (ball (F a) (δ / 2)) →
      (∀ y ∈ ball (F a) (δ / 2) \ {F a},
        ∃ e : OpenPartialHomeomorph ℂ ℂ,
          y ∈ e.target ∧ e.source ⊆ ball a r \ {a} ∧
          (e : ℂ → ℂ) = F ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
          H =ᶠ[𝓝 y] (fun y' => Q N (X (e.symm y') - X a))) →
      ∃ L : ℂ →L[ℝ] E,
        (∀ w, L w = lift w) ∧ (∀ w, proj (L w) = w) ∧
        range V = range (fun z : (fun z : closedBall a r => F z.val) ⁻¹'
          closedBall (F a) (δ / 2) => U z.val.val) ∧
        (∀ y : closedBall (F a) (δ / 2),
          V y ∈ (chartAt E p).source ∧
          extChartAt 𝓘(ℝ, E) p (V y) = X a + L (y.val - F a) + H y.val • N ∧
          X a + L (y.val - F a) + H y.val • N ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
          (extChartAt 𝓘(ℝ, E) p).symm
            (X a + L (y.val - F a) + H y.val • N) = V y) ∧
        let flux : ℂ → ℝ × ℝ := fun y =>
          chartGraphAreaFlux g p (X a) (F a) L N y (H y)
            (fderiv ℝ H y 1, fderiv ℝ H y Complex.I)
        let P : ℂ → EuclideanSpace ℝ (Fin 2) := fun y =>
          WithLp.toLp 2 ![(flux y).1, (flux y).2]
        let source : ℂ → ℝ := fun y =>
          chartGraphAreaSource g p (X a) (F a) L N y (H y)
            (fderiv ℝ H y 1, fderiv ℝ H y Complex.I)
        ContinuousOn source (ball (F a) (δ / 2)) ∧
        ContinuousOn P (ball (F a) (δ / 2)) ∧
        ContDiffOn ℝ 1 P (ball (F a) (δ / 2) \ {F a}) ∧
        DeGiorgi.HasWeakDiv (source ∘ Complex.orthonormalBasisOneI.repr.symm)
          (P ∘ Complex.orthonormalBasisOneI.repr.symm)
          (Complex.orthonormalBasisOneI.repr '' ball (F a) (δ / 2)) := by
  classical
  dsimp only
  intro r δ hr hδ hsub hchart hcard N hunit hprojN hsplit V hV H hH hHoff hHone hgerms
  let U := diskExtension u
  let p := U a
  let Q := chartGramBilin g p p
  let proj := chartLeadingPlaneProjection g p p (B a)
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let F : ℂ → ℂ := fun z => proj (X z)
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * B a i).re)
  let Ω := ball (F a) (δ / 2)
  let s := ball a r \ {a}
  have hs : IsOpen s := isOpen_ball.sdiff isClosed_singleton
  have hsdisk : s ⊆ ball (0 : ℂ) 1 :=
    sdiff_subset.trans (ball_subset_closedBall.trans hsub)
  have hsChart : ∀ z ∈ s, U z ∈ (chartAt E p).source :=
    fun z hz => hchart z (ball_subset_closedBall hz.1)
  let y₀ : ℂ := F a + (δ / 4 : ℝ)
  have hy₀dist : dist y₀ (F a) = δ / 4 := by
    simp only [y₀, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (show 0 < δ / 4 by positivity)]
  have hy₀ : y₀ ∈ Ω \ {F a} := by
    constructor
    · change dist y₀ (F a) < δ / 2
      rw [hy₀dist]
      linarith
    · intro h
      have heq : y₀ = F a := h
      rw [heq, dist_self] at hy₀dist
      linarith
  obtain ⟨e₀, he₀target, he₀source, he₀, he₀smooth, _⟩ := hgerms y₀ hy₀
  obtain ⟨L, hL, hprojL, _, _⟩ :=
    chartLeadingPlaneProjection_graph_area_equation g hs hsdisk
      hu.smoothInterior hu.conformal hu.harmonic hsChart N hunit hprojN hsplit
      e₀ he₀source he₀ he₀smooth y₀ he₀target
  have hsplitL (v : E) : v = L (proj v) + Q N v • N := by
    rw [hL]
    exact hsplit v
  have hcover : closedBall (F a) (δ / 2) ⊆
      range (fun z : closedBall a r => F z.val) :=
    closedHalfTarget_subset_range F a r δ hr.le hδ m hcard
  have hgraph := closedFactor_chart_graph
    U p a r (δ / 2) proj L Q N hsplitL hchart V H hcover hV hH
  have hrange : range V = range
      (fun z : (fun z : closedBall a r => F z.val) ⁻¹' closedBall (F a) (δ / 2) =>
        U z.val.val) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := hcover y.property
      change F z.val = y.val at hz
      have hzK : F z.val ∈ closedBall (F a) (δ / 2) := by rw [hz]; exact y.property
      refine ⟨⟨z, hzK⟩, ?_⟩
      change U z.val = V y
      calc
        U z.val = V ⟨F z.val, hzK⟩ := (hV z hzK).symm
        _ = V y := congrArg V (Subtype.ext hz)
    · rintro ⟨z, rfl⟩
      exact ⟨⟨F z.val.val, z.property⟩, hV z.val z.property⟩
  have hYchart (y : ℂ) (hy : y ∈ Ω) :
      X a + L (y - F a) + H y • N ∈ (extChartAt 𝓘(ℝ, E) p).target :=
    (hgraph ⟨y, ball_subset_closedBall hy⟩).2.2.1
  let flux : ℂ → ℝ × ℝ := fun y =>
    chartGraphAreaFlux g p (X a) (F a) L N y (H y)
      (fderiv ℝ H y 1, fderiv ℝ H y Complex.I)
  let P : ℂ → EuclideanSpace ℝ (Fin 2) := fun y =>
    WithLp.toLp 2 ![(flux y).1, (flux y).2]
  let source : ℂ → ℝ := fun y =>
    chartGraphAreaSource g p (X a) (F a) L N y (H y)
      (fderiv ℝ H y 1, fderiv ℝ H y Complex.I)
  have hzero := chartGraphArea_firstJet_contDiffOn
    g p (X a) (F a) proj L N hprojL hprojN (n := 0) (by simp)
    (hHone.of_le (by simp)) (hHone.fderiv_of_isOpen isOpen_ball (by norm_num)) hYchart
  have hsource : ContinuousOn source Ω := hzero.2.continuousOn
  have hPzero : ContDiffOn ℝ 0 P Ω := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    fin_cases i
    · exact hzero.1.fst
    · exact hzero.1.snd
  have hopenOff : IsOpen (Ω \ {F a}) := isOpen_ball.sdiff isClosed_singleton
  have hDhOff : ContDiffOn ℝ ∞ (fderiv ℝ H) (Ω \ {F a}) :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hopenOff).mp hHoff |>.2
  have hoff := chartGraphArea_firstJet_contDiffOn
    g p (X a) (F a) proj L N hprojL hprojN (n := ∞) le_rfl
    hHoff hDhOff (fun y hy => hYchart y hy.1)
  have hPoff : ContDiffOn ℝ 1 P (Ω \ {F a}) := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    fin_cases i
    · exact hoff.1.fst.of_le (by simp)
    · exact hoff.1.snd.of_le (by simp)
  have hdiv (y : ℂ) (hy : y ∈ Ω) (hne : y ≠ F a) :
      fderiv ℝ (fun w => P w 0) y 1 +
        fderiv ℝ (fun w => P w 1) y Complex.I = source y := by
    obtain ⟨e, heTarget, heSource, he, heSmooth, hHnear⟩ := hgerms y ⟨hy, hne⟩
    obtain ⟨L', hL', _, _, heDiv⟩ :=
      chartLeadingPlaneProjection_graph_area_equation g hs hsdisk
        hu.smoothInterior hu.conformal hu.harmonic hsChart N hunit hprojN hsplit
        e heSource he heSmooth y heTarget
    have hLeq : L' = L := ContinuousLinearMap.ext (fun w => (hL' w).trans (hL w).symm)
    subst L'
    let h : ℂ → ℝ := fun y' => Q N (X (e.symm y') - X a)
    have hjet : fderiv ℝ H =ᶠ[𝓝 y] fderiv ℝ h := hHnear.fderiv
    have hfluxNear : flux =ᶠ[𝓝 y] (fun q =>
        chartGraphAreaFlux g p (X a) (F a) L N q (h q)
          (fderiv ℝ h q 1, fderiv ℝ h q Complex.I)) := by
      filter_upwards [hHnear, hjet] with q hq hDq
      simp only [flux, hq, hDq]
      rfl
    have hfirst : (fun q => (flux q).1) =ᶠ[𝓝 y] (fun q =>
        (chartGraphAreaFlux g p (X a) (F a) L N q (h q)
          (fderiv ℝ h q 1, fderiv ℝ h q Complex.I)).1) :=
      hfluxNear.mono (fun q hq => congrArg Prod.fst hq)
    have hsecond : (fun q => (flux q).2) =ᶠ[𝓝 y] (fun q =>
        (chartGraphAreaFlux g p (X a) (F a) L N q (h q)
          (fderiv ℝ h q 1, fderiv ℝ h q Complex.I)).2) :=
      hfluxNear.mono (fun q hq => congrArg Prod.snd hq)
    change fderiv ℝ (fun q => (flux q).1) y 1 +
      fderiv ℝ (fun q => (flux q).2) y Complex.I = source y
    rw [hfirst.fderiv_eq, hsecond.fderiv_eq]
    have heq := heDiv y heTarget
    dsimp only [Analysis.complexDivergence] at heq
    exact heq.trans (by
      simp only [source, hHnear.eq_of_nhds, hjet.eq_of_nhds, h]
      rfl)
  have hweak := DeGiorgi.hasWeakDiv_of_complex_divergence_off_point
    (a := F a) isOpen_ball hsource hPzero.continuousOn hPoff hdiv
  exact ⟨L, hL, hprojL, hrange, hgraph, hsource, hPzero.continuousOn, hPoff, hweak⟩

end DifferentialGeometry.Geometry
