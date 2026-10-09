import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.CoordinateRegularity
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.Segments

/-!
# LFR11, tier T1 (T1.b): coordinate lines and surjectivity of `dt`

Blueprint LFR11 (A:25566–25672), second paragraph of the proof: the lift under `e⁻¹` of a
coordinate line through `e x` is a unit-speed Riemannian geodesic, and along it
`dt(c') = u`. Hence `dt_x` is surjective at every point (the regularity input of the level set
`Z = t⁻¹(0)` in tier T2).

* `exists_unit_line_expMap`: for `‖u‖ = 1` and `L ≥ 0` there is a `g_x`-unit `w` with
  `exp_x(s w) = e⁻¹((e x).fst + s u, (e x).snd)` for `s ∈ [0, L]` (CM2.a);
* `mfderiv_splitting_fst_of_line`: any such `w` (with `L > 0`) satisfies `dt_x(w) = u`;
* `mfderiv_splitting_fst_surjective`: `dt_x` is onto `F`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞} {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MetricSpace Y]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] in
/-- The lifted coordinate line `s ↦ e⁻¹((e x).fst + s u, (e x).snd)` passes through `x` at `0`. -/
theorem splitting_line_zero (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) (u : F) :
    e.symm (toLp 2 ((e x).fst + (0 : ℝ) • u, (e x).snd)) = x := by
  have h : toLp 2 ((e x).fst, (e x).snd) = e x := by
    apply (WithLp.equiv 2 _).injective
    rfl
  rw [zero_smul, add_zero, h, e.symm_apply_apply]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] in
/-- A lifted coordinate line in a unit direction is a unit-speed line. -/
theorem dist_splitting_line (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) {u : F} (hu : ‖u‖ = 1)
    (s s' : ℝ) :
    dist (e.symm (toLp 2 ((e x).fst + s • u, (e x).snd)))
      (e.symm (toLp 2 ((e x).fst + s' • u, (e x).snd))) = |s - s'| := by
  rw [e.symm.dist_eq]
  have h := (WithLp.isometry_prodMk_right (E := F) (e x).snd).dist_eq
    ((e x).fst + s • u) ((e x).fst + s' • u)
  rw [h, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hu, mul_one,
    Real.norm_eq_abs]

omit [CompleteSpace M] in
/-- **LFR11 T1.b, lines.** A lifted coordinate line in a unit direction is `s ↦ exp_x(s w)` for a
`g_x`-unit vector `w`, on any interval `[0, L]`. (`NeZero (finrank E)` is CM2.a's standing
assumption; it holds for every positive-dimensional model.) -/
theorem exists_unit_line_expMap [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) {u : F} (hu : ‖u‖ = 1) (L : ℝ) :
    ∃ w : E, g.inner x w w = 1 ∧ ∀ s ∈ Icc 0 L,
      g.expMap (⟨x, s • w⟩ : TangentBundle I M) =
        e.symm (toLp 2 ((e x).fst + s • u, (e x).snd)) := by
  set c : ℝ → M := fun s => e.symm (toLp 2 ((e x).fst + s • u, (e x).snd)) with hc
  have hseg : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, dist (c s) (c t) = |s - t| :=
    fun s _ t _ => dist_splitting_line e x hu s t
  obtain ⟨w, hw, hexp⟩ := g.exists_expMap_eq_of_segment hr hnorm hseg
  have hc0 : c 0 = x := splitting_line_zero e x u
  refine ⟨w, ?_, fun s hs => ?_⟩
  · rw [← hc0]; exact hw
  · have h := (hexp s hs).2
    rw [hc0] at h
    exact h.symm

/-- **LFR11 T1.b, derivative along a line.** If `exp_x(s w)` follows the lifted coordinate line
in direction `u` on `[0, L]`, `L > 0`, then `dt_x(w) = u` (`mvfderiv` is the `F`-valued
differential). -/
theorem mvfderiv_splitting_fst_of_line [FiniteDimensional ℝ F]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) {u : F} {L : ℝ} (hL : 0 < L) {w : E}
    (hw : ∀ s ∈ Icc 0 L, g.expMap (⟨x, s • w⟩ : TangentBundle I M) =
      e.symm (toLp 2 ((e x).fst + s • u, (e x).snd))) :
    mvfderiv I (fun x => (e x).fst) x w = u := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : ∀ s : ℝ, ((⟨x, w⟩ : TangentBundle I M), s) ∈ g.geodesicFlowDomain := by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]
    exact fun _ => mem_univ _
  have hγ := g.hasMFDerivAt_geodesicFlow_proj hr1 (hD 0)
  rw [g.geodesicFlow_zero hr1] at hγ
  have h0 : (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) 0).proj = x := by
    rw [g.geodesicFlow_zero hr1]
  have htd : MDifferentiableAt I 𝓘(ℝ, F) (fun x => (e x).fst)
      (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) 0).proj := by
    rw [h0]
    exact ((contMDiff_splitting_fst g hr hnorm e) x).mdifferentiableAt (by simp)
  have hder0 := TauCeti.Manifold.hasDerivAt_comp_curve htd hγ
  have hder : HasDerivAt ((fun x => (e x).fst) ∘
      (fun s => (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s).proj))
      (mvfderiv I (fun x => (e x).fst) x w) 0 := by
    rw [h0] at hder0
    exact hder0
  have heq : ∀ s ∈ Icc 0 L, ((fun x => (e x).fst) ∘
      (fun s => (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s).proj)) s =
        (e x).fst + s • u := by
    intro s hs
    have h1 := (g.expMap_smul_eq_proj_geodesicFlow hr1 x w s (hD s)).symm
    simp only [Function.comp_apply]
    rw [h1]
    erw [hw s hs, e.apply_symm_apply]
    rfl
  have hwithin : HasDerivWithinAt ((fun x => (e x).fst) ∘
      (fun s => (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s).proj)) u (Ici 0) 0 := by
    have h1 : HasDerivWithinAt (fun s : ℝ => (e x).fst + s • u) u (Ici 0) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (e x).fst).hasDerivWithinAt
        (s := Ici 0)
      simpa using this
    refine h1.congr_of_eventuallyEq ?_ (heq 0 ⟨le_rfl, hL.le⟩)
    filter_upwards [Ico_mem_nhdsGE hL] with s hs using heq s ⟨hs.1, hs.2.le⟩
  exact (uniqueDiffWithinAt_Ici 0).eq_deriv _ hder.hasDerivWithinAt hwithin

/-- **LFR11 T1.b.** The differential of the splitting coordinate is onto `F` at every point. -/
theorem mvfderiv_splitting_fst_surjective [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) :
    Function.Surjective (mvfderiv I (fun x => (e x).fst) x) := by
  intro u
  rcases eq_or_ne u 0 with rfl | hu0
  · exact ⟨0, map_zero _⟩
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hû1 : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  obtain ⟨w, -, hw⟩ := exists_unit_line_expMap g hr hnorm e x hû1 1
  set w' : TangentSpace I x := w with hw'
  have h : mvfderiv I (fun x => (e x).fst) x w' = ‖u‖⁻¹ • u :=
    mvfderiv_splitting_fst_of_line g hr hnorm e x one_pos hw
  refine ⟨‖u‖ • w', ?_⟩
  rw [map_smul, h, smul_smul, mul_inv_cancel₀ hn, one_smul]

end DifferentialGeometry.Geometry.ExactSplitting
