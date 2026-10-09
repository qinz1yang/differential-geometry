import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.Tangency
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.NormalCoordinates
import DifferentialGeometry.Topology.Manifold.BoundaryTransitionFlow
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpace

/-!
# Local flows of boundary-tangent vector fields

Let `X` be a smooth vector field on a manifold `M` with boundary (model `𝓡∂ (n + 1)`) whose normal
coordinate vanishes at boundary points. Near every point `q₀` there is a jointly smooth local flow
`φ : (-ε, ε) × O → M` of `X` (`exists_boundaryTangent_localFlow`).

Route: in the chart at `q₀`, split as `ℝ × ℝⁿ` (`normalSplit`), the chart field is smooth on the closed
half-space near the chart point; a Borel extension (`SmoothExtension/HalfSpace.lean`) cut off by a bump
supported where it agrees with the chart field gives a compactly supported smooth field on `ℝ × ℝⁿ`
whose normal component vanishes on the whole hyperplane; its complete flow
(`Diffeomorph.compactSupportFlow`) preserves the half-space (`BoundaryTransitionFlow.lean:71`), and
for small times and nearby points it stays where the extension is the chart field, so its chart
pull-back is a local flow of `X` (`BoundaryCollar/ChartField.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.BoundaryTangentFlow

open DifferentialGeometry.Manifold.BoundaryCollar

/-- A smooth map `v : E → E` is a smooth section of the tangent bundle of `E`. -/
theorem contMDiff_tangentSection_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : E → E} (hv : ContDiff ℝ ∞ v) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x : E => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
  intro x
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  refine hv.contMDiff.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rw [trivializationAt_model_space_apply]

/-- **Half-space flow.** A compactly supported smooth field on `ℝ × G` whose normal component
vanishes on the hyperplane `{z.1 = 0}` has a complete, jointly smooth flow preserving the closed
half-space `{0 ≤ z.1}`. -/
theorem exists_halfSpace_tangent_flow {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] (g : ℝ × G → ℝ × G) (hg : ContDiff ℝ ∞ g)
    (hgK : HasCompactSupport g) (htan : ∀ z : ℝ × G, z.1 = 0 → (g z).1 = 0) :
    ∃ ψ : ℝ → ℝ × G → ℝ × G,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × G)) 𝓘(ℝ, ℝ × G) ∞
        (fun p : ℝ × (ℝ × G) => ψ p.1 p.2) ∧
      (∀ x, ψ 0 x = x) ∧
      (∀ x t, HasDerivAt (fun s => ψ s x) (g (ψ t x)) t) ∧
      ∀ t x, 0 ≤ x.1 → 0 ≤ (ψ t x).1 := by
  let V : (z : ℝ × G) → TangentSpace 𝓘(ℝ, ℝ × G) z := g
  have hV : ContMDiff 𝓘(ℝ, ℝ × G) (𝓘(ℝ, ℝ × G)).tangent ∞
      (fun z : ℝ × G => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, ℝ × G) (ℝ × G))) :=
    contMDiff_tangentSection_of_contDiff hg
  have hsupp : IsCompact (tsupport V) := hgK
  refine ⟨fun t x => Diffeomorph.compactSupportFlow V hV hsupp t x,
    Diffeomorph.contMDiff_compactSupportFlow V hV hsupp, ?_, ?_, ?_⟩
  · intro x
    change (Diffeomorph.compactSupportFlow V hV hsupp 0) x = x
    rw [Diffeomorph.compactSupportFlow_zero]
    rfl
  · intro x t
    have h := Diffeomorph.isMIntegralCurve_compactSupportFlow V hV hsupp x t
    exact hasDerivAt_iff_hasFDerivAt.mpr (hasMFDerivAt_iff_hasFDerivAt.mp h)
  · intro t x hx
    exact ((Diffeomorph.compactSupportFlow_halfSpace_mem_iff V hV hsupp htan t x).2.1).mpr hx

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]

/-- **Local flow.** A smooth vector field whose normal coordinate vanishes at boundary points has,
near every point, a jointly smooth local flow on `(-ε, ε) × O`. -/
theorem exists_boundaryTangent_localFlow {X : (q : M) → TangentSpace (𝓡∂ (n + 1)) q}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (htan : ∀ q, (𝓡∂ (n + 1)).IsBoundaryPoint q →
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) (X q) = 0)
    (q₀ : M) :
    ∃ O : Set M, IsOpen O ∧ q₀ ∈ O ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℝ × M → M,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡∂ (n + 1))) (𝓡∂ (n + 1)) ∞ φ (Ioo (-ε) ε ×ˢ O) ∧
      (∀ y ∈ O, φ (0, y) = y) ∧
      ∀ y ∈ O, IsMIntegralCurveOn (fun t => φ (t, y)) X (Ioo (-ε) ε) := by
  let I := 𝓡∂ (n + 1)
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let G := EuclideanSpace ℝ (Fin n)
  let e := extChartAt I q₀
  let A := normalSplit n
  let f : ℝ × G → ℝ × G := normalChartField q₀ X
  obtain ⟨B, hB, hBT⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (extChartAt_target_mem_nhdsWithin (I := I) q₀)
  obtain ⟨O₁, hO₁B, hO₁, heO₁⟩ := mem_nhds_iff.mp hB
  let U : Set (ℝ × G) := A.symm ⁻¹' O₁
  have hU : IsOpen U := hO₁.preimage A.symm.continuous
  let x₀ : ℝ × G := A (e q₀)
  have hx₀U : x₀ ∈ U := by
    change A.symm (A (e q₀)) ∈ O₁
    rw [A.symm_apply_apply]
    exact heO₁
  let H : Set (ℝ × G) := Ici (0 : ℝ) ×ˢ (univ : Set G)
  have hmaps : MapsTo A.symm (H ∩ U) e.target := by
    intro z hz
    exact hBT ⟨hO₁B hz.2, (normalSplit_symm_mem_range_iff n z).mpr hz.1.1⟩
  have hf : ContDiffOn ℝ ∞ f (H ∩ U) :=
    A.contDiff.comp_contDiffOn
      ((contDiffOn_chartField I q₀ hX).comp A.symm.contDiff.contDiffOn hmaps)
  have hftan : ∀ z ∈ H ∩ U, z.1 = 0 → (f z).1 = 0 := by
    intro z hz hz0
    have hzt := hmaps hz
    have hysrc : e.symm (A.symm z) ∈ (chartAt (EuclideanHalfSpace (n + 1)) q₀).source := by
      have h := e.map_target hzt
      rw [extChartAt_source] at h
      exact h
    have hyb : I.IsBoundaryPoint (e.symm (A.symm z)) := by
      apply (chartHeight_eq_zero_iff (n := n + 1) q₀ hysrc).mp
      change e (e.symm (A.symm z)) 0 = 0
      rw [e.right_inv hzt]
      exact hz0
    change (A (chartField I q₀ X (A.symm z))).1 = 0
    rw [normalSplit_fst, chartField_eq_mfderiv I q₀ X hzt]
    exact (proj_zero_mfderiv_extChartAt_eq_zero_iff q₀ hysrc hyb).mpr
      (htan (e.symm (A.symm z)) hyb)
  -- a compactly supported smooth extension, tangent along the whole hyperplane
  obtain ⟨G₀, hG₀, hG₀f⟩ := ContDiffOn.exists_contDiff_extension_Ici_prod_nhdsWithin hf hU hx₀U
  obtain ⟨N, hN, hNf⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hG₀f
  obtain ⟨r, hr, hrN⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hN (hU.mem_nhds hx₀U))
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let g : ℝ × G → ℝ × G := fun z => b z • G₀ z
  have hg : ContDiff ℝ ∞ g := b.contDiff.smul hG₀
  have hgK : HasCompactSupport g := b.hasCompactSupport.smul_right
  have hball : Metric.ball x₀ (r / 2) ⊆ N ∩ U := fun z hz =>
    hrN (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz))
  have hgf : ∀ z ∈ H, z ∈ Metric.ball x₀ (r / 2) → g z = f z := by
    intro z hzH hz
    have hb1 : b z = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
    change b z • G₀ z = f z
    rw [hb1, one_smul]
    exact hNf ⟨(hball hz).1, hzH⟩
  have hgtan : ∀ z : ℝ × G, z.1 = 0 → (g z).1 = 0 := by
    intro z hz0
    by_cases hz : z ∈ Metric.closedBall x₀ r
    · have hzNU := hrN hz
      have hzH : z ∈ H := ⟨(show (0 : ℝ) ≤ z.1 from hz0.symm ▸ le_rfl), mem_univ _⟩
      have hGf : G₀ z = f z := hNf ⟨hzNU.1, hzH⟩
      change (b z • G₀ z).1 = 0
      rw [Prod.smul_fst, hGf, hftan z ⟨hzH, hzNU.2⟩ hz0, smul_zero]
    · have hb0 : b z = 0 := by
        apply Function.notMem_support.mp
        rw [b.support_eq]
        exact fun h => hz (Metric.ball_subset_closedBall h)
      change (b z • G₀ z).1 = 0
      rw [hb0, zero_smul]
      rfl
  obtain ⟨ψ, hψ, hψ0, hψd, hψH⟩ := exists_halfSpace_tangent_flow g hg hgK hgtan
  -- a uniform time on a neighbourhood of `x₀`
  have hcont : ContinuousAt (fun p : ℝ × (ℝ × G) => ψ p.1 p.2) (0, x₀) :=
    hψ.continuous.continuousAt
  have hballnhds : Metric.ball x₀ (r / 2) ∈
      𝓝 ((fun p : ℝ × (ℝ × G) => ψ p.1 p.2) (0, x₀)) := by
    change Metric.ball x₀ (r / 2) ∈ 𝓝 (ψ 0 x₀)
    rw [hψ0]
    exact Metric.ball_mem_nhds x₀ (half_pos hr)
  obtain ⟨T, hT, W', hW', hTW⟩ := mem_nhds_prod_iff.mp (hcont.preimage_mem_nhds hballnhds)
  obtain ⟨W, hWW', hW, hx₀W⟩ := mem_nhds_iff.mp hW'
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  have hsmall : ∀ t ∈ Ioo (-ε) ε, ∀ x ∈ W, ψ t x ∈ Metric.ball x₀ (r / 2) := by
    intro t ht x hx
    apply hTW (mk_mem_prod (hεT ?_) (hWW' hx))
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨ht.1, ht.2⟩
  -- back to `M`
  let C : M → ℝ × G := fun y => A (e y)
  have hC : ContMDiffOn I 𝓘(ℝ, ℝ × G) ∞ C (chartAt (EuclideanHalfSpace (n + 1)) q₀).source :=
    A.contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt (I := I) (x := q₀) (n := ∞))
  have hCH : ∀ y, 0 ≤ (C y).1 := fun y => chartHeight_nonneg (n := n + 1) q₀ y
  let O : Set M := (chartAt (EuclideanHalfSpace (n + 1)) q₀).source ∩ C ⁻¹' W
  have hO : IsOpen O :=
    hC.continuousOn.isOpen_inter_preimage (chartAt (EuclideanHalfSpace (n + 1)) q₀).open_source hW
  have hq₀O : q₀ ∈ O := ⟨mem_chart_source _ q₀, hx₀W⟩
  have hγH : ∀ t ∈ Ioo (-ε) ε, ∀ y ∈ O,
      ψ t (C y) ∈ H ∧ ψ t (C y) ∈ Metric.ball x₀ (r / 2) := fun t ht y hy =>
    ⟨⟨hψH t (C y) (hCH y), mem_univ _⟩, hsmall t ht (C y) hy.2⟩
  have hγT : ∀ t ∈ Ioo (-ε) ε, ∀ y ∈ O, A.symm (ψ t (C y)) ∈ e.target := fun t ht y hy =>
    hmaps ⟨(hγH t ht y hy).1, (hball (hγH t ht y hy).2).2⟩
  refine ⟨O, hO, hq₀O, ε, hε, fun p => e.symm (A.symm (ψ p.1 (C p.2))), ?_, ?_, ?_⟩
  · have hpair := (contMDiffOn_id (I := 𝓘(ℝ, ℝ)) (n := ∞) (s := Ioo (-ε) ε)).prodMap
      (hC.mono (inter_subset_left : O ⊆ _))
    have hγs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
        (fun p : ℝ × M => A.symm (ψ p.1 (C p.2))) (Ioo (-ε) ε ×ˢ O) :=
      A.symm.contDiff.contMDiff.comp_contMDiffOn (hψ.comp_contMDiffOn hpair)
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) q₀).comp hγs
      (fun p hp => hγT p.1 hp.1 p.2 hp.2)
  · intro y hy
    change e.symm (A.symm (ψ 0 (C y))) = y
    rw [hψ0]
    change e.symm (A.symm (A (e y))) = y
    rw [A.symm_apply_apply]
    exact e.left_inv (by rw [extChartAt_source]; exact hy.1)
  · intro y hy
    have hcurve := isMIntegralCurveOn_of_chartField I q₀ X
      (γ := fun t => A.symm (ψ t (C y))) (s := Ioo (-ε) ε) (fun t ht => hγT t ht y hy) ?_
    · exact hcurve
    intro t ht
    have hd := A.symm.hasFDerivAt.comp_hasDerivAt t (hψd (C y) t)
    have hgt : g (ψ t (C y)) = f (ψ t (C y)) :=
      hgf _ (hγH t ht y hy).1 (hγH t ht y hy).2
    have he : A.symm (g (ψ t (C y))) = chartField I q₀ X (A.symm (ψ t (C y))) := by
      rw [hgt]
      exact A.symm_apply_apply _
    change HasDerivAt (fun s => A.symm (ψ s (C y))) (A.symm (g (ψ t (C y)))) t at hd
    rw [he] at hd
    exact hd.hasDerivWithinAt

end DifferentialGeometry.Manifold.BoundaryTangentFlow
