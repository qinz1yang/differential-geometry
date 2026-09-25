import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingSideConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorCrossingChartsSurface
import DifferentialGeometry.Topology.PiecewiseLinear.CrossHalfPlaneCharts

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCrossingAt.exists_full_plane_coordinate_chart_of_local_ball_charts
    {A B : Set E} {x : E}
    (hcross : HasPLCrossingAt A B x)
    (hA : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x)
    (hB : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (B ∩ N) ∧ g c = x) :
    ∃ (U : Set E) (φ : E → ℝ × ℝ × ℝ) (ρ : ℝ),
      IsOpen U ∧ x ∈ U ∧ 0 < ρ ∧ IsPLHomeomorphOn φ U (Metric.ball 0 ρ) ∧ φ x = 0 ∧
        ∀ y ∈ U, (y ∈ A ↔ (φ y).2.2 = 0) ∧ (y ∈ B ↔ (φ y).2.1 = 0) := by
  obtain ⟨U, φ, ρ, α, β, hU, hxU, hρ, hφ, hφx, hα, hβ, hloc⟩ :=
    hcross.exists_coordinateChart
  have hα0 : α = 0 := by
    rcases hα with h | h
    · exact h
    · exact (false_of_ballChart_of_halfPlane hU hxU hφ hφx h
        (fun y hy hyA => (hloc y hy).1.mp hyA)
        hA).elim
  let L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ) :=
    (LinearEquiv.refl ℝ ℝ).prodCongr (LinearEquiv.prodComm ℝ ℝ ℝ)
  have hLn (z : ℝ × ℝ × ℝ) : ‖L z‖ = ‖z‖ := by
    simp [L, Prod.norm_def, max_comm]
  have hLB : L '' Metric.ball 0 ρ = Metric.ball 0 ρ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [mem_ball_zero_iff, hLn] using hw
    · intro hz
      refine ⟨L.symm z, ?_, L.apply_symm_apply z⟩
      rw [mem_ball_zero_iff] at hz ⊢
      calc
        ‖L.symm z‖ = ‖L (L.symm z)‖ := (hLn _).symm
        _ = ‖z‖ := congrArg norm (L.apply_symm_apply z)
        _ < ρ := hz
  have hLφ : IsPLHomeomorphOn (L ∘ φ) U (Metric.ball 0 ρ) := by
    simpa only [hLB] using hφ.trans (isPLHomeomorphOn_linearEquiv L Metric.isOpen_ball)
  have hβ0 : β = 0 := by
    rcases hβ with h | h
    · exact h
    · let β' := β.comp L.symm.toLinearMap
      have hβ' : β' (1, 0, 0) ≠ 0 := by simpa [β', L] using h
      apply False.elim
      apply false_of_ballChart_of_halfPlane hU hxU hLφ
        (by simp only [Function.comp_apply, hφx, map_zero]) hβ'
      · intro y hy hyB
        simpa [β', L] using (hloc y hy).2.mp hyB
      · exact hB
  refine ⟨U, φ, ρ, hU, hxU, hρ, hφ, hφx, fun y hy => ?_⟩
  simpa only [hα0, hβ0, LinearMap.zero_apply, le_refl, and_true] using hloc y hy

theorem HasPLCrossingAt.exists_isolated_circle_chart_of_local_ball_charts {A B J N : Set E} {x : E}
    (hcross : HasPLCrossingAt A B x)
    (hA : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x)
    (hB : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (B ∩ N) ∧ g c = x)
    (hJ : J ⊆ A ∩ B)
    (hN : IsOpen N) (hxN : x ∈ N) (htrace : (A ∩ B) ∩ N ⊆ J) :
    ∃ (ψ : (ℝ × ℝ) × ℝ → E) (V : Set ((ℝ × ℝ) × ℝ)) (Ω : Set E),
      IsOpen V ∧ IsOpen Ω ∧ x ∈ Ω ∧ Ω ⊆ N ∧ IsPLHomeomorphOn ψ V Ω ∧
        (∀ p ∈ V, (ψ p ∈ A ↔ p.1.2 = 0) ∧ (ψ p ∈ B ↔ p.1.1 = 0)) ∧
        (∀ p ∈ V, ψ p ∈ A ∪ B ↔ p ∈ crossPlanes) ∧
        ∀ p ∈ V, ψ p ∈ J ↔ p.1 = 0 := by
  obtain ⟨U, φ, ρ, hU, hxU, -, hφ, -, hloc⟩ :=
    hcross.exists_full_plane_coordinate_chart_of_local_ball_charts hA hB
  let L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × ℝ) :=
    LinearEquiv.prodComm ℝ ℝ (ℝ × ℝ)
  let χ : E → (ℝ × ℝ) × ℝ := L ∘ φ
  have hV : IsOpen (L '' Metric.ball (0 : ℝ × ℝ × ℝ) ρ) :=
    L.toContinuousLinearEquiv.toHomeomorph.isOpenMap _ Metric.isOpen_ball
  have hL : IsPLHomeomorphOn L (Metric.ball 0 ρ) (L '' Metric.ball 0 ρ) := by
    refine ⟨L.injective.injOn.bijOn_image,
      isPiecewiseAffineOn_of_affine L.toLinearMap.toAffineMap Metric.isOpen_ball, ?_⟩
    apply (isPiecewiseAffineOn_of_affine L.symm.toLinearMap.toAffineMap hV).congr
    rintro y ⟨z, hz, rfl⟩
    change Function.invFunOn (⇑L) (Metric.ball 0 ρ) (L z) = L.symm (L z)
    rw [L.injective.injOn.leftInvOn_invFunOn hz, L.symm_apply_apply]
  have hχ : IsPLHomeomorphOn χ U (L '' Metric.ball 0 ρ) := hφ.trans hL
  have hO := hU.inter hN
  have hχO := hχ.isOpen_image_of_isOpen hV hO inter_subset_left
  have hχ' := hχ.restrict_isOpen hO inter_subset_left hχO
  let ψ := Function.invFunOn χ (U ∩ N)
  have hread : ∀ p ∈ χ '' (U ∩ N),
      (ψ p ∈ A ↔ p.1.2 = 0) ∧ (ψ p ∈ B ↔ p.1.1 = 0) := by
    intro p hp
    have hy := hχ'.symm.bijOn.mapsTo hp
    have heq := hχ'.bijOn.invOn_invFunOn.2 hp
    have hh := hloc (ψ p) hy.1
    change χ (ψ p) = p at heq
    have h₁ := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.2) heq
    have h₂ := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) heq
    change (φ (ψ p)).2.2 = p.1.2 at h₁
    change (φ (ψ p)).2.1 = p.1.1 at h₂
    rwa [h₁, h₂] at hh
  refine ⟨ψ, χ '' (U ∩ N), U ∩ N, hχO, hO, ⟨hxU, hxN⟩,
    inter_subset_right, hχ'.symm, hread, ?_, ?_⟩
  · intro p hp
    change (ψ p ∈ A ∨ ψ p ∈ B) ↔ p.1.1 = 0 ∨ p.1.2 = 0
    rw [(hread p hp).1, (hread p hp).2, or_comm]
  · intro p hp
    have hy := hχ'.symm.bijOn.mapsTo hp
    rw [Prod.ext_iff]
    change (ψ p ∈ J) ↔ p.1.1 = 0 ∧ p.1.2 = 0
    rw [← (hread p hp).1, ← (hread p hp).2, and_comm]
    exact ⟨fun h => hJ h, fun h => htrace ⟨h, hy.2⟩⟩

theorem HasPLCrossingAt.exists_isolated_circle_disks_of_local_ball_charts {A B J N : Set E} {x : E}
    (hcross : HasPLCrossingAt A B x)
    (hA : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x)
    (hB : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (B ∩ N) ∧ g c = x)
    (hxJ : x ∈ J) (hJ : J ⊆ A ∩ B)
    (hN : IsOpen N) (hxN : x ∈ N) (htrace : (A ∩ B) ∩ N ⊆ J) :
    ∃ (ψ : (ℝ × ℝ) × ℝ → E) (V : Set ((ℝ × ℝ) × ℝ)) (Ω W : Set E)
      (P : Fin 4 → Set E) (q : Fin 4 → (Fin 3 → ℝ) → E),
      IsOpen V ∧ IsOpen Ω ∧ IsOpen W ∧ x ∈ W ∧ W ⊆ Ω ∧ Ω ⊆ N ∧
      IsPLHomeomorphOn ψ V Ω ∧
      (∀ p ∈ V, (ψ p ∈ A ↔ p.1.2 = 0) ∧ (ψ p ∈ B ↔ p.1.1 = 0)) ∧
      (∀ p ∈ V, ψ p ∈ A ∪ B ↔ p ∈ crossPlanes) ∧
      (∀ p ∈ V, ψ p ∈ J ↔ p.1 = 0) ∧
      (∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (P i)) ∧
      (∀ i, P i ⊆ N ∩ (A ∪ B)) ∧
      (∀ y ∈ W, ∀ i, y ∈ P i ↔ Function.invFunOn ψ V y ∈ crossHalfPlane i) ∧
      ∀ y ∈ W, ∀ i, y ∈ q i '' stdSimplexBoundary 2 ↔ y ∈ J := by
  obtain ⟨ψ, V, Ω, hV, hΩ, hxΩ, hΩN, hψ, hAB, hF, hΓ⟩ :=
    hcross.exists_isolated_circle_chart_of_local_ball_charts hA hB hJ hN hxN htrace
  have hψ' : IsPLHomeomorphOn ψ V (N ∩ Ω) := by
    simpa only [inter_eq_right.mpr hΩN] using hψ
  obtain ⟨W, P, q, hW, hxW, hWΩ, hq, hP, hread, hbd⟩ :=
    hψ'.exists_crossHalfPlane_disks hV hΩ hF hΓ ⟨hxN, hxΩ⟩ hxJ
  exact ⟨ψ, V, Ω, W, P, q, hV, hΩ, hW, hxW, hWΩ, hΩN, hψ, hAB, hF, hΓ, hq, hP,
    fun y hy => hread y ⟨hΩN (hWΩ hy), hy⟩,
    fun y hy => hbd y ⟨hΩN (hWΩ hy), hy⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
