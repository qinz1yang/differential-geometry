import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleFiber

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isHPolytope_coordinate_triangle :
    IsHPolytope {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} := by
  have hbox := (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isHPolytope_Icc (a := (0 : ℝ)) (b := 1))
  have hcut := hbox.inter_affine_le
    (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).toAffineMap 1
  convert hcut using 1
  ext z
  change (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ↔
    ((0 ≤ z.1 ∧ z.1 ≤ 1) ∧ 0 ≤ z.2 ∧ z.2 ≤ 1) ∧ z.1 + z.2 ≤ 1
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨⟨⟨hx, by linarith⟩, hy, by linarith⟩, hxy⟩
  · rintro ⟨⟨⟨hx, -⟩, hy, -⟩, hxy⟩
    exact ⟨hx, hy, hxy⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventually_exists_isPLHomeomorphOn_triangle_fiber_of_affine_height
    {G : ℝ × ℝ → E}
    (hG : IsPiecewiseAffineOn G {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (ℓ : E →L[ℝ] ℝ) {a c d : ℝ} (hc : 0 < c) (hac : c < a)
    (hheight : ∀ z, 0 ≤ z.1 → 0 ≤ z.2 → z.1 + z.2 ≤ 1 →
      ℓ (G z) = a * z.1 + c * z.2 + d) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ r, f (G (0, 0)) < r → r < f (G (1, 0)) →
      ∃ t ∈ Ioc (0 : ℝ) 1, IsPLHomeomorphOn Prod.snd
        {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ f (G z) = r} (Icc 0 t) := by
  let T : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}
  have hT : IsPolyhedron T := isHPolytope_coordinate_triangle.isPolyhedron
  obtain ⟨G', k, hG', hLip, hEq, -, -⟩ :=
    hG.exists_lipschitz_extension hT isOpen_univ (subset_univ _)
  obtain ⟨δ, hδ, hkδ⟩ := exists_pos_mul_lt
    (a := min c (a - c)) (lt_min hc (sub_pos.mpr hac)) (k : ℝ)
  filter_upwards [Metric.ball_mem_nhds ℓ hδ] with f hf
  have hfδ : ‖f - ℓ‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hf
  have hsmall : ‖f - ℓ‖ * (k : ℝ) < min c (a - c) := by
    calc
      ‖f - ℓ‖ * (k : ℝ) ≤ δ * (k : ℝ) := mul_le_mul_of_nonneg_right hfδ.le k.coe_nonneg
      _ = (k : ℝ) * δ := mul_comm _ _
      _ < min c (a - c) := hkδ
  let A : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
    (a • LinearMap.fst ℝ ℝ ℝ + c • LinearMap.snd ℝ ℝ ℝ).toAffineMap +
      AffineMap.const ℝ (ℝ × ℝ) d
  have hA : ∀ z, A z = a * z.1 + c * z.2 + d := fun _ => rfl
  let b : ℝ × ℝ → ℝ := fun z => A z + (f - ℓ) (G' z)
  have hb : IsPiecewiseAffineOn b T :=
    ((isPiecewiseAffineOn_of_affine A isOpen_univ).add
      (hG'.affine_comp (f - ℓ).toLinearMap.toAffineMap)).mono_of_isPolyhedron hT (subset_univ _)
  have hbEq : EqOn b (fun z => f (G z)) T := by
    rintro z ⟨hx, hy, hxy⟩
    dsimp only [b]
    rw [hA, hEq ⟨hx, hy, hxy⟩, sub_apply, hheight z hx hy hxy]
    ring
  have hbLip : LipschitzWith (‖f - ℓ‖₊ * k)
      (fun z => b z - (a * z.1 + c * z.2 + d)) := by
    have heq : (fun z => b z - (a * z.1 + c * z.2 + d)) = (f - ℓ) ∘ G' := by
      funext z
      dsimp only [b, Function.comp_apply]
      rw [hA]
      ring
    rw [heq]
    exact (f - ℓ).lipschitz.comp hLip
  intro r h₀ h₁
  obtain ⟨t, ht, hbij⟩ := exists_isPLHomeomorphOn_snd_triangle_fiber_of_lipschitz hb hbLip
    (show ((‖f - ℓ‖₊ * k : NNReal) : ℝ) < c from lt_of_lt_of_le hsmall (min_le_left _ _))
    (show ((‖f - ℓ‖₊ * k : NNReal) : ℝ) < a - c from lt_of_lt_of_le hsmall (min_le_right _ _))
    (by rwa [hbEq (show (0, 0) ∈ T from ⟨le_rfl, le_rfl, by norm_num⟩)])
    (by rwa [hbEq (show (1, 0) ∈ T from ⟨by norm_num, le_rfl, by norm_num⟩)])
  refine ⟨t, ht, ?_⟩
  convert hbij using 1
  ext z
  exact and_congr_right fun hz => by rw [hbEq hz]

theorem eventually_isPLBall_image_triangle_fiber_of_affine_height [FiniteDimensional ℝ E]
    {G : ℝ × ℝ → E}
    (hG : IsPiecewiseAffineOn G {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hinj : InjOn G {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (ℓ : E →L[ℝ] ℝ) {a c d : ℝ} (hc : 0 < c) (hac : c < a)
    (hheight : ∀ z, 0 ≤ z.1 → 0 ≤ z.2 → z.1 + z.2 ≤ 1 →
      ℓ (G z) = a * z.1 + c * z.2 + d) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ r, f (G (0, 0)) < r → r < f (G (1, 0)) →
      IsPLBall 1 ((G '' {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}) ∩ {x | f x = r}) := by
  filter_upwards [eventually_exists_isPLHomeomorphOn_triangle_fiber_of_affine_height
    hG ℓ hc hac hheight] with f hf
  intro r h₀ h₁
  obtain ⟨t, ht, hPL⟩ := hf r h₀ h₁
  have hball := (isPLBall_Icc ht.1).of_isPLHomeomorphOn hPL.symm
  apply hball.of_isPLHomeomorphOn
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hball.isPolyhedron
    (hG.mono_of_isPolyhedron hball.isPolyhedron (fun _ hz => hz.1)) ?_
  refine ⟨?_, hinj.mono (fun _ hz => hz.1), ?_⟩
  · intro z hz
    exact ⟨⟨z, hz.1, rfl⟩, hz.2⟩
  · rintro x ⟨⟨z, hz, rfl⟩, hfx⟩
    exact ⟨z, ⟨hz, hfx⟩, rfl⟩

theorem eventually_isPLBall_affine_triangle_image_fiber [FiniteDimensional ℝ E]
    (A : (ℝ × ℝ) →ᵃ[ℝ] E) (hA : Function.Injective A)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (ℓ : E →L[ℝ] ℝ)
    (hheight : ∀ x, ℓ (H x) = ℓ x)
    (hmin : ℓ (A (0, 0)) < ℓ (A (0, 1))) (hmax : ℓ (A (0, 1)) < ℓ (A (1, 0))) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      ∀ r, f (H (A (0, 0))) < r → r < f (H (A (1, 0))) →
        IsPLBall 1 ((H '' (A '' {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})) ∩
          {x | f x = r}) := by
  have hApl := (isPiecewiseAffineOn_of_affine A isOpen_univ).mono_of_isPolyhedron
    isHPolytope_coordinate_triangle.isPolyhedron (subset_univ _)
  have hG : IsPiecewiseAffineOn (H ∘ A)
      {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} := by
    simpa only [preimage_univ, inter_univ] using hH.isPiecewiseAffineOn.comp hApl
  let a : ℝ := ℓ (A.linear (1, 0))
  let c : ℝ := ℓ (A.linear (0, 1))
  let d : ℝ := ℓ (A 0)
  have hℓA : ∀ z : ℝ × ℝ, ℓ (A z) = a * z.1 + c * z.2 + d := by
    intro z
    have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
    have hlin : A.linear z = z.1 • A.linear (1, 0) + z.2 • A.linear (0, 1) := by
      calc
        A.linear z = A.linear (z.1 • (1, 0) + z.2 • (0, 1)) := congrArg A.linear hz
        _ = _ := by rw [map_add, map_smul, map_smul]
    have hAz : A z = A.linear z + A 0 := by simpa using A.map_vadd 0 z
    rw [hAz, hlin, map_add, map_add, map_smul, map_smul]
    dsimp only [a, c, d, smul_eq_mul]
    ring
  have hc : 0 < c := by
    rw [hℓA, hℓA] at hmin
    dsimp at hmin
    linarith
  have hac : c < a := by
    rw [hℓA, hℓA] at hmax
    dsimp at hmax
    linarith
  have hresult := eventually_isPLBall_image_triangle_fiber_of_affine_height hG
    (H.injective.comp hA).injOn ℓ hc hac
    (fun z _ _ _ => (hheight (A z)).trans (hℓA z))
  simpa only [Function.comp_apply, image_image] using hresult

end DifferentialGeometry.Topology.PiecewiseLinear
