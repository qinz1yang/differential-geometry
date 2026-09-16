import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleFiberEquivalence
import DifferentialGeometry.Topology.PiecewiseLinear.HeightPerturbation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isHPolytope_coordinate_triangle :
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

theorem eventually_strictMonoOn_triangle_height
    {G : ℝ × ℝ → E}
    (hG : IsPiecewiseAffineOn G {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (ℓ : E →L[ℝ] ℝ) {a c d : ℝ} (hc : 0 < c) (hac : c < a)
    (hheight : ∀ z, 0 ≤ z.1 → 0 ≤ z.2 → z.1 + z.2 ≤ 1 →
      ℓ (G z) = a * z.1 + c * z.2 + d) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      (∀ y ∈ Icc (0 : ℝ) 1,
        StrictMonoOn (fun x => f (G (x, y))) (Icc 0 (1 - y))) ∧
      StrictMonoOn (fun y => f (G (0, y))) (Icc (0 : ℝ) 1) ∧
      StrictAntiOn (fun y => f (G (1 - y, y))) (Icc (0 : ℝ) 1) := by
  let T : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}
  have hT : IsPolyhedron T := isHPolytope_coordinate_triangle.isPolyhedron
  obtain ⟨G', k, -, hLip, hEq, -, -⟩ :=
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
  let b : ℝ × ℝ → ℝ := fun z => a * z.1 + c * z.2 + d + (f - ℓ) (G' z)
  have hbEq : EqOn b (fun z => f (G z)) T := by
    rintro z ⟨hx, hy, hxy⟩
    dsimp only [b]
    rw [hEq ⟨hx, hy, hxy⟩, sub_apply, hheight z hx hy hxy]
    ring
  have hbLip : LipschitzWith (‖f - ℓ‖₊ * k)
      (fun z => b z - (a * z.1 + c * z.2 + d)) := by
    have heq : (fun z => b z - (a * z.1 + c * z.2 + d)) = (f - ℓ) ∘ G' := by
      funext z
      dsimp only [b, Function.comp_apply]
      ring
    rw [heq]
    exact (f - ℓ).lipschitz.comp hLip
  obtain ⟨hh, hl, hr⟩ := strictMonoOn_triangle_slices_of_lipschitz_sub_affine hbLip
    (show ((‖f - ℓ‖₊ * k : NNReal) : ℝ) < c from lt_of_lt_of_le hsmall (min_le_left _ _))
    (show ((‖f - ℓ‖₊ * k : NNReal) : ℝ) < a - c from lt_of_lt_of_le hsmall (min_le_right _ _))
  refine ⟨?_, ?_, ?_⟩
  · intro y hy x hx x' hx' hxx
    have hbx := hbEq (show (x, y) ∈ T from ⟨hx.1, hy.1, by linarith [hx.2]⟩)
    have hbx' := hbEq (show (x', y) ∈ T from ⟨hx'.1, hy.1, by linarith [hx'.2]⟩)
    rw [← hbx, ← hbx']
    exact hh y hy hx hx' hxx
  · intro y hy y' hy' hyy
    have hby := hbEq (show (0, y) ∈ T from ⟨le_rfl, hy.1, by simpa using hy.2⟩)
    have hby' := hbEq (show (0, y') ∈ T from ⟨le_rfl, hy'.1, by simpa using hy'.2⟩)
    rw [← hby, ← hby']
    exact hl hy hy' hyy
  · intro y hy y' hy' hyy
    have hby := hbEq (show (1 - y, y) ∈ T from ⟨by linarith [hy.2], hy.1, by linarith⟩)
    have hby' := hbEq (show (1 - y', y') ∈ T from ⟨by linarith [hy'.2], hy'.1, by linarith⟩)
    rw [← hby, ← hby']
    exact hr hy hy' hyy

theorem eventually_exists_isPLHomeomorphOn_triangle_fiber_of_affine_height
    {G : ℝ × ℝ → E}
    (hG : IsPiecewiseAffineOn G {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (ℓ : E →L[ℝ] ℝ) {a c d : ℝ} (hc : 0 < c) (hac : c < a)
    (hheight : ∀ z, 0 ≤ z.1 → 0 ≤ z.2 → z.1 + z.2 ≤ 1 →
      ℓ (G z) = a * z.1 + c * z.2 + d) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ r, f (G (0, 0)) < r → r < f (G (1, 0)) →
      ∃ t ∈ Ioc (0 : ℝ) 1, IsPLHomeomorphOn Prod.snd
        {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ f (G z) = r} (Icc 0 t) := by
  filter_upwards [eventually_strictMonoOn_triangle_height hG ℓ hc hac hheight] with f hf
  intro r h₀ h₁
  exact exists_isPLHomeomorphOn_snd_triangle_fiber
    (hG.affine_comp f.toLinearMap.toAffineMap) hf.1 hf.2.1 hf.2.2 h₀ h₁

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

theorem eventually_exists_isPLHomeomorphOn_triangle_fiber_preserving_edges
    {G : ℝ × ℝ → E}
    (hG : IsPiecewiseAffineOn G {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (ℓ : E →L[ℝ] ℝ) {a c d : ℝ} (hc : 0 < c) (hac : c < a)
    (hheight : ∀ z, 0 ≤ z.1 → 0 ≤ z.2 → z.1 + z.2 ≤ 1 →
      ℓ (G z) = a * z.1 + c * z.2 + d) {p : E}
    (hunique : ∀ z ∈ ({(0, 0), (0, 1), (1, 0)} : Set (ℝ × ℝ)),
      ℓ (G z) = ℓ p → G z = p) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ g : ℝ × ℝ → ℝ × ℝ, IsPLHomeomorphOn g
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ f (G z) = f p}
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ ℓ (G z) = ℓ p} ∧
      ∀ z, (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) → f (G z) = f p →
        ((g z).1 = 0 ↔ z.1 = 0) ∧ ((g z).2 = 0 ↔ z.2 = 0) ∧
        ((g z).1 + (g z).2 = 1 ↔ z.1 + z.2 = 1) := by
  have hmono := eventually_strictMonoOn_triangle_height hG ℓ hc hac hheight
  obtain ⟨hℓh, hℓl, hℓr⟩ := hmono.self_of_nhds
  let V : Set E := {G (0, 0), G (0, 1), G (1, 0), p}
  have hV : V.Finite := by simp [V]
  filter_upwards [hmono, eventually_preserves_strict_order hV ℓ] with f hf horder
  by_cases hlo : ℓ (G (0, 0)) < ℓ p
  · by_cases hhi : ℓ p < ℓ (G (1, 0))
    · have hflo : f (G (0, 0)) < f p := horder _ (by simp [V]) _ (by simp [V]) hlo
      have hfhi : f p < f (G (1, 0)) := horder _ (by simp [V]) _ (by simp [V]) hhi
      have hcompare : (f p ≤ f (G (0, 1)) ↔ ℓ p ≤ ℓ (G (0, 1))) ∧
          (f (G (0, 1)) ≤ f p ↔ ℓ (G (0, 1)) ≤ ℓ p) := by
        rcases lt_trichotomy (ℓ (G (0, 1))) (ℓ p) with hlt | heq | hgt
        · have hflt := horder _ (show G (0, 1) ∈ V by simp [V]) _ (show p ∈ V by simp [V]) hlt
          exact ⟨iff_of_false (not_le.mpr hflt) (not_le.mpr hlt), iff_of_true hflt.le hlt.le⟩
        · have hpoint := hunique (0, 1) (by simp) heq
          simp [hpoint]
        · have hfgt := horder _ (show p ∈ V by simp [V]) _ (show G (0, 1) ∈ V by simp [V]) hgt
          exact ⟨iff_of_true hfgt.le hgt.le, iff_of_false (not_le.mpr hfgt) (not_le.mpr hgt)⟩
      exact exists_isPLHomeomorphOn_triangle_fibers_preserving_edges
        (hG.affine_comp f.toLinearMap.toAffineMap) (hG.affine_comp ℓ.toLinearMap.toAffineMap)
        hf.1 hf.2.1 hf.2.2 hℓh hℓl hℓr hflo hfhi hlo hhi hcompare.1 hcompare.2
    · rcases lt_or_eq_of_le (le_of_not_gt hhi) with hmax | heq
      · have hfmax := horder _ (show G (1, 0) ∈ V by simp [V]) _ (show p ∈ V by simp [V]) hmax
        have hnew := triangle_fiber_eq_empty_of_notMem_Icc (b := fun z => f (G z)) (r := f p) hf.1 hf.2.1 hf.2.2
          (fun h => (not_le.mpr hfmax) h.2)
        have hold := triangle_fiber_eq_empty_of_notMem_Icc (b := fun z => ℓ (G z)) (r := ℓ p) hℓh hℓl hℓr
          (fun h => (not_le.mpr hmax) h.2)
        refine ⟨id, ?_, fun _ _ _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
        rw [hnew, hold]
        exact IsPolyhedron.empty.isPLHomeomorphOn_id
      · have hpoint := hunique (1, 0) (by simp) heq
        have hnew := triangle_fiber_max_eq_singleton_of_monotone (b := fun z => f (G z)) hf.1 hf.2.1 hf.2.2
        have hold := triangle_fiber_max_eq_singleton_of_monotone (b := fun z => ℓ (G z)) hℓh hℓl hℓr
        rw [hpoint] at hnew hold
        refine ⟨id, ?_, fun _ _ _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
        rw [hnew, hold]
        exact (isHPolytope_singleton (1, 0)).isPolyhedron.isPLHomeomorphOn_id
  · rcases lt_or_eq_of_le (le_of_not_gt hlo) with hmin | heq
    · have hfmin := horder _ (show p ∈ V by simp [V]) _ (show G (0, 0) ∈ V by simp [V]) hmin
      have hnew := triangle_fiber_eq_empty_of_notMem_Icc (b := fun z => f (G z)) (r := f p) hf.1 hf.2.1 hf.2.2
        (fun h => (not_le.mpr hfmin) h.1)
      have hold := triangle_fiber_eq_empty_of_notMem_Icc (b := fun z => ℓ (G z)) (r := ℓ p) hℓh hℓl hℓr
        (fun h => (not_le.mpr hmin) h.1)
      refine ⟨id, ?_, fun _ _ _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
      rw [hnew, hold]
      exact IsPolyhedron.empty.isPLHomeomorphOn_id
    · have hpoint := hunique (0, 0) (by simp) heq.symm
      have hnew := triangle_fiber_min_eq_singleton_of_monotone (b := fun z => f (G z)) hf.1 hf.2.1 hf.2.2
      have hold := triangle_fiber_min_eq_singleton_of_monotone (b := fun z => ℓ (G z)) hℓh hℓl hℓr
      rw [hpoint] at hnew hold
      refine ⟨id, ?_, fun _ _ _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
      rw [hnew, hold]
      exact (isHPolytope_singleton (0, 0)).isPolyhedron.isPLHomeomorphOn_id

end DifferentialGeometry.Topology.PiecewiseLinear
