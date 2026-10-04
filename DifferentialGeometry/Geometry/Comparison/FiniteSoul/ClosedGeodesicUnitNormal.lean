import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShapeTwo
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftNormalExists
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicNormal

/-!
# A continuous unit normal along a closed geodesic of a surface (S-SOUL2 adapter SA6)

`exists_unitNormal_closedGeodesic_dim_two`: along a closed unit geodesic `Φ_ℓ p = p` of a
complete finite surface there is a unit normal field `ν : ℝ → E`, continuous along the geodesic in
the tangent bundle, on the whole line. This is the input of lane CMS-T's holonomy and tube
theorems (`exists_unitNormal_holonomy`, `exists_closedGeodesic_tube`), which take `ν` on `ℝ`.

Route: a unit normal `w` at `p` (Gram–Schmidt in `g_p`); CMS-J's `exists_unitNormal_dim_two`
gives a continuous unit normal `ξ` on `[0, ℓ]` with `ξ 0 = w`; since `Φ_ℓ p = p`, `ξ ℓ = σ w` with
`σ ∈ ℤˣ` (two unit normals in dimension two); then `ν t = σ^k ξ (t - k ℓ)` on `[k ℓ, k ℓ + ℓ]`,
`k = ⌊t / ℓ⌋`, agrees at the seams and is continuous (closed pieces, fibrewise `±1`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- `g_z(c a, b) = c g_z(a, b)`. -/
theorem inner_smul_left_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (z : M) (c : ℝ) (a b : E) : g.inner z (c • a) b = c * g.inner z a b := by
  have h : g.inner z (c • a) = c • g.inner z a := (g.inner z).map_smul c a
  rw [h]
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- A unit normal to a unit vector exists in dimension two. -/
theorem exists_unit_orthogonal_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hdim : Module.finrank ℝ E = 2) (z : M) {U : E} (hU : g.inner z U U = 1) :
    ∃ w : E, g.inner z w w = 1 ∧ g.inner z w U = 0 := by
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner z with hBdef
  have hsymm : ∀ a b : E, B a b = B b a := fun a b => g.symm z a b
  have hU0 : U ≠ 0 := by
    intro h0
    have h1 := inner_smul_smul_self_finite g z 0 U
    rw [zero_smul, ← h0, hU] at h1
    norm_num at h1
  obtain ⟨W, hW⟩ := exists_not_mem_span_singleton_dim_two hdim hU0
  set c : ℝ := B W U with hcdef
  have hne : W - c • U ≠ 0 := by
    intro h0
    have h1 := LinearIndependent.pair_iff.1 hW (-c) 1 (by rw [neg_smul, one_smul, ← h0]; abel)
    exact one_ne_zero h1.2
  have hpos : 0 < B (W - c • U) (W - c • U) := g.pos z _ hne
  have hexp : B (W - c • U) (W - c • U) = B W W - c ^ 2 := by
    simp only [map_sub, map_smul, sub_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    have hU' : B U U = 1 := hU
    rw [hsymm U W, ← hcdef]
    linear_combination c ^ 2 * hU'
  have hd : 0 < B W W - (B W U) ^ 2 := by rw [← hcdef, ← hexp]; exact hpos
  obtain ⟨h1, h2⟩ := gramSchmidt_unit B hsymm hU hd
  exact ⟨_, h2, h1⟩

/-- **SA6.** A continuous unit normal field on the whole line along a closed unit geodesic of a
complete finite surface. -/
theorem exists_unitNormal_closedGeodesic_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p) :
    ∃ ν : ℝ → E,
      Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)) ∧
      (∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1) ∧
      ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (Q : TangentBundle I M) (τ : ℝ), (Q, τ) ∈ g.geodesicFlowDomain := fun Q τ => by
    rw [hD]; exact mem_univ _
  have hshift : ∀ (k : ℤ) (t : ℝ), g.geodesicFlow p (t - k * ℓ) = g.geodesicFlow p t := by
    intro k t
    have h := geodesicFlow_add_int_mul g hr1 hD hper (t - k * ℓ) k
    rw [sub_add_cancel] at h
    exact h.symm
  -- a unit normal at `p` and CMS-J's normal on `[0, ℓ]`
  set U : E := p.snd with hUdef
  obtain ⟨w, hw, hwU⟩ := exists_unit_orthogonal_dim_two g hdim p.proj (U := U) hunit
  obtain ⟨ξ, hξc, hξ, hξ0⟩ := exists_unitNormal_dim_two g hr1 hdim p (fun t => hmem p t) hunit
    hw hwU (a := 0) (b := ℓ) le_rfl hℓ.le
  -- the holonomy sign
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤˣ, ξ ℓ = (((σ : ℤ) : ℝ)) • w := by
    have hℓmem : ℓ ∈ Icc (0 : ℝ) ℓ := ⟨hℓ.le, le_rfl⟩
    have h1 := (hξ ℓ hℓmem).1
    have h2 := (hξ ℓ hℓmem).2
    rw [hper] at h1 h2
    set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p.proj with hBdef
    have hsymm : ∀ a b : E, B a b = B b a := fun a b => g.symm p.proj a b
    have heq := eq_smul_of_orthonormal_dim_two hdim (B := B) hsymm (U := U) (N := w) (X := ξ ℓ)
      hunit hw hwU h2
    set s : ℝ := B (ξ ℓ) w with hsdef
    have hs2 : s ^ 2 = 1 := by
      have h3 := inner_smul_smul_self_finite g p.proj s w
      rw [← heq, h1, hw, mul_one] at h3
      exact h3.symm
    have hs : s = 1 ∨ s = -1 := by
      have h4 : (s - 1) * (s + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.1 h4 with h | h
      · left; linarith
      · right; linarith
    rcases hs with hs | hs
    · exact ⟨1, by rw [heq, hs]; simp⟩
    · exact ⟨-1, by rw [heq, hs]; simp⟩
  set c : ℤ → ℝ := fun k => (((σ ^ k : ℤˣ) : ℤ) : ℝ) with hcdef
  have hc_succ : ∀ k : ℤ, c (k + 1) = c k * ((σ : ℤ) : ℝ) := by
    intro k
    simp only [c, zpow_add_one, Units.val_mul, Int.cast_mul]
  have hc_sq : ∀ k : ℤ, c k * c k = 1 := by
    intro k
    rcases Int.units_eq_one_or (σ ^ k) with h | h
    · simp only [c, h]; norm_num
    · simp only [c, h]; norm_num
  have hc_pm : ∀ k : ℤ, c k = 1 ∨ c k = -1 := by
    intro k
    rcases Int.units_eq_one_or (σ ^ k) with h | h
    · left; simp only [c, h]; norm_num
    · right; simp only [c, h]; norm_num
  set ν : ℝ → E := fun t => c ⌊t / ℓ⌋ • ξ (t - ⌊t / ℓ⌋ * ℓ) with hνdef
  -- on each closed piece `[k ℓ, k ℓ + ℓ]`, `ν t = c k • ξ (t - k ℓ)`
  have hpiece : ∀ (k : ℤ) (t : ℝ), t ∈ Icc ((k : ℝ) * ℓ) (k * ℓ + ℓ) →
      ν t = c k • ξ (t - k * ℓ) := by
    intro k t ht
    rcases eq_or_lt_of_le ht.2 with htop | hlt
    · -- the right end: `⌊t / ℓ⌋ = k + 1`
      have hfl : ⌊t / ℓ⌋ = k + 1 := by
        rw [Int.floor_eq_iff, htop]
        constructor
        · rw [le_div_iff₀ hℓ]; push_cast; linarith
        · rw [div_lt_iff₀ hℓ]; push_cast; linarith
      simp only [ν, hfl]
      have h1 : t - ((k + 1 : ℤ) : ℝ) * ℓ = 0 := by rw [htop]; push_cast; ring
      have h2 : t - (k : ℝ) * ℓ = ℓ := by rw [htop]; ring
      rw [h1, h2, hξ0, hσ, smul_smul, hc_succ]
    · have hfl : ⌊t / ℓ⌋ = k := by
        rw [Int.floor_eq_iff]
        constructor
        · rw [le_div_iff₀ hℓ]; exact ht.1
        · rw [div_lt_iff₀ hℓ]; linarith
      simp only [ν, hfl]
  -- continuity on each closed piece
  have hpiece_cont : ∀ k : ℤ, ContinuousOn
      (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M))
      (Icc ((k : ℝ) * ℓ) (k * ℓ + ℓ)) := by
    intro k
    have hmaps : MapsTo (fun t : ℝ => t - k * ℓ) (Icc ((k : ℝ) * ℓ) (k * ℓ + ℓ)) (Icc 0 ℓ) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hbase : ContinuousOn
        (fun t => (⟨(g.geodesicFlow p (t - k * ℓ)).proj, ξ (t - k * ℓ)⟩ : TangentBundle I M))
        (Icc ((k : ℝ) * ℓ) (k * ℓ + ℓ)) :=
      hξc.comp (continuous_id.sub continuous_const).continuousOn hmaps
    have hsigned : ContinuousOn
        (fun t => (⟨(g.geodesicFlow p (t - k * ℓ)).proj, c k • ξ (t - k * ℓ)⟩ :
          TangentBundle I M)) (Icc ((k : ℝ) * ℓ) (k * ℓ + ℓ)) := by
      rcases hc_pm k with h | h
      · rw [h]; simpa only [one_smul] using hbase
      · rw [h]; simpa only [neg_one_smul] using continuousOn_neg_field hbase
    refine hsigned.congr fun t ht => ?_
    simp only []
    rw [hpiece k t ht, hshift k t]
  -- global continuity
  refine ⟨ν, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun t => ?_
    set k : ℤ := ⌊t / ℓ⌋ with hkdef
    have h1 : (k : ℝ) * ℓ ≤ t := by rw [← le_div_iff₀ hℓ]; exact Int.floor_le _
    have h2 : t < (k : ℝ) * ℓ + ℓ := by
      have := Int.lt_floor_add_one (t / ℓ)
      rw [div_lt_iff₀ hℓ] at this
      linarith
    have hk1 : ((k - 1 : ℤ) : ℝ) * ℓ + ℓ = (k : ℝ) * ℓ := by push_cast; ring
    have hunion : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M))
        (Icc (((k - 1 : ℤ) : ℝ) * ℓ) (((k - 1 : ℤ) : ℝ) * ℓ + ℓ) ∪
          Icc ((k : ℝ) * ℓ) (k * ℓ + ℓ)) :=
      (hpiece_cont (k - 1)).union_of_isClosed (hpiece_cont k) isClosed_Icc isClosed_Icc
    refine hunion.continuousAt (mem_of_superset (Icc_mem_nhds (a := ((k - 1 : ℤ) : ℝ) * ℓ)
      (b := (k : ℝ) * ℓ + ℓ) ?_ h2) ?_)
    · have : ((k - 1 : ℤ) : ℝ) * ℓ = (k : ℝ) * ℓ - ℓ := by push_cast; ring
      rw [this]; linarith
    · intro τ hτ
      rcases le_total τ ((k : ℝ) * ℓ) with h | h
      · exact Or.inl ⟨hτ.1, by rw [hk1]; exact h⟩
      · exact Or.inr ⟨h, hτ.2⟩
  all_goals intro t
  all_goals
    set k : ℤ := ⌊t / ℓ⌋ with hkdef
    have h1 : (k : ℝ) * ℓ ≤ t := by rw [← le_div_iff₀ hℓ]; exact Int.floor_le _
    have h2 : t < (k : ℝ) * ℓ + ℓ := by
      have := Int.lt_floor_add_one (t / ℓ)
      rw [div_lt_iff₀ hℓ] at this
      linarith
    have hτ : t - k * ℓ ∈ Icc (0 : ℝ) ℓ := ⟨by linarith, by linarith⟩
    have hνt : ν t = c k • ξ (t - k * ℓ) := hpiece k t ⟨h1, h2.le⟩
    rw [hνt, ← hshift k t]
  · rw [inner_smul_smul_self_finite, (hξ _ hτ).1, mul_one, ← hc_sq k]
    ring
  · exact (inner_smul_left_finite g _ (c k) _ _).trans (mul_eq_zero_of_right _ (hξ _ hτ).2)

end DifferentialGeometry.Geometry.FiniteSoul
