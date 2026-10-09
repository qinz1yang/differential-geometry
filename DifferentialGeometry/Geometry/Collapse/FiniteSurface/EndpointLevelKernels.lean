import DifferentialGeometry.Geometry.Comparison.FiniteSoul.HittingTime
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Topological kernels for the levels of LFR23 (flow bands)

Pure topology, for a continuous flow `Φ` and a continuous height `η` that increases at a positive
rate along orbit segments inside an open set `U` (the situation of LFR23 with `η = d(z₀, ·)` and the
outward field's flow):
* `mem_closure_lt_of_rate`, `mem_frontier_le_of_rate`: every point of `U` is a limit of points of
  larger height, so a level point in `U` lies on the frontier of the sublevel;
* `lt_of_rate_of_lt`: the height strictly increases along orbit segments inside `U`;
* `isPathConnected_level_of_hittingTime`: a level is path connected when any two of its points are
  joined inside the band (project the joining path to the level by the hitting time);
* `exists_embedding_level_of_band_product`: in a band product `e : P × [a, b] → X` (`P` compact
  Hausdorff), a continuous `F` strictly increasing along every fibre and crossing `s₀` between the
  two ends has the level `{F = s₀} ∩ range e` as the image of an embedding of `P` (a cross-section
  homeomorphic to the base level).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.FiniteSoul (hittingTime)

variable {X : Type*} [TopologicalSpace X]

/-- A point of `U` is a limit of points of strictly larger height (flow forward a little). -/
theorem mem_closure_lt_of_rate {Φ : ℝ → X → X} (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) {η : X → ℝ} {U : Set X} (hU : IsOpen U) {κ : ℝ} (hκ : 0 < κ)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : x ∈ U) : x ∈ closure {y | η x < η y} := by
  have hc : Continuous (fun t : ℝ => Φ t x) := hΦ.comp (continuous_id.prodMk continuous_const)
  have hT : Tendsto (fun t : ℝ => Φ t x) (𝓝[>] 0) (𝓝 x) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [hΦ0] using this
  have hopen : IsOpen {t : ℝ | Φ t x ∈ U} := hU.preimage hc
  have h0 : (0 : ℝ) ∈ {t : ℝ | Φ t x ∈ U} := by
    change Φ 0 x ∈ U; rw [hΦ0]; exact hx
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  have hsub : ∀ s ∈ Icc 0 t, Φ s x ∈ U := fun s hs => hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt ht.2)
  have := hrate x t ht.1.le hsub
  change η x < η (Φ t x)
  nlinarith [ht.1]

/-- A level point inside `U` lies on the frontier of the sublevel. -/
theorem mem_frontier_le_of_rate {Φ : ℝ → X → X} (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) {η : X → ℝ} {U : Set X} (hU : IsOpen U) {κ : ℝ} (hκ : 0 < κ)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : x ∈ U) {a : ℝ} (hxa : η x = a) : x ∈ frontier {y | η y ≤ a} := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (show η x ≤ a from hxa.le), ?_⟩
  refine closure_mono (fun y hy => ?_) (mem_closure_lt_of_rate hΦ hΦ0 hU hκ hrate hx)
  change ¬ η y ≤ a
  have : η x < η y := hy
  linarith

omit [TopologicalSpace X] in
/-- The height strictly increases along orbit segments inside `U`. -/
theorem lt_of_rate_of_lt {Φ : ℝ → X → X} (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    {η : X → ℝ} {U : Set X} {κ : ℝ} (hκ : 0 < κ)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (hU : ∀ s ∈ Icc t₁ t₂, Φ s x ∈ U) :
    η (Φ t₁ x) < η (Φ t₂ x) := by
  have h := hrate (Φ t₁ x) (t₂ - t₁) (by linarith) fun s hs => by
    rw [← hΦadd]
    exact hU (s + t₁) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rw [← hΦadd, sub_add_cancel] at h
  nlinarith

/-- **Level connectivity.** A level `{η = c}` is path connected if it is nonempty, any two of its
points are joined inside the band `η⁻¹[a, b]`, and the hitting time of level `c` is continuous on
the band with the usual specification. -/
theorem isPathConnected_level_of_hittingTime {Φ : ℝ → X → X}
    (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2)) (hΦ0 : ∀ x, Φ 0 x = x) {η : X → ℝ}
    {a b c : ℝ} (hc : c ∈ Icc a b)
    (hcont : ContinuousOn (fun p : X × ℝ => hittingTime Φ η p.1 p.2) ((η ⁻¹' Icc a b) ×ˢ Icc a b))
    (hspec : ∀ x, η x ∈ Icc a b → η (Φ (hittingTime Φ η x c) x) = c)
    (hself : ∀ x, η x = c → hittingTime Φ η x c = 0) (hne : ∃ x, η x = c)
    (hjoin : ∀ x y, η x = c → η y = c → JoinedIn (η ⁻¹' Icc a b) x y) :
    IsPathConnected {x | η x = c} := by
  refine isPathConnected_iff.2 ⟨hne, fun x hx y hy => ?_⟩
  have hJ := hjoin x y hx hy
  set γ := hJ.somePath with hγ
  have hγmem : ∀ t, γ t ∈ η ⁻¹' Icc a b := hJ.somePath_mem
  have hτ : Continuous (fun t : unitInterval => hittingTime Φ η (γ t) c) := by
    have h1 : Continuous (fun t : unitInterval => ((γ t, c) : X × ℝ)) :=
      γ.continuous.prodMk continuous_const
    exact hcont.comp_continuous h1 fun t => ⟨hγmem t, hc⟩
  refine ⟨⟨⟨fun t => Φ (hittingTime Φ η (γ t) c) (γ t), hΦ.comp (hτ.prodMk γ.continuous)⟩,
    ?_, ?_⟩, fun t => hspec (γ t) (hγmem t)⟩
  · change Φ (hittingTime Φ η (γ 0) c) (γ 0) = x
    rw [γ.source, hself x hx, hΦ0]
  · change Φ (hittingTime Φ η (γ 1) c) (γ 1) = y
    rw [γ.target, hself y hy, hΦ0]

/-- **A cross-section of a band product.** Let `e : P × [a, b] → X` be continuous and injective,
`P` compact and Hausdorff, and let `F : X → ℝ` be continuous, strictly increasing
along every fibre `s ↦ e (p, s)`, below `s₀` on the bottom and above `s₀` on the top. Then some
continuous injective `c : P → X` has range `{x ∈ range e | F x = s₀}` (hence is an embedding onto
the level). -/
theorem exists_embedding_level_of_band_product {P : Type*} [TopologicalSpace P] [CompactSpace P]
    [T2Space P] {a b : ℝ} (hab : a ≤ b) {e : P × Icc a b → X} (he : Continuous e)
    (heinj : Function.Injective e) {F : X → ℝ} (hF : Continuous F) {s₀ : ℝ}
    (hmono : ∀ p, StrictMono (fun s : Icc a b => F (e (p, s))))
    (hlow : ∀ p, F (e (p, ⟨a, left_mem_Icc.2 hab⟩)) < s₀)
    (hhigh : ∀ p, s₀ < F (e (p, ⟨b, right_mem_Icc.2 hab⟩))) :
    ∃ c : P → X, Continuous c ∧ Function.Injective c ∧
      range c = {x | x ∈ range e ∧ F x = s₀} := by
  set G : Set (P × Icc a b) := {q | F (e q) = s₀} with hG
  have hGc : IsClosed G := isClosed_eq (hF.comp he) continuous_const
  have : CompactSpace G := isCompact_iff_compactSpace.1 hGc.isCompact
  -- existence of a root on every fibre
  have hex : ∀ p, ∃ s : Icc a b, F (e (p, s)) = s₀ := by
    intro p
    set f : ℝ → ℝ := fun s => F (e (p, projIcc a b hab s)) with hf
    have hfc : ContinuousOn f (Icc a b) :=
      (hF.comp (he.comp (continuous_const.prodMk continuous_projIcc))).continuousOn
    have hfa : f a = F (e (p, ⟨a, left_mem_Icc.2 hab⟩)) := by rw [hf]; simp [projIcc_left]
    have hfb : f b = F (e (p, ⟨b, right_mem_Icc.2 hab⟩)) := by rw [hf]; simp [projIcc_right]
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab hfc
      ⟨(hfa ▸ hlow p).le, (hfb ▸ hhigh p).le⟩
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [← hfs, hf]
    simp only [projIcc_of_mem hab hs]
  -- the projection `G → P` is a continuous bijection
  set π : G → P := fun q => q.1.1 with hπ
  have hπc : Continuous π := continuous_fst.comp continuous_subtype_val
  have hπbij : Function.Bijective π := by
    refine ⟨fun q q' hqq' => ?_, fun p => ?_⟩
    · obtain ⟨⟨p, s⟩, hq⟩ := q
      obtain ⟨⟨p', s'⟩, hq'⟩ := q'
      change p = p' at hqq'
      subst hqq'
      have hs : s = s' := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have := hmono p h
          change F (e (p, s)) = s₀ at hq
          change F (e (p, s')) = s₀ at hq'
          linarith
        · have := hmono p h
          change F (e (p, s)) = s₀ at hq
          change F (e (p, s')) = s₀ at hq'
          linarith
      subst hs
      rfl
    · obtain ⟨s, hs⟩ := hex p
      exact ⟨⟨(p, s), hs⟩, rfl⟩
  set h : G ≃ₜ P := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective π hπbij) hπc with hh
  refine ⟨fun p => e (h.symm p).1, he.comp (continuous_subtype_val.comp h.symm.continuous),
    fun p p' hpp' => h.symm.injective (Subtype.ext (heinj hpp')), ?_⟩
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨_, rfl⟩, (h.symm p).2⟩
  · rintro ⟨⟨q, rfl⟩, hq⟩
    refine ⟨h ⟨q, hq⟩, ?_⟩
    change e (h.symm (h ⟨q, hq⟩)).1 = e q
    rw [h.symm_apply_apply]

end DifferentialGeometry.Geometry.Collapse
