import DifferentialGeometry.Topology.VectorBundle.SphereBundleEnds

/-!
# Exact end counts of Riemannian vector bundles over a compact base (LFR52)

Lane LFR54-ROW, group G3. Frozen blueprint master207A, LFR52 (A:29386–29387, proof A:29425–29436):
"The first, second, fifth and sixth total spaces in (LFR51.1) have one end; the third and fourth have
two ends … its number of ends is the number of components of the unit sphere bundle."

In LC77's language (a homeomorphism `e : TotalSpace F V ≃ₜ N` onto a proper metric space, unbounded
connected components of complements of compact sets; F7-LFR51 G2 gives the `≤ 1` and `≥ 2`
directions):

* `exists_unbounded_component_of_nonempty_sphereBundle`: if the unit sphere bundle is nonempty,
  every compact `K ⊆ N` has an unbounded component of `Kᶜ` (a radial ray);
* `unbounded_components_two_of_sphereBundle_subset_union`: if the unit sphere bundle is covered by
  two preconnected subsets, any three unbounded components of `Kᶜ` contain two equal ones;
* `exactly_one_end_of_isConnected_sphereBundle`: connected unit sphere bundle ⇒ exactly one end;
* `exactly_two_ends_of_sphereBundle_eq_union`: unit sphere bundle = union of two preconnected sets
  and not preconnected ⇒ exactly two ends.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Topology

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

open DifferentialGeometry.Topology.VectorBundle

variable {B : Type*} [TopologicalSpace B] [CompactSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
  {N : Type*} [MetricSpace N]

omit [CompactSpace B] [FiniteDimensional ℝ F] [IsContinuousRiemannianBundle F V] in
/-- The radial image `{t • u : u ∈ P, t > T}` of a preconnected set of unit vectors is
preconnected. -/
theorem isPreconnected_radialImage {P : Set (TotalSpace F V)} (hP : IsPreconnected P) (T : ℝ) :
    IsPreconnected ((fun p : TotalSpace F V × ℝ => (⟨p.1.proj, p.2 • p.1.2⟩ : TotalSpace F V)) ''
      (P ×ˢ Ioi T)) :=
  (hP.prod isPreconnected_Ioi).image _
    ((_root_.VectorBundle.continuous_totalSpace_smul (𝕜 := ℝ) (F := F) (V := V)).comp
      (continuous_snd.prodMk continuous_fst)).continuousOn

/-- An unbounded component of `Kᶜ` meets the transported outside `{T < ‖z‖}` of any disc bundle. -/
theorem exists_mem_component_radius_gt (e : TotalSpace F V ≃ₜ N) (K : Set N) (T : ℝ) (c : N)
    (hc : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ c)) :
    ∃ x ∈ connectedComponentIn Kᶜ c, T < ‖(e.symm x).2‖ := by
  have hD : Bornology.IsBounded (e '' {z : TotalSpace F V | ‖z.2‖ ≤ T}) :=
    (isCompact_transportedClosedDiscBundle e T).isBounded
  have hnot : ¬ connectedComponentIn Kᶜ c ⊆ e '' {z : TotalSpace F V | ‖z.2‖ ≤ T} :=
    fun hsub => hc (hD.subset hsub)
  obtain ⟨x, hxc, hxD⟩ := not_subset.mp hnot
  refine ⟨x, hxc, ?_⟩
  by_contra hle
  exact hxD ⟨e.symm x, not_lt.mp hle, e.apply_symm_apply x⟩

omit [CompactSpace B] [FiniteDimensional ℝ F] in
/-- **At least one end.** If the unit sphere bundle is nonempty, every compact `K ⊆ N` has an
unbounded connected component of `Kᶜ`. -/
theorem exists_unbounded_component_of_nonempty_sphereBundle [ProperSpace N]
    (e : TotalSpace F V ≃ₜ N) (hne : {z : TotalSpace F V | ‖z.2‖ = 1}.Nonempty) (K : Set N) (hK : IsCompact K) :
    ∃ a : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) := by
  obtain ⟨u, hu⟩ := hne
  have hr : Continuous (fun x : N => ‖(e.symm x).2‖) :=
    continuous_fiberRadius.comp e.symm.continuous
  obtain ⟨T₀, hT₀⟩ := (hK.image hr).bddAbove
  set T := max T₀ 0 with hTdef
  have hT : 0 ≤ T := le_max_right _ _
  obtain ⟨hpre, hunb⟩ := isPreconnected_and_not_isBounded_ray e hu T
  let R : Set N := (fun t : ℝ => e ⟨u.proj, t • u.2⟩) '' Ioi T
  have hRK : R ⊆ Kᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hK'
    have h1 : ‖(e.symm (e ⟨u.proj, t • u.2⟩)).2‖ ≤ T₀ := hT₀ ⟨_, hK', rfl⟩
    rw [Homeomorph.symm_apply_apply] at h1
    change ‖t • u.2‖ ≤ T₀ at h1
    have ht' : T < t := ht
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (hT.trans_lt ht')] at h1
    exact (lt_irrefl T) (ht'.trans_le (h1.trans (le_max_left _ _)))
  have ha : e ⟨u.proj, (T + 1) • u.2⟩ ∈ R := ⟨T + 1, by simp [Set.mem_Ioi], rfl⟩
  refine ⟨e ⟨u.proj, (T + 1) • u.2⟩, fun hb => hunb (hb.subset ?_)⟩
  exact hpre.subset_connectedComponentIn ha hRK

/-- **At most two ends.** If the unit sphere bundle is covered by two preconnected sets of unit
vectors, then for every compact `K ⊆ N`, of any three unbounded components of `Kᶜ` two coincide. -/
theorem unbounded_components_two_of_sphereBundle_subset_union (e : TotalSpace F V ≃ₜ N)
    {P Q : Set (TotalSpace F V)} (hP : IsPreconnected P) (hQ : IsPreconnected Q)
    (hPS : P ⊆ {z : TotalSpace F V | ‖z.2‖ = 1}) (hQS : Q ⊆ {z : TotalSpace F V | ‖z.2‖ = 1})
    (hS : {z : TotalSpace F V | ‖z.2‖ = 1} ⊆ P ∪ Q) (K : Set N) (hK : IsCompact K) (a b c : N)
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b))
    (hc : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ c)) :
    connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b ∨
      connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ c ∨
      connectedComponentIn Kᶜ b = connectedComponentIn Kᶜ c := by
  have hr : Continuous (fun x : N => ‖(e.symm x).2‖) :=
    continuous_fiberRadius.comp e.symm.continuous
  obtain ⟨T₀, hT₀⟩ := (hK.image hr).bddAbove
  set T := max T₀ 0 with hTdef
  have hT : 0 ≤ T := le_max_right _ _
  let rad : TotalSpace F V × ℝ → TotalSpace F V := fun p => ⟨p.1.proj, p.2 • p.1.2⟩
  -- the two radial pieces outside the disc of radius `T`
  let O : Set (TotalSpace F V) → Set N := fun W => e '' (rad '' (W ×ˢ Ioi T))
  have hOpre : ∀ W, IsPreconnected W → IsPreconnected (O W) := fun W hW =>
    (isPreconnected_radialImage hW T).image _ e.continuous.continuousOn
  have hOK : ∀ W, W ⊆ {z : TotalSpace F V | ‖z.2‖ = 1} → O W ⊆ Kᶜ := by
    rintro W hW _ ⟨_, ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩, rfl⟩ hzK
    have h1 : ‖(e.symm (e (rad (u, t)))).2‖ ≤ T₀ := hT₀ ⟨_, hzK, rfl⟩
    rw [Homeomorph.symm_apply_apply] at h1
    have hu1 : ‖u.2‖ = 1 := hW hu
    have ht' : T < t := ht
    change ‖t • u.2‖ ≤ T₀ at h1
    rw [norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_of_pos (hT.trans_lt ht')] at h1
    exact (lt_irrefl T) (ht'.trans_le (h1.trans (le_max_left _ _)))
  -- every unbounded component meets `O P` or `O Q`
  have hmeet : ∀ d : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ d) →
      (∃ x ∈ O P, x ∈ connectedComponentIn Kᶜ d) ∨ ∃ x ∈ O Q, x ∈ connectedComponentIn Kᶜ d := by
    intro d hd
    obtain ⟨x, hxd, hxT⟩ := exists_mem_component_radius_gt e K T d hd
    set z := e.symm x with hz
    have hpos : 0 < ‖z.2‖ := hT.trans_lt hxT
    let u : TotalSpace F V := ⟨z.proj, ‖z.2‖⁻¹ • z.2⟩
    have hu : ‖u.2‖ = 1 := by
      change ‖‖z.2‖⁻¹ • z.2‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    have hx : x = e (rad (u, ‖z.2‖)) := by
      change x = e ⟨z.proj, ‖z.2‖ • ‖z.2‖⁻¹ • z.2⟩
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      change x = e (e.symm x)
      rw [e.apply_symm_apply]
    rcases hS hu with huP | huQ
    · exact Or.inl ⟨x, by rw [hx]; exact ⟨_, ⟨(u, ‖z.2‖), ⟨huP, hxT⟩, rfl⟩, rfl⟩, hxd⟩
    · exact Or.inr ⟨x, by rw [hx]; exact ⟨_, ⟨(u, ‖z.2‖), ⟨huQ, hxT⟩, rfl⟩, rfl⟩, hxd⟩
  -- two components meeting the same preconnected piece coincide
  have hsame : ∀ W, IsPreconnected W → W ⊆ {z : TotalSpace F V | ‖z.2‖ = 1} → ∀ d₁ d₂ : N,
      (∃ x ∈ O W, x ∈ connectedComponentIn Kᶜ d₁) → (∃ x ∈ O W, x ∈ connectedComponentIn Kᶜ d₂) →
      connectedComponentIn Kᶜ d₁ = connectedComponentIn Kᶜ d₂ := by
    rintro W hW hWS d₁ d₂ ⟨x, hxO, hx1⟩ ⟨y, hyO, hy2⟩
    have hxy : y ∈ connectedComponentIn Kᶜ x :=
      (hOpre W hW).subset_connectedComponentIn hxO (hOK W hWS) hyO
    rw [connectedComponentIn_eq hx1, connectedComponentIn_eq hy2, connectedComponentIn_eq hxy]
  rcases hmeet a ha with hA | hA <;> rcases hmeet b hb with hB | hB <;>
    rcases hmeet c hc with hC | hC
  · exact Or.inl (hsame P hP hPS a b hA hB)
  · exact Or.inl (hsame P hP hPS a b hA hB)
  · exact Or.inr (Or.inl (hsame P hP hPS a c hA hC))
  · exact Or.inr (Or.inr (hsame Q hQ hQS b c hB hC))
  · exact Or.inr (Or.inr (hsame P hP hPS b c hB hC))
  · exact Or.inr (Or.inl (hsame Q hQ hQS a c hA hC))
  · exact Or.inl (hsame Q hQ hQS a b hA hB)
  · exact Or.inl (hsame Q hQ hQS a b hA hB)

/-- **Exactly one end.** A connected unit sphere bundle gives, for every compact `K ⊆ N`, an
unbounded component of `Kᶜ`, and all unbounded components of `Kᶜ` coincide. -/
theorem exactly_one_end_of_isConnected_sphereBundle (e : TotalSpace F V ≃ₜ N) [ProperSpace N]
    (hS : IsConnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    ∀ K : Set N, IsCompact K →
      (∃ a : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a)) ∧
      ∀ a b : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b :=
  fun K hK => ⟨exists_unbounded_component_of_nonempty_sphereBundle e hS.nonempty K hK,
    fun a b ha hb => unbounded_components_eq_of_isPreconnected_sphereBundle e hS.isPreconnected K hK
      a b ha hb⟩

/-- **Exactly two ends.** If the unit sphere bundle is the union of two preconnected sets but is not
preconnected, some compact `K ⊆ N` has two different unbounded components of `Kᶜ`, and for every
compact `K` any three unbounded components of `Kᶜ` contain two equal ones. -/
theorem exactly_two_ends_of_sphereBundle_eq_union (e : TotalSpace F V ≃ₜ N) [ProperSpace N]
    {P Q : Set (TotalSpace F V)} (hP : IsPreconnected P) (hQ : IsPreconnected Q)
    (hPQ : {z : TotalSpace F V | ‖z.2‖ = 1} = P ∪ Q)
    (hnc : ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    (∃ K : Set N, IsCompact K ∧ ∃ a b : N,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) ∧
      connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) ∧
    ∀ K : Set N, IsCompact K → ∀ a b c : N,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ c) →
      connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b ∨
      connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ c ∨
      connectedComponentIn Kᶜ b = connectedComponentIn Kᶜ c :=
  ⟨exists_two_unbounded_components_of_not_isPreconnected e hnc,
    fun K hK a b c ha hb hc => unbounded_components_two_of_sphereBundle_subset_union e hP hQ
      (hPQ ▸ subset_union_left) (hPQ ▸ subset_union_right) hPQ.subset K hK a b c ha hb hc⟩

end DifferentialGeometry.Geometry.Collapse.ZeroModel
