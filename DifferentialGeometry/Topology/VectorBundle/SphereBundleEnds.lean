import DifferentialGeometry.Topology.VectorBundle.ClosedDiscCompact
import DifferentialGeometry.Bundle.Homotopy
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Ends of the total space of a Riemannian vector bundle over a compact base (LFR52)

Frozen blueprint master207A, lemma `lem:collapse-twisted-core-identifications` (LFR52, lines
29425–29436): "its closed radius-`R` disk bundles are a cofinal compact exhaustion … Hence its
number of ends is the number of components of the unit sphere bundle. Rank at least two gives a
connected sphere bundle over the connected base." LFR54 (lines 29547–29548): "LFR52 and LC77 exclude
its two trivial surface-line bundles".

The end count is stated in the language of LC77 (`exists_selected_model_one_end_parameter`): for a
homeomorphism `e` of the total space onto a proper metric space `N`,

* `unbounded_components_eq_of_isPreconnected_sphereBundle`: if the unit sphere bundle is
  preconnected, then for every compact `K ⊆ N` all unbounded components of `Kᶜ` coincide;
* `exists_two_unbounded_components_of_not_isPreconnected`: otherwise some compact `K` has two
  different unbounded components of `Kᶜ`;
* `isPreconnected_sphereBundle_iff`: the two statements combined;
* `isConnected_sphereBundle_of_one_lt_finrank`: rank `≥ 2` over a connected base gives a connected
  unit sphere bundle (rows `ℝ³`, `S¹ × ℝ²` have one end);
* `not_isPreconnected_sphereBundle_trivial_real`: the trivial line bundle has a disconnected unit
  sphere bundle (rows `S² × ℝ`, `T² × ℝ` have two ends).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Topology

namespace DifferentialGeometry.Topology.VectorBundle


variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
  {N : Type*} [MetricSpace N] [ProperSpace N]

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V] in
private theorem norm_smul_unit {u : TotalSpace F V} (hu : ‖u.2‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖((⟨u.proj, t • u.2⟩ : TotalSpace F V)).2‖ = t := by
  change ‖t • u.2‖ = t
  rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonneg ht]

omit [FiniteDimensional ℝ F] [IsContinuousRiemannianBundle F V] in
/-- Outside the closed `T`-disc bundle (`T ≥ 0`) the total space is the radial image of the unit
sphere bundle; hence it is preconnected when the unit sphere bundle is. -/
theorem isPreconnected_outside_of_isPreconnected_sphereBundle
    (hS : IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) {T : ℝ} (hT : 0 ≤ T) :
    IsPreconnected {z : TotalSpace F V | T < ‖z.2‖} := by
  have himage : {z : TotalSpace F V | T < ‖z.2‖} =
      (fun p : TotalSpace F V × ℝ => (⟨p.1.proj, p.2 • p.1.2⟩ : TotalSpace F V)) ''
        ({z : TotalSpace F V | ‖z.2‖ = 1} ×ˢ Ioi T) := by
    ext z
    constructor
    · intro hz
      have hz' : T < ‖z.2‖ := hz
      have hpos : 0 < ‖z.2‖ := hT.trans_lt hz'
      refine ⟨(⟨z.proj, ‖z.2‖⁻¹ • z.2⟩, ‖z.2‖), ⟨?_, hz'⟩, ?_⟩
      · change ‖‖z.2‖⁻¹ • z.2‖ = 1
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      · change (⟨z.proj, ‖z.2‖ • ‖z.2‖⁻¹ • z.2⟩ : TotalSpace F V) = z
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have ht' : T < t := ht
      change T < ‖((⟨u.proj, t • u.2⟩ : TotalSpace F V)).2‖
      rw [norm_smul_unit hu (hT.trans ht'.le)]
      exact ht'
  rw [himage]
  exact (hS.prod isPreconnected_Ioi).image _
    ((_root_.VectorBundle.continuous_totalSpace_smul (𝕜 := ℝ) (F := F) (V := V)).comp
      (continuous_snd.prodMk continuous_fst)).continuousOn

omit [FiniteDimensional ℝ F] in
/-- A subset of `N` on which the transported fibre radius is unbounded is not bounded. -/
theorem not_isBounded_of_forall_exists_norm_gt (e : TotalSpace F V ≃ₜ N) {A : Set N}
    (hA : ∀ M : ℝ, ∃ x ∈ A, M < ‖(e.symm x).2‖) : ¬ Bornology.IsBounded A := by
  intro hbdd
  have hc : IsCompact (closure A) := hbdd.isCompact_closure
  have hr : Continuous (fun x : N => ‖(e.symm x).2‖) :=
    continuous_fiberRadius.comp e.symm.continuous
  obtain ⟨M, hM⟩ := (hc.image hr).bddAbove
  obtain ⟨x, hx, hxM⟩ := hA M
  exact (hM ⟨x, subset_closure hx, rfl⟩).not_gt hxM

omit [FiniteDimensional ℝ F] in
/-- The ray `t ↦ t • u` (`t > c`) through a unit vector, transported to `N`, is preconnected and
unbounded. -/
theorem isPreconnected_and_not_isBounded_ray (e : TotalSpace F V ≃ₜ N) {u : TotalSpace F V}
    (hu : ‖u.2‖ = 1) (c : ℝ) :
    IsPreconnected ((fun t : ℝ => e ⟨u.proj, t • u.2⟩) '' Ioi c) ∧
      ¬ Bornology.IsBounded ((fun t : ℝ => e ⟨u.proj, t • u.2⟩) '' Ioi c) := by
  have hcont : Continuous (fun t : ℝ => e ⟨u.proj, t • u.2⟩) :=
    e.continuous.comp
      ((_root_.VectorBundle.continuous_totalSpace_smul (𝕜 := ℝ) (F := F) (V := V)).comp
      (continuous_id.prodMk continuous_const))
  refine ⟨isPreconnected_Ioi.image _ hcont.continuousOn, ?_⟩
  apply not_isBounded_of_forall_exists_norm_gt e
  intro M
  refine ⟨e ⟨u.proj, (max M c + 1 + |M|) • u.2⟩, ⟨max M c + 1 + |M|, ?_, rfl⟩, ?_⟩
  · change c < max M c + 1 + |M|
    have := le_max_right M c
    have := abs_nonneg M
    linarith
  · rw [e.symm_apply_apply, norm_smul_unit hu (by
      have := le_max_left M c
      have := neg_abs_le M
      linarith)]
    have := le_max_left M c
    have := abs_nonneg M
    linarith

variable [CompactSpace B]

omit [ProperSpace N] in
/-- **LFR52 one end, LC77 form.** If the unit sphere bundle is preconnected, then for every compact
`K ⊆ N` all unbounded connected components of `Kᶜ` coincide. -/
theorem unbounded_components_eq_of_isPreconnected_sphereBundle (e : TotalSpace F V ≃ₜ N)
    (hS : IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) (K : Set N) (hK : IsCompact K)
    (a b : N) (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b)) :
    connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  have hr : Continuous (fun x : N => ‖(e.symm x).2‖) :=
    continuous_fiberRadius.comp e.symm.continuous
  obtain ⟨T₀, hT₀⟩ := (hK.image hr).bddAbove
  set T := max T₀ 0 with hTdef
  have hT : 0 ≤ T := le_max_right _ _
  let O : Set N := e '' {z : TotalSpace F V | T < ‖z.2‖}
  have hO : IsPreconnected O :=
    (isPreconnected_outside_of_isPreconnected_sphereBundle hS hT).image _ e.continuous.continuousOn
  have hOK : O ⊆ Kᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzK
    have h1 : ‖(e.symm (e z)).2‖ ≤ T₀ := hT₀ ⟨e z, hzK, rfl⟩
    rw [e.symm_apply_apply] at h1
    exact (lt_irrefl T) (hz.trans_le (h1.trans (le_max_left _ _)))
  have hD : Bornology.IsBounded (e '' {z : TotalSpace F V | ‖z.2‖ ≤ T}) :=
    (isCompact_transportedClosedDiscBundle e T).isBounded
  have hmeet : ∀ c : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ c) →
      ∃ x ∈ O, x ∈ connectedComponentIn Kᶜ c := by
    intro c hc
    have hnot : ¬ connectedComponentIn Kᶜ c ⊆ e '' {z : TotalSpace F V | ‖z.2‖ ≤ T} :=
      fun hsub => hc (hD.subset hsub)
    obtain ⟨x, hxc, hxD⟩ := not_subset.mp hnot
    refine ⟨x, ⟨e.symm x, ?_, e.apply_symm_apply x⟩, hxc⟩
    change T < ‖(e.symm x).2‖
    by_contra hle
    exact hxD ⟨e.symm x, not_lt.mp hle, e.apply_symm_apply x⟩
  obtain ⟨x, hxO, hxa⟩ := hmeet a ha
  obtain ⟨y, hyO, hyb⟩ := hmeet b hb
  have hxy : y ∈ connectedComponentIn Kᶜ x :=
    hO.subset_connectedComponentIn hxO hOK hyO
  rw [connectedComponentIn_eq hxa, connectedComponentIn_eq hyb, connectedComponentIn_eq hxy]

/-- **LFR52 at least two ends.** If the unit sphere bundle is not preconnected, some compact
`K ⊆ N` has two different unbounded connected components of `Kᶜ`. -/
theorem exists_two_unbounded_components_of_not_isPreconnected (e : TotalSpace F V ≃ₜ N)
    (hS : ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    ∃ K : Set N, IsCompact K ∧ ∃ a b : N,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) ∧
      connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b := by
  set S := {z : TotalSpace F V | ‖z.2‖ = 1} with hSdef
  obtain ⟨u, v, hu, hv, hSuv, ⟨p, hpS, hpu⟩, ⟨q, hqS, hqv⟩, huv⟩ : ∃ u v : Set (TotalSpace F V),
      IsOpen u ∧ IsOpen v ∧ S ⊆ u ∪ v ∧ (S ∩ u).Nonempty ∧ (S ∩ v).Nonempty ∧
        ¬ (S ∩ (u ∩ v)).Nonempty := by
    simpa only [IsPreconnected, not_forall, exists_prop] using hS
  let K : Set N := e '' {z : TotalSpace F V | ‖z.2‖ ≤ 1}
  have hK : IsCompact K := isCompact_transportedClosedDiscBundle e 1
  -- radial normalization on the outside of the unit disc bundle
  let ρ : TotalSpace F V → TotalSpace F V := fun z => ⟨z.proj, ‖z.2‖⁻¹ • z.2⟩
  let Out : Set (TotalSpace F V) := {z | 1 < ‖z.2‖}
  have hρc : ContinuousOn ρ Out := by
    have hn : ContinuousOn (fun z : TotalSpace F V => ‖z.2‖⁻¹) Out :=
      continuous_fiberRadius.continuousOn.inv₀ fun z hz => (zero_lt_one.trans hz).ne'
    exact
      (_root_.VectorBundle.continuous_totalSpace_smul (𝕜 := ℝ) (F := F) (V := V)).comp_continuousOn
      (hn.prodMk continuousOn_id)
  have hρS : ∀ z ∈ Out, ρ z ∈ S := by
    intro z hz
    have hpos : 0 < ‖z.2‖ := zero_lt_one.trans hz
    change ‖‖z.2‖⁻¹ • z.2‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
  have hKc : ∀ x, x ∈ Kᶜ ↔ e.symm x ∈ Out := by
    intro x
    constructor
    · intro hx
      change 1 < ‖(e.symm x).2‖
      by_contra hle
      exact hx ⟨e.symm x, not_lt.mp hle, e.apply_symm_apply x⟩
    · rintro hx ⟨z, hz, rfl⟩
      rw [e.symm_apply_apply] at hx
      exact (lt_irrefl (1 : ℝ)) (hx.trans_le hz)
  -- the normalized image of a component meets only one side
  have hside : ∀ c : N, c ∈ Kᶜ →
      IsPreconnected (ρ '' (e.symm '' connectedComponentIn Kᶜ c)) ∧
        ρ '' (e.symm '' connectedComponentIn Kᶜ c) ⊆ S ∧
        ρ (e.symm c) ∈ ρ '' (e.symm '' connectedComponentIn Kᶜ c) := by
    intro c hc
    have hsub : e.symm '' connectedComponentIn Kᶜ c ⊆ Out := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hKc x).mp (connectedComponentIn_subset _ _ hx)
    refine ⟨((isPreconnected_connectedComponentIn).image _
      e.symm.continuous.continuousOn).image _ (hρc.mono hsub), ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hρS z (hsub hz)
    · exact ⟨e.symm c, ⟨c, mem_connectedComponentIn hc, rfl⟩, rfl⟩
  have hone : ∀ c : N, c ∈ Kᶜ → ρ (e.symm c) ∈ u →
      ¬ (ρ '' (e.symm '' connectedComponentIn Kᶜ c) ∩ v).Nonempty := by
    intro c hc hcu hcv
    obtain ⟨hpre, hsubS, hmem⟩ := hside c hc
    obtain ⟨y, hy, hyuv⟩ := hpre u v hu hv (hsubS.trans hSuv) ⟨_, hmem, hcu⟩ hcv
    exact huv ⟨y, hsubS hy, hyuv⟩
  -- the two base points
  let a : N := e ⟨p.proj, (2 : ℝ) • p.2⟩
  let b : N := e ⟨q.proj, (2 : ℝ) • q.2⟩
  have hp1 : ‖p.2‖ = 1 := hpS
  have hq1 : ‖q.2‖ = 1 := hqS
  have hρa : ρ (e.symm a) = p := by
    change ρ (e.symm (e ⟨p.proj, (2 : ℝ) • p.2⟩)) = p
    rw [e.symm_apply_apply]
    change (⟨p.proj, ‖(2 : ℝ) • p.2‖⁻¹ • (2 : ℝ) • p.2⟩ : TotalSpace F V) = p
    rw [norm_smul, hp1, mul_one, Real.norm_two, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hρb : ρ (e.symm b) = q := by
    change ρ (e.symm (e ⟨q.proj, (2 : ℝ) • q.2⟩)) = q
    rw [e.symm_apply_apply]
    change (⟨q.proj, ‖(2 : ℝ) • q.2‖⁻¹ • (2 : ℝ) • q.2⟩ : TotalSpace F V) = q
    rw [norm_smul, hq1, mul_one, Real.norm_two, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have haK : a ∈ Kᶜ := by
    rw [hKc]
    change 1 < ‖(e.symm (e ⟨p.proj, (2 : ℝ) • p.2⟩)).2‖
    rw [e.symm_apply_apply, norm_smul_unit hp1 zero_le_two]
    norm_num
  have hbK : b ∈ Kᶜ := by
    rw [hKc]
    change 1 < ‖(e.symm (e ⟨q.proj, (2 : ℝ) • q.2⟩)).2‖
    rw [e.symm_apply_apply, norm_smul_unit hq1 zero_le_two]
    norm_num
  -- each component contains an unbounded ray
  have hunb : ∀ (w : TotalSpace F V), ‖w.2‖ = 1 → e ⟨w.proj, (2 : ℝ) • w.2⟩ ∈ Kᶜ →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ (e ⟨w.proj, (2 : ℝ) • w.2⟩)) := by
    intro w hw hwK hbdd
    obtain ⟨hpre, hnb⟩ := isPreconnected_and_not_isBounded_ray e hw 1
    have hray : (fun t : ℝ => e ⟨w.proj, t • w.2⟩) '' Ioi 1 ⊆ Kᶜ := by
      rintro _ ⟨t, ht, rfl⟩
      rw [hKc, e.symm_apply_apply]
      change 1 < ‖((⟨w.proj, t • w.2⟩ : TotalSpace F V)).2‖
      rw [norm_smul_unit hw (zero_le_one.trans (le_of_lt ht))]
      exact ht
    have h2 : e ⟨w.proj, (2 : ℝ) • w.2⟩ ∈ (fun t : ℝ => e ⟨w.proj, t • w.2⟩) '' Ioi 1 :=
      ⟨2, by norm_num, rfl⟩
    exact hnb (hbdd.subset (hpre.subset_connectedComponentIn h2 hray))
  refine ⟨K, hK, a, b, hunb p hp1 haK, hunb q hq1 hbK, fun heq => ?_⟩
  have hbmem : ρ (e.symm b) ∈ ρ '' (e.symm '' connectedComponentIn Kᶜ a) := by
    rw [heq]
    exact (hside b hbK).2.2
  apply hone a haK (by rw [hρa]; exact hpu)
  exact ⟨_, hbmem, by rw [hρb]; exact hqv⟩

/-- **LFR52 end count in LC77's language.** The unit sphere bundle is preconnected iff for every
compact `K ⊆ N` all unbounded connected components of `Kᶜ` coincide. -/
theorem isPreconnected_sphereBundle_iff (e : TotalSpace F V ≃ₜ N) :
    IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1} ↔
      ∀ K : Set N, IsCompact K → ∀ a b : N,
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  refine ⟨fun hS K hK a b ha hb =>
    unbounded_components_eq_of_isPreconnected_sphereBundle e hS K hK a b ha hb, fun h => ?_⟩
  by_contra hS
  obtain ⟨K, hK, a, b, ha, hb, hne⟩ := exists_two_unbounded_components_of_not_isPreconnected e hS
  exact hne (h K hK a b ha hb)

omit [CompactSpace B] in
/-- **LFR52, rank at least two.** Over a connected base, a Riemannian bundle of rank `≥ 2` has a
connected unit sphere bundle (its fibres are connected spheres and the projection is open). -/
theorem isConnected_sphereBundle_of_one_lt_finrank [ConnectedSpace B]
    (hF : 1 < Module.finrank ℝ F) : IsConnected {z : TotalSpace F V | ‖z.2‖ = 1} := by
  set S := {z : TotalSpace F V | ‖z.2‖ = 1} with hSdef
  let p : S → B := fun z => z.1.proj
  have hpc : Continuous p := (FiberBundle.continuous_proj F V).comp continuous_subtype_val
  have hfin : ∀ b : B, Module.finrank ℝ (V b) = Module.finrank ℝ F := fun b =>
    ((trivializationAt F V b).continuousLinearEquivAt ℝ b
      (FiberBundle.mem_baseSet_trivializationAt' b)).toLinearEquiv.finrank_eq
  have hfd : ∀ b : B, FiniteDimensional ℝ (V b) := fun b =>
    ((trivializationAt F V b).continuousLinearEquivAt ℝ b
      (FiberBundle.mem_baseSet_trivializationAt' b)).toLinearEquiv.symm.finiteDimensional
  -- fibres are spheres of dimension `≥ 1`
  have hfib : ∀ b : B, IsConnected (p ⁻¹' {b}) := by
    intro b
    have hrank : 1 < Module.rank ℝ (V b) := by
      rw [← Module.finrank_eq_rank, hfin b]
      exact_mod_cast hF
    have hsph : IsConnected (Metric.sphere (0 : V b) 1) := isConnected_sphere hrank 0 zero_le_one
    have : ConnectedSpace (Metric.sphere (0 : V b) 1) := isConnected_iff_connectedSpace.mp hsph
    let f : Metric.sphere (0 : V b) 1 → S := fun v =>
      ⟨⟨b, v.1⟩, by
        change ‖v.1‖ = 1
        exact norm_eq_of_mem_sphere v⟩
    have hf : Continuous f :=
      ((FiberBundle.totalSpaceMk_isInducing F V b).continuous.comp
        continuous_subtype_val).subtype_mk _
    have hrange : range f = p ⁻¹' {b} := by
      ext z
      constructor
      · rintro ⟨v, rfl⟩
        rfl
      · intro hz
        obtain ⟨⟨b', w⟩, hw⟩ := z
        change b' = b at hz
        subst hz
        refine ⟨⟨w, mem_sphere_zero_iff_norm.mpr hw⟩, rfl⟩
    rw [← hrange]
    exact isConnected_range hf
  -- the projection is surjective
  have hsurj : Function.Surjective p := by
    intro b
    have : Nontrivial (V b) := Module.nontrivial_of_finrank_pos (by rw [hfin b]; omega)
    obtain ⟨v, hv⟩ := exists_norm_eq (V b) zero_le_one
    exact ⟨⟨⟨b, v⟩, hv⟩, rfl⟩
  -- the projection is open: normalized local sections through every point
  have hopen : IsOpenMap p := by
    intro O hO
    obtain ⟨O', hO', hOO'⟩ := isOpen_induced_iff.mp hO
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hzO, rfl⟩
    let b₀ := z.1.proj
    let et := trivializationAt F V b₀
    have hb₀ : b₀ ∈ et.baseSet := FiberBundle.mem_baseSet_trivializationAt' b₀
    let c : F := (et z.1).2
    let σ₀ : B → TotalSpace F V := fun b => et.toPartialHomeomorph.symm (b, c)
    have hzsrc : z.1 ∈ et.source := et.mem_source.mpr hb₀
    have het : et z.1 = (b₀, c) := Prod.ext (et.coe_fst hzsrc) rfl
    have hσ₀b₀ : σ₀ b₀ = z.1 := by
      change et.toPartialHomeomorph.symm (b₀, c) = z.1
      rw [← het]
      exact et.toPartialHomeomorph.left_inv hzsrc
    have htgt : (b₀, c) ∈ et.target := et.mem_target.mpr hb₀
    have hσ₀c : ContinuousAt σ₀ b₀ := by
      have h1 : ContinuousAt et.toPartialHomeomorph.symm (b₀, c) :=
        et.toPartialHomeomorph.continuousOn_symm.continuousAt (et.open_target.mem_nhds htgt)
      have h2 : ContinuousAt (fun b : B => (b, c)) b₀ := continuousAt_id.prodMk continuousAt_const
      exact ContinuousAt.comp (x := b₀) h1 h2
    have hz1 : ‖z.1.2‖ = 1 := z.2
    have hnorm : ContinuousAt (fun b => ‖(σ₀ b).2‖) b₀ :=
      continuous_fiberRadius.continuousAt.comp hσ₀c
    have hne : ‖(σ₀ b₀).2‖ ≠ 0 := by rw [hσ₀b₀, hz1]; exact one_ne_zero
    let σ : B → TotalSpace F V := fun b => ⟨(σ₀ b).proj, ‖(σ₀ b).2‖⁻¹ • (σ₀ b).2⟩
    have hσc : ContinuousAt σ b₀ :=
      (_root_.VectorBundle.continuous_totalSpace_smul (𝕜 := ℝ) (F := F) (V := V)).continuousAt.comp
        ((hnorm.inv₀ hne).prodMk hσ₀c)
    have hσb₀ : σ b₀ = z.1 := by
      change (⟨(σ₀ b₀).proj, ‖(σ₀ b₀).2‖⁻¹ • (σ₀ b₀).2⟩ : TotalSpace F V) = z.1
      rw [hσ₀b₀, hz1, inv_one, one_smul]
    have hzO' : z.1 ∈ O' := by
      have : z ∈ Subtype.val ⁻¹' O' := hOO'.symm ▸ hzO
      exact this
    have hev1 : ∀ᶠ b in 𝓝 b₀, σ b ∈ O' := hσc (hσb₀ ▸ hO'.mem_nhds hzO')
    have hev2 : ∀ᶠ b in 𝓝 b₀, b ∈ et.baseSet := et.open_baseSet.mem_nhds hb₀
    have hev3 : ∀ᶠ b in 𝓝 b₀, ‖(σ₀ b).2‖ ≠ 0 := hnorm.eventually_ne hne
    filter_upwards [hev1, hev2, hev3] with b h1 h2 h3
    have hσS : σ b ∈ S := by
      change ‖‖(σ₀ b).2‖⁻¹ • (σ₀ b).2‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h3]
    have hproj : (σ b).proj = b := by
      change (et.toPartialHomeomorph.symm (b, c)).proj = b
      exact et.proj_symm_apply (et.mem_target.mpr h2)
    refine ⟨⟨σ b, hσS⟩, ?_, hproj⟩
    rw [← hOO']
    exact h1
  have hq : Topology.IsQuotientMap p := hopen.isQuotientMap hpc hsurj
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  obtain ⟨z, -⟩ := hsurj b
  have hcc : connectedComponent z = univ := by
    rw [← hq.preimage_connectedComponent hfib z, PreconnectedSpace.connectedComponent_eq_univ,
      preimage_univ]
  have : ConnectedSpace S := connectedSpace_iff_connectedComponent.mpr ⟨z, hcc⟩
  exact isConnected_iff_connectedSpace.mpr this

end DifferentialGeometry.Topology.VectorBundle
