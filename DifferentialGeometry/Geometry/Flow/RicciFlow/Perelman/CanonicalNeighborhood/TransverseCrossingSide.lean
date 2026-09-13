import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseGeometry
import DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation (TwoSidedSeparation)

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]


private theorem isPathConnected_sphereTwo : IsPathConnected (Sphere 2) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by norm_num : (1 : ℕ) < 2 + 1)
  exact isPathConnected_sphere hrank 0 zero_le_one

private theorem sphereTwo_nonempty : (Sphere 2).Nonempty :=
  isPathConnected_sphereTwo.nonempty

private theorem isConnected_univ_sphereTwo : IsConnected (univ : Set (Sphere 2)) := by
  have : ConnectedSpace (Sphere 2) :=
    isConnected_iff_connectedSpace.mp isPathConnected_sphereTwo.isConnected
  exact isConnected_univ

def TransversePath.negativeBand {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : Set M :=
  c.collar '' (univ ×ˢ Ioo (-1 : ℝ) 0)

def TransversePath.positiveBand {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : Set M :=
  c.collar '' (univ ×ˢ Ioo (0 : ℝ) 1)

def TransversePath.collarStrip {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : Set M :=
  c.collar '' (univ ×ˢ Ioo (-1 : ℝ) 1)

omit [IsManifold I3 ∞ M] in
theorem TransversePath.strip_subset_source {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) :
    univ ×ˢ Ioo (-1 : ℝ) 1 ⊆ c.collar.source :=
  (Set.prod_mono (subset_refl _) Ioo_subset_Icc_self).trans c.collar_domain

omit [IsManifold I3 ∞ M] in
theorem TransversePath.negativeBand_subset_source {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) :
    univ ×ˢ Ioo (-1 : ℝ) 0 ⊆ c.collar.source :=
  (Set.prod_mono (subset_refl _) (fun x hx => (⟨by linarith [hx.1], by linarith [hx.2]⟩ :
    x ∈ Icc (-1 : ℝ) 1))).trans c.collar_domain

omit [IsManifold I3 ∞ M] in
theorem TransversePath.positiveBand_subset_source {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) :
    univ ×ˢ Ioo (0 : ℝ) 1 ⊆ c.collar.source :=
  (Set.prod_mono (subset_refl _) (fun x hx => (⟨by linarith [hx.1], by linarith [hx.2]⟩ :
    x ∈ Icc (-1 : ℝ) 1))).trans c.collar_domain

omit [IsManifold I3 ∞ M] in
theorem TransversePath.negativeBand_subset_compl {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : c.negativeBand ⊆ sphereᶜ := by
  rintro x ⟨⟨q, t⟩, ⟨-, ht⟩, rfl⟩ hx
  have hx' : c.collar (q, t) ∈ c.collar '' (univ ×ˢ ({0} : Set ℝ)) := by
    simpa only [c.central_eq] using hx
  obtain ⟨⟨q', t'⟩, ⟨-, ht'⟩, heq⟩ := hx'
  have hsrc' : (q', t') ∈ c.collar.source :=
    c.collar_domain ⟨mem_univ _, by rw [Set.mem_singleton_iff.mp ht']; norm_num⟩
  have h1 : (q, t) = (q', t') :=
    c.collar.injOn (c.negativeBand_subset_source ⟨mem_univ _, ht⟩) hsrc' heq.symm
  have ht0 : t = 0 := (congrArg Prod.snd h1).trans (Set.mem_singleton_iff.mp ht')
  have htneg : t < 0 := ht.2
  exact absurd (ht0 ▸ htneg) (lt_irrefl (0 : ℝ))

omit [IsManifold I3 ∞ M] in
theorem TransversePath.positiveBand_subset_compl {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : c.positiveBand ⊆ sphereᶜ := by
  rintro x ⟨⟨q, t⟩, ⟨-, ht⟩, rfl⟩ hx
  have hx' : c.collar (q, t) ∈ c.collar '' (univ ×ˢ ({0} : Set ℝ)) := by
    simpa only [c.central_eq] using hx
  obtain ⟨⟨q', t'⟩, ⟨-, ht'⟩, heq⟩ := hx'
  have hsrc' : (q', t') ∈ c.collar.source :=
    c.collar_domain ⟨mem_univ _, by rw [Set.mem_singleton_iff.mp ht']; norm_num⟩
  have h1 : (q, t) = (q', t') :=
    c.collar.injOn (c.positiveBand_subset_source ⟨mem_univ _, ht⟩) hsrc' heq.symm
  have ht0 : t = 0 := (congrArg Prod.snd h1).trans (Set.mem_singleton_iff.mp ht')
  have htpos : 0 < t := ht.1
  exact absurd (ht0 ▸ htpos) (lt_irrefl (0 : ℝ))

omit [IsManifold I3 ∞ M] in
theorem TransversePath.isConnected_negativeBand {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : IsConnected c.negativeBand :=
  (isConnected_univ_sphereTwo.prod (isConnected_Ioo (by norm_num : (-1 : ℝ) < 0))).image c.collar
    (c.collar.contMDiffOn.continuousOn.mono c.negativeBand_subset_source)

omit [IsManifold I3 ∞ M] in
theorem TransversePath.isConnected_positiveBand {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : IsConnected c.positiveBand :=
  (isConnected_univ_sphereTwo.prod (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))).image c.collar
    (c.collar.contMDiffOn.continuousOn.mono c.positiveBand_subset_source)

omit [IsManifold I3 ∞ M] in
theorem TransversePath.isOpen_collarStrip {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : IsOpen c.collarStrip := by
  have h := c.collar.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) c.strip_subset_source
  have hfun : ⇑(c.collar.toOpenPartialHomeomorph : OpenPartialHomeomorph Cylinder M) = ⇑c.collar := rfl
  rw [hfun] at h
  exact h

omit [IsManifold I3 ∞ M] in
theorem TransversePath.sphere_subset_collarStrip {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : sphere ⊆ c.collarStrip := by
  intro x hx
  have hx' : x ∈ c.collar '' (univ ×ˢ ({0} : Set ℝ)) := by
    simpa only [c.central_eq] using hx
  obtain ⟨⟨q, t⟩, ⟨-, ht⟩, rfl⟩ := hx'
  have ht0 : t = 0 := Set.mem_singleton_iff.mp ht
  exact ⟨(q, 0), ⟨mem_univ _, ⟨by norm_num, by norm_num⟩⟩, by rw [ht0]⟩

omit [IsManifold I3 ∞ M] in
theorem TransversePath.collarStrip_subset_bands {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) :
    c.collarStrip ⊆ (c.negativeBand ∪ sphere) ∪ c.positiveBand := by
  rintro x ⟨⟨q, t⟩, ⟨-, ht⟩, rfl⟩
  rcases lt_trichotomy t 0 with h | h | h
  · exact Or.inl (Or.inl ⟨(q, t), ⟨mem_univ _, ⟨ht.1, h⟩⟩, rfl⟩)
  · refine Or.inl (Or.inr ?_)
    have : c.collar (q, t) ∈ c.collar '' (univ ×ˢ ({0} : Set ℝ)) :=
      ⟨(q, t), ⟨mem_univ _, by simpa using h⟩, rfl⟩
    simpa only [c.central_eq] using this
  · exact Or.inr ⟨(q, t), ⟨mem_univ _, ⟨h, ht.2⟩⟩, rfl⟩

omit [IsManifold I3 ∞ M] in
theorem TransversePath.bands_opposite_sides {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) (d : TwoSidedSeparation sphere) :
    (c.negativeBand ⊆ d.positiveSide ∧ c.positiveBand ⊆ d.negativeSide) ∨
      (c.negativeBand ⊆ d.negativeSide ∧ c.positiveBand ⊆ d.positiveSide) := by
  have hS : sphere.Nonempty := by
    obtain ⟨q, hq⟩ := sphereTwo_nonempty
    refine ⟨c.collar (⟨q, hq⟩, 0), ?_⟩
    have hmem : c.collar (⟨q, hq⟩, 0) ∈ c.collar '' (univ ×ˢ ({0} : Set ℝ)) :=
      ⟨(⟨q, hq⟩, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    simpa only [c.central_eq] using hmem
  rcases d.neighborhood_halves_opposite hS c.isConnected_negativeBand c.isConnected_positiveBand
    c.negativeBand_subset_compl c.positiveBand_subset_compl c.isOpen_collarStrip
    c.sphere_subset_collarStrip c.collarStrip_subset_bands with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h


omit [IsManifold I3 ∞ M] in
private theorem exists_sign_neighborhood_of_hasDerivAt_pos {g : ℝ → ℝ} {d s : ℝ}
    (hgs : g s = 0) (hd : 0 < d) (h : HasDerivAt g d s) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ t ∈ Ioo (s - ε) s, g t < 0) ∧
      (∀ t ∈ Ioo s (s + ε), 0 < g t) := by
  have hslope : Tendsto (slope g s) (𝓝[≠] s) (𝓝 d) := h.tendsto_slope
  have hev : ∀ᶠ t in 𝓝[≠] s, d / 2 < slope g s t :=
    hslope.eventually (eventually_gt_nhds (by linarith))
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp hev
  have hkey : ∀ t : ℝ, (t - s) * slope g s t = g t := by
    intro t
    have h1 : (t - s) • slope g s t = g t -ᵥ g s := sub_smul_slope g s t
    rw [smul_eq_mul, vsub_eq_sub, hgs, sub_zero] at h1
    exact h1
  refine ⟨ε, hε, ?_, ?_⟩
  · intro t ht
    have hts : t ≠ s := by intro hh; rw [hh] at ht; simp at ht
    have hdist : dist t s < ε := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsl := hε' hdist hts
    have : (t - s) * slope g s t < 0 := mul_neg_of_neg_of_pos (by linarith [ht.2]) (by linarith)
    rwa [hkey t] at this
  · intro t ht
    have hts : t ≠ s := by intro hh; rw [hh] at ht; simp at ht
    have hdist : dist t s < ε := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsl := hε' hdist hts
    have : 0 < (t - s) * slope g s t := mul_pos (by linarith [ht.1]) (by linarith)
    rwa [hkey t] at this

omit [IsManifold I3 ∞ M] in
private theorem exists_sign_neighborhood_of_hasDerivAt_neg {g : ℝ → ℝ} {d s : ℝ}
    (hgs : g s = 0) (hd : d < 0) (h : HasDerivAt g d s) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ t ∈ Ioo (s - ε) s, 0 < g t) ∧
      (∀ t ∈ Ioo s (s + ε), g t < 0) := by
  obtain ⟨ε, hε, h1, h2⟩ := exists_sign_neighborhood_of_hasDerivAt_pos
    (g := fun t => -g t) (d := -d) (s := s) (by simp [hgs]) (by linarith) h.neg
  refine ⟨ε, hε, ?_, ?_⟩
  · intro t ht
    simpa using h1 t ht
  · intro t ht
    simpa using h2 t ht

omit [IsManifold I3 ∞ M] in
theorem TransversePath.exists_band_neighborhood_of_mem_crossings {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) {s : ℝ} (hs : s ∈ c.crossings) :
    (∃ ε : ℝ, 0 < ε ∧ (∀ t ∈ Ioo (s - ε) s, c.curve t ∈ c.negativeBand) ∧
        (∀ t ∈ Ioo s (s + ε), c.curve t ∈ c.positiveBand)) ∨
      (∃ ε : ℝ, 0 < ε ∧ (∀ t ∈ Ioo (s - ε) s, c.curve t ∈ c.positiveBand) ∧
        (∀ t ∈ Ioo s (s + ε), c.curve t ∈ c.negativeBand)) := by
  have hsIoo : s ∈ Ioo (0 : ℝ) 1 := c.crossings_interior s hs
  have hsphere : c.curve s ∈ sphere :=
    (c.crossings_eq s ⟨hsIoo.1.le, hsIoo.2.le⟩).mpr hs
  have hmemimg : c.curve s ∈ c.collar '' (univ ×ˢ ({0} : Set ℝ)) := by
    simpa only [c.central_eq] using hsphere
  obtain ⟨⟨q, u⟩, ⟨-, hu⟩, heq⟩ := hmemimg
  have hu0 : u = 0 := Set.mem_singleton_iff.mp hu
  have hcs : c.curve s = c.collar (q, 0) := by rw [← heq, hu0]
  have hsrc0 : (q, 0) ∈ c.collar.source :=
    c.collar_domain ⟨mem_univ _, ⟨by norm_num, by norm_num⟩⟩
  have htarget : c.curve s ∈ c.collar.target := by
    rw [hcs, ← PartialEquiv.image_source_eq_target c.collar.toPartialEquiv]
    exact ⟨(q, 0), hsrc0, rfl⟩
  have hgs : (fun t => (c.collar.symm (c.curve t)).2) s = 0 := by
    change (c.collar.symm (c.curve s)).2 = 0
    rw [hcs]
    exact congrArg Prod.snd (c.collar.left_inv' hsrc0)
  have hgs0 : (c.collar.symm (c.curve s)).2 = 0 := hgs
  have hderiv_ne : deriv (fun t => (c.collar.symm (c.curve t)).2) s ≠ 0 := c.transverse s hs
  have hdiff : DifferentiableAt ℝ (fun t => (c.collar.symm (c.curve t)).2) s := by
    by_contra hcon
    exact hderiv_ne (deriv_zero_of_not_differentiableAt hcon)
  have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 s := by
    have hmem : s ∈ interior (Icc (0 : ℝ) 1) := by simpa [interior_Icc] using hsIoo
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hmem) interior_subset
  have hcurve_cont : ContinuousAt c.curve s := c.continuous.continuousAt hnhds
  have hsymm_cont : ContinuousAt c.collar.symm (c.curve s) :=
    ((c.collar.symm.contMDiffOn.continuousOn).continuousAt
      (c.collar.open_target.mem_nhds htarget))
  have hgc : ContinuousAt (fun t => (c.collar.symm (c.curve t)).2) s :=
    (hsymm_cont.comp hcurve_cont).snd
  have hevbig : ∀ᶠ t in 𝓝 s, c.curve t ∈ c.collar.target ∧
      |(c.collar.symm (c.curve t)).2| < 1 := by
    have h1 : ∀ᶠ t in 𝓝 s, c.curve t ∈ c.collar.target :=
      hcurve_cont.preimage_mem_nhds (c.collar.open_target.mem_nhds htarget)
    have h2 : ∀ᶠ t in 𝓝 s, |(c.collar.symm (c.curve t)).2| < 1 := by
      filter_upwards [Metric.tendsto_nhds.1 hgc 1 (by norm_num)] with t ht
      rw [Real.dist_eq, hgs0, sub_zero] at ht
      exact ht
    filter_upwards [h1, h2] with t ht1 ht2
    exact ⟨ht1, ht2⟩
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.mem_nhds_iff.mp hevbig
  rcases lt_or_gt_of_ne hderiv_ne with hdneg | hdpos
  · obtain ⟨ε₂, hε₂, hs2, hs3⟩ :=
      exists_sign_neighborhood_of_hasDerivAt_neg hgs hdneg hdiff.hasDerivAt
    refine Or.inr ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
    · intro t ht
      have hd1 : dist t s < ε₁ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, min_le_left ε₁ ε₂], by linarith [ht.2, min_le_left ε₁ ε₂]⟩
      obtain ⟨htgt, habs⟩ := hε₁' hd1
      have hpos : 0 < (c.collar.symm (c.curve t)).2 :=
        hs2 t ⟨by linarith [ht.1, min_le_right ε₁ ε₂], ht.2⟩
      rw [abs_lt] at habs
      exact ⟨c.collar.symm (c.curve t), ⟨mem_univ _, ⟨hpos, habs.2⟩⟩,
        c.collar.right_inv' htgt⟩
    · intro t ht
      have hd1 : dist t s < ε₁ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, min_le_left ε₁ ε₂], by linarith [ht.2, min_le_left ε₁ ε₂]⟩
      obtain ⟨htgt, habs⟩ := hε₁' hd1
      have hneg : (c.collar.symm (c.curve t)).2 < 0 :=
        hs3 t ⟨ht.1, by linarith [ht.2, min_le_right ε₁ ε₂]⟩
      rw [abs_lt] at habs
      exact ⟨c.collar.symm (c.curve t), ⟨mem_univ _, ⟨habs.1, hneg⟩⟩,
        c.collar.right_inv' htgt⟩
  · obtain ⟨ε₂, hε₂, hs2, hs3⟩ :=
      exists_sign_neighborhood_of_hasDerivAt_pos hgs hdpos hdiff.hasDerivAt
    refine Or.inl ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
    · intro t ht
      have hd1 : dist t s < ε₁ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, min_le_left ε₁ ε₂], by linarith [ht.2, min_le_left ε₁ ε₂]⟩
      obtain ⟨htgt, habs⟩ := hε₁' hd1
      have hneg : (c.collar.symm (c.curve t)).2 < 0 :=
        hs2 t ⟨by linarith [ht.1, min_le_right ε₁ ε₂], ht.2⟩
      rw [abs_lt] at habs
      exact ⟨c.collar.symm (c.curve t), ⟨mem_univ _, ⟨habs.1, hneg⟩⟩,
        c.collar.right_inv' htgt⟩
    · intro t ht
      have hd1 : dist t s < ε₁ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, min_le_left ε₁ ε₂], by linarith [ht.2, min_le_left ε₁ ε₂]⟩
      obtain ⟨htgt, habs⟩ := hε₁' hd1
      have hpos : 0 < (c.collar.symm (c.curve t)).2 :=
        hs3 t ⟨ht.1, by linarith [ht.2, min_le_right ε₁ ε₂]⟩
      rw [abs_lt] at habs
      exact ⟨c.collar.symm (c.curve t), ⟨mem_univ _, ⟨hpos, habs.2⟩⟩,
        c.collar.right_inv' htgt⟩


private theorem zmodTwo_add_one_ne_self (x : ZMod 2) : x + 1 ≠ x := by
  intro h
  have h1 : x + 1 = x + 0 := by rw [h, add_zero]
  exact one_ne_zero (add_left_cancel h1)

private theorem zmodTwo_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private theorem zmodTwo_intCast_neg_one : ((-1 : ℤ) : ZMod 2) = 1 := by decide

private theorem zmod_two_eq_add_card_of_between (F : Finset ℝ) (a b : ℝ)
    (f : ℝ → ZMod 2)
    (hconst : ∀ t t' : ℝ, a ≤ t → t ≤ t' → t' ≤ b →
      (∀ s ∈ F, ¬ (t ≤ s ∧ s ≤ t')) → f t = f t')
    (hflip : ∀ s ∈ F, ∃ A : ZMod 2,
      (∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (s - ε) s, f t = A) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo s (s + ε), f t = A + 1)) :
    ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b → u ∉ F → v ∉ F → u ≤ v →
      f v = f u + ((F.filter fun s => u < s ∧ s < v).card : ZMod 2) := by
  suffices ∀ n : ℕ, ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b → u ∉ F → v ∉ F → u ≤ v →
      (F.filter (fun s => u < s ∧ s < v)).card = n →
      f v = f u + ((F.filter (fun s => u < s ∧ s < v)).card : ZMod 2) by
    intro u v hu hv huF hvF huv
    exact this _ u v hu hv huF hvF huv rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hu hv huF hvF huv hcard
    by_cases hne : (F.filter (fun s => u < s ∧ s < v)).Nonempty
    · obtain ⟨s, hsG, hsmin⟩ : ∃ s ∈ F.filter (fun s => u < s ∧ s < v),
          ∀ x ∈ F.filter (fun s => u < s ∧ s < v), s ≤ x :=
        ⟨_, Finset.min'_mem _ hne, fun x hx => Finset.min'_le _ x hx⟩
      have hsF : s ∈ F := (Finset.mem_filter.mp hsG).1
      have hsuv : u < s ∧ s < v := (Finset.mem_filter.mp hsG).2
      obtain ⟨A, ⟨ε, hε, hleft⟩, ⟨ε', hε', hright⟩⟩ := hflip s hsF
      have hnext : ∃ w : ℝ, s < w ∧ w < s + ε' ∧ w < v ∧ w ∉ F ∧
          ∀ x ∈ F, s < x → x < v → w < x := by
        by_cases hnx : ((F.filter (fun s => u < s ∧ s < v)).erase s).Nonempty
        · obtain ⟨T, hTmem, hTmin⟩ : ∃ T ∈ (F.filter (fun s => u < s ∧ s < v)).erase s,
              ∀ x ∈ (F.filter (fun s => u < s ∧ s < v)).erase s, T ≤ x :=
            ⟨_, Finset.min'_mem _ hnx, fun x hx => Finset.min'_le _ x hx⟩
          have hTmemG : T ∈ F.filter (fun s => u < s ∧ s < v) := Finset.mem_of_mem_erase hTmem
          have hTne : T ≠ s := (Finset.mem_erase.mp hTmem).1
          have hsT : s < T := lt_of_le_of_ne (hsmin T hTmemG) (Ne.symm hTne)
          have hTv : T < v := (Finset.mem_filter.mp hTmemG).2.2
          have hpos : 0 < min ε' (T - s) := lt_min hε' (by linarith)
          have hltε : min ε' (T - s) / 2 < ε' := by
            have h1 : min ε' (T - s) ≤ ε' := min_le_left _ _
            linarith
          have hltT : min ε' (T - s) / 2 < T - s := by
            have h1 : min ε' (T - s) ≤ T - s := min_le_right _ _
            linarith
          refine ⟨s + min ε' (T - s) / 2, by linarith, by linarith,
            by linarith, ?_, ?_⟩
          · intro hwF
            have hwG : s + min ε' (T - s) / 2 ∈ F.filter (fun s => u < s ∧ s < v) :=
              Finset.mem_filter.mpr ⟨hwF, ⟨by linarith, by linarith⟩⟩
            have hwmem : s + min ε' (T - s) / 2 ∈
                (F.filter (fun s => u < s ∧ s < v)).erase s :=
              Finset.mem_erase.mpr ⟨by linarith, hwG⟩
            exact absurd (hTmin _ hwmem) (by linarith)
          · intro x hxF hsx hxv
            have hxG : x ∈ F.filter (fun s => u < s ∧ s < v) :=
              Finset.mem_filter.mpr ⟨hxF, ⟨by linarith, hxv⟩⟩
            have hxmem : x ∈ (F.filter (fun s => u < s ∧ s < v)).erase s :=
              Finset.mem_erase.mpr ⟨by linarith, hxG⟩
            have hTx : T ≤ x := hTmin _ hxmem
            linarith
        · have hempty : (F.filter (fun s => u < s ∧ s < v)).erase s = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hnx
          have hvs : 0 < v - s := by linarith
          have hpos : 0 < min ε' (v - s) := lt_min hε' hvs
          have hltε : min ε' (v - s) / 2 < ε' := by
            have h1 : min ε' (v - s) ≤ ε' := min_le_left _ _
            linarith
          have hltT : min ε' (v - s) / 2 < v - s := by
            have h1 : min ε' (v - s) ≤ v - s := min_le_right _ _
            linarith
          refine ⟨s + min ε' (v - s) / 2, by linarith, by linarith,
            by linarith, ?_, ?_⟩
          · intro hwF
            have hwG : s + min ε' (v - s) / 2 ∈ F.filter (fun s => u < s ∧ s < v) :=
              Finset.mem_filter.mpr ⟨hwF, ⟨by linarith, by linarith⟩⟩
            have hwmem : s + min ε' (v - s) / 2 ∈
                (F.filter (fun s => u < s ∧ s < v)).erase s :=
              Finset.mem_erase.mpr ⟨by linarith, hwG⟩
            rw [hempty] at hwmem
            simp at hwmem
          · intro x hxF hsx hxv
            exfalso
            have hxG : x ∈ F.filter (fun s => u < s ∧ s < v) :=
              Finset.mem_filter.mpr ⟨hxF, ⟨by linarith, hxv⟩⟩
            have hxmem : x ∈ (F.filter (fun s => u < s ∧ s < v)).erase s :=
              Finset.mem_erase.mpr ⟨by linarith, hxG⟩
            rw [hempty] at hxmem
            simp at hxmem
      obtain ⟨w, hsw, hwsε, hwv, hwF, hwmin⟩ := hnext
      have hδ : 0 < min ε (s - u) := lt_min hε (by linarith [hsuv.1])
      have hδu : min ε (s - u) ≤ s - u := min_le_right _ _
      have hδε : min ε (s - u) ≤ ε := min_le_left _ _
      have ht1 : s - min ε (s - u) / 2 ∈ Ioo (s - ε) s :=
        ⟨by linarith, by linarith⟩
      have hgap : ∀ x ∈ F, ¬ (u ≤ x ∧ x ≤ s - min ε (s - u) / 2) := by
        intro x hxF hx
        have hxu : u ≠ x := fun h => huF (h ▸ hxF)
        have hxG : x ∈ F.filter (fun s => u < s ∧ s < v) :=
          Finset.mem_filter.mpr ⟨hxF, ⟨lt_of_le_of_ne hx.1 hxu, by linarith [hx.2, hδ]⟩⟩
        have hsm : s ≤ x := hsmin x hxG
        have hlt : min ε (s - u) / 2 < s - u := by linarith
        linarith
      have ht1u : u ≤ s - min ε (s - u) / 2 := by linarith
      have ht1b : s - min ε (s - u) / 2 ≤ b := le_trans (by linarith : s - min ε (s - u) / 2 ≤ s)
        (le_trans hsuv.2.le hv.2)
      have hfu : f u = A := by
        have h1 : f u = f (s - min ε (s - u) / 2) :=
          hconst u (s - min ε (s - u) / 2) hu.1 ht1u ht1b hgap
        exact h1.trans (hleft _ ht1)
      have hfw : f w = A + 1 := hright w ⟨hsw, hwsε⟩
      have hsub : F.filter (fun x => w < x ∧ x < v) ⊆
          (F.filter (fun s => u < s ∧ s < v)).erase s := by
        intro x hx
        have hxF : x ∈ F := (Finset.mem_filter.mp hx).1
        have hxw : w < x ∧ x < v := (Finset.mem_filter.mp hx).2
        exact Finset.mem_erase.mpr ⟨by linarith, Finset.mem_filter.mpr
          ⟨hxF, ⟨by linarith, hxw.2⟩⟩⟩
      have hG'eq : F.filter (fun x => w < x ∧ x < v) =
          (F.filter (fun s => u < s ∧ s < v)).erase s := by
        refine Finset.Subset.antisymm hsub ?_
        intro x hx
        obtain ⟨hxne, hxG⟩ := Finset.mem_erase.mp hx
        have hxF : x ∈ F := (Finset.mem_filter.mp hxG).1
        have hxuv : u < x ∧ x < v := (Finset.mem_filter.mp hxG).2
        exact Finset.mem_filter.mpr ⟨hxF, ⟨hwmin x hxF (lt_of_le_of_ne (hsmin x hxG) (Ne.symm hxne)) hxuv.2,
          hxuv.2⟩⟩
      have hGN : (F.filter (fun x => w < x ∧ x < v)).card + 1 =
          (F.filter (fun s => u < s ∧ s < v)).card := by
        rw [hG'eq, Finset.card_erase_of_mem hsG]
        have hpos : 0 < (F.filter (fun s => u < s ∧ s < v)).card :=
          Finset.card_pos.mpr ⟨s, hsG⟩
        omega
      have hcard' : ((F.filter (fun x => w < x ∧ x < v)).card : ZMod 2) + 1 =
          ((F.filter (fun s => u < s ∧ s < v)).card : ZMod 2) := by
        rw [← hGN]
        push_cast
        ring
      have hlt' : (F.filter (fun x => w < x ∧ x < v)).card < n := by
        have h1 : (F.filter (fun x => w < x ∧ x < v)).card ≤
            ((F.filter (fun s => u < s ∧ s < v)).erase s).card := Finset.card_le_card hsub
        have h2 : ((F.filter (fun s => u < s ∧ s < v)).erase s).card <
            (F.filter (fun s => u < s ∧ s < v)).card := Finset.card_erase_lt_of_mem hsG
        omega
      have hIH := ih _ hlt' w v
        ⟨by linarith [hu.1], by linarith [hwv, hv.2]⟩ hv hwF hvF (le_of_lt hwv) rfl
      have hcard'' : (1 : ZMod 2) + ((F.filter (fun x => w < x ∧ x < v)).card : ZMod 2) =
          ((F.filter (fun s => u < s ∧ s < v)).card : ZMod 2) := by
        rw [add_comm, hcard']
      rw [hIH, hfw, hfu, add_assoc, hcard'']
    · have hempty : (F.filter (fun s => u < s ∧ s < v)) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty, Finset.card_empty, Nat.cast_zero, add_zero]
      exact (hconst u v hu.1 huv hv.2 (by
        intro x hxF hxuv
        have hxu : u ≠ x := fun h => huF (h ▸ hxF)
        have hxv : x ≠ v := fun h => hvF (h.symm ▸ hxF)
        exact hne ⟨x, Finset.mem_filter.mpr ⟨hxF, ⟨lt_of_le_of_ne hxuv.1 hxu,
          lt_of_le_of_ne hxuv.2 hxv⟩⟩⟩)).symm

omit [IsManifold I3 ∞ M] in
theorem TransversePath.not_mem_connectedComponentIn_of_intersection
    {p z : M} {sphere : Set M} (c : TransversePath p z sphere)
    (d : TwoSidedSeparation sphere) (hp : p ∉ sphere) (hz : z ∉ sphere)
    (hint : c.intersection = 1 ∨ c.intersection = -1) :
    z ∉ connectedComponentIn sphereᶜ p := by
  classical
  let f : ℝ → ZMod 2 := fun t => if c.curve t ∈ d.positiveSide then 1 else 0
  have hfconst : ∀ t t' : ℝ, (0 : ℝ) ≤ t → t ≤ t' → t' ≤ 1 →
      (∀ s ∈ c.crossings, ¬ (t ≤ s ∧ s ≤ t')) → f t = f t' := by
    intro t t' ht0 htt' ht'1 hnone
    have hsub : c.curve '' Icc t t' ⊆ sphereᶜ := by
      rintro x ⟨w, hw, rfl⟩
      have hw01 : w ∈ Icc (0 : ℝ) 1 := ⟨le_trans ht0 hw.1, le_trans hw.2 ht'1⟩
      intro hwsphere
      exact hnone w ((c.crossings_eq w hw01).mp hwsphere) hw
    have hpre : IsPreconnected (c.curve '' Icc t t') :=
      isPreconnected_Icc.image c.curve (c.continuous.mono (Icc_subset_Icc ht0 ht'1))
    rcases d.subset_positiveSide_or_subset_negativeSide hpre hsub with h | h
    · have htB : c.curve t ∈ d.positiveSide := h ⟨t, ⟨le_rfl, htt'⟩, rfl⟩
      have ht'B : c.curve t' ∈ d.positiveSide := h ⟨t', ⟨htt', le_rfl⟩, rfl⟩
      change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) =
        (if c.curve t' ∈ d.positiveSide then (1 : ZMod 2) else 0)
      rw [if_pos htB, if_pos ht'B]
    · have htB : c.curve t ∉ d.positiveSide :=
        fun hcon => Set.disjoint_left.mp d.disjoint hcon (h ⟨t, ⟨le_rfl, htt'⟩, rfl⟩)
      have ht'B : c.curve t' ∉ d.positiveSide :=
        fun hcon => Set.disjoint_left.mp d.disjoint hcon (h ⟨t', ⟨htt', le_rfl⟩, rfl⟩)
      change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) =
        (if c.curve t' ∈ d.positiveSide then (1 : ZMod 2) else 0)
      rw [if_neg htB, if_neg ht'B]
  have hflip : ∀ s ∈ c.crossings, ∃ A : ZMod 2,
      (∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (s - ε) s, f t = A) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo s (s + ε), f t = A + 1) := by
    intro s hs
    rcases c.bands_opposite_sides d with hcase | hcase
    · obtain ⟨hNB, hPE⟩ := hcase
      rcases c.exists_band_neighborhood_of_mem_crossings hs with hloc | hloc
      · obtain ⟨ε, hε, h1, h2⟩ := hloc
        refine ⟨1, ⟨⟨ε, hε, fun t ht => ?_⟩, ⟨ε, hε, fun t ht => ?_⟩⟩⟩
        · change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) = 1
          rw [if_pos (hNB (h1 t ht))]
        · change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) = 1 + 1
          rw [if_neg (fun hcon => Set.disjoint_left.mp d.disjoint hcon (hPE (h2 t ht))),
            zmodTwo_one_add_one]
      · obtain ⟨ε, hε, h1, h2⟩ := hloc
        refine ⟨0, ⟨⟨ε, hε, fun t ht => ?_⟩, ⟨ε, hε, fun t ht => ?_⟩⟩⟩
        · change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) = 0
          rw [if_neg (fun hcon => Set.disjoint_left.mp d.disjoint hcon (hPE (h1 t ht)))]
        · change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) = 0 + 1
          rw [if_pos (hNB (h2 t ht))]
          ring
    · obtain ⟨hNE, hPB⟩ := hcase
      rcases c.exists_band_neighborhood_of_mem_crossings hs with hloc | hloc
      · obtain ⟨ε, hε, h1, h2⟩ := hloc
        refine ⟨0, ⟨⟨ε, hε, fun t ht => ?_⟩, ⟨ε, hε, fun t ht => ?_⟩⟩⟩
        · change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) = 0
          rw [if_neg (fun hcon => Set.disjoint_left.mp d.disjoint hcon (hNE (h1 t ht)))]
        · change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) = 0 + 1
          rw [if_pos (hPB (h2 t ht))]
          ring
      · obtain ⟨ε, hε, h1, h2⟩ := hloc
        refine ⟨1, ⟨⟨ε, hε, fun t ht => ?_⟩, ⟨ε, hε, fun t ht => ?_⟩⟩⟩
        · change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) = 1
          rw [if_pos (hPB (h1 t ht))]
        · change (if c.curve t ∈ d.positiveSide then (1 : ZMod 2) else 0) = 1 + 1
          rw [if_neg (fun hcon => Set.disjoint_left.mp d.disjoint hcon (hNE (h2 t ht))),
            zmodTwo_one_add_one]
  have h0 : (0 : ℝ) ∉ c.crossings := fun h => absurd (c.crossings_interior 0 h).1 (lt_irrefl 0)
  have h1 : (1 : ℝ) ∉ c.crossings := fun h => absurd (c.crossings_interior 1 h).2 (lt_irrefl 1)
  have hpar := zmod_two_eq_add_card_of_between c.crossings 0 1 f hfconst hflip 0 1
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ h0 h1 zero_le_one
  have hfilter : c.crossings.filter (fun s => 0 < s ∧ s < 1) = c.crossings :=
    Finset.filter_true_of_mem (fun s hs => c.crossings_interior s hs)
  rw [hfilter] at hpar
  have hcard : (c.crossings.card : ZMod 2) = 1 := by
    have hterm : ∀ x ∈ c.crossings,
        (((if 0 < deriv (fun t => (c.collar.symm (c.curve t)).2) x then (1 : ℤ) else -1) : ℤ) :
          ZMod 2) = 1 := by
      intro x _
      by_cases hx : 0 < deriv (fun t => (c.collar.symm (c.curve t)).2) x
      · rw [if_pos hx]
        exact Int.cast_one
      · rw [if_neg hx]
        exact zmodTwo_intCast_neg_one
    have hsum : ((c.intersection : ℤ) : ZMod 2) = (c.crossings.card : ZMod 2) := by
      calc ((c.intersection : ℤ) : ZMod 2)
          = ∑ x ∈ c.crossings,
              (((if 0 < deriv (fun t => (c.collar.symm (c.curve t)).2) x then (1 : ℤ) else -1) :
                ℤ) : ZMod 2) := by
            rw [TransversePath.intersection, Int.cast_sum]
        _ = ∑ _x ∈ c.crossings, (1 : ZMod 2) := Finset.sum_congr rfl hterm
        _ = (c.crossings.card : ZMod 2) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rcases hint with h | h
    · rw [h] at hsum
      exact hsum.symm
    · rw [h, zmodTwo_intCast_neg_one] at hsum
      exact hsum.symm
  have hf01 : f 1 = f 0 + 1 := by
    rw [hcard] at hpar
    exact hpar
  have hne01 : f 1 ≠ f 0 := fun hcon => zmodTwo_add_one_ne_self (f 0) (hf01.symm.trans hcon)
  have hf0 : f 0 = (if p ∈ d.positiveSide then (1 : ZMod 2) else 0) := by
    change (if c.curve 0 ∈ d.positiveSide then (1 : ZMod 2) else 0) = _
    rw [c.start]
  have hf1 : f 1 = (if z ∈ d.positiveSide then (1 : ZMod 2) else 0) := by
    change (if c.curve 1 ∈ d.positiveSide then (1 : ZMod 2) else 0) = _
    rw [c.finish]
  by_cases hpB : p ∈ d.positiveSide
  · have hzB : z ∉ d.positiveSide := by
      intro hzB'
      exact hne01 (by rw [hf0, hf1, if_pos hpB, if_pos hzB'])
    have hzE : z ∈ d.negativeSide := by
      have hmem : z ∈ d.positiveSide ∪ d.negativeSide := by rw [d.union_eq_compl]; exact hz
      exact hmem.resolve_left hzB
    exact d.not_mem_connectedComponentIn_of_mem_other_side_symm hpB hzE
  · have hpE : p ∈ d.negativeSide := by
      have hmem : p ∈ d.positiveSide ∪ d.negativeSide := by rw [d.union_eq_compl]; exact hp
      exact hmem.resolve_left hpB
    have hzB : z ∈ d.positiveSide := by
      by_contra hzB'
      have hzE : z ∈ d.negativeSide := by
        have hmem : z ∈ d.positiveSide ∪ d.negativeSide := by rw [d.union_eq_compl]; exact hz
        exact hmem.resolve_left hzB'
      exact hne01 (by rw [hf0, hf1, if_neg hpB, if_neg hzB'])
    exact d.not_mem_connectedComponentIn_of_mem_other_side hpE hzB


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
