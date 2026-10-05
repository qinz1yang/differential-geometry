import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverGenericBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.SmoothCompactOneDomainBCF

/-!
# The shared `K₃` kernel (review 74, D74-9, package K0; lane B-BCF134)

`exists_compact_oneManifold_choice74` on a one-dimensional base in graph-chart form
(`GraphAtlas1_BCF`, the closed `finalBase_slim_chart_BAS` shape agreed with C14-ZSP35c):

* `GraphAtlas1_BCF.halfChart_BCF`: a graph chart read with a sign `σ = ±1` and an origin `u`
  (`t ↦ param j (u + σ t)`) is a half chart of any `T` it cuts out correctly;
* `GraphAtlas1_BCF.exists_halfChart_of_cover_BCF`: the union `T` of finitely many closed chart
  intervals with GENERIC endpoints has a half chart at each of its points (an interior chart at a point
  of an open interval; a one-sided chart at an endpoint covered by no open interval, the other closed
  intervals being at positive distance);
* `GraphAtlas1_BCF.exists_compact_oneManifold_choice_BCF` (K0): for compact `Kset ⊆ Bs`, finite
  `Fset` and a regular `Dset` with relative frontier in `Kset`, a compact smooth one-dimensional domain
  `D` (arcs AND loops, `SmoothCompactOneDomain_BCF`) with `Kset ⊆ int_{Bs} D`, relative frontier
  disjoint from `Fset`, and `D ∩ Dset` regular in `Bs`;
* `GraphAtlas1_BCF.exists_compact_oneManifold_choice74_BCF`: the D74-9 form (no `Dset`).

Circle components are KEPT (D74-9); the boundary route removes them in its binding
(`no_closed_base_component_BCF`).
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

namespace GraphAtlas1_BCF

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}
  (At : GraphAtlas1_BCF ι Bs)

/-- `param j` is injective on `dom j`. -/
theorem injOn_param_BCF (j : ι) : InjOn (At.param j) (At.dom j) := fun s hs t ht hst => by
  rw [← At.coord_param j s hs, ← At.coord_param j t ht, hst]

/-- **A graph chart read with sign `σ` and origin `u`** as a half chart of `T`, given the
cut-out identity `T ∩ O = π '' (V ∩ [0, ∞))` for `π t = param j (u + σ t)`. -/
def halfChart_BCF {T : Set H} (j : ι) (σ u : ℝ) (hσ : σ * σ = 1) (V : Set ℝ) (O : Set H)
    (hV : IsOpen V) (hVW : ∀ t ∈ V, u + σ * t ∈ At.dom j) (hO : IsOpen O)
    (hTO : T ∩ O = (fun t => At.param j (u + σ * t)) '' (V ∩ Ici 0)) : HalfChart_BCF Bs T where
  L := σ • At.coord j
  κ := -(σ * u)
  π := fun t => At.param j (u + σ * t)
  W := {t | u + σ * t ∈ At.dom j}
  V := V
  O := O
  isOpen_W := (At.isOpen_dom j).preimage (continuous_const.add (continuous_const.mul continuous_id))
  isOpen_V := hV
  V_subset := hVW
  smooth := (At.param_smooth j).comp (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
    fun _ ht => ht
  coord := fun t ht => by
    change σ • At.coord j (At.param j (u + σ * t)) + -(σ * u) = t
    rw [At.coord_param j _ ht, smul_eq_mul]
    linear_combination t * hσ
  mem := fun t ht => At.param_mem_BCF ht
  relOpen := by
    obtain ⟨G, hG, hGB⟩ := At.piece_relOpen j
    refine ⟨G, hG, hGB.trans ?_⟩
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨σ * (s - u), ?_, ?_⟩
      · change u + σ * (σ * (s - u)) ∈ At.dom j
        rwa [← mul_assoc, hσ, one_mul, add_sub_cancel]
      · change At.param j (u + σ * (σ * (s - u))) = At.param j s
        rw [← mul_assoc, hσ, one_mul, add_sub_cancel]
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, ht, rfl⟩
  isOpen_O := hO
  inter_eq := hTO

theorem halfChart_O_BCF {T : Set H} (j : ι) (σ u : ℝ) (hσ : σ * σ = 1) (V : Set ℝ) (O : Set H)
    (hV : IsOpen V) (hVW : ∀ t ∈ V, u + σ * t ∈ At.dom j) (hO : IsOpen O)
    (hTO : T ∩ O = (fun t => At.param j (u + σ * t)) '' (V ∩ Ici 0)) :
    (At.halfChart_BCF j σ u hσ V O hV hVW hO hTO).O = O := rfl

/-- **Half charts of a generic finite union of closed chart intervals**: every point of
`T = ⋃ r, param (c r) '' [a r, b r]` lies in the open set of some half chart of `T`. -/
theorem exists_halfChart_of_cover_BCF {n : ℕ} {c : Fin n → ι} {a b : Fin n → ℝ}
    (hab : ∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r)) (hgen : At.GenericEndpoints_BCF c a b)
    {y : H} (hy : y ∈ ⋃ r, At.param (c r) '' Icc (a r) (b r)) :
    ∃ d : HalfChart_BCF Bs (⋃ r, At.param (c r) '' Icc (a r) (b r)), y ∈ d.O := by
  set T := ⋃ r, At.param (c r) '' Icc (a r) (b r) with hT
  have hTB : T ⊆ Bs := iUnion_subset fun r => by
    rintro _ ⟨t, ht, rfl⟩
    exact At.param_mem_BCF ((hab r).2 ht)
  by_cases hAc : ∃ r, y ∈ At.param (c r) '' Ioo (a r) (b r)
  · -- an interior chart on the open interval `(a r, b r)`
    obtain ⟨r, hr⟩ := hAc
    obtain ⟨G, hG, hGB⟩ := At.image_relOpen_BCF isOpen_Ioo (Ioo_subset_Icc_self.trans (hab r).2)
    have hσ : (1 : ℝ) * 1 = 1 := one_mul 1
    have hVW : ∀ t ∈ Ioo 0 (b r - a r), a r + 1 * t ∈ At.dom (c r) := fun t ht =>
      (hab r).2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hTO : T ∩ G = (fun t => At.param (c r) (a r + 1 * t)) '' (Ioo 0 (b r - a r) ∩ Ici 0) := by
      ext z
      constructor
      · rintro ⟨hzT, hzG⟩
        obtain ⟨u, hu, rfl⟩ : z ∈ At.param (c r) '' Ioo (a r) (b r) := hGB ▸ ⟨hzG, hTB hzT⟩
        refine ⟨u - a r, ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩, ?_⟩
        · exact mem_Ici.mpr (by linarith [hu.1])
        · change At.param (c r) (a r + 1 * (u - a r)) = At.param (c r) u
          rw [one_mul, add_sub_cancel]
      · rintro ⟨t, ⟨ht, -⟩, rfl⟩
        have hu : a r + 1 * t ∈ Ioo (a r) (b r) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        refine ⟨mem_iUnion.mpr ⟨r, _, Ioo_subset_Icc_self hu, rfl⟩, ?_⟩
        have : At.param (c r) (a r + 1 * t) ∈ G ∩ Bs := hGB ▸ ⟨_, hu, rfl⟩
        exact this.1
    refine ⟨At.halfChart_BCF (c r) 1 (a r) hσ (Ioo 0 (b r - a r)) G isOpen_Ioo hVW hG hTO, ?_⟩
    rw [halfChart_O_BCF]
    have : y ∈ G ∩ Bs := hGB ▸ hr
    exact this.1
  · -- an uncovered endpoint: a one-sided chart
    obtain ⟨r, e, he, rfl⟩ := mem_iUnion.mp hy
    have hend : e = a r ∨ e = b r := by
      by_contra h
      push Not at h
      exact hAc ⟨r, e, ⟨lt_of_le_of_ne he.1 (Ne.symm h.1), lt_of_le_of_ne he.2 h.2⟩, rfl⟩
    set j := c r with hj
    -- the other closed intervals avoid the endpoint
    set Q : Set H := ⋃ s, ⋃ _ : s ≠ r, At.param (c s) '' Icc (a s) (b s) with hQ
    have hQc : IsClosed Q :=
      (isCompact_iUnion fun s => isCompact_iUnion fun _ => At.isCompact_image_Icc_BCF (hab s).2).isClosed
    have hyQ : At.param j e ∉ Q := by
      intro hq
      obtain ⟨s, hq⟩ := mem_iUnion.mp hq
      obtain ⟨hs, hq⟩ := mem_iUnion.mp hq
      obtain ⟨u, hu, hus⟩ := hq
      by_cases hu' : u ∈ Ioo (a s) (b s)
      · exact hAc ⟨s, u, hu', hus⟩
      · have hus' : u = a s ∨ u = b s := by
          by_contra h
          push Not at h
          exact hu' ⟨lt_of_le_of_ne hu.1 (Ne.symm h.1), lt_of_le_of_ne hu.2 h.2⟩
        have hmem_r : At.param j e ∈ ({At.param (c r) (a r), At.param (c r) (b r)} : Set H) := by
          rcases hend with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hmem_s : At.param j e ∈ ({At.param (c s) (a s), At.param (c s) (b s)} : Set H) := by
          rcases hus' with rfl | rfl
          · exact Or.inl hus.symm
          · exact Or.inr hus.symm
        exact hgen.2 r s (Ne.symm hs) _ hmem_r hmem_s
    -- a radius `η`
    have hedom : e ∈ At.dom j := (hab r).2 he
    have hcont : ContinuousAt (At.param j) e :=
      (At.continuousOn_param_BCF j).continuousAt ((At.isOpen_dom j).mem_nhds hedom)
    have hnhds : At.dom j ∩ At.param j ⁻¹' Qᶜ ∈ 𝓝 e :=
      Filter.inter_mem ((At.isOpen_dom j).mem_nhds hedom) (hcont.preimage_mem_nhds
        (hQc.isOpen_compl.mem_nhds hyQ))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    set η : ℝ := min δ (b r - a r) / 2 with hη
    have hηpos : 0 < η := by
      have := (hab r).1
      positivity
    have hηδ : η < δ := by
      have h1 : min δ (b r - a r) ≤ δ := min_le_left _ _
      have h2 : 0 < min δ (b r - a r) := lt_min hδ (by linarith [(hab r).1])
      linarith
    have hηab : η < b r - a r := by
      have h1 : min δ (b r - a r) ≤ b r - a r := min_le_right _ _
      have h2 : 0 < min δ (b r - a r) := lt_min hδ (by linarith [(hab r).1])
      linarith
    have hball' : ∀ v, |v - e| < δ → v ∈ At.dom j ∧ At.param j v ∉ Q := fun v hv =>
      hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hv)
    obtain ⟨G, hG, hGB⟩ := At.image_relOpen_BCF (j := j) (O := Ioo (e - η) (e + η)) isOpen_Ioo
      fun v hv => (hball' v (by rw [abs_lt]; constructor <;> linarith [hv.1, hv.2])).1
    -- the sign: `σ = 1` at `a r`, `σ = -1` at `b r`
    obtain ⟨σ, hσ, h1, h2⟩ : ∃ σ : ℝ, σ * σ = 1 ∧
        (∀ t ∈ Ico (0 : ℝ) η, e + σ * t ∈ Icc (a r) (b r)) ∧
        (∀ u ∈ Icc (a r) (b r), u ∈ Ioo (e - η) (e + η) → σ * (u - e) ∈ Ico (0 : ℝ) η) := by
      rcases hend with rfl | rfl
      · refine ⟨1, one_mul 1, fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩,
          fun u hu hu' => ⟨by linarith [hu.1], by linarith [hu'.2]⟩⟩
      · refine ⟨-1, by norm_num, fun t ht => ⟨by linarith [ht.1, ht.2], by linarith [ht.1]⟩,
          fun u hu hu' => ⟨by linarith [hu.2], by linarith [hu'.1]⟩⟩
    have hσabs : ∀ t : ℝ, |σ * t| = |t| := fun t => by
      have : |σ| = 1 := by
        have h := congrArg abs hσ
        rw [abs_mul, abs_one] at h
        nlinarith [abs_nonneg σ]
      rw [abs_mul, this, one_mul]
    have hVW : ∀ t ∈ Ioo (-η) η, e + σ * t ∈ At.dom j := fun t ht =>
      (hball' _ (by rw [add_sub_cancel_left, hσabs, abs_lt]; constructor <;> linarith [ht.1, ht.2])).1
    have hTO : T ∩ (G ∩ Qᶜ) = (fun t => At.param j (e + σ * t)) '' (Ioo (-η) η ∩ Ici 0) := by
      ext z
      constructor
      · rintro ⟨hzT, hzG, hzQ⟩
        obtain ⟨s, u, hu, rfl⟩ := mem_iUnion.mp hzT
        have hsr : s = r := by
          by_contra hsr
          exact hzQ (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hsr, u, hu, rfl⟩⟩)
        subst hsr
        obtain ⟨v, hv, hvu⟩ : At.param j u ∈ At.param j '' Ioo (e - η) (e + η) :=
          hGB ▸ ⟨hzG, At.param_mem_BCF ((hab s).2 hu)⟩
        have hvdom : v ∈ At.dom j :=
          (hball' v (by rw [abs_lt]; constructor <;> linarith [hv.1, hv.2])).1
        have huv : v = u := At.injOn_param_BCF j hvdom ((hab s).2 hu) hvu
        subst huv
        have hm := h2 v hu hv
        refine ⟨σ * (v - e), ⟨⟨by linarith [hm.1], hm.2⟩, mem_Ici.mpr hm.1⟩, ?_⟩
        change At.param j (e + σ * (σ * (v - e))) = At.param j v
        rw [← mul_assoc, hσ, one_mul, add_sub_cancel]
      · rintro ⟨t, ⟨ht, ht0⟩, rfl⟩
        have htI : t ∈ Ico (0 : ℝ) η := ⟨ht0, ht.2⟩
        refine ⟨mem_iUnion.mpr ⟨r, _, h1 t htI, rfl⟩, ?_, ?_⟩
        · have hv : e + σ * t ∈ Ioo (e - η) (e + η) := by
            have habs : |σ * t| < η := by
              rw [hσabs, abs_of_nonneg (mem_Ici.mp ht0)]
              exact ht.2
            have h := abs_lt.mp habs
            exact ⟨by linarith [h.1], by linarith [h.2]⟩
          have : At.param j (e + σ * t) ∈ G ∩ Bs := hGB ▸ ⟨_, hv, rfl⟩
          exact this.1
        · exact (hball' _ (by rw [add_sub_cancel_left, hσabs, abs_lt]; constructor <;>
            linarith [ht.1, ht.2])).2
    refine ⟨At.halfChart_BCF j σ e hσ (Ioo (-η) η) (G ∩ Qᶜ) isOpen_Ioo hVW
      (hG.inter hQc.isOpen_compl) hTO, ?_⟩
    rw [halfChart_O_BCF]
    refine ⟨?_, hyQ⟩
    have : At.param j e ∈ G ∩ Bs := hGB ▸ ⟨e, ⟨by linarith, by linarith⟩, rfl⟩
    exact this.1

include At in
/-- **K0 (D74-9): the shared `K₃` kernel.** For a compact `Kset ⊆ Bs`, a finite `Fset` (the face
points `∂C₃`) and a regular `Dset ⊆ Bs` (`C₃`) whose relative frontier lies in `Kset`, there is a
compact smooth one-dimensional domain `D` of `Bs` — finitely many smooth regular arcs AND loops — with
`Kset ⊆ int_{Bs} D`, relative frontier of `D` disjoint from `Fset`, and `D ∩ Dset` regular in `Bs`. -/
theorem exists_compact_oneManifold_choice_BCF {Kset Fset Dset : Set H} (hK : IsCompact Kset)
    (hKB : Kset ⊆ Bs) (hF : Fset.Finite)
    (hDreg : Dset ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs)))
    (hKfront : Dset \ Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs) ⊆ Kset) :
    ∃ D : SmoothCompactOneDomain_BCF Bs,
      Kset ⊆ Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set Bs) ∧
      Disjoint (D.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set Bs)) Fset ∧
      D.carrier ∩ Dset ⊆
        closure (Subtype.val '' interior (Subtype.val ⁻¹' (D.carrier ∩ Dset) : Set Bs)) := by
  obtain ⟨n, c, a, b, hab, hgen, hcpt, -, hcov, hreg⟩ :=
    At.exists_cover_union_generic_BCF hK hKB hF hDreg hKfront
  set T := ⋃ r, At.param (c r) '' Icc (a r) (b r) with hT
  have hch : ∀ y : T, ∃ d : HalfChart_BCF Bs T, (y : H) ∈ d.O := fun y =>
    At.exists_halfChart_of_cover_BCF (fun r => ⟨(hab r).1, (hab r).2.1⟩) hgen y.2
  choose ch hch using hch
  obtain ⟨D, hD⟩ := exists_smoothCompactOneDomain_BCF ⟨ch, hch⟩ hcpt
  refine ⟨D, hD ▸ hcov, ?_, hD ▸ hreg⟩
  rw [hD, Set.disjoint_left]
  rintro y ⟨hyT, hyI⟩ hyF
  obtain ⟨r, t, ht, rfl⟩ := mem_iUnion.mp hyT
  by_cases hto : t ∈ Ioo (a r) (b r)
  · exact hyI (At.image_Ioo_subset_relInterior_BCF (hab r).2.1
      (subset_iUnion (fun r => At.param (c r) '' Icc (a r) (b r)) r) ⟨t, hto, rfl⟩)
  · have hend : t = a r ∨ t = b r := by
      by_contra h
      push Not at h
      exact hto ⟨lt_of_le_of_ne ht.1 (Ne.symm h.1), lt_of_le_of_ne ht.2 h.2⟩
    rcases hend with rfl | rfl
    · exact (hab r).2.2.1 hyF
    · exact (hab r).2.2.2 hyF

include At in
/-- **K0 in the D74-9 form** `exists_compact_oneManifold_choice74`: a compact `Q ⊆ Bs` and a finite
`F` admit a compact smooth one-dimensional domain `K` (arcs AND loops) with `Q ⊆ int_{Bs} K` and
`∂_{Bs} K ∩ F = ∅`. -/
theorem exists_compact_oneManifold_choice74_BCF {Q F : Set H} (hQ : IsCompact Q) (hQB : Q ⊆ Bs)
    (hF : F.Finite) :
    ∃ K : SmoothCompactOneDomain_BCF Bs,
      Q ⊆ Subtype.val '' interior (Subtype.val ⁻¹' K.carrier : Set Bs) ∧
      Disjoint (K.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' K.carrier : Set Bs)) F := by
  obtain ⟨K, hQK, hKF, -⟩ := At.exists_compact_oneManifold_choice_BCF (Dset := ∅) hQ hQB hF
    (empty_subset _) (by rw [empty_sdiff]; exact empty_subset _)
  exact ⟨K, hQK, hKF⟩

end GraphAtlas1_BCF

end DifferentialGeometry.Topology
