import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverBCF

/-!
# The shared `K₃` kernel, part (K-a'): generic endpoints (lane B-BCF134)

Blueprint `master207B.tex`, ZSP04 / BCF01: the chart intervals of `K₃` are "enlarged slightly with
endpoints avoiding" a finite set. For the one-manifold structure of
`K₃ = ⋃_r param (c r) '' [a r, b r]` the `2n` endpoints must moreover be pairwise distinct (no two
intervals end at the same point).

* `GraphAtlas1_BCF.exists_enlarge_BCF`: one closed chart interval is enlarged inside its domain to
  new endpoints outside a finite set, with distinct endpoints;
* `GraphAtlas1_BCF.exists_enlarge_family_BCF`: a finite family is enlarged simultaneously so that
  the `2n` endpoints are pairwise distinct and outside a finite set;
* `GraphAtlas1_BCF.exists_cover_union_generic_BCF`: part (K-a) with generic endpoints.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Topology

namespace GraphAtlas1_BCF

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}
  (At : GraphAtlas1_BCF ι Bs)

/-- **Enlarging one chart interval** to endpoints outside a finite set `G`, inside the domain. -/
theorem exists_enlarge_BCF {j : ι} {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ At.dom j)
    {G : Set H} (hG : G.Finite) :
    ∃ a' b', a' < a ∧ b < b' ∧ Icc a' b' ⊆ At.dom j ∧ At.param j a' ∉ G ∧ At.param j b' ∉ G ∧
      At.param j a' ≠ At.param j b' := by
  obtain ⟨δa, hδa, hba⟩ := Metric.isOpen_iff.mp (At.isOpen_dom j) a (hsub (left_mem_Icc.mpr hab.le))
  obtain ⟨δb, hδb, hbb⟩ :=
    Metric.isOpen_iff.mp (At.isOpen_dom j) b (hsub (right_mem_Icc.mpr hab.le))
  have hGc : (At.coord j '' G).Finite := hG.image _
  obtain ⟨a', ⟨ha1, ha2⟩, haG⟩ :=
    ((Set.Ioo_infinite (by linarith : a - δa / 2 < a)).sdiff hGc).nonempty
  obtain ⟨b', ⟨hb1, hb2⟩, hbG⟩ :=
    ((Set.Ioo_infinite (by linarith : b < b + δb / 2)).sdiff hGc).nonempty
  have hIcc : Icc a' b' ⊆ At.dom j := by
    intro t ht
    by_cases h1 : t < a
    · exact hba (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1])
    · by_cases h2 : b < t
      · exact hbb (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2])
      · exact hsub ⟨not_lt.mp h1, not_lt.mp h2⟩
  have hca : At.coord j (At.param j a') = a' :=
    At.coord_param j a' (hIcc (left_mem_Icc.mpr (by linarith)))
  have hcb : At.coord j (At.param j b') = b' :=
    At.coord_param j b' (hIcc (right_mem_Icc.mpr (by linarith)))
  refine ⟨a', b', ha2, hb1, hIcc, fun hm => haG ⟨_, hm, hca⟩, fun hm => hbG ⟨_, hm, hcb⟩,
    fun he => ?_⟩
  have : a' = b' := by rw [← hca, ← hcb, he]
  linarith

/-- **Generic endpoints**: each interval has two distinct endpoint points, and two different
intervals share no endpoint point. -/
def GenericEndpoints_BCF {n : ℕ} (c : Fin n → ι) (a b : Fin n → ℝ) : Prop :=
  (∀ r, At.param (c r) (a r) ≠ At.param (c r) (b r)) ∧
    ∀ r s, r ≠ s → ∀ p ∈ ({At.param (c r) (a r), At.param (c r) (b r)} : Set H),
      p ∉ ({At.param (c s) (a s), At.param (c s) (b s)} : Set H)

/-- **Enlarging a finite family** so that the endpoints are generic and outside a finite set `G`. -/
theorem exists_enlarge_family_BCF {G : Set H} (hG : G.Finite) :
    ∀ (n : ℕ) (c : Fin n → ι) (a b : Fin n → ℝ),
      (∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r)) →
      ∃ a' b' : Fin n → ℝ, (∀ r, a' r < a r ∧ b r < b' r ∧ Icc (a' r) (b' r) ⊆ At.dom (c r)) ∧
        (∀ r, At.param (c r) (a' r) ∉ G ∧ At.param (c r) (b' r) ∉ G) ∧
        At.GenericEndpoints_BCF c a' b' := by
  intro n
  induction n with
  | zero =>
    intro c a b _
    exact ⟨a, b, fun r => r.elim0, fun r => r.elim0, fun r => r.elim0, fun r => r.elim0⟩
  | succ n ih =>
    intro c a b hab
    obtain ⟨a₁, b₁, hab₁, hG₁, hgen₁, hdis₁⟩ := ih (fun r => c r.succ) (fun r => a r.succ)
      (fun r => b r.succ) (fun r => hab r.succ)
    set Old : Set H := (range fun r => At.param (c r.succ) (a₁ r)) ∪
      (range fun r => At.param (c r.succ) (b₁ r)) with hOld
    have hG' : (G ∪ Old).Finite := hG.union ((finite_range _).union (finite_range _))
    obtain ⟨a₀, b₀, ha₀, hb₀, hI₀, haG, hbG, hne⟩ := At.exists_enlarge_BCF (hab 0).1 (hab 0).2 hG'
    have hnewOld : ∀ q ∈ ({At.param (c 0) a₀, At.param (c 0) b₀} : Set H), q ∉ Old := by
      rintro q (rfl | rfl) hq
      · exact haG (Or.inr hq)
      · exact hbG (Or.inr hq)
    have holdIn : ∀ r, At.param (c r.succ) (a₁ r) ∈ Old ∧ At.param (c r.succ) (b₁ r) ∈ Old :=
      fun r => ⟨Or.inl ⟨r, rfl⟩, Or.inr ⟨r, rfl⟩⟩
    refine ⟨Fin.cons a₀ a₁, Fin.cons b₀ b₁, fun r => ?_, fun r => ?_, fun r => ?_, ?_⟩
    · refine Fin.cases ?_ (fun r => ?_) r
      · exact ⟨ha₀, hb₀, hI₀⟩
      · simpa only [Fin.cons_succ] using hab₁ r
    · refine Fin.cases ?_ (fun r => ?_) r
      · exact ⟨fun h => haG (Or.inl h), fun h => hbG (Or.inl h)⟩
      · simpa only [Fin.cons_succ] using hG₁ r
    · refine Fin.cases ?_ (fun r => ?_) r
      · simpa only [Fin.cons_zero] using hne
      · simpa only [Fin.cons_succ] using hgen₁ r
    · intro r s hrs
      induction r using Fin.cases with
      | zero =>
        induction s using Fin.cases with
        | zero => exact (hrs rfl).elim
        | succ s =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          intro q hq hq'
          exact hnewOld q hq (by
            rcases hq' with rfl | rfl
            · exact (holdIn s).1
            · exact (holdIn s).2)
      | succ r =>
        induction s using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          intro q hq hq'
          exact hnewOld q hq' (by
            rcases hq with rfl | rfl
            · exact (holdIn r).1
            · exact (holdIn r).2)
        | succ s =>
          simp only [Fin.cons_succ]
          exact hdis₁ r s fun h => hrs (h ▸ rfl)

/-- **(K-a) with generic endpoints**: the cover of `exists_cover_union_BCF` with the `2n` endpoints
pairwise distinct and outside the finite set `Fset`. -/
theorem exists_cover_union_generic_BCF {Kset Fset Dset : Set H} (hK : IsCompact Kset)
    (hKB : Kset ⊆ Bs) (hF : Fset.Finite)
    (hDreg : Dset ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs)))
    (hKfront : Dset \ Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs) ⊆ Kset) :
    ∃ (n : ℕ) (c : Fin n → ι) (a b : Fin n → ℝ),
      (∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r) ∧ At.param (c r) (a r) ∉ Fset ∧
        At.param (c r) (b r) ∉ Fset) ∧ At.GenericEndpoints_BCF c a b ∧
      IsCompact (⋃ r, At.param (c r) '' Icc (a r) (b r)) ∧
      (⋃ r, At.param (c r) '' Icc (a r) (b r)) ⊆ Bs ∧
      Kset ⊆ Subtype.val '' interior
        (Subtype.val ⁻¹' (⋃ r, At.param (c r) '' Icc (a r) (b r)) : Set Bs) ∧
      (⋃ r, At.param (c r) '' Icc (a r) (b r)) ∩ Dset ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' ((⋃ r, At.param (c r) '' Icc (a r) (b r)) ∩ Dset) : Set Bs)) := by
  obtain ⟨n, c, a, b, hab, hcov⟩ := At.exists_interval_cover_BCF hK hKB hF
  obtain ⟨a', b', hab', hF', hgen⟩ := At.exists_enlarge_family_BCF hF n c a b
    (fun r => ⟨(hab r).1, (hab r).2.1⟩)
  have hlt : ∀ r, a' r < b' r := fun r => by linarith [(hab' r).1, (hab' r).2.1, (hab r).1]
  have hcov' : Kset ⊆ ⋃ r, At.param (c r) '' Ioo (a' r) (b' r) := by
    intro y hy
    obtain ⟨r, t, ht, rfl⟩ := mem_iUnion.mp (hcov hy)
    exact mem_iUnion.mpr ⟨r, t, ⟨(hab' r).1.trans ht.1, ht.2.trans (hab' r).2.1⟩, rfl⟩
  exact ⟨n, c, a', b', fun r => ⟨hlt r, (hab' r).2.2, (hF' r).1, (hF' r).2⟩, hgen,
    At.cover_union_spec_BCF (fun r => ⟨hlt r, (hab' r).2.2⟩) hcov' hDreg hKfront⟩

end GraphAtlas1_BCF

end DifferentialGeometry.Topology
