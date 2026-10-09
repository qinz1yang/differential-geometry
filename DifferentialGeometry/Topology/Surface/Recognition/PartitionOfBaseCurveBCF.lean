import DifferentialGeometry.Topology.Surface.Recognition.DiskRimBaseBCF

/-!
# The embedded face partition from the base curve (lane S-BCF03b; BCF03 G7 part 1 assembly kernel)

Generic combinatorial lemmas of the assembly: a preconnected set meeting a connected component of a
set lies in it (`subset_component_of_meets_BCF`), and the degree count of the disks over an arc
(`card_filter_eq_two_BCF`) or a loop (`card_filter_eq_zero_BCF`).
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

section Generic

/-- A preconnected subset of `Bd` meeting the component of `x` in `Bd` lies in it. -/
theorem subset_component_of_meets_BCF {Wt : Type*} [TopologicalSpace Wt] {Bd s : Set Wt}
    (hs : IsPreconnected s) (hsB : s ⊆ Bd) {x q : Wt} (hq : q ∈ s)
    (hqY : q ∈ connectedComponentIn Bd x) : s ⊆ connectedComponentIn Bd x := by
  rw [connectedComponentIn_eq hqY]
  exact hs.subset_connectedComponentIn hq hsB

/-- Exactly two disks over an arc: the two end points of the arc each carry one disk. -/
theorem card_filter_eq_two_BCF {I J H : Type*} [Fintype I] [DecidableEq J] (side : I → J)
    (β : I → H) (hinj : Injective β) (j : J) {e₀ e₁ : H} (hne : e₀ ≠ e₁)
    (hsub : ∀ i, side i = j → β i = e₀ ∨ β i = e₁) (h0 : ∃ i, side i = j ∧ β i = e₀)
    (h1 : ∃ i, side i = j ∧ β i = e₁) :
    (Finset.univ.filter (fun i => side i = j)).card = 2 := by
  classical
  obtain ⟨i₀, hs₀, hb₀⟩ := h0
  obtain ⟨i₁, hs₁, hb₁⟩ := h1
  rw [Finset.card_eq_two]
  refine ⟨i₀, i₁, fun h => hne (by rw [← hb₀, ← hb₁, h]), ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hi
    rcases hsub i hi with h | h
    · exact Or.inl (hinj (h.trans hb₀.symm))
    · exact Or.inr (hinj (h.trans hb₁.symm))
  · rintro (rfl | rfl)
    · exact hs₀
    · exact hs₁

/-- No disk over a loop. -/
theorem card_filter_eq_zero_BCF {I J : Type*} [Fintype I] [DecidableEq J] (side : I → J) (j : J)
    (hempty : ∀ i, side i ≠ j) : (Finset.univ.filter (fun i => side i = j)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun i _ => hempty i

end Generic


section RimBase

variable {Wt H : Type*} [TopologicalSpace Wt] {fib₀ fib₁ : H → Set Wt} {f₁ f₂ : Wt → H}
  {T : Wt → ℝ} {c : ℝ} {X₁ X₂ Bd Rc : Set Wt} {Z0 : H → Prop}

/-- **The rim base points.** Every horizontal disk has a rim base point `bpt y` on the base curve
at which the zero-coordinate predicate holds; `bpt` is injective on the horizontal disks and every
zero-coordinate point of the base curve is a rim base point. -/
theorem exists_rimBasePoint_BCF (hfib₀ : ∀ y, fib₀ y = X₁ ∩ f₁ ⁻¹' {y})
    (hfib₁ : ∀ y, fib₁ y = X₂ ∩ f₂ ⁻¹' {y})
    (hdisk : ∀ p ∈ Bd ∩ X₂, ∃ ed : fib₁ (f₂ p) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = rim_BCF fib₁ T c (f₂ p))
    (hF1 : ∀ p ∈ Bd ∩ X₂, T p = c → rim_BCF fib₁ T c (f₂ p) = fib₀ (f₁ p))
    (hrim : ∀ p ∈ Bd ∩ X₂, p ∈ Rc ↔ T p = c)
    (hHe : ∀ p ∈ Bd ∩ X₂, ∀ q ∈ X₂, f₂ q = f₂ p → q ∈ Bd ∩ X₂)
    (hE : ∀ y ∈ f₁ '' (Bd ∩ Rc), Z0 y ↔ ∃ p ∈ Bd ∩ X₂, T p = c ∧ f₁ p = y) :
    ∃ bpt : H → H, (∀ y ∈ f₂ '' (Bd ∩ X₂), rim_BCF fib₁ T c y = fib₀ (bpt y) ∧
      (rim_BCF fib₁ T c y).Nonempty ∧ rim_BCF fib₁ T c y ⊆ Bd ∩ Rc ∧
      bpt y ∈ f₁ '' (Bd ∩ Rc) ∧ Z0 (bpt y)) ∧ InjOn bpt (f₂ '' (Bd ∩ X₂)) ∧
      ∀ e ∈ f₁ '' (Bd ∩ Rc), Z0 e → ∃ y ∈ f₂ '' (Bd ∩ X₂), bpt y = e := by
  have hrb : ∀ y ∈ f₂ '' (Bd ∩ X₂), ∃ b : H, rim_BCF fib₁ T c y = fib₀ b ∧
      (rim_BCF fib₁ T c y).Nonempty ∧ rim_BCF fib₁ T c y ⊆ Bd ∩ Rc ∧
      ∀ q ∈ rim_BCF fib₁ T c y, f₁ q = b := fun y hy =>
    exists_rimBase_BCF hfib₀ hdisk hF1 hrim hHe hfib₁ hy
  choose! bpt hbrim hbne hbS hbf using hrb
  have hbΓ : ∀ y ∈ f₂ '' (Bd ∩ X₂), bpt y ∈ f₁ '' (Bd ∩ Rc) := by
    intro y hy
    obtain ⟨q, hq⟩ := hbne y hy
    exact ⟨q, hbS y hy hq, hbf y hy q hq⟩
  have hbZ : ∀ y ∈ f₂ '' (Bd ∩ X₂), Z0 (bpt y) := by
    intro y hy
    obtain ⟨q, hq⟩ := hbne y hy
    refine (hE _ (hbΓ y hy)).mpr ⟨q, ?_, hq.2, hbf y hy q hq⟩
    have hq1 : q ∈ fib₁ y := hq.1
    rw [hfib₁] at hq1
    exact ⟨(hbS y hy hq).1, hq1.1⟩
  refine ⟨bpt, fun y hy => ⟨hbrim y hy, hbne y hy, hbS y hy, hbΓ y hy, hbZ y hy⟩, ?_, ?_⟩
  · intro y hy y' hy' hyy'
    refine rimBase_injOn_BCF (fib₀ := fib₀) (T := T) (c := c) (b := bpt y) hfib₁ (hbrim y hy) ?_
      (hbne y hy)
    rw [hyy']
    exact hbrim y' hy'
  · intro e he hZe
    obtain ⟨p, hpHe, hpT, hpf⟩ := (hE e he).mp hZe
    have hy : f₂ p ∈ f₂ '' (Bd ∩ X₂) := ⟨p, hpHe, rfl⟩
    refine ⟨f₂ p, hy, ?_⟩
    have hp : p ∈ rim_BCF fib₁ T c (f₂ p) := ⟨by rw [hfib₁]; exact ⟨hpHe.2, rfl⟩, hpT⟩
    exact (hbf (f₂ p) hy p hp).symm.trans hpf

end RimBase


section Main

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {Wt H : Type*} [TopologicalSpace Wt] [T2Space Wt] [TopologicalSpace H] [T2Space H]
  {fib₀ fib₁ : H → Set Wt} {f₁ f₂ : Wt → H} {T : Wt → ℝ} {c : ℝ} {X₁ X₂ Bd Rc : Set Wt}
  {B₀ : Set H} {n m : ℕ} {a : Fin n → ℝ → H} {l : Fin m → Circle → H} {Z0 : H → Prop}

/-- **The embedded face partition of every component of `∂M₂` from the components of the base
curve** (abstract assembly of BCF03 G7 part 1). -/
theorem exists_partition_of_components_BCF (hfib₀ : ∀ y, fib₀ y = X₁ ∩ f₁ ⁻¹' {y})
    (hfib₁ : ∀ y, fib₁ y = X₂ ∩ f₂ ⁻¹' {y}) (hS : IsClosed (Bd ∩ Rc))
    (hRcX : Rc ⊆ X₁) (hf₁ : ContinuousOn f₁ X₁)
    (hsat : ∀ p ∈ Bd ∩ Rc, ∀ q ∈ X₁, f₁ q = f₁ p → q ∈ Bd ∩ Rc) (hB : f₁ '' (Bd ∩ Rc) ⊆ B₀)
    (hch : ∀ y ∈ f₁ '' (Bd ∩ Rc), ∃ (σ : E2 → H) (φ : E2 × Circle → Wt) (O : Set H) (x₀ : E2),
      σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧ range σ = B₀ ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = X₁ ∩ f₁ ⁻¹' range σ ∧ ∀ x z, f₁ (φ (x, z)) = σ x)
    (hHe : ∀ p ∈ Bd ∩ X₂, ∀ q ∈ X₂, f₂ q = f₂ p → q ∈ Bd ∩ X₂)
    (hdisk : ∀ p ∈ Bd ∩ X₂, ∃ ed : fib₁ (f₂ p) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = rim_BCF fib₁ T c (f₂ p))
    (hF1 : ∀ p ∈ Bd ∩ X₂, T p = c → rim_BCF fib₁ T c (f₂ p) = fib₀ (f₁ p))
    (hcover : Bd ⊆ (Bd ∩ X₂) ∪ (Bd ∩ Rc)) (hrim : ∀ p ∈ Bd ∩ X₂, p ∈ Rc ↔ T p = c)
    (ha : ∀ k, ContinuousOn (a k) (Icc 0 1) ∧ InjOn (a k) (Icc 0 1))
    (hl : ∀ j, Continuous (l j) ∧ Injective (l j)) (hdis : Pairwise (Disjoint on compSet_BCF a l))
    (hcov : f₁ '' (Bd ∩ Rc) = ⋃ k, compSet_BCF a l k)
    (hZarc : ∀ k, ∀ y ∈ a k '' Icc 0 1, Z0 y ↔ y = a k 0 ∨ y = a k 1)
    (hZloop : ∀ j, ∀ y ∈ range (l j), ¬ Z0 y)
    (hE : ∀ y ∈ f₁ '' (Bd ∩ Rc), Z0 y ↔ ∃ p ∈ Bd ∩ X₂, T p = c ∧ f₁ p = y) :
    ∀ x ∈ Bd, ∃ Pt : EmbeddedFacePartition_BCF ↥(connectedComponentIn Bd x),
      (∀ i, ∃ y ∈ f₂ '' (Bd ∩ X₂),
        Subtype.val '' Pt.disk i = connectedComponentIn Bd x ∩ fib₁ y) ∧
      Subtype.val '' (⋃ j, Pt.piece j) = connectedComponentIn Bd x ∩ Rc := by
  classical
  intro x hx
  obtain ⟨bpt, hbpt, hbinj, hbsurj⟩ := exists_rimBasePoint_BCF hfib₀ hfib₁ hdisk hF1 hrim hHe hE
  have hSX : Bd ∩ Rc ⊆ X₁ := fun p hp => hRcX hp.2
  have hPcl := piece_closed_BCF (a := a) (l := l) hS (hf₁.mono hSX) (fun k => (ha k).1)
    (fun j => (hl j).1)
  have hPne := piece_nonempty_BCF (S := Bd ∩ Rc) (f := f₁) (a := a) (l := l) hcov
  have hPdis := piece_disjoint_BCF (S := Bd ∩ Rc) (f := f₁) hdis
  have hPun := iUnion_piece_BCF (S := Bd ∩ Rc) (f := f₁) (a := a) (l := l) hcov
  have hPconn := isPreconnected_piece_BCF hSX hsat hcov hB hch ha hl
  have hannP := annulus_param_piece_BCF hSX hsat hcov hB hch ha
  have hcircP := circle_base_piece_BCF hSX hsat hcov hB hf₁ hch hl
  have hPS : ∀ k, piece_BCF (Bd ∩ Rc) f₁ a l k ⊆ Bd ∩ Rc := fun k => piece_subset_BCF k
  set Y : Set Wt := connectedComponentIn Bd x with hYdef
  set P : Fin n ⊕ Fin m → Set Wt := piece_BCF (Bd ∩ Rc) f₁ a l with hPdef
  have hYBd : Y ⊆ Bd := connectedComponentIn_subset Bd x
  have hPY : ∀ k, (P k ∩ Y).Nonempty → P k ⊆ Y := by
    rintro k ⟨q, hqP, hqY⟩
    exact subset_component_of_meets_BCF (hPconn k) (fun p hp => (hPS k hp).1) hqP hqY
  have hmemP : ∀ p ∈ Bd ∩ Rc, ∃ k, p ∈ P k := by
    intro p hp
    have : p ∈ ⋃ k, P k := hPun ▸ hp
    exact mem_iUnion.mp this
  set Dset : Set H := f₂ '' (Bd ∩ X₂) with hDset
  have hDcl : ∀ y ∈ Dset, IsClosed (fib₁ y) := fun y hy =>
    (isCompact_edgeDisk_BCF hdisk hy).isClosed
  have hDpre : ∀ y ∈ Dset, IsPreconnected (fib₁ y) := fun y hy =>
    isPreconnected_edgeDisk_BCF hdisk hy
  have hDHe : ∀ y ∈ Dset, fib₁ y ⊆ Bd ∩ X₂ := by
    rintro y ⟨p, hp, rfl⟩ q hq
    rw [hfib₁] at hq
    exact hHe p hp q hq.1 hq.2
  have hDY : ∀ y ∈ Dset, (fib₁ y ∩ Y).Nonempty → fib₁ y ⊆ Y := by
    rintro y hy ⟨q, hqD, hqY⟩
    exact subset_component_of_meets_BCF (hDpre y hy) (fun p hp => (hDHe y hy hp).1) hqD hqY
  have hbmem : ∀ y ∈ Dset, ∃ k, bpt y ∈ compSet_BCF a l k := fun y hy =>
    mem_iUnion.mp (hcov ▸ (hbpt y hy).2.2.2.1)
  have hKne : Nonempty (Fin n ⊕ Fin m) := by
    by_contra hne
    have hK : IsEmpty (Fin n ⊕ Fin m) := not_nonempty_iff.mp hne
    rcases hcover hx with hxHe | hxS
    · have hy : f₂ x ∈ f₂ '' (Bd ∩ X₂) := ⟨x, hxHe, rfl⟩
      have hΓ := (hbpt (f₂ x) hy).2.2.2.1
      rw [hcov] at hΓ
      exact hK.false (mem_iUnion.mp hΓ).choose
    · have hΓ : f₁ x ∈ f₁ '' (Bd ∩ Rc) := ⟨x, hxS, rfl⟩
      rw [hcov] at hΓ
      exact hK.false (mem_iUnion.mp hΓ).choose
  choose! ks hks using hbmem
  have hks_uniq : ∀ y ∈ Dset, ∀ k, bpt y ∈ compSet_BCF a l k → k = ks y := by
    intro y hy k hk
    by_contra hne
    exact (Set.disjoint_left.mp (hdis hne) hk) (hks y hy)
  have hrimf : ∀ y ∈ Dset, ∀ q ∈ rim_BCF fib₁ T c y, f₁ q = bpt y := by
    intro y hy q hq
    have : q ∈ fib₀ (bpt y) := (hbpt y hy).1 ▸ hq
    rw [hfib₀] at this
    exact this.2
  have hrimP : ∀ y ∈ Dset, rim_BCF fib₁ T c y ⊆ P (ks y) := by
    intro y hy q hq
    refine ⟨(hbpt y hy).2.2.1 hq, ?_⟩
    change f₁ q ∈ compSet_BCF a l (ks y)
    rw [hrimf y hy q hq]
    exact hks y hy
  have hDP : ∀ y ∈ Dset, ∀ k, fib₁ y ∩ P k ⊆ rim_BCF fib₁ T c y := by
    rintro y hy k q ⟨hqD, hqP⟩
    exact ⟨hqD, (hrim q (hDHe y hy hqD)).mp (hPS k hqP).2⟩
  have hDPk : ∀ y ∈ Dset, ∀ k, (fib₁ y ∩ P k).Nonempty → k = ks y := by
    rintro y hy k ⟨q, hq⟩
    have hf : f₁ q = bpt y := hrimf y hy q (hDP y hy k hq)
    refine hks_uniq y hy k ?_
    have hqk : f₁ q ∈ compSet_BCF a l k := hq.2.2
    rwa [hf] at hqk
  have hEfin : {e : H | e ∈ f₁ '' (Bd ∩ Rc) ∧ Z0 e}.Finite := by
    refine (Set.finite_iUnion (fun k : Fin n => (Set.toFinite ({a k 0, a k 1} : Set H)))).subset ?_
    rintro e ⟨he, hZe⟩
    have : e ∈ ⋃ k, compSet_BCF a l k := hcov ▸ he
    obtain ⟨k, hk⟩ := mem_iUnion.mp this
    rcases k with k | j
    · exact mem_iUnion.mpr ⟨k, (hZarc k e hk).mp hZe⟩
    · exact (hZloop j e hk hZe).elim
  have hIfin : {y : H | y ∈ Dset ∧ fib₁ y ⊆ Y}.Finite := by
    refine Set.Finite.of_injOn (f := bpt) (t := {e | e ∈ f₁ '' (Bd ∩ Rc) ∧ Z0 e}) ?_
      (hbinj.mono fun y hy => hy.1) hEfin
    intro y hy
    exact ⟨(hbpt y hy.1).2.2.2.1, (hbpt y hy.1).2.2.2.2⟩
  have hPksY : ∀ y ∈ Dset, fib₁ y ⊆ Y → P (ks y) ⊆ Y := by
    intro y hy hyY
    obtain ⟨q, hq⟩ := (hbpt y hy).2.1
    exact hPY _ ⟨q, hrimP y hy hq, hyY hq.1⟩
  -- the index types
  let I : Type _ := ↥{y : H | y ∈ Dset ∧ fib₁ y ⊆ Y}
  let J : Type _ := {k : Fin n ⊕ Fin m // P k ⊆ Y}
  let _ : Fintype I := hIfin.fintype
  have hβinj : Injective fun i : I => bpt i.1 := fun i i' h => Subtype.ext (hbinj i.2.1 i'.2.1 h)
  let side : I → J := fun i => ⟨ks i.1, hPksY i.1 i.2.1 i.2.2⟩
  have hsideks : ∀ (i : I) (j : J), side i = j → ks i.1 = j.1 := fun i j h => congrArg Subtype.val h
  have hZi : ∀ i : I, Z0 (bpt i.1) := fun i => (hbpt i.1 i.2.1).2.2.2.2
  -- degree over an arc / a loop
  have hcard2 : ∀ (j : J) (k : Fin n), j.1 = .inl k →
      (Finset.univ.filter (fun i : I => side i = j)).card = 2 := by
    intro j k hjk
    have hend : ∀ e ∈ ({a k 0, a k 1} : Set H), ∃ i : I, side i = j ∧ bpt i.1 = e := by
      intro e he
      have heG : e ∈ compSet_BCF a l (.inl k) := by
        rcases he with rfl | he
        · exact ⟨0, ⟨le_refl _, zero_le_one⟩, rfl⟩
        · rw [mem_singleton_iff] at he
          exact ⟨1, ⟨zero_le_one, le_refl _⟩, he.symm⟩
      have heΓ : e ∈ f₁ '' (Bd ∩ Rc) := hcov ▸ mem_iUnion.mpr ⟨.inl k, heG⟩
      have hZe : Z0 e := (hZarc k e heG).mpr he
      obtain ⟨y, hy, hye⟩ := hbsurj e heΓ hZe
      have hksy : ks y = j.1 := by
        refine (hks_uniq y hy j.1 ?_).symm
        rw [hjk, hye]
        exact heG
      obtain ⟨q, hq⟩ := (hbpt y hy).2.1
      have hqP : q ∈ P j.1 := hksy ▸ hrimP y hy hq
      have hsub : fib₁ y ⊆ Y := hDY y hy ⟨q, hq.1, j.2 hqP⟩
      exact ⟨⟨y, hy, hsub⟩, Subtype.ext hksy, hye⟩
    refine card_filter_eq_two_BCF side (fun i : I => bpt i.1) hβinj j (e₀ := a k 0) (e₁ := a k 1)
      ?_ ?_ (hend _ (Or.inl rfl)) (hend _ (Or.inr rfl))
    · intro h
      have := (ha k).2 ⟨le_refl _, zero_le_one⟩ ⟨zero_le_one, le_refl _⟩ h
      norm_num at this
    · intro i hi
      have hG : bpt i.1 ∈ compSet_BCF a l (.inl k) := by
        have := hks i.1 i.2.1
        rwa [hsideks i j hi, hjk] at this
      exact (hZarc k _ hG).mp (hZi i)
  have hcard0 : ∀ (j : J) (j' : Fin m), j.1 = .inr j' →
      (Finset.univ.filter (fun i : I => side i = j)).card = 0 := by
    intro j j' hjk
    refine card_filter_eq_zero_BCF side j fun i hi => ?_
    have hG : bpt i.1 ∈ compSet_BCF a l (.inr j') := by
      have := hks i.1 i.2.1
      rwa [hsideks i j hi, hjk] at this
    exact hZloop j' _ hG (hZi i)
  have key : ∃ (Pt : EmbeddedFacePartition_BCF ↥Y) (eI : I ≃ Fin Pt.diskCount)
      (eJ : J ≃ Fin Pt.pieceCount), Pt.diskCount = Fintype.card I ∧
      Pt.pieceCount = Fintype.card J ∧ (∀ i, Pt.disk (eI i) = Subtype.val ⁻¹' fib₁ i.1) ∧
      (∀ j, Pt.piece (eJ j) = Subtype.val ⁻¹' P j.1) ∧ ∀ i, Pt.side (eI i) = eJ (side i) := by
    refine exists_embeddedFacePartition_of_family_BCF (Y := Y) (I := I) (J := J)
      (fun i => fib₁ i.1) (fun j => P j.1) side (fun i => i.2.2) (fun j => j.2)
      (fun i => hDcl i.1 i.2.1) (fun j => hPcl j.1) (fun j => hPne j.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- cover
      intro p hpY
      rcases hcover (hYBd hpY) with hpHe | hpS
      · left
        have hy : f₂ p ∈ Dset := ⟨p, hpHe, rfl⟩
        have hpD : p ∈ fib₁ (f₂ p) := by
          rw [hfib₁]
          exact ⟨hpHe.2, rfl⟩
        exact mem_iUnion.mpr ⟨⟨f₂ p, hy, hDY _ hy ⟨p, hpD, hpY⟩⟩, hpD⟩
      · right
        obtain ⟨k, hk⟩ := hmemP p hpS
        exact mem_iUnion.mpr ⟨⟨k, hPY k ⟨p, hk, hpY⟩⟩, hk⟩
    · -- disks pairwise disjoint
      intro i i' hii'
      have hne : i.1 ≠ i'.1 := fun h => hii' (Subtype.ext h)
      rw [Function.onFun, Set.disjoint_left]
      intro q hq hq'
      rw [hfib₁] at hq hq'
      exact hne (hq.2.symm.trans hq'.2)
    · -- pieces pairwise disjoint
      intro j j' hjj'
      exact hPdis fun e => hjj' (Subtype.ext e)
    · -- side
      intro i j hij
      exact Subtype.ext (hDPk i.1 i.2.1 j.1 hij).symm
    · -- degree
      rintro ⟨jj, hjP⟩
      rcases jj with k | j'
      · exact Or.inr (hcard2 ⟨.inl k, hjP⟩ k rfl)
      · exact Or.inl (hcard0 ⟨.inr j', hjP⟩ j' rfl)
    · -- disk parametrization
      rintro ⟨y, hyD, hyY⟩
      obtain ⟨p, hp, rfl⟩ := hyD
      obtain ⟨ed, hed⟩ := hdisk p hp
      obtain ⟨h, hc, hi, hr, himg⟩ := exists_diskParam_of_fibre_BCF ed hed
      have hyD' : f₂ p ∈ Dset := ⟨p, hp, rfl⟩
      refine ⟨h, hc, hi, hr, ?_⟩
      rw [himg]
      refine Subset.antisymm (fun q hq => ⟨hq.1, hrimP _ hyD' hq⟩) ?_
      exact hDP _ hyD' (ks (f₂ p))
    · -- annulus parametrization
      rintro ⟨jj, hjP⟩ hj2
      rcases jj with k | j'
      · obtain ⟨e, hec, hei, her, he0, he1⟩ := hannP k
        refine ⟨e, hec, hei, her, ?_⟩
        intro i hi
        have hks' : ks i.1 = .inl k := hsideks i _ hi
        have hrim' : fib₁ i.1 ∩ P (.inl k) = fib₀ (bpt i.1) := by
          rw [← (hbpt i.1 i.2.1).1, ← hks']
          exact Subset.antisymm (hDP _ i.2.1 _) fun q hq => ⟨hq.1, hrimP _ i.2.1 hq⟩
        have hG : bpt i.1 ∈ compSet_BCF a l (.inl k) := by
          have := hks i.1 i.2.1
          rwa [hks'] at this
        rcases (hZarc k _ hG).mp (hZi i) with h | h
        · left
          change fib₁ i.1 ∩ P (.inl k) = _
          rw [hrim', h, he0, hfib₀]
        · right
          change fib₁ i.1 ∩ P (.inl k) = _
          rw [hrim', h, he1, hfib₀]
      · exact absurd (hcard0 ⟨.inr j', hjP⟩ j' rfl) (by omega)
    · -- circle base
      rintro ⟨jj, hjP⟩ hj0
      rcases jj with k | j'
      · exact absurd (hcard2 ⟨.inl k, hjP⟩ k rfl) (by omega)
      · exact hcircP j'
  obtain ⟨Pt, eI, eJ, -, -, hdisk_eq, hpiece_eq, -⟩ := key
  refine ⟨Pt, ?_, ?_⟩
  · intro k
    have h := hdisk_eq (eI.symm k)
    rw [eI.apply_symm_apply] at h
    refine ⟨(eI.symm k).1, (eI.symm k).2.1, ?_⟩
    rw [h, Subtype.image_preimage_coe]
  · have hun : (⋃ k, Pt.piece k) = ⋃ j : J, Subtype.val ⁻¹' (P j.1) := by
      ext z
      simp only [mem_iUnion]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨eJ.symm k, ?_⟩
        have h := hpiece_eq (eJ.symm k)
        rw [eJ.apply_symm_apply] at h
        rw [← h]
        exact hk
      · rintro ⟨j, hj⟩
        exact ⟨eJ j, by rw [hpiece_eq j]; exact hj⟩
    rw [hun, Set.image_iUnion]
    ext p
    constructor
    · intro hp
      obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      obtain ⟨z, hz, rfl⟩ := hj
      exact ⟨j.2 hz, (hPS j.1 hz).2⟩
    · rintro ⟨hpY, hpRc⟩
      obtain ⟨k, hk⟩ := hmemP p ⟨hYBd hpY, hpRc⟩
      exact mem_iUnion.mpr ⟨⟨k, hPY k ⟨p, hk, hpY⟩⟩, ⟨p, hpY⟩, hk, rfl⟩

end Main

end DifferentialGeometry.Topology.Surface
