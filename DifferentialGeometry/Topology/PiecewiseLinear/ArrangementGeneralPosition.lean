import DifferentialGeometry.Topology.PiecewiseLinear.CellComplex
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def arrangementDirection {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ) (x : E) : Submodule ℝ E :=
  ⨅ k : {k : κ // l k x = 0}, LinearMap.ker (l k).linear

def arrangementLayer {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ) (x : E) : AffineSubspace ℝ E :=
  AffineSubspace.mk' x (arrangementDirection l x)

theorem mem_arrangementDirection_iff {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ) {x v : E} :
    v ∈ arrangementDirection l x ↔ ∀ k, l k x = 0 → (l k).linear v = 0 := by
  simp only [arrangementDirection, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]

theorem mem_arrangementLayer_iff {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ) {x y : E} :
    y ∈ arrangementLayer l x ↔ ∀ k, l k x = 0 → l k y = 0 := by
  rw [arrangementLayer, AffineSubspace.mem_mk', mem_arrangementDirection_iff]
  constructor
  · intro h k hk
    have hmap := (l k).linearMap_vsub y x
    calc
      l k y = l k y - l k x := by rw [hk, sub_zero]
      _ = (l k).linear (y - x) := by simpa only [vsub_eq_sub] using hmap.symm
      _ = 0 := by simpa only [vsub_eq_sub] using h k hk
  · intro h k hk
    have hmap := (l k).linearMap_vsub y x
    simpa only [vsub_eq_sub, h k hk, hk, sub_self] using hmap

theorem self_mem_arrangementLayer {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ) (x : E) :
    x ∈ arrangementLayer l x := by
  rw [mem_arrangementLayer_iff]
  exact fun _ h => h

theorem direction_arrangementLayer {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ) (x : E) :
    (arrangementLayer l x).direction = arrangementDirection l x :=
  AffineSubspace.direction_mk' _ _

theorem openCell_subset_arrangementLayer {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ) (x : E) :
    openCell l (signVec l x) ⊆ arrangementLayer l x := by
  intro y hy
  change y ∈ arrangementLayer l x
  rw [mem_arrangementLayer_iff]
  intro k hk
  have hsign := congrFun hy k
  exact sign_eq_zero_iff.mp (hsign.trans (sign_eq_zero_iff.mpr hk))

theorem arrangementLayer_eq_of_mem_openCell {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (hy : y ∈ openCell l (signVec l x)) : arrangementLayer l y = arrangementLayer l x := by
  ext z
  simp only [mem_arrangementLayer_iff]
  have hsign : signVec l y = signVec l x := hy
  constructor
  · intro h k hk
    apply h k
    have hsignk := congrFun hsign k
    exact sign_eq_zero_iff.mp (hsignk.trans (sign_eq_zero_iff.mpr hk))
  · intro h k hk
    apply h k
    have hsignk := congrFun hsign k
    exact sign_eq_zero_iff.mp (hsignk.symm.trans (sign_eq_zero_iff.mpr hk))

theorem openCell_mem_nhdsWithin_arrangementLayer {κ : Type*} [Finite κ]
    [FiniteDimensional ℝ E] (l : κ → E →ᵃ[ℝ] ℝ) (x : E) :
    openCell l (signVec l x) ∈ 𝓝[arrangementLayer l x] x := by
  let U : Set E := ⋂ k,
    ({y | 0 < l k x → 0 < l k y} ∩ {y | l k x < 0 → l k y < 0})
  have hUopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro k
    exact (isOpen_setOf_imp _ (isOpen_lt continuous_const (l k).continuous_of_finiteDimensional)).inter
      (isOpen_setOf_imp _ (isOpen_lt (l k).continuous_of_finiteDimensional continuous_const))
  have hxU : x ∈ U := by
    rw [mem_iInter]
    exact fun _ => ⟨id, id⟩
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
  refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
  rintro y ⟨hyU, hyL⟩
  funext k
  have hyUk := mem_iInter.mp hyU k
  change SignType.sign (l k y) = SignType.sign (l k x)
  rcases lt_trichotomy (l k x) 0 with hxneg | hxzero | hxpos
  · exact (sign_eq_neg_one_iff.mpr (hyUk.2 hxneg)).trans (sign_eq_neg_one_iff.mpr hxneg).symm
  · have hyzero := (mem_arrangementLayer_iff l).mp hyL k hxzero
    rw [hyzero, hxzero]
  · exact (sign_eq_one_iff.mpr (hyUk.1 hxpos)).trans (sign_eq_one_iff.mpr hxpos).symm

open Classical in
theorem exists_mem_openCell_notMem_affineSubspaces {κ ι : Type*} [Finite κ] [Finite ι]
    [FiniteDimensional ℝ E] (l : κ → E →ᵃ[ℝ] ℝ) (A : ι → AffineSubspace ℝ E)
    (x : E) (hA : ∀ i, ¬arrangementLayer l x ≤ A i) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ openCell l (signVec l x), dist y x < ε ∧ ∀ i, y ∉ A i := by
  let H := arrangementDirection l x
  let e : H →ᵃ[ℝ] E := H.subtype.toAffineMap + AffineMap.const ℝ H x
  let B : ι → AffineSubspace ℝ H := fun i => (A i).comap e
  have hB : ∀ i, B i ≠ ⊤ := by
    intro i hi
    apply hA i
    intro y hy
    let z : H := ⟨y - x, by
      change y - x ∈ arrangementDirection l x
      rw [← vsub_eq_sub, ← direction_arrangementLayer l x]
      exact AffineSubspace.vsub_mem_direction hy (self_mem_arrangementLayer l x)⟩
    have hz : z ∈ B i := by rw [hi]; exact Set.mem_univ z
    rw [AffineSubspace.mem_comap] at hz
    have heq : e z = y := by
      change (z : E) + x = y
      simp only [z]
      abel
    rwa [heq] at hz
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.mem_nhdsWithin_iff.mp (openCell_mem_nhdsWithin_arrangementLayer l x)
  obtain ⟨z, hzclose, hzavoid⟩ :=
    exists_mem_ball_notMem_affineSubspaces B hB (x := (0 : H)) (lt_min hε hδ)
  let y := e z
  have hyL : y ∈ arrangementLayer l x := by
    change (z : E) + x ∈ arrangementLayer l x
    rw [arrangementLayer, AffineSubspace.mem_mk']
    simpa only [vsub_eq_sub, add_sub_cancel_right, H] using z.property
  have hydist : dist y x = dist z 0 := by
    change dist ((z : E) + x) x = dist z 0
    simp only [dist_eq_norm, add_sub_cancel_right, sub_zero]
    rfl
  have hyball : y ∈ ball x δ := by
    rw [mem_ball, hydist]
    exact hzclose.trans_le (min_le_right ε δ)
  refine ⟨y, hball ⟨hyball, hyL⟩, ?_, ?_⟩
  · rw [hydist]
    exact hzclose.trans_le (min_le_left ε δ)
  · intro i hyA
    apply hzavoid i
    rw [AffineSubspace.mem_comap]
    exact hyA

open Classical in
theorem exists_small_vertexMap_avoiding_in_arrangement {κ ι η : Type*} [Finite κ] [Finite η]
    [FiniteDimensional ℝ E] (l : κ → E →ᵃ[ℝ] ℝ) (V B : Finset ι)
    (φ₀ : ι → E) (A : ι → η → AffineSubspace ℝ E)
    (hA : ∀ v ∈ V \ B, ∀ j, ¬arrangementLayer l (φ₀ v) ≤ A v j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → E, EqOn φ φ₀ ((V \ B : Finset ι) : Set ι)ᶜ ∧
      (∀ v, dist (φ v) (φ₀ v) < ε) ∧
        (∀ v, φ v ∈ openCell l (signVec l (φ₀ v))) ∧
          ∀ v ∈ V \ B, ∀ j, φ v ∉ A v j := by
  have hsel : ∀ v : ι, ∃ y : E,
      (v ∉ V \ B → y = φ₀ v) ∧ y ∈ openCell l (signVec l (φ₀ v)) ∧
        dist y (φ₀ v) < ε ∧ (v ∈ V \ B → ∀ j, y ∉ A v j) := by
    intro v
    by_cases hv : v ∈ V \ B
    · obtain ⟨y, hycell, hyclose, hyavoid⟩ :=
        exists_mem_openCell_notMem_affineSubspaces l (A v) (φ₀ v) (hA v hv) hε
      exact ⟨y, fun h => False.elim (h hv), hycell, hyclose, fun _ => hyavoid⟩
    · exact ⟨φ₀ v, fun _ => rfl, mem_openCell_signVec l (φ₀ v), by simpa using hε,
        fun h => False.elim (hv h)⟩
  choose φ hfix hcell hclose havoid using hsel
  exact ⟨φ, fun v hv => hfix v hv, hclose, hcell, fun v hv => havoid v hv⟩

open Classical in
theorem exists_small_update_affineIndependent_in_arrangement {κ ι η : Type*} [Finite κ] [Finite η]
    [FiniteDimensional ℝ E] (l : κ → E →ᵃ[ℝ] ℝ) (φ : ι → E) (v : ι)
    (s : η → Finset ι) (hv : ∀ j, v ∉ s j)
    (hs : ∀ j, AffineIndependent ℝ (fun w : s j => φ (w : ι)))
    (hroom : ∀ j, ¬arrangementLayer l (φ v) ≤ affineSpan ℝ (s j |>.image φ : Set E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ι → E, EqOn ψ φ ({v} : Set ι)ᶜ ∧ (∀ w, dist (ψ w) (φ w) < ε) ∧
      ψ v ∈ openCell l (signVec l (φ v)) ∧
        ∀ j, AffineIndependent ℝ (fun w : (insert v (s j) : Finset ι) => ψ (w : ι)) := by
  let A : η → AffineSubspace ℝ E := fun j => affineSpan ℝ (s j |>.image φ : Set E)
  obtain ⟨p, hpcell, hpclose, hpavoid⟩ :=
    exists_mem_openCell_notMem_affineSubspaces l A (φ v) hroom hε
  let ψ := Function.update φ v p
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact Function.update_of_ne (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw) p φ
  · intro w
    by_cases hw : w = v
    · subst w
      simpa only [ψ, Function.update_self] using hpclose
    · simpa only [ψ, Function.update_of_ne hw, dist_self] using hε
  · simpa only [ψ, Function.update_self] using hpcell
  · intro j
    exact affineIndependent_update_insert (hv j) (hs j) (hpavoid j)

open Classical in
theorem arrangementLayer_not_le_affineSpan_of_affineIndependent {κ ι : Type*} [Finite κ]
    [FiniteDimensional ℝ E] (l : κ → E →ᵃ[ℝ] ℝ) (φ : ι → E) (v : ι)
    (s : Finset ι) (hs : AffineIndependent ℝ (fun w : s => φ (w : ι)))
    (hcard : s.card ≤ Module.finrank ℝ (arrangementDirection l (φ v))) :
    ¬arrangementLayer l (φ v) ≤ affineSpan ℝ (s.image φ : Set E) := by
  intro hle
  by_cases hsempty : s = ∅
  · have hv := hle (self_mem_arrangementLayer l (φ v))
    rw [hsempty, Finset.image_empty, Finset.coe_empty, AffineSubspace.span_empty] at hv
    change φ v ∈ ((⊥ : AffineSubspace ℝ E) : Set E) at hv
    rw [AffineSubspace.bot_coe] at hv
    exact hv
  · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsempty
    let _ : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
    have hrange : Set.range (fun w : s => φ (w : ι)) = (s.image φ : Set E) := by
      ext y
      simp
    have hrank := hs.finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (Set.range (fun w : s => φ (w : ι)))) + 1 =
      Fintype.card s at hrank
    rw [hrange] at hrank
    have hdim := Submodule.finrank_mono (AffineSubspace.direction_le hle)
    rw [direction_arrangementLayer, direction_affineSpan] at hdim
    simp only [Fintype.card_coe] at hrank
    omega

def arrangementEnvelope {κ ι : Type*} (l : κ → E →ᵃ[ℝ] ℝ) (φ₀ : ι → E)
    (s : Finset ι) : AffineSubspace ℝ E :=
  affineSpan ℝ {x | ∃ v ∈ s, x ∈ arrangementLayer l (φ₀ v)}

theorem arrangementLayer_le_arrangementEnvelope {κ ι : Type*} (l : κ → E →ᵃ[ℝ] ℝ)
    (φ₀ : ι → E) {s : Finset ι} {v : ι} (hv : v ∈ s) :
    arrangementLayer l (φ₀ v) ≤ arrangementEnvelope l φ₀ s := by
  intro x hx
  exact subset_affineSpan ℝ _ ⟨v, hv, hx⟩

theorem mem_arrangementEnvelope_of_mem_openCell {κ ι : Type*} (l : κ → E →ᵃ[ℝ] ℝ)
    (φ₀ φ : ι → E) {s : Finset ι} {v : ι} (hv : v ∈ s)
    (hφ : φ v ∈ openCell l (signVec l (φ₀ v))) : φ v ∈ arrangementEnvelope l φ₀ s :=
  arrangementLayer_le_arrangementEnvelope l φ₀ hv (openCell_subset_arrangementLayer l (φ₀ v) hφ)

open Classical in
theorem vectorSpan_sup_eq_direction_of_affineIndependent_subsets {ι : Type*}
    [FiniteDimensional ℝ E] (L : AffineSubspace ℝ E) (V : Finset ι) (φ : ι → E)
    (hmem : ∀ v ∈ V, φ v ∈ L)
    (hφ : ∀ u : Finset ι, u ⊆ V → u.card ≤ Module.finrank ℝ L.direction + 1 →
      AffineIndependent ℝ (fun v : u => φ (v : ι)))
    {s t : Finset ι} (hs : s ⊆ V) (ht : t ⊆ V) (hst : Disjoint s t)
    (hinter : (convexHull ℝ (s.image φ : Set E) ∩ convexHull ℝ (t.image φ : Set E)).Nonempty) :
    vectorSpan ℝ (s.image φ : Set E) ⊔ vectorSpan ℝ (t.image φ : Set E) = L.direction := by
  have hsub : s ∪ t ⊆ V := Finset.union_subset hs ht
  by_cases hcard : (s ∪ t).card ≤ Module.finrank ℝ L.direction + 1
  · have hAI := (affineIndependent_image_iff (s ∪ t) φ).mp (hφ _ hsub hcard)
    have hdisj : Disjoint (s.image φ) (t.image φ) := by
      rw [Finset.disjoint_left]
      intro y hys hyt
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hys
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hyt
      have heq : b = a := hAI.1 (Finset.mem_union_right s hb) (Finset.mem_union_left t ha) hba
      exact Finset.disjoint_left.mp hst ha (heq ▸ hb)
    obtain ⟨y, hy⟩ := hinter
    have hbad := convexHull_inter_subset_of_affineIndependent hAI.2
      (Finset.image_subset_image Finset.subset_union_left)
      (Finset.image_subset_image Finset.subset_union_right) hy
    rw [← Finset.coe_inter, Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.coe_empty,
      convexHull_empty] at hbad
    exact False.elim hbad
  · have hunion : (s ∪ t).Nonempty := by
      obtain ⟨y, hys, _⟩ := hinter
      by_contra h
      have hu0 := Finset.not_nonempty_iff_eq_empty.mp h
      have hs0 : s = ∅ := (Finset.union_eq_empty.mp hu0).1
      simp only [hs0, Finset.image_empty, Finset.coe_empty, convexHull_empty,
        Set.mem_empty_iff_false] at hys
    obtain ⟨v, hv⟩ := hunion
    have herase := Finset.card_erase_of_mem hv
    obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq
      (show Module.finrank ℝ L.direction ≤ ((s ∪ t).erase v).card by omega)
    have hvu : v ∉ u := fun h => Finset.notMem_erase v (s ∪ t) (hu h)
    have hins : insert v u ⊆ s ∪ t := Finset.insert_subset_iff.mpr
      ⟨hv, hu.trans (Finset.erase_subset v (s ∪ t))⟩
    have hinscard : (insert v u).card = Module.finrank ℝ L.direction + 1 := by
      rw [Finset.card_insert_of_notMem hvu, hucard]
    have huAI := hφ (insert v u) (hins.trans hsub) hinscard.le
    have huSpan : affineSpan ℝ ((insert v u).image φ : Set E) = L := by
      have hrange : Set.range (fun w : (insert v u : Finset ι) => φ (w : ι)) =
          ((insert v u).image φ : Set E) := by
        ext y
        simp [eq_comm]
      rw [← hrange]
      apply huAI.affineSpan_eq_of_le_of_card_eq_finrank_add_one
      · apply affineSpan_le_of_subset_coe
        rintro y ⟨w, rfl⟩
        exact hmem w (hsub (hins w.property))
      · simpa only [Fintype.card_coe] using hinscard
    have hspan : affineSpan ℝ ((s.image φ : Set E) ∪ (t.image φ : Set E)) = L := by
      apply le_antisymm
      · apply affineSpan_le_of_subset_coe
        rintro y (hy | hy)
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          exact hmem w (hs hw)
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          exact hmem w (ht hw)
      · rw [← huSpan]
        apply affineSpan_mono ℝ
        intro y hy
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
        rcases Finset.mem_union.mp (hins hw) with hws | hwt
        · exact Or.inl (Finset.mem_image_of_mem φ hws)
        · exact Or.inr (Finset.mem_image_of_mem φ hwt)
    obtain ⟨y, hys, hyt⟩ := hinter
    have hdir := congrArg AffineSubspace.direction hspan
    rw [AffineSubspace.span_union, AffineSubspace.direction_sup
      (convexHull_subset_affineSpan _ hys) (convexHull_subset_affineSpan _ hyt),
      direction_affineSpan, direction_affineSpan, vsub_self,
      Submodule.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at hdir
    exact hdir

open Classical in
theorem exists_small_affineIndependent_constraints_in_arrangement {κ ι η : Type*}
    [Finite κ] [Finite η] [FiniteDimensional ℝ E] (l : κ → E →ᵃ[ℝ] ℝ)
    (V : List ι) (B : Finset ι) (hV : V.Nodup) (hVB : Disjoint V.toFinset B)
    (φ₀ : ι → E) (c : η → Finset ι)
    (hfixed : ∀ j, AffineIndependent ℝ (fun w : (c j ∩ B : Finset ι) => φ₀ (w : ι)))
    (hdim : ∀ (V₁ V₂ : List ι) (v : ι), V = V₁ ++ v :: V₂ →
      ∀ j, v ∈ c j →
        (c j ∩ (B ∪ V₂.toFinset)).card ≤
          Module.finrank ℝ (arrangementDirection l (φ₀ v)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → E, EqOn φ φ₀ ((V.toFinset : Set ι)ᶜ) ∧
      (∀ v, dist (φ v) (φ₀ v) < ε) ∧
        (∀ v ∈ V.toFinset, φ v ∈ openCell l (signVec l (φ₀ v))) ∧
          ∀ j, AffineIndependent ℝ
            (fun w : (c j ∩ (B ∪ V.toFinset) : Finset ι) => φ (w : ι)) := by
  induction V with
  | nil =>
      refine ⟨φ₀, fun _ _ => rfl, fun _ => by simpa only [dist_self] using hε, ?_, ?_⟩
      · intro v hv
        simp at hv
      · intro j
        have heq : B ∪ ([] : List ι).toFinset = B := by
          ext x
          simp
        rw [heq]
        exact hfixed j
  | cons v V ih =>
      have hvV : v ∉ V := (List.nodup_cons.mp hV).1
      have hVtail : V.Nodup := (List.nodup_cons.mp hV).2
      have hvB : v ∉ B := by
        intro hv
        exact Finset.disjoint_left.mp hVB (by simp) hv
      have hVBtail : Disjoint V.toFinset B := by
        apply Finset.disjoint_left.mpr
        intro x hxV hxB
        exact Finset.disjoint_left.mp hVB (by simp only [List.toFinset_cons, Finset.mem_insert]; exact Or.inr hxV) hxB
      have hdimTail : ∀ (V₁ V₂ : List ι) (w : ι), V = V₁ ++ w :: V₂ →
          ∀ j, w ∈ c j →
            (c j ∩ (B ∪ V₂.toFinset)).card ≤
              Module.finrank ℝ (arrangementDirection l (φ₀ w)) := by
        intro V₁ V₂ w hlist j hw
        apply hdim (v :: V₁) V₂ w
        · simpa only [List.cons_append] using congrArg (v :: ·) hlist
        · exact hw
      obtain ⟨φ, hφfix, hφclose, hφcell, hφgood⟩ :=
        ih hVtail hVBtail hdimTail
      have hφv : φ v = φ₀ v := by
        apply hφfix
        simp only [Set.mem_compl_iff, Finset.mem_coe, List.mem_toFinset]
        exact hvV
      let J := {j : η // v ∈ c j}
      let s : J → Finset ι := fun j => c j ∩ (B ∪ V.toFinset)
      have hvS : ∀ j, v ∉ s j := by
        intro j hvs
        rcases Finset.mem_inter.mp hvs with ⟨_, hvUnion⟩
        rcases Finset.mem_union.mp hvUnion with hvB' | hvV'
        · exact hvB hvB'
        · exact hvV (List.mem_toFinset.mp hvV')
      have hs : ∀ j, AffineIndependent ℝ (fun w : s j => φ (w : ι)) := by
        intro j
        exact hφgood j
      have hroom : ∀ j, ¬arrangementLayer l (φ v) ≤ affineSpan ℝ (s j |>.image φ : Set E) := by
        intro j
        have hcard := hdim [] V v (by simp) j j.property
        have hcard' : (s j).card ≤ Module.finrank ℝ (arrangementDirection l (φ v)) := by
          dsimp only [s]
          rw [hφv]
          exact hcard
        exact arrangementLayer_not_le_affineSpan_of_affineIndependent l φ v (s j) (hs j) hcard'
      obtain ⟨ψ, hψfix, hψclose, hψcell, hψgood⟩ :=
        exists_small_update_affineIndependent_in_arrangement l φ v s hvS hs hroom hε
      refine ⟨ψ, ?_, ?_, ?_, ?_⟩
      · intro x hx
        change x ∉ (v :: V).toFinset at hx
        have hxv : x ≠ v := fun h => hx (by simp only [List.toFinset_cons, Finset.mem_insert, h, true_or])
        have hxV : x ∉ V.toFinset := fun h => hx (by simp only [List.toFinset_cons, Finset.mem_insert]; exact Or.inr h)
        exact (hψfix (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxv)).trans
          (hφfix (by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hxV))
      · intro x
        by_cases hxv : x = v
        · subst x
          simpa only [hφv] using hψclose v
        · have hsame := hψfix (show x ∈ ({v} : Set ι)ᶜ by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxv)
          rw [hsame]
          exact hφclose x
      · intro x hx
        rw [List.toFinset_cons, Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · simpa only [hφv] using hψcell
        · have hxv : x ≠ v := fun h => hvV (h ▸ List.mem_toFinset.mp hx)
          have hsame := hψfix (show x ∈ ({v} : Set ι)ᶜ by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxv)
          rw [hsame]
          exact hφcell x hx
      · intro j
        by_cases hvj : v ∈ c j
        · let q : J := ⟨j, hvj⟩
          have heq : c j ∩ (B ∪ (v :: V).toFinset) = insert v (s q) := by
            ext x
            simp only [List.toFinset_cons, Finset.mem_inter, Finset.mem_union, Finset.mem_insert,
              s, q]
            constructor
            · rintro ⟨hxc, hxB | hxv | hxV⟩
              · exact Or.inr ⟨hxc, Or.inl hxB⟩
              · exact Or.inl hxv
              · exact Or.inr ⟨hxc, Or.inr hxV⟩
            · rintro (rfl | ⟨hxc, hxB | hxV⟩)
              · exact ⟨hvj, Or.inr (Or.inl rfl)⟩
              · exact ⟨hxc, Or.inl hxB⟩
              · exact ⟨hxc, Or.inr (Or.inr hxV)⟩
          rw [heq]
          exact hψgood q
        · have heq : c j ∩ (B ∪ (v :: V).toFinset) = c j ∩ (B ∪ V.toFinset) := by
            ext x
            simp only [List.toFinset_cons, Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
            constructor
            · rintro ⟨hxc, hxB | hxv | hxV⟩
              · exact ⟨hxc, Or.inl hxB⟩
              · exact False.elim (hvj (hxv ▸ hxc))
              · exact ⟨hxc, Or.inr hxV⟩
            · rintro ⟨hxc, hxB | hxV⟩
              · exact ⟨hxc, Or.inl hxB⟩
              · exact ⟨hxc, Or.inr (Or.inr hxV)⟩
          rw [heq]
          have hfun : (fun w : (c j ∩ (B ∪ V.toFinset) : Finset ι) => ψ (w : ι)) =
              fun w : (c j ∩ (B ∪ V.toFinset) : Finset ι) => φ (w : ι) := by
            funext w
            apply hψfix
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact ne_of_mem_of_not_mem (Finset.mem_inter.mp w.property).1 hvj
          rw [hfun]
          exact hφgood j

open Classical in
theorem exists_small_vertexMap_transverse_in_arrangement {κ ι η ζ : Type*}
    [Finite κ] [Finite η] [Finite ζ] [FiniteDimensional ℝ E]
    (l : κ → E →ᵃ[ℝ] ℝ) (V : List ι) (B : Finset ι) (hV : V.Nodup)
    (hVB : Disjoint V.toFinset B) (φ₀ : ι → E) (c : η → Finset ι)
    (s t : ζ → Finset ι)
    (hfixed : ∀ j, AffineIndependent ℝ (fun w : (c j ∩ B : Finset ι) => φ₀ (w : ι)))
    (hdim : ∀ (V₁ V₂ : List ι) (v : ι), V = V₁ ++ v :: V₂ →
      ∀ j, v ∈ c j →
        (c j ∩ (B ∪ V₂.toFinset)).card ≤
          Module.finrank ℝ (arrangementDirection l (φ₀ v)))
    (hs : ∀ q, s q ⊆ B ∪ V.toFinset) (ht : ∀ q, t q ⊆ B ∪ V.toFinset)
    (hcomplete : ∀ q (u : Finset ι), u ⊆ s q ∪ t q →
      u.card ≤ Module.finrank ℝ (arrangementEnvelope l φ₀ (s q ∪ t q)).direction + 1 →
        ∃ j, c j = u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → E, EqOn φ φ₀ ((V.toFinset : Set ι)ᶜ) ∧
      (∀ v, dist (φ v) (φ₀ v) < ε) ∧
        (∀ v ∈ V.toFinset, φ v ∈ openCell l (signVec l (φ₀ v))) ∧
          (∀ j, AffineIndependent ℝ
            (fun w : (c j ∩ (B ∪ V.toFinset) : Finset ι) => φ (w : ι))) ∧
            ∀ q, Disjoint (s q) (t q) →
              (convexHull ℝ ((s q).image φ : Set E) ∩
                convexHull ℝ ((t q).image φ : Set E)).Nonempty →
                vectorSpan ℝ ((s q).image φ : Set E) ⊔
                  vectorSpan ℝ ((t q).image φ : Set E) =
                    (arrangementEnvelope l φ₀ (s q ∪ t q)).direction := by
  obtain ⟨φ, hfix, hclose, hcell, hgood⟩ :=
    exists_small_affineIndependent_constraints_in_arrangement l V B hV hVB φ₀ c hfixed hdim hε
  have hcellAll : ∀ v ∈ B ∪ V.toFinset, φ v ∈ openCell l (signVec l (φ₀ v)) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvB | hvV
    · have hvnotV : v ∉ V.toFinset := fun hvV => Finset.disjoint_left.mp hVB hvV hvB
      have heq := hfix (show v ∈ ((V.toFinset : Set ι)ᶜ) by
        simpa only [Set.mem_compl_iff, Finset.mem_coe] using hvnotV)
      rw [heq]
      exact mem_openCell_signVec l (φ₀ v)
    · exact hcell v hvV
  refine ⟨φ, hfix, hclose, hcell, hgood, ?_⟩
  intro q hdisj hinter
  let U := s q ∪ t q
  have hU : U ⊆ B ∪ V.toFinset := Finset.union_subset (hs q) (ht q)
  apply vectorSpan_sup_eq_direction_of_affineIndependent_subsets
    (arrangementEnvelope l φ₀ U) U φ
  · intro v hv
    exact mem_arrangementEnvelope_of_mem_openCell l φ₀ φ hv (hcellAll v (hU hv))
  · intro u hu hcard
    obtain ⟨j, hj⟩ := hcomplete q u hu hcard
    have huTotal : u ⊆ B ∪ V.toFinset := hu.trans hU
    have heq : c j ∩ (B ∪ V.toFinset) = u := by
      rw [hj]
      exact Finset.inter_eq_left.mpr huTotal
    rw [← heq]
    exact hgood j
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right
  · exact hdisj
  · exact hinter

end DifferentialGeometry.Topology.PiecewiseLinear
