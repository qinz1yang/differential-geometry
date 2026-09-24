import DifferentialGeometry.Topology.VanKampen.ConnectedSum
import DifferentialGeometry.Topology.VanKampen.BallChartEmbeddedCellCollar
import DifferentialGeometry.Topology.Collar.Attachment
import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionInjectivity
import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction

set_option autoImplicit false

open Set Topology Filter
open scoped ContinuousMap unitInterval Manifold ContDiff

noncomputable section

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Collar
open DifferentialGeometry.Topology.Manifold.Attachment

theorem connectedSumNeck_homeomorph_adjunctionSpace_of_collar
    {X Y : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    (ℓ : CellBoundary 3 → X) (r : CellBoundary 3 → Y)
    (hℓ : Continuous ℓ) (hr : Continuous r)
    (hℓinj : Function.Injective ℓ) (hrinj : Function.Injective r)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (c : CellBoundary 3 × Icc (0 : ℝ) 1 → X) (hc : Topology.IsEmbedding c)
    (hzero : ∀ b : CellBoundary 3, c (b, (0 : Icc (0 : ℝ) 1)) = ℓ b)
    (hopen : IsOpen (c '' {q | (q.2 : ℝ) < 3 / 4})) :
    Nonempty (ConnectedSumNeck ℓ r glue ≃ₜ
      AdjunctionSpace ℓ (fun b => r (glue b))) := by
  classical
  let smap : C(Icc (0 : ℝ) 1, Icc (0 : ℝ) 1) := intervalPush (1 / 4) (by norm_num)
  have hsmap_zero : smap (0 : Icc (0 : ℝ) 1) = (⟨1 / 4, by norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    rw [intervalPush_coe]
    norm_num
  have hsmap_inj : Function.Injective smap :=
    (strictMono_intervalPush (1 / 4) (by norm_num)).injective
  have hsmap_range : Set.range smap =
      {t : Icc (0 : ℝ) 1 | (1 / 4 : ℝ) ≤ (t : ℝ)} :=
    range_intervalPush (by norm_num)
  have hsmap_fix : ∀ t : Icc (0 : ℝ) 1, (1 / 2 : ℝ) ≤ (t : ℝ) → smap t = t :=
    fun t ht => intervalPush_fixed (1 / 4) (by norm_num) t (by linarith)
  let res : X → X := rescale c hc smap
  have hrescont : Continuous res := continuous_rescale c hc smap (by norm_num) hopen hsmap_fix
  have hresinj : Function.Injective res := injective_rescale c hc smap hsmap_inj
  have hresrange : Set.range res =
      (Set.range c)ᶜ ∪ c '' {q | (1 / 4 : ℝ) ≤ (q.2 : ℝ)} :=
    range_rescale c hc smap hsmap_range
  have hc_inj : Function.Injective c := hc.injective
  let φr : CellBoundary 3 → Y := fun b => r (glue b)
  have hφrcont : Continuous φr := hr.comp glue.continuous
  have hφrinj : Function.Injective φr := hrinj.comp glue.injective
  let neckAttach : CellBoundary 3 ⊕ CellBoundary 3 → X ⊕ Y :=
    connectedSumNeckAttachingMap ℓ r glue
  have hcylmem : ∀ t : Icc (0 : ℝ) 1,
      (0 : ℝ) ≤ (1 / 4) * (1 - (t : ℝ)) ∧ (1 / 4) * (1 - (t : ℝ)) ≤ 1 :=
    fun t => ⟨by nlinarith [t.property.1, t.property.2],
      by nlinarith [t.property.1, t.property.2]⟩
  let cylHalf : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
    fun t => ⟨(1 / 4) * (1 - (t : ℝ)), hcylmem t⟩
  let cyl : CellBoundary 3 × Icc (0 : ℝ) 1 → X := fun q => c (q.1, cylHalf q.2)
  have hcyl_apply : ∀ (b : CellBoundary 3) (t : Icc (0 : ℝ) 1),
      cyl (b, t) = c (b, cylHalf t) := fun b t => rfl
  have hcylHalf_val : ∀ t : Icc (0 : ℝ) 1,
      (cylHalf t : ℝ) = (1 / 4) * (1 - (t : ℝ)) := fun t => rfl
  have hcylHalf_cont : Continuous cylHalf :=
    Continuous.subtype_mk (f := fun t : Icc (0 : ℝ) 1 => (1 / 4) * (1 - (t : ℝ)))
      (by fun_prop) (fun t => hcylmem t)
  have hcylcont : Continuous cyl :=
    hc.continuous.comp (Continuous.prodMk continuous_fst (hcylHalf_cont.comp continuous_snd))
  have hcylHalf_zero : cylHalf (0 : Icc (0 : ℝ) 1) =
      (⟨1 / 4, by norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    simp [cylHalf]
  have hcylHalf_one : cylHalf (1 : Icc (0 : ℝ) 1) = (0 : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    simp [cylHalf]
  have hres_collar : ∀ (b : CellBoundary 3) (s : Icc (0 : ℝ) 1),
      res (c (b, s)) = c (b, smap s) := fun b s => rescale_apply c hc smap (b, s)
  have hres_ell : ∀ b : CellBoundary 3,
      res (ℓ b) = c (b, (⟨1 / 4, by norm_num⟩ : Icc (0 : ℝ) 1)) := by
    intro b
    rw [← hzero b, hres_collar b, hsmap_zero]
  have hmem_range : ∀ (b : CellBoundary 3) (s : Icc (0 : ℝ) 1),
      c (b, s) ∈ Set.range res ↔ (1 / 4 : ℝ) ≤ (s : ℝ) := by
    intro b s
    rw [hresrange]
    constructor
    · rintro (h | ⟨q, hq, hqc⟩)
      · exact absurd ⟨(b, s), rfl⟩ h
      · have hq' : q = (b, s) := hc_inj hqc
        rw [hq'] at hq
        exact hq
    · intro hs
      exact Or.inr ⟨(b, s), hs, rfl⟩
  let Φ₀ : ((CellBoundary 3 × Icc (0 : ℝ) 1) ⊕ (X ⊕ Y)) → AdjunctionSpace ℓ φr
    | Sum.inl q => adjunctionCell ℓ φr (cyl q)
    | Sum.inr (Sum.inl x) => adjunctionCell ℓ φr (res x)
    | Sum.inr (Sum.inr y) => adjunctionLower φr y
  have hΦ₀cont : Continuous Φ₀ := by
    rw [continuous_sum_dom]
    constructor
    · change Continuous fun q : CellBoundary 3 × Icc (0 : ℝ) 1 => adjunctionCell ℓ φr (cyl q)
      exact (continuous_adjunctionCell ℓ φr).comp hcylcont
    · rw [continuous_sum_dom]
      constructor
      · change Continuous fun x : X => adjunctionCell ℓ φr (res x)
        exact (continuous_adjunctionCell ℓ φr).comp hrescont
      · change Continuous fun y : Y => adjunctionLower φr y
        exact continuous_adjunctionLower ℓ φr
  have hcyl_zero : ∀ b : CellBoundary 3, cyl (b, (0 : Icc (0 : ℝ) 1)) = res (ℓ b) := by
    intro b
    rw [hcyl_apply, hres_ell]
    congr 1
    exact Prod.ext rfl hcylHalf_zero
  have hcyl_one : ∀ b : CellBoundary 3, cyl (b, (1 : Icc (0 : ℝ) 1)) = ℓ b := by
    intro b
    rw [hcyl_apply, ← hzero b]
    congr 1
    exact Prod.ext rfl hcylHalf_one
  have hrel : ∀ a b : (CellBoundary 3 × Icc (0 : ℝ) 1) ⊕ (X ⊕ Y),
      adjunctionRel connectedSumNeckBoundaryInclusion neckAttach a b → Φ₀ a = Φ₀ b := by
    rintro a b ⟨s, hs | hs⟩
    · rcases hs with ⟨rfl, rfl⟩
      cases s with
      | inl u =>
        change adjunctionCell ℓ φr (cyl (u, (0 : Icc (0 : ℝ) 1))) =
          adjunctionCell ℓ φr (res (ℓ u))
        rw [hcyl_zero u]
      | inr u =>
        change adjunctionCell ℓ φr (cyl (u, (1 : Icc (0 : ℝ) 1))) =
          adjunctionLower φr (φr u)
        rw [hcyl_one u]
        exact adjunction_coherence ℓ φr u
    · rcases hs with ⟨rfl, rfl⟩
      cases s with
      | inl u =>
        change adjunctionCell ℓ φr (res (ℓ u)) =
          adjunctionCell ℓ φr (cyl (u, (0 : Icc (0 : ℝ) 1)))
        rw [hcyl_zero u]
      | inr u =>
        change adjunctionLower φr (φr u) =
          adjunctionCell ℓ φr (cyl (u, (1 : Icc (0 : ℝ) 1)))
        rw [hcyl_one u]
        exact (adjunction_coherence ℓ φr u).symm
  let Φ : ConnectedSumNeck ℓ r glue → AdjunctionSpace ℓ φr := Quot.lift Φ₀ hrel
  have hΦcont : Continuous Φ := continuous_adjunction_lift _ _ hrel hΦ₀cont
  have hlinked_zero : ∀ b : CellBoundary 3,
      Quot.mk (adjunctionRel connectedSumNeckBoundaryInclusion neckAttach)
          (Sum.inl (b, (0 : Icc (0 : ℝ) 1))) =
        Quot.mk (adjunctionRel connectedSumNeckBoundaryInclusion neckAttach)
          (Sum.inr (Sum.inl (ℓ b))) := by
    intro b
    have h1 : (Sum.inl (b, (0 : Icc (0 : ℝ) 1)) :
        (CellBoundary 3 × Icc (0 : ℝ) 1) ⊕ (X ⊕ Y)) =
        Sum.inl (connectedSumNeckBoundaryInclusion (Sum.inl b)) := by
      congr 1
    rw [h1]
    exact Quot.sound ⟨Sum.inl b, Or.inl ⟨rfl, rfl⟩⟩
  have hlinked_one : ∀ b : CellBoundary 3,
      Quot.mk (adjunctionRel connectedSumNeckBoundaryInclusion neckAttach)
          (Sum.inl (b, (1 : Icc (0 : ℝ) 1))) =
        Quot.mk (adjunctionRel connectedSumNeckBoundaryInclusion neckAttach)
          (Sum.inr (Sum.inr (φr b))) := by
    intro b
    have h1 : (Sum.inl (b, (1 : Icc (0 : ℝ) 1)) :
        (CellBoundary 3 × Icc (0 : ℝ) 1) ⊕ (X ⊕ Y)) =
        Sum.inl (connectedSumNeckBoundaryInclusion (Sum.inr b)) := by
      congr 1
    rw [h1]
    exact Quot.sound ⟨Sum.inr b, Or.inl ⟨rfl, rfl⟩⟩
  have hsurj : Function.Surjective Φ := by
    intro z
    refine Quot.inductionOn z ?_
    intro p
    rcases p with x | y
    · by_cases hx : x ∈ Set.range res
      · obtain ⟨x', rfl⟩ := hx
        exact ⟨Quot.mk _ (Sum.inr (Sum.inl x')), rfl⟩
      · have hxc : x ∈ Set.range c := by
          by_contra hc'
          exact hx (by rw [hresrange]; exact Or.inl hc')
        obtain ⟨q, hq⟩ := hxc
        obtain ⟨b, s⟩ := q
        have hs : (s : ℝ) ≤ 1 / 4 := by
          by_contra hlt
          exact hx (by rw [← hq]; exact (hmem_range b s).mpr (le_of_lt (lt_of_not_ge hlt)))
        let t : Icc (0 : ℝ) 1 := ⟨1 - 4 * (s : ℝ), by
          constructor <;> nlinarith [s.property.1, s.property.2, hs]⟩
        refine ⟨Quot.mk _ (Sum.inl (b, t)), ?_⟩
        change adjunctionCell ℓ φr (cyl (b, t)) = adjunctionCell ℓ φr x
        rw [← hq]
        refine congrArg (adjunctionCell ℓ φr) ?_
        rw [hcyl_apply]
        congr 1
        exact Prod.ext rfl (Subtype.ext (by
          change (1 / 4) * (1 - (1 - 4 * (s : ℝ))) = (s : ℝ)
          ring))
    · exact ⟨Quot.mk _ (Sum.inr (Sum.inr y)), rfl⟩
  have hinj : Function.Injective Φ := by
    intro zu zv
    refine Quot.inductionOn zu ?_
    intro u
    refine Quot.inductionOn zv ?_
    intro v h
    change Φ₀ u = Φ₀ v at h
    rcases u with q | w
    · rcases v with q' | w'
      · change adjunctionCell ℓ φr (cyl q) = adjunctionCell ℓ φr (cyl q') at h
        have h1 : cyl q = cyl q' := (adjunctionCell_injective ℓ φr hℓinj hφrinj) h
        have hq : q = q' := by
          rcases q with ⟨b, s⟩
          rcases q' with ⟨b', s'⟩
          have h2 : (b, cylHalf s) = (b', cylHalf s') := hc_inj h1
          have hb : b = b' := congrArg (fun z : CellBoundary 3 × Icc (0 : ℝ) 1 => z.1) h2
          have hss : s = s' := by
            apply Subtype.ext
            have hv := congrArg Subtype.val
              (congrArg (fun z : CellBoundary 3 × Icc (0 : ℝ) 1 => z.2) h2)
            rw [hcylHalf_val, hcylHalf_val] at hv
            linarith
          rw [hb, hss]
        rw [hq]
      · rcases w' with x | y
        · change adjunctionCell ℓ φr (cyl q) = adjunctionCell ℓ φr (res x) at h
          have h1 : cyl q = res x := (adjunctionCell_injective ℓ φr hℓinj hφrinj) h
          rcases q with ⟨b, s⟩
          have h1' : c (b, cylHalf s) = res x := by rw [← hcyl_apply]; exact h1
          have hmem : (1 / 4 : ℝ) ≤ (cylHalf s : ℝ) :=
            (hmem_range b (cylHalf s)).mp ⟨x, h1'.symm⟩
          have hle : (cylHalf s : ℝ) ≤ 1 / 4 := by
            rw [hcylHalf_val]; nlinarith [s.property.1]
          have hval : (cylHalf s : ℝ) = 1 / 4 := le_antisymm hle hmem
          have hsv : (s : ℝ) = 0 := by rw [hcylHalf_val] at hval; linarith
          have hs0 : s = (0 : Icc (0 : ℝ) 1) := Subtype.ext (by rw [hsv]; rfl)
          have hxell : x = ℓ b := by
            have h2 : res x = res (ℓ b) := by
              rw [← h1', hres_ell]
              congr 1
              exact Prod.ext rfl (Subtype.ext hval)
            exact hresinj h2
          rw [hs0, hxell]
          exact hlinked_zero b
        · change adjunctionCell ℓ φr (cyl q) = adjunctionLower φr y at h
          obtain ⟨b₀, hb₀, hy₀⟩ :=
            (adjunctionCell_eq_lower_iff ℓ φr hℓinj (cyl q) y).mp h
          rcases q with ⟨b, s⟩
          have h1 : c (b₀, (0 : Icc (0 : ℝ) 1)) = c (b, cylHalf s) := by
            rw [← hcyl_apply, ← hb₀, hzero b₀]
          have h2 : (b₀, (0 : Icc (0 : ℝ) 1)) = (b, cylHalf s) := hc_inj h1
          have hbb : b₀ = b := congrArg Prod.fst h2
          have hs1 : (s : ℝ) = 1 := by
            have hss : cylHalf s = (0 : Icc (0 : ℝ) 1) := (congrArg Prod.snd h2).symm
            have hv := congrArg Subtype.val hss
            rw [hcylHalf_val] at hv
            have h0 : (((0 : Icc (0 : ℝ) 1)) : ℝ) = 0 := rfl
            rw [h0] at hv
            linarith
          have hs1' : s = (1 : Icc (0 : ℝ) 1) := Subtype.ext (by rw [hs1]; rfl)
          have hy : y = φr b := by rw [← hy₀, hbb]
          rw [hs1', hy]
          exact hlinked_one b
    · rcases w with x | y
      · rcases v with q' | w'
        · change adjunctionCell ℓ φr (res x) = adjunctionCell ℓ φr (cyl q') at h
          have h1 : res x = cyl q' := (adjunctionCell_injective ℓ φr hℓinj hφrinj) h
          rcases q' with ⟨b, s⟩
          have h1' : res x = c (b, cylHalf s) := h1.trans (hcyl_apply b s)
          have hmem : (1 / 4 : ℝ) ≤ (cylHalf s : ℝ) :=
            (hmem_range b (cylHalf s)).mp ⟨x, h1'⟩
          have hle : (cylHalf s : ℝ) ≤ 1 / 4 := by
            rw [hcylHalf_val]; nlinarith [s.property.1]
          have hval : (cylHalf s : ℝ) = 1 / 4 := le_antisymm hle hmem
          have hsv : (s : ℝ) = 0 := by rw [hcylHalf_val] at hval; linarith
          have hs0 : s = (0 : Icc (0 : ℝ) 1) := Subtype.ext (by rw [hsv]; rfl)
          have hxell : x = ℓ b := by
            have h2 : res x = res (ℓ b) := by
              rw [h1', hres_ell]
              congr 1
              exact Prod.ext rfl (Subtype.ext hval)
            exact hresinj h2
          rw [hs0, hxell]
          exact (hlinked_zero b).symm
        · rcases w' with x' | y'
          · change adjunctionCell ℓ φr (res x) = adjunctionCell ℓ φr (res x') at h
            have h1 : res x = res x' := (adjunctionCell_injective ℓ φr hℓinj hφrinj) h
            rw [hresinj h1]
          · change adjunctionCell ℓ φr (res x) = adjunctionLower φr y' at h
            obtain ⟨b, hb, -⟩ := (adjunctionCell_eq_lower_iff ℓ φr hℓinj (res x) y').mp h
            have hmem : c (b, (0 : Icc (0 : ℝ) 1)) ∈ Set.range res :=
              ⟨x, hb.symm.trans (hzero b).symm⟩
            have hbad := (hmem_range b (0 : Icc (0 : ℝ) 1)).mp hmem
            exact absurd hbad (by norm_num)
      · rcases v with q' | w'
        · change adjunctionLower φr y = adjunctionCell ℓ φr (cyl q') at h
          obtain ⟨b₀, hb₀, hy₀⟩ :=
            (adjunctionCell_eq_lower_iff ℓ φr hℓinj (cyl q') y).mp h.symm
          rcases q' with ⟨b, s⟩
          have h1 : c (b₀, (0 : Icc (0 : ℝ) 1)) = c (b, cylHalf s) := by
            rw [← hcyl_apply, ← hb₀, hzero b₀]
          have h2 : (b₀, (0 : Icc (0 : ℝ) 1)) = (b, cylHalf s) := hc_inj h1
          have hbb : b₀ = b := congrArg Prod.fst h2
          have hs1 : (s : ℝ) = 1 := by
            have hss : cylHalf s = (0 : Icc (0 : ℝ) 1) := (congrArg Prod.snd h2).symm
            have hv := congrArg Subtype.val hss
            rw [hcylHalf_val] at hv
            have h0 : (((0 : Icc (0 : ℝ) 1)) : ℝ) = 0 := rfl
            rw [h0] at hv
            linarith
          have hs1' : s = (1 : Icc (0 : ℝ) 1) := Subtype.ext (by rw [hs1]; rfl)
          have hy : y = φr b := by rw [← hy₀, hbb]
          rw [hs1', hy]
          exact (hlinked_one b).symm
        · rcases w' with x' | y'
          · change adjunctionLower φr y = adjunctionCell ℓ φr (res x') at h
            obtain ⟨b, hb, -⟩ :=
              (adjunctionCell_eq_lower_iff ℓ φr hℓinj (res x') y).mp h.symm
            have hmem : c (b, (0 : Icc (0 : ℝ) 1)) ∈ Set.range res :=
              ⟨x', hb.symm.trans (hzero b).symm⟩
            have hbad := (hmem_range b (0 : Icc (0 : ℝ) 1)).mp hmem
            exact absurd hbad (by norm_num)
          · change adjunctionLower φr y = adjunctionLower φr y' at h
            rw [(adjunctionLower_injective ℓ φr hℓinj) h]
  let _ : T2Space (AdjunctionSpace ℓ φr) :=
    adjunction_t2Space ℓ φr hℓinj hφrinj hℓ hφrcont
  exact ⟨IsHomeomorph.homeomorph Φ
    ((isHomeomorph_iff_continuous_bijective).mpr ⟨hΦcont, hinj, hsurj⟩)⟩

end DifferentialGeometry.Topology.ThreeManifold

namespace DifferentialGeometry.Topology

theorem adjunctionSpace_homeomorph_of_piece_homeomorph
    {A B X A' B' X' : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    [TopologicalSpace A'] [TopologicalSpace B'] [TopologicalSpace X']
    (i : A → B) (φ : A → X) (i' : A' → B') (φ' : A' → X')
    (eA : A ≃ₜ A') (eB : B ≃ₜ B') (eX : X ≃ₜ X')
    (hB : ∀ a, eB (i a) = i' (eA a)) (hX : ∀ a, eX (φ a) = φ' (eA a)) :
    Nonempty (AdjunctionSpace i φ ≃ₜ AdjunctionSpace i' φ') := by
  have hB' : ∀ a', eB.symm (i' a') = i (eA.symm a') := by
    intro a'
    have h1 : i' a' = eB (i (eA.symm a')) := by
      have h2 := hB (eA.symm a')
      rw [eA.apply_symm_apply] at h2
      exact h2.symm
    rw [h1, eB.symm_apply_apply]
  have hX' : ∀ a', eX.symm (φ' a') = φ (eA.symm a') := by
    intro a'
    have h1 : φ' a' = eX (φ (eA.symm a')) := by
      have h2 := hX (eA.symm a')
      rw [eA.apply_symm_apply] at h2
      exact h2.symm
    rw [h1, eX.symm_apply_apply]
  let F : B ⊕ X → AdjunctionSpace i' φ' := adjunctionMk i' φ' ∘ Sum.map eB eX
  have hF : ∀ a b, adjunctionRel i φ a b → F a = F b := by
    rintro a b ⟨s, hs | hs⟩
    · rcases hs with ⟨rfl, rfl⟩
      change adjunctionCell i' φ' (eB (i s)) = adjunctionLower φ' (eX (φ s))
      rw [hB s, hX s]
      exact adjunction_coherence i' φ' (eA s)
    · rcases hs with ⟨rfl, rfl⟩
      change adjunctionLower φ' (eX (φ s)) = adjunctionCell i' φ' (eB (i s))
      rw [hB s, hX s]
      exact (adjunction_coherence i' φ' (eA s)).symm
  let F' : B' ⊕ X' → AdjunctionSpace i φ := adjunctionMk i φ ∘ Sum.map eB.symm eX.symm
  have hF' : ∀ a b, adjunctionRel i' φ' a b → F' a = F' b := by
    rintro a b ⟨s, hs | hs⟩
    · rcases hs with ⟨rfl, rfl⟩
      change adjunctionCell i φ (eB.symm (i' s)) = adjunctionLower φ (eX.symm (φ' s))
      rw [hB' s, hX' s]
      exact adjunction_coherence i φ (eA.symm s)
    · rcases hs with ⟨rfl, rfl⟩
      change adjunctionLower φ (eX.symm (φ' s)) = adjunctionCell i φ (eB.symm (i' s))
      rw [hB' s, hX' s]
      exact (adjunction_coherence i φ (eA.symm s)).symm
  let Ψ : AdjunctionSpace i φ → AdjunctionSpace i' φ' := Quot.lift F hF
  let Ψinv : AdjunctionSpace i' φ' → AdjunctionSpace i φ := Quot.lift F' hF'
  have hFcont : Continuous F :=
    (continuous_adjunctionMk i' φ').comp (eB.continuous.sumMap eX.continuous)
  have hF'cont : Continuous F' :=
    (continuous_adjunctionMk i φ).comp (eB.symm.continuous.sumMap eX.symm.continuous)
  have hΨcont : Continuous Ψ := continuous_adjunction_lift i φ hF hFcont
  have hΨinv_cont : Continuous Ψinv := continuous_adjunction_lift i' φ' hF' hF'cont
  have hleft : Function.LeftInverse Ψinv Ψ := by
    intro z
    refine Quot.inductionOn z ?_
    intro u
    rcases u with b | x
    · change Ψinv (adjunctionCell i' φ' (eB b)) = adjunctionCell i φ b
      change adjunctionCell i φ (eB.symm (eB b)) = adjunctionCell i φ b
      rw [eB.symm_apply_apply]
    · change Ψinv (adjunctionLower φ' (eX x)) = adjunctionLower φ x
      change adjunctionLower φ (eX.symm (eX x)) = adjunctionLower φ x
      rw [eX.symm_apply_apply]
  have hright : Function.RightInverse Ψinv Ψ := by
    intro w
    refine Quot.inductionOn w ?_
    intro u
    rcases u with b | x
    · change Ψ (adjunctionCell i φ (eB.symm b)) = adjunctionCell i' φ' b
      change adjunctionCell i' φ' (eB (eB.symm b)) = adjunctionCell i' φ' b
      rw [eB.apply_symm_apply]
    · change Ψ (adjunctionLower φ (eX.symm x)) = adjunctionLower φ' x
      change adjunctionLower φ' (eX (eX.symm x)) = adjunctionLower φ' x
      rw [eX.apply_symm_apply]
  have hHom : AdjunctionSpace i φ ≃ₜ AdjunctionSpace i' φ' :=
    { toFun := Ψ
      invFun := Ψinv
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hΨcont
      continuous_invFun := hΨinv_cont }
  exact ⟨hHom⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.ThreeManifold

open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Collar
open DifferentialGeometry.Topology.Manifold.Attachment

theorem exists_collar_of_smoothEmbeddedClosedThreeCellWithCollar
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (B : SmoothEmbeddedClosedThreeCellWithCollar M) :
    ∃ col : CellBoundary 3 × Icc (0 : ℝ) 1 → B.complement,
      Topology.IsEmbedding col ∧
        (∀ b : CellBoundary 3, col (b, (0 : Icc (0 : ℝ) 1)) = B.boundaryMap b) ∧
        IsOpen (col '' {q | (q.2 : ℝ) < 3 / 4}) := by
  let col : CellBoundary 3 × Icc (0 : ℝ) 1 → B.complement := fun q =>
    ⟨B.twoSidedCollar.toFun (q.1, (q.2 : ℝ)),
      (B.twoSidedCollar.mem_complement_iff (q.1, (q.2 : ℝ))).mpr q.2.property.1⟩
  have hcol_val : ∀ q : CellBoundary 3 × Icc (0 : ℝ) 1,
      (col q : M) = B.twoSidedCollar.toFun (q.1, (q.2 : ℝ)) := fun q => rfl
  have hbase : Topology.IsEmbedding (Prod.map (id : CellBoundary 3 → CellBoundary 3)
      (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) :=
    Topology.IsEmbedding.id.prodMap isClosed_Icc.isClosedEmbedding_subtypeVal.isEmbedding
  have hcompeq : (Subtype.val ∘ col) =
      (B.twoSidedCollar.toFun ∘ Prod.map (id : CellBoundary 3 → CellBoundary 3)
        (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) := by
    funext q
    exact hcol_val q
  have hcomp : Topology.IsEmbedding (Subtype.val ∘ col) := by
    rw [hcompeq]
    exact B.twoSidedCollar.isOpenEmbedding_toFun.isEmbedding.comp hbase
  have hcont1 : Continuous (fun q : CellBoundary 3 × Icc (0 : ℝ) 1 =>
      B.twoSidedCollar.toFun (q.1, (q.2 : ℝ))) :=
    B.twoSidedCollar.isOpenEmbedding_toFun.continuous.comp (by fun_prop)
  have hcolcont : Continuous col :=
    Continuous.subtype_mk (f := fun q : CellBoundary 3 × Icc (0 : ℝ) 1 =>
        B.twoSidedCollar.toFun (q.1, (q.2 : ℝ))) hcont1
      (fun q => (B.twoSidedCollar.mem_complement_iff (q.1, (q.2 : ℝ))).mpr q.2.property.1)
  have hisEmb : Topology.IsEmbedding col :=
    Topology.IsEmbedding.of_comp (f := col) (g := Subtype.val) hcolcont
      continuous_subtype_val hcomp
  refine ⟨col, hisEmb, ?_, ?_⟩
  · intro b
    apply Subtype.ext
    change B.twoSidedCollar.toFun (b, (0 : ℝ)) = B.toFun (cellBoundaryInclusion 3 b)
    rw [B.twoSidedCollar.zero_eq]
  · have hW : IsOpen (B.twoSidedCollar.toFun ''
        (Set.univ ×ˢ Set.Ioo (-1 : ℝ) (3 / 4))) :=
      B.twoSidedCollar.isOpenEmbedding_toFun.isOpenMap _
        (isOpen_univ.prod isOpen_Ioo)
    have hset : col '' {q : CellBoundary 3 × Icc (0 : ℝ) 1 | (q.2 : ℝ) < 3 / 4} =
        Subtype.val ⁻¹' (B.twoSidedCollar.toFun ''
          (Set.univ ×ˢ Set.Ioo (-1 : ℝ) (3 / 4))) := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨(q.1, (q.2 : ℝ)), ⟨Set.mem_univ _, by
          exact ⟨by linarith [q.2.property.1], hq⟩⟩, (hcol_val q).symm⟩
      · rintro ⟨q, hq, hpq⟩
        have hq2 : q.2 ∈ Set.Ioo (-1 : ℝ) (3 / 4) := hq.2
        have hpmem : B.twoSidedCollar.toFun q ∈ embeddedCellComplement B.toFun :=
          hpq ▸ p.2
        have hq0 : (0 : ℝ) ≤ q.2 := (B.twoSidedCollar.mem_complement_iff q).mp hpmem
        refine ⟨(q.1, ⟨q.2, hq0, le_of_lt (lt_of_lt_of_le hq2.2 (by norm_num))⟩), ?_, ?_⟩
        · exact lt_of_lt_of_le hq2.2 (by norm_num)
        · apply Subtype.ext
          rw [hcol_val, hpq]
    rw [hset]
    exact hW.preimage continuous_subtype_val

def EmbeddedCellChartIdentification {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (B : SmoothEmbeddedClosedThreeCellWithCollar M) (c : BallChart 3 (𝓡 3) M) : Prop :=
  ∃ e : B.complement ≃ₜ c.Punctured,
    ∀ b : CellBoundary 3,
      e (B.boundaryMap b) =
        c.boundaryMap (CellAttachment.cellBoundaryThreeHomeomorphSphereTwo b)

def EmbeddedCellAttachingCompatibility {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (B : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (d : BallChart 3 (𝓡 3) N)
    (a : SphereTwo ≃ₜ SphereTwo) : Prop :=
  ∃ e : B.complement ≃ₜ d.Punctured,
    ∀ b : CellBoundary 3,
      e (B.boundaryMap (glue b)) =
        d.boundaryMap (a (CellAttachment.cellBoundaryThreeHomeomorphSphereTwo b))

theorem embeddedCellChartIdentification_smoothEmbeddedClosedThreeCellWithCollarOfBallChart
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] (c : BallChart 3 (𝓡 3) M) :
    EmbeddedCellChartIdentification (smoothEmbeddedClosedThreeCellWithCollarOfBallChart c) c :=
  ⟨ballChartCellComplementHomeomorph c, fun _ => Subtype.ext rfl⟩

theorem embeddedCellAttachingCompatibility_smoothEmbeddedClosedThreeCellWithCollarOfBallChart
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] (d : BallChart 3 (𝓡 3) N)
    (a : SphereTwo ≃ₜ SphereTwo) :
    EmbeddedCellAttachingCompatibility (smoothEmbeddedClosedThreeCellWithCollarOfBallChart d)
      (CellAttachment.cellBoundaryThreeHomeomorphSphereTwo.trans
        (a.trans CellAttachment.cellBoundaryThreeHomeomorphSphereTwo.symm))
      d a :=
  ⟨ballChartCellComplementHomeomorph d, fun _ => Subtype.ext rfl⟩

theorem embeddedCellConnectedSum_homeomorph_connectedSumQuotient
    {M N : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [TopologicalSpace N] [T2Space N] [CompactSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : SphereTwo ≃ₜ SphereTwo)
    (hM : EmbeddedCellChartIdentification BM c)
    (hN : EmbeddedCellAttachingCompatibility BN glue d a) :
    Nonempty (EmbeddedCellConnectedSum BM BN glue ≃ₜ ConnectedSumQuotient c d a) := by
  obtain ⟨eM, heM⟩ := hM
  obtain ⟨eN, heN⟩ := hN
  obtain ⟨collar, hcollar, hcollar_zero, hcollar_open⟩ :=
    exists_collar_of_smoothEmbeddedClosedThreeCellWithCollar BM
  have hopenM : IsOpen (embeddedCellInteriorImage BM.toFun) :=
    isOpen_embeddedCellInteriorImage_of_isSmoothEmbedding BM.toFun
      BM.isSmoothEmbedding_interior
  have hopenN : IsOpen (embeddedCellInteriorImage BN.toFun) :=
    isOpen_embeddedCellInteriorImage_of_isSmoothEmbedding BN.toFun
      BN.isSmoothEmbedding_interior
  have hcompM : CompactSpace BM.complement :=
    isCompact_iff_compactSpace.mp hopenM.isClosed_compl.isCompact
  have hcompN : CompactSpace BN.complement :=
    isCompact_iff_compactSpace.mp hopenN.isClosed_compl.isCompact
  let _ : CompactSpace BM.complement := hcompM
  let _ : CompactSpace BN.complement := hcompN
  have hinjM : Function.Injective BM.boundaryMap := by
    intro b b' h
    exact injective_cellBoundaryInclusion 3
      (BM.injective_toFun (congrArg Subtype.val h))
  have hinjN : Function.Injective BN.boundaryMap := by
    intro b b' h
    exact injective_cellBoundaryInclusion 3
      (BN.injective_toFun (congrArg Subtype.val h))
  obtain ⟨hneck⟩ := connectedSumNeck_homeomorph_adjunctionSpace_of_collar
    BM.boundaryMap BN.boundaryMap BM.continuous_boundaryMap BN.continuous_boundaryMap
    hinjM hinjN glue collar hcollar hcollar_zero hcollar_open
  obtain ⟨hpiece⟩ := adjunctionSpace_homeomorph_of_piece_homeomorph
    (A := CellBoundary 3) (B := BM.complement) (X := BN.complement)
    (A' := SphereTwo) (B' := c.Punctured) (X' := d.Punctured)
    BM.boundaryMap (fun b => BN.boundaryMap (glue b))
    c.boundaryMap (fun z => d.boundaryMap (a z))
    CellAttachment.cellBoundaryThreeHomeomorphSphereTwo eM eN heM heN
  exact ⟨hneck.trans (hpiece.trans (Homeomorph.refl _))⟩

example : Nonempty (ConnectedSumNeck
      (fun b : CellBoundary 3 => (b, (0 : Icc (0 : ℝ) 1)))
      (fun b : CellBoundary 3 => (b, (0 : Icc (0 : ℝ) 1)))
      (Homeomorph.refl (CellBoundary 3))
    ≃ₜ AdjunctionSpace
      (fun b : CellBoundary 3 => (b, (0 : Icc (0 : ℝ) 1)))
      (fun b : CellBoundary 3 => (b, (0 : Icc (0 : ℝ) 1)))) :=
  connectedSumNeck_homeomorph_adjunctionSpace_of_collar
    (fun b : CellBoundary 3 => (b, (0 : Icc (0 : ℝ) 1)))
    (fun b : CellBoundary 3 => (b, (0 : Icc (0 : ℝ) 1)))
    (by fun_prop) (by fun_prop)
    (fun b b' h => congrArg (fun z : CellBoundary 3 × Icc (0 : ℝ) 1 => z.1) h)
    (fun b b' h => congrArg (fun z : CellBoundary 3 × Icc (0 : ℝ) 1 => z.1) h)
    (Homeomorph.refl (CellBoundary 3)) id Topology.IsEmbedding.id
    (fun b => rfl)
    (by
      rw [Set.image_id]
      exact isOpen_Iio.preimage (continuous_subtype_val.comp continuous_snd))

theorem exists_embeddedCellConnectedSum_homeomorph_connectedSum
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M.Carrier)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N.Carrier)
    (hM : EmbeddedCellChartIdentification BM (orientedBallChart M).toBallChart)
    (hN : EmbeddedCellAttachingCompatibility BN
      (CellAttachment.cellBoundaryThreeHomeomorphSphereTwo.trans
        (boundaryAttachment.1.toHomeomorph.trans
          CellAttachment.cellBoundaryThreeHomeomorphSphereTwo.symm))
      (orientedBallChart N).toBallChart boundaryAttachment.1.toHomeomorph) :
    Nonempty (EmbeddedCellConnectedSum BM BN
      (CellAttachment.cellBoundaryThreeHomeomorphSphereTwo.trans
        (boundaryAttachment.1.toHomeomorph.trans
          CellAttachment.cellBoundaryThreeHomeomorphSphereTwo.symm)) ≃ₜ
      (connectedSum M N).Carrier) :=
  embeddedCellConnectedSum_homeomorph_connectedSumQuotient BM BN _
    (orientedBallChart M).toBallChart (orientedBallChart N).toBallChart
    boundaryAttachment.1.toHomeomorph hM hN

end DifferentialGeometry.Topology.ThreeManifold
