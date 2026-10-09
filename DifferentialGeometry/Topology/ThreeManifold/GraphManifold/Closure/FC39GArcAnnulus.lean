import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# FC39 GROUP G arcs (A6): the whole-fibre annulus over an embedded interval

Lane FC39-G-ARC (external draft 58 §四 A6, disposition D58-5). Over a continuous injective path
`γ : [0, 1] → R.Base` of the base of a circle region, the circle bundle is a product, in the weakest
form the arc layer asks for: a map `S¹ × [0, 1] → W` that is continuous, injective, has the whole
circle preimage of `range γ` as its image, and projects onto `γ` of the second parameter
(`CircleRegion.exists_annulus_GARC`). No framing alignment, no trivialization over loops, no
Ehresmann theorem: a Lebesgue number for the cover by trivializing neighbourhoods and induction on
the subdivision `[0, k/M]`, extending through the fibre coordinate of the trivialization of the next
step (`CircleRegion.sect_GARC`, `CircleRegion.coord_GARC`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology GC.Endpoint
open scoped Manifold Topology

universe u

namespace GC.GraphManifold.Assembly

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-! ## The local section and the fibre coordinate of one trivialization -/

section Local

variable (b : R.Base)

/-- The points of `W` over the neighbourhood `b` (an open set of `W`). -/
def CircleRegion.overNbhd_GARC : Set W.Carrier :=
  {x | ∃ hx : x ∈ R.domain, R.proj ⟨x, hx⟩ ∈ R.neighborhood b}

/-- The local section `(c, z) ↦ triv_b⁻¹ (c, z)` (the point `x₀` off the neighbourhood). -/
def CircleRegion.sect_GARC (x₀ : W.Carrier) (c : R.Base) (z : Circle) : W.Carrier := by
  classical
  exact if h : c ∈ R.neighborhood b then ((R.trivialization b).symm (⟨c, h⟩, z)).1.1 else x₀

/-- The fibre coordinate of the trivialization `b` (`1` off the neighbourhood). -/
def CircleRegion.coord_GARC (x : W.Carrier) : Circle := by
  classical
  exact if h : x ∈ R.overNbhd_GARC b then (R.trivialization b ⟨⟨x, h.1⟩, h.2⟩).2 else 1

variable {b}

theorem CircleRegion.sect_mem_GARC (x₀ : W.Carrier) {c : R.Base} (hc : c ∈ R.neighborhood b)
    (z : Circle) :
    ∃ hx : R.sect_GARC b x₀ c z ∈ R.domain, R.proj ⟨R.sect_GARC b x₀ c z, hx⟩ = c := by
  unfold CircleRegion.sect_GARC
  rw [dite_eq_left hc]
  refine ⟨((R.trivialization b).symm (⟨c, hc⟩, z)).1.2, ?_⟩
  have h := R.projection_trivialization b ((R.trivialization b).symm (⟨c, hc⟩, z))
  rw [(R.trivialization b).apply_symm_apply] at h
  exact h.symm

theorem CircleRegion.coord_sect_GARC (x₀ : W.Carrier) {c : R.Base} (hc : c ∈ R.neighborhood b)
    (z : Circle) : R.coord_GARC b (R.sect_GARC b x₀ c z) = z := by
  obtain ⟨hx, hpx⟩ := R.sect_mem_GARC x₀ hc z
  have hmem : R.sect_GARC b x₀ c z ∈ R.overNbhd_GARC b := ⟨hx, by rw [hpx]; exact hc⟩
  unfold CircleRegion.coord_GARC
  rw [dite_eq_left hmem]
  have hpt : (⟨⟨R.sect_GARC b x₀ c z, hmem.1⟩, hmem.2⟩ :
      TopologicalSpace.Opens.comap R.proj (R.neighborhood b)) =
      (R.trivialization b).symm (⟨c, hc⟩, z) := by
    apply Subtype.ext
    apply Subtype.ext
    change R.sect_GARC b x₀ c z = _
    unfold CircleRegion.sect_GARC
    rw [dite_eq_left hc]
  rw [hpt, (R.trivialization b).apply_symm_apply]

theorem CircleRegion.sect_coord_GARC (x₀ : W.Carrier) {x : W.Carrier} (hx : x ∈ R.domain)
    (hb : R.proj ⟨x, hx⟩ ∈ R.neighborhood b) :
    R.sect_GARC b x₀ (R.proj ⟨x, hx⟩) (R.coord_GARC b x) = x := by
  have hmem : x ∈ R.overNbhd_GARC b := ⟨hx, hb⟩
  set y : TopologicalSpace.Opens.comap R.proj (R.neighborhood b) := ⟨⟨x, hx⟩, hb⟩
  have hy : R.trivialization b y = (⟨R.proj ⟨x, hx⟩, hb⟩, R.coord_GARC b x) := by
    refine Prod.ext (Subtype.ext (R.projection_trivialization b y)) ?_
    unfold CircleRegion.coord_GARC
    rw [dite_eq_left hmem]
  unfold CircleRegion.sect_GARC
  rw [dite_eq_left hb]
  have := (R.trivialization b).symm_apply_apply y
  rw [hy] at this
  rw [this]

theorem CircleRegion.isOpen_overNbhd_GARC : IsOpen (R.overNbhd_GARC b) := by
  have h : R.overNbhd_GARC b = Subtype.val '' (R.proj ⁻¹' (R.neighborhood b : Set R.Base)) := by
    ext x
    constructor
    · rintro ⟨hx, hb⟩
      exact ⟨⟨x, hx⟩, hb, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  rw [h]
  exact R.domain.2.isOpenMap_subtype_val _
    ((R.neighborhood b).2.preimage R.proj.continuous)

theorem CircleRegion.continuousOn_coord_GARC :
    ContinuousOn (R.coord_GARC b) (R.overNbhd_GARC b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : (R.overNbhd_GARC b).domRestrict (R.coord_GARC b) = fun x =>
      (R.trivialization b ⟨⟨x.1, x.2.1⟩, x.2.2⟩).2 := by
    funext x
    change R.coord_GARC b x.1 = _
    unfold CircleRegion.coord_GARC
    rw [dite_eq_left x.2]
  rw [hfun]
  refine continuous_snd.comp ((R.trivialization b).continuous.comp ?_)
  exact (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem CircleRegion.continuousOn_sect_GARC (x₀ : W.Carrier) :
    ContinuousOn (fun p : R.Base × Circle => R.sect_GARC b x₀ p.1 p.2)
      ((R.neighborhood b : Set R.Base) ×ˢ univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : ((R.neighborhood b : Set R.Base) ×ˢ (univ : Set Circle)).domRestrict
      (fun p : R.Base × Circle => R.sect_GARC b x₀ p.1 p.2) = fun p =>
      ((R.trivialization b).symm (⟨p.1.1, (mem_prod.mp p.2).1⟩, p.1.2)).1.1 := by
    funext p
    change R.sect_GARC b x₀ p.1.1 p.1.2 = _
    unfold CircleRegion.sect_GARC
    rw [dite_eq_left (show p.1.1 ∈ R.neighborhood b from (mem_prod.mp p.2).1)]
  rw [hfun]
  refine continuous_subtype_val.comp (continuous_subtype_val.comp
    ((R.trivialization b).symm.continuous.comp ?_))
  exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)

end Local

/-! ## Extension along a subdivision -/

section Annulus

variable {R}

theorem CircleRegion.sect_injective_GARC {b : R.Base} (x₀ : W.Carrier) {c : R.Base}
    (hc : c ∈ R.neighborhood b) : Injective (R.sect_GARC b x₀ c) := fun z z' h => by
  rw [← R.coord_sect_GARC x₀ hc z, ← R.coord_sect_GARC x₀ hc z', h]

theorem CircleRegion.eq_of_coord_eq_GARC {b : R.Base} (x₀ : W.Carrier) {x y : W.Carrier}
    (hx : x ∈ R.domain) (hy : y ∈ R.domain) (hb : R.proj ⟨x, hx⟩ ∈ R.neighborhood b)
    (hxy : R.proj ⟨x, hx⟩ = R.proj ⟨y, hy⟩) (hc : R.coord_GARC b x = R.coord_GARC b y) :
    x = y := by
  rw [← R.sect_coord_GARC x₀ hx hb, ← R.sect_coord_GARC x₀ hy (hxy ▸ hb), hxy, hc]

/-- **The annulus over a path of the base, on `[0, 1]` inside `ℝ`.** -/
theorem CircleRegion.exists_annulusOn_GARC (γ : ℝ → R.Base) (hγ : Continuous γ)
    (hinj : InjOn γ (Icc 0 1)) (x₀ : W.Carrier) :
    ∃ A : Circle × ℝ → W.Carrier, ContinuousOn A (univ ×ˢ Icc 0 1) ∧
      InjOn A (univ ×ˢ Icc 0 1) ∧
      (∀ p ∈ (univ : Set Circle) ×ˢ Icc (0 : ℝ) 1,
        ∃ hx : A p ∈ R.domain, R.proj ⟨A p, hx⟩ = γ p.2) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x (hx : x ∈ R.domain), R.proj ⟨x, hx⟩ = γ t → ∃ z, A (z, t) = x := by
  classical
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := Icc (0 : ℝ) 1)
    (c := fun b : R.Base => γ ⁻¹' (R.neighborhood b)) isCompact_Icc
    (fun b => (R.neighborhood b).2.preimage hγ)
    (fun t _ => mem_iUnion.mpr ⟨γ t, R.mem_neighborhood (γ t)⟩)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  have hMpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  let P : ℕ → Prop := fun k => ∃ A : Circle × ℝ → W.Carrier,
    ContinuousOn A (univ ×ˢ Icc 0 (k / ((N : ℝ) + 1))) ∧
    InjOn A (univ ×ˢ Icc 0 (k / ((N : ℝ) + 1))) ∧
    (∀ p ∈ (univ : Set Circle) ×ˢ Icc (0 : ℝ) (k / ((N : ℝ) + 1)),
      ∃ hx : A p ∈ R.domain, R.proj ⟨A p, hx⟩ = γ p.2) ∧
    ∀ t ∈ Icc (0 : ℝ) (k / ((N : ℝ) + 1)), ∀ x (hx : x ∈ R.domain), R.proj ⟨x, hx⟩ = γ t →
      ∃ z, A (z, t) = x
  have key : ∀ k, k ≤ N + 1 → P k := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 : ((0 : ℕ) : ℝ) / ((N : ℝ) + 1) = 0 := by simp
      have hb₀ : γ 0 ∈ R.neighborhood (γ 0) := R.mem_neighborhood (γ 0)
      refine ⟨fun p => R.sect_GARC (γ 0) x₀ (γ 0) p.1, ?_, ?_, ?_, ?_⟩ <;> rw [h0]
      · refine Continuous.continuousOn ?_
        exact (R.continuousOn_sect_GARC x₀).comp_continuous
          (continuous_const.prodMk continuous_fst) fun p => ⟨hb₀, mem_univ _⟩
      · rintro p ⟨-, hp⟩ p' ⟨-, hp'⟩ h
        have e1 : p.2 = 0 := le_antisymm hp.2 hp.1
        have e2 : p'.2 = 0 := le_antisymm hp'.2 hp'.1
        exact Prod.ext (R.sect_injective_GARC x₀ hb₀ h) (e1.trans e2.symm)
      · rintro p ⟨-, hp⟩
        have e1 : p.2 = 0 := le_antisymm hp.2 hp.1
        rw [e1]
        exact R.sect_mem_GARC x₀ hb₀ p.1
      · intro t ht x hx hpx
        have e1 : t = 0 := le_antisymm ht.2 ht.1
        subst e1
        refine ⟨R.coord_GARC (γ 0) x, ?_⟩
        change R.sect_GARC (γ 0) x₀ (γ 0) (R.coord_GARC (γ 0) x) = x
        rw [← hpx]
        exact R.sect_coord_GARC x₀ hx (hpx ▸ hb₀)
    | succ k ih =>
      intro hk
      obtain ⟨A, h1, h2, h3, h4⟩ := ih (by omega)
      set s : ℝ := k / ((N : ℝ) + 1) with hsdef
      set s' : ℝ := ((k + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) with hs'def
      have hs0 : 0 ≤ s := by positivity
      have hss' : s' = s + 1 / ((N : ℝ) + 1) := by
        rw [hs'def, hsdef]
        push_cast
        ring
      have hs'1 : s' ≤ 1 := by
        rw [hs'def, div_le_one hMpos]
        exact_mod_cast hk
      have hs1 : s ≤ 1 := by
        have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
        linarith
      have hN' : 1 / ((N : ℝ) + 1) < δ := hN
      have hsle : s ≤ s' := by
        have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
        linarith
      obtain ⟨b, hb⟩ := hball s ⟨hs0, hs1⟩
      have hγb : ∀ t, s ≤ t → t ≤ s' → γ t ∈ R.neighborhood b := by
        intro t ht1 ht2
        apply hb
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith
      have hAs : ∀ z, ∃ hx : A (z, s) ∈ R.domain, R.proj ⟨A (z, s), hx⟩ = γ s :=
        fun z => h3 (z, s) ⟨mem_univ _, hs0, le_rfl⟩
      let B : Circle × ℝ → W.Carrier := fun p =>
        R.sect_GARC b x₀ (γ p.2) (R.coord_GARC b (A (p.1, s)))
      have hAB : ∀ z, B (z, s) = A (z, s) := by
        intro z
        obtain ⟨hx, hpx⟩ := hAs z
        change R.sect_GARC b x₀ (γ s) (R.coord_GARC b (A (z, s))) = A (z, s)
        rw [← hpx]
        exact R.sect_coord_GARC x₀ hx (hpx ▸ hγb s le_rfl hsle)
      have hcoordc : Continuous fun z => R.coord_GARC b (A (z, s)) := by
        refine (R.continuousOn_coord_GARC).comp_continuous
          (h1.comp_continuous (continuous_id.prodMk continuous_const)
            fun z => ⟨mem_univ _, hs0, le_rfl⟩) fun z => ?_
        obtain ⟨hx, hpx⟩ := hAs z
        exact ⟨hx, by rw [hpx]; exact hγb s le_rfl hsle⟩
      have hBc : ContinuousOn B {p : Circle × ℝ | s ≤ p.2 ∧ p.2 ≤ s'} := by
        refine (R.continuousOn_sect_GARC x₀).comp
          ((hγ.comp continuous_snd).prodMk (hcoordc.comp continuous_fst)).continuousOn ?_
        intro p hp
        exact ⟨hγb p.2 hp.1 hp.2, mem_univ _⟩
      let A' : Circle × ℝ → W.Carrier := fun p => if p.2 ≤ s then A p else B p
      have hproj' : ∀ p ∈ (univ : Set Circle) ×ˢ Icc (0 : ℝ) s',
          ∃ hx : A' p ∈ R.domain, R.proj ⟨A' p, hx⟩ = γ p.2 := by
        rintro p ⟨-, hp⟩
        by_cases hps : p.2 ≤ s
        · have e : A' p = A p := ite_eq_left hps
          rw [e]
          exact h3 p ⟨mem_univ _, hp.1, hps⟩
        · have e : A' p = B p := ite_eq_right hps
          rw [e]
          exact R.sect_mem_GARC x₀ (hγb p.2 (le_of_lt (not_le.mp hps)) hp.2) _
      refine ⟨A', ?_, ?_, hproj', ?_⟩
      · apply ContinuousOn.if
        · rintro p ⟨-, hpf⟩
          have e : p.2 = s := frontier_le_subset_eq continuous_snd continuous_const hpf
          have hp : p = (p.1, s) := Prod.ext rfl e
          rw [hp, hAB]
        · refine h1.mono ?_
          rintro p ⟨⟨-, hp⟩, hpc⟩
          rw [(isClosed_le continuous_snd continuous_const).closure_eq] at hpc
          exact ⟨mem_univ _, hp.1, hpc⟩
        · refine hBc.mono ?_
          rintro p ⟨⟨-, hp⟩, hpc⟩
          have hsub : closure {a : Circle × ℝ | ¬ a.2 ≤ s} ⊆ {a | s ≤ a.2} := by
            simp only [not_le]
            exact closure_lt_subset_le continuous_const continuous_snd
          exact ⟨hsub hpc, hp.2⟩
      · intro p hp p' hp' h
        obtain ⟨hx, hpx⟩ := hproj' p hp
        obtain ⟨hx', hpx'⟩ := hproj' p' hp'
        have hγeq : γ p.2 = γ p'.2 := by
          rw [← hpx, ← hpx']
          congr 2
        have e2 : p.2 = p'.2 := hinj ⟨hp.2.1, hp.2.2.trans hs'1⟩
          ⟨hp'.2.1, hp'.2.2.trans hs'1⟩ hγeq
        by_cases hps : p.2 ≤ s
        · have hps' : p'.2 ≤ s := e2 ▸ hps
          have e : A' p = A p := ite_eq_left hps
          have e' : A' p' = A p' := ite_eq_left hps'
          rw [e, e'] at h
          exact h2 ⟨mem_univ _, hp.2.1, hps⟩ ⟨mem_univ _, hp'.2.1, hps'⟩ h
        · have hps' : ¬ p'.2 ≤ s := e2 ▸ hps
          have e : A' p = B p := ite_eq_right hps
          have e' : A' p' = B p' := ite_eq_right hps'
          rw [e, e'] at h
          change R.sect_GARC b x₀ (γ p.2) (R.coord_GARC b (A (p.1, s))) =
            R.sect_GARC b x₀ (γ p'.2) (R.coord_GARC b (A (p'.1, s))) at h
          rw [← e2] at h
          have hc := R.sect_injective_GARC x₀
            (hγb p.2 (le_of_lt (not_le.mp hps)) hp.2.2) h
          obtain ⟨hy, hpy⟩ := hAs p.1
          obtain ⟨hy', hpy'⟩ := hAs p'.1
          have hA := R.eq_of_coord_eq_GARC x₀ hy hy'
            (by rw [hpy]; exact hγb s le_rfl hsle) (hpy.trans hpy'.symm) hc
          have h12 := h2 ⟨mem_univ _, hs0, le_rfl⟩ ⟨mem_univ _, hs0, le_rfl⟩ hA
          have h12' := congrArg Prod.fst h12
          exact Prod.ext h12' e2
      · intro t ht x hx hpx
        by_cases hts : t ≤ s
        · obtain ⟨z, hz⟩ := h4 t ⟨ht.1, hts⟩ x hx hpx
          refine ⟨z, ?_⟩
          have e : A' (z, t) = A (z, t) := ite_eq_left hts
          rw [e, hz]
        · have htb := hγb t (le_of_lt (not_le.mp hts)) ht.2
          have hsb := hγb s le_rfl hsle
          obtain ⟨hx', hpx'⟩ := R.sect_mem_GARC x₀ hsb (R.coord_GARC b x)
          obtain ⟨z, hz⟩ := h4 s ⟨hs0, le_rfl⟩ _ hx' hpx'
          refine ⟨z, ?_⟩
          have e : A' (z, t) = B (z, t) := ite_eq_right hts
          rw [e]
          change R.sect_GARC b x₀ (γ t) (R.coord_GARC b (A (z, s))) = x
          rw [hz, R.coord_sect_GARC x₀ hsb, ← hpx]
          exact R.sect_coord_GARC x₀ hx (hpx ▸ htb)
  obtain ⟨A, h1, h2, h3, h4⟩ := key (N + 1) le_rfl
  have hM1 : ((N + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) = 1 := by
    push_cast
    exact div_self hMpos.ne'
  rw [hM1] at h1 h2 h3 h4
  exact ⟨A, h1, h2, h3, h4⟩

/-- The unit circle of the plane and `Circle`. -/
def sphereCircleHomeomorph_GARC :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map]).symm

/-- **A6: the whole-fibre annulus over an embedded interval** — continuous, injective, onto the
whole circle preimage of `range γ`, projecting onto `γ` of the second parameter. -/
theorem CircleRegion.exists_annulus_GARC (γ : Icc (0 : ℝ) 1 → R.Base) (hγ : Continuous γ)
    (hinj : Injective γ) :
    ∃ A : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → W.Carrier,
      Continuous A ∧ Injective A ∧ range A = Subtype.val '' (R.proj ⁻¹' range γ) ∧
      ∀ q, ∃ hx : A q ∈ R.domain, R.proj ⟨A q, hx⟩ = γ q.2 := by
  let x₀ : W.Carrier := ((R.trivialization (γ (iccEnd false))).symm
    (⟨γ (iccEnd false), R.mem_neighborhood _⟩, 1)).1.1
  let γ' : ℝ → R.Base := γ ∘ projIcc (0 : ℝ) 1 zero_le_one
  have hγ' : Continuous γ' := hγ.comp continuous_projIcc
  have hγ'v : ∀ t : Icc (0 : ℝ) 1, γ' t.1 = γ t := fun t => by
    change γ (projIcc (0 : ℝ) 1 zero_le_one t.1) = γ t
    rw [projIcc_val]
  have hinj' : InjOn γ' (Icc 0 1) := by
    intro t ht t' ht' h
    have := hinj ((hγ'v ⟨t, ht⟩).symm.trans (h.trans (hγ'v ⟨t', ht'⟩)))
    exact congrArg Subtype.val this
  obtain ⟨A, h1, h2, h3, h4⟩ := R.exists_annulusOn_GARC γ' hγ' hinj' x₀
  let e := sphereCircleHomeomorph_GARC
  have hmem : ∀ q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1,
      (e q.1, q.2.1) ∈ (univ : Set Circle) ×ˢ Icc (0 : ℝ) 1 := fun q => ⟨mem_univ _, q.2.2⟩
  refine ⟨fun q => A (e q.1, q.2.1), ?_, ?_, ?_, ?_⟩
  · exact h1.comp_continuous ((e.continuous.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) hmem
  · intro q q' h
    have h' := h2 (hmem q) (hmem q') h
    exact Prod.ext (e.injective (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨hx, hpx⟩ := h3 _ (hmem q)
      exact ⟨⟨_, hx⟩, ⟨q.2, by rw [hpx]; exact (hγ'v q.2).symm⟩, rfl⟩
    · rintro ⟨y, ⟨t, ht⟩, rfl⟩
      obtain ⟨z, hz⟩ := h4 t.1 t.2 y.1 y.2 (by rw [hγ'v t]; exact ht.symm)
      exact ⟨(e.symm z, t), by
        change A (e (e.symm z), t.1) = y.1
        rw [e.apply_symm_apply, hz]⟩
  · intro q
    obtain ⟨hx, hpx⟩ := h3 _ (hmem q)
    exact ⟨hx, hpx.trans (hγ'v q.2)⟩

end Annulus

end GC.GraphManifold.Assembly
