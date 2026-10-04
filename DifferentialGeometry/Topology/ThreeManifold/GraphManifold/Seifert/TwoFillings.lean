import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsDegrees

/-!
# Blocks with two fillings

Chapter 6, packet K10d: the two-filling case `D²(p₁, p₂)` of `FilledBlockGoodness`.

Algebra. A nonempty reduced word in a free product is not `1` (`neWord_prod_ne_one`, via
`Monoid.CoprodI.Word.equiv`). In `TwoConeGroup p₁ p₂ = ℤ/p₁ ∗ ℤ/p₂` with generators `x`, `y`
(`coneX`, `coneY`) and `p₁, p₂ ≥ 2`, the alternating word `(xy)^(n+1)` (`coneWord`) is reduced, so
`xy` has infinite order (`coneXY_zpow_injective`). `TwoFillingGroup p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂` is the
iterated `Monoid.PushoutI` over `Bool` given by two applications of `seamVanKampen`. The inner
pushout `OnceFilledGroup` glues the second solid torus `ℤ` to `F(a, b) × ℤ` (`h` generating `ℤ`)
along `secondFillingEdge`: meridian `↦ 1` resp. `b^p₂ h^q₂`, longitude `↦` the generator resp.
`b^r₂ h^s₂`. The outer one glues the first solid torus to it along `firstFillingEdge` (`a^p₁ h^q₁`,
`a^r₁ h^s₁`). So it is `⟨a, b, h | h central, a^p₁ h^q₁, b^p₂ h^q₂⟩`. `twoFillingAbelian` maps it
to `ℤ × (ℤ/p₁ ∗ ℤ/p₂)` by `h ↦ (p₁p₂, 1)`, `a ↦ (-q₁p₂, x)`, `b ↦ (-q₂p₁, y)` (`pantsDetect`, well
defined by `onceFilledDetect_comp`, `twoFillingDetect_comp`). The free port
`twoFillingPort : (m, n) ↦ (ab)^m h^n` goes to `(-(q₁p₂ + q₂p₁) m + p₁p₂ n, (xy)^m)`, hence
`twoFillingPort_injective` for all `q, r, s`, and `twistedIBundlePort_injective` for `D²(2, 2)`.

Topology. Every Seifert block is connected (`SeifertBlock.connectedSpace`), and every filling seam
separates (`isSeparating_seam`). This holds because the solid torus owns only the left side of its
seam (`pieceImage_inter_pieceComplImage_subset_of_owned`, `isSeparating_of_owned`, without
`TwoSolidTori`'s hypothesis `count = 1`). So `seamVanKampen` applies to each seam of a
two-filling block. The identification of π₁ with `TwoFillingGroup` is stated, not proved, as
`TwoFillingDetection`: a homomorphism from π₁ of `W` at the free port to some
`TwoFillingGroup` with `p₁, p₂ ≥ 2`, under which the port becomes `twoFillingPort` after an
injective change of coordinates. From it `isGoodBlock_of_twoFillingDetection` and
`twistedIBundle_isGoodBlock` follow, and `filledBlockGoodness_of_twoFillingDetection` reduces all
of `FilledBlockGoodness` to `TwoFillingDetection` for two-filling blocks.
-/

set_option autoImplicit false

noncomputable section
open Multiplicative
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

universe u

namespace GC.Seifert

section Words
variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

theorem neWord_prod_ne_one {i j : ι} (w : Monoid.CoprodI.NeWord M i j) : w.prod ≠ 1 := by
  classical
  intro h
  have hw : w.toWord = Monoid.CoprodI.Word.empty := by
    rw [← Monoid.CoprodI.Word.equiv.apply_symm_apply w.toWord]
    change Monoid.CoprodI.Word.equiv w.prod = _
    rw [h]
    change (1 : Monoid.CoprodI M) • (Monoid.CoprodI.Word.empty : Monoid.CoprodI.Word M) = _
    exact one_smul _ _
  exact w.toList_ne_nil (congrArg Monoid.CoprodI.Word.toList hw)

end Words

theorem monoidHom_prod_ext {M N P : Type*} [MulOneClass M] [MulOneClass N] [Monoid P]
    {f g : M × N →* P} (h1 : f.comp (MonoidHom.inl M N) = g.comp (MonoidHom.inl M N))
    (h2 : f.comp (MonoidHom.inr M N) = g.comp (MonoidHom.inr M N)) : f = g := by
  refine MonoidHom.ext fun x => ?_
  have hx : x = MonoidHom.inl M N x.1 * MonoidHom.inr M N x.2 := by simp
  rw [hx, map_mul, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun h1 x.1) (DFunLike.congr_fun h2 x.2)

abbrev twoConeFactor (p₁ p₂ : ℕ) : Bool → Type
  | false => Multiplicative (ZMod p₁)
  | true => Multiplicative (ZMod p₂)

instance twoConeFactorGroup (p₁ p₂ : ℕ) (i : Bool) : Group (twoConeFactor p₁ p₂ i) := by
  cases i <;> simp only [twoConeFactor] <;> infer_instance

abbrev TwoConeGroup (p₁ p₂ : ℕ) := Monoid.CoprodI (twoConeFactor p₁ p₂)

def coneX (p₁ p₂ : ℕ) : TwoConeGroup p₁ p₂ :=
  Monoid.CoprodI.of (i := false) (ofAdd 1 : Multiplicative (ZMod p₁))

def coneY (p₁ p₂ : ℕ) : TwoConeGroup p₁ p₂ :=
  Monoid.CoprodI.of (i := true) (ofAdd 1 : Multiplicative (ZMod p₂))

theorem ofAdd_one_ne_one {p : ℕ} (hp : 2 ≤ p) : (ofAdd 1 : Multiplicative (ZMod p)) ≠ 1 := by
  have : Fact (1 < p) := ⟨hp⟩
  simp

def coneWord {p₁ p₂ : ℕ} (hp₁ : 2 ≤ p₁) (hp₂ : 2 ≤ p₂) :
    ℕ → Monoid.CoprodI.NeWord (twoConeFactor p₁ p₂) false true
  | 0 => .append (.singleton (i := false) (ofAdd 1 : Multiplicative (ZMod p₁))
      (ofAdd_one_ne_one hp₁)) (by decide)
      (.singleton (i := true) (ofAdd 1 : Multiplicative (ZMod p₂)) (ofAdd_one_ne_one hp₂))
  | n + 1 => .append (coneWord hp₁ hp₂ n) (by decide) (coneWord hp₁ hp₂ 0)

theorem coneWord_prod {p₁ p₂ : ℕ} (hp₁ : 2 ≤ p₁) (hp₂ : 2 ≤ p₂) (n : ℕ) :
    (coneWord hp₁ hp₂ n).prod = (coneX p₁ p₂ * coneY p₁ p₂) ^ (n + 1) := by
  have h0 : (coneWord hp₁ hp₂ 0).prod = coneX p₁ p₂ * coneY p₁ p₂ := by
    simp [coneWord, coneX, coneY]
  induction n with
  | zero => rw [h0, zero_add, pow_one]
  | succ n ih => rw [coneWord, Monoid.CoprodI.NeWord.append_prod, ih, h0, ← pow_succ]

theorem coneXY_zpow_injective {p₁ p₂ : ℕ} (hp₁ : 2 ≤ p₁) (hp₂ : 2 ≤ p₂) :
    Function.Injective fun m : ℤ => (coneX p₁ p₂ * coneY p₁ p₂) ^ m := by
  intro m m' h
  simp only at h
  by_contra hne
  have h1 : (coneX p₁ p₂ * coneY p₁ p₂) ^ (m - m') = 1 := by
    rw [zpow_sub, h, mul_inv_cancel]
  rcases Int.eq_nat_or_neg (m - m') with ⟨n, hn | hn⟩ <;> rw [hn] at h1
  · obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_add_one.2 (by omega)
    rw [zpow_natCast, ← coneWord_prod hp₁ hp₂] at h1
    exact neWord_prod_ne_one _ h1
  · obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_add_one.2 (by omega)
    rw [zpow_neg, zpow_natCast, inv_eq_one, ← coneWord_prod hp₁ hp₂] at h1
    exact neWord_prod_ne_one _ h1

theorem coneX_zpow_self (p₁ p₂ : ℕ) : coneX p₁ p₂ ^ (p₁ : ℤ) = 1 := by
  rw [coneX, ← map_zpow, ← ofAdd_zsmul]
  simp

theorem coneY_zpow_self (p₁ p₂ : ℕ) : coneY p₁ p₂ ^ (p₂ : ℤ) = 1 := by
  rw [coneY, ← map_zpow, ← ofAdd_zsmul]
  simp

theorem coneX_pow_self (p₁ p₂ : ℕ) : coneX p₁ p₂ ^ p₁ = 1 := by
  rw [← zpow_natCast, coneX_zpow_self]

theorem coneY_pow_self (p₁ p₂ : ℕ) : coneY p₁ p₂ ^ p₂ = 1 := by
  rw [← zpow_natCast, coneY_zpow_self]

theorem seamLinearForm_apply (x y : ℤ) (g : SeamGroup) :
    seamLinearForm x y g = ofAdd (toAdd g.1 * x + toAdd g.2 * y) :=
  toAdd.injective (toAdd_seamLinearForm x y g)

def secondFillingEdge (p q r s : ℤ) : ∀ i, SeamGroup →* filledBlockFactor i
  | false => MonoidHom.snd _ _
  | true => MonoidHom.prod ((zpowersHom _ (FreeGroup.of 1)).comp (seamLinearForm p r))
      (seamLinearForm q s)

abbrev OnceFilledGroup (p q r s : ℤ) := Monoid.PushoutI (secondFillingEdge p q r s)

abbrev twoFillingFactor (p q r s : ℤ) : Bool → Type
  | false => Multiplicative ℤ
  | true => OnceFilledGroup p q r s

instance twoFillingFactorGroup (p q r s : ℤ) (i : Bool) : Group (twoFillingFactor p q r s i) := by
  cases i <;> simp only [twoFillingFactor] <;> infer_instance

def firstFillingEdge (p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ : ℤ) :
    ∀ i, SeamGroup →* twoFillingFactor p₂ q₂ r₂ s₂ i
  | false => MonoidHom.snd _ _
  | true => (Monoid.PushoutI.of (φ := secondFillingEdge p₂ q₂ r₂ s₂) true).comp
      (MonoidHom.prod ((zpowersHom _ (FreeGroup.of 0)).comp (seamLinearForm p₁ r₁))
        (seamLinearForm q₁ s₁))

abbrev TwoFillingGroup (p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ : ℤ) :=
  Monoid.PushoutI (firstFillingEdge p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂)

def twoFillingPort (p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ : ℤ) :
    SeamGroup →* TwoFillingGroup p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ :=
  (Monoid.PushoutI.of (φ := firstFillingEdge p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂) true).comp
    ((Monoid.PushoutI.of (φ := secondFillingEdge p₂ q₂ r₂ s₂) true).comp
      ((zpowersHom _ (FreeGroup.of 0 * FreeGroup.of 1)).prodMap (MonoidHom.id _)))

abbrev TwoFillingTarget (p₁ p₂ : ℕ) := Multiplicative ℤ × TwoConeGroup p₁ p₂

def pantsDetect (p₁ p₂ : ℕ) (q₁ q₂ : ℤ) :
    FreeGroup (Fin 2) × Multiplicative ℤ →* TwoFillingTarget p₁ p₂ :=
  MonoidHom.prod
    (MonoidHom.coprod (FreeGroup.lift ![ofAdd (-q₁ * p₂), ofAdd (-q₂ * p₁)])
      (zpowersHom _ (ofAdd ((p₁ : ℤ) * p₂))))
    ((FreeGroup.lift ![coneX p₁ p₂, coneY p₁ p₂]).comp (MonoidHom.fst _ _))

theorem pantsDetect_apply (p₁ p₂ : ℕ) (q₁ q₂ : ℤ) (w : FreeGroup (Fin 2))
    (n : Multiplicative ℤ) :
    pantsDetect p₁ p₂ q₁ q₂ (w, n) =
      (FreeGroup.lift ![ofAdd (-q₁ * p₂), ofAdd (-q₂ * p₁)] w *
        ofAdd ((p₁ : ℤ) * p₂ * toAdd n), FreeGroup.lift ![coneX p₁ p₂, coneY p₁ p₂] w) := by
  simp [pantsDetect, mul_comm]

def onceFilledDetect (p₁ p₂ : ℕ) (q₁ q₂ r₂ s₂ : ℤ) :
    ∀ i, filledBlockFactor i →* TwoFillingTarget p₁ p₂
  | false => zpowersHom _ (pantsDetect p₁ p₂ q₁ q₂ (FreeGroup.of 1 ^ r₂, ofAdd s₂))
  | true => pantsDetect p₁ p₂ q₁ q₂

theorem onceFilledDetect_comp (p₁ p₂ : ℕ) (q₁ q₂ r₂ s₂ : ℤ) (i : Bool) :
    (onceFilledDetect p₁ p₂ q₁ q₂ r₂ s₂ i).comp (secondFillingEdge p₂ q₂ r₂ s₂ i) =
      (zpowersHom _ (pantsDetect p₁ p₂ q₁ q₂ (FreeGroup.of 1 ^ r₂, ofAdd s₂))).comp
        (MonoidHom.snd _ _) := by
  cases i with
  | false => rfl
  | true =>
    refine monoidHom_prod_ext (MonoidHom.ext_mint ?_) (MonoidHom.ext_mint ?_)
    · refine Prod.ext (toAdd.injective ?_) ?_
      · simp [onceFilledDetect, secondFillingEdge, pantsDetect_apply, toAdd_seamLinearForm]
        ring
      · simp [onceFilledDetect, secondFillingEdge, pantsDetect_apply, toAdd_seamLinearForm,
          coneY_pow_self]
    · simp [onceFilledDetect, secondFillingEdge, seamLinearForm_apply]

def onceFilledAbelian (p₁ p₂ : ℕ) (q₁ q₂ r₂ s₂ : ℤ) :
    OnceFilledGroup p₂ q₂ r₂ s₂ →* TwoFillingTarget p₁ p₂ :=
  Monoid.PushoutI.lift (onceFilledDetect p₁ p₂ q₁ q₂ r₂ s₂) _
    (onceFilledDetect_comp p₁ p₂ q₁ q₂ r₂ s₂)

def twoFillingDetect (p₁ p₂ : ℕ) (q₁ r₁ s₁ q₂ r₂ s₂ : ℤ) :
    ∀ i, twoFillingFactor p₂ q₂ r₂ s₂ i →* TwoFillingTarget p₁ p₂
  | false => zpowersHom _ (pantsDetect p₁ p₂ q₁ q₂ (FreeGroup.of 0 ^ r₁, ofAdd s₁))
  | true => onceFilledAbelian p₁ p₂ q₁ q₂ r₂ s₂

theorem twoFillingDetect_comp (p₁ p₂ : ℕ) (q₁ r₁ s₁ q₂ r₂ s₂ : ℤ) (i : Bool) :
    (twoFillingDetect p₁ p₂ q₁ r₁ s₁ q₂ r₂ s₂ i).comp
        (firstFillingEdge p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ i) =
      (zpowersHom _ (pantsDetect p₁ p₂ q₁ q₂ (FreeGroup.of 0 ^ r₁, ofAdd s₁))).comp
        (MonoidHom.snd _ _) := by
  cases i with
  | false => rfl
  | true =>
    refine monoidHom_prod_ext (MonoidHom.ext_mint ?_) (MonoidHom.ext_mint ?_)
    · refine Prod.ext (toAdd.injective ?_) ?_
      · simp [twoFillingDetect, firstFillingEdge, onceFilledAbelian, onceFilledDetect,
          pantsDetect_apply, toAdd_seamLinearForm]
        ring
      · simp [twoFillingDetect, firstFillingEdge, onceFilledAbelian, onceFilledDetect,
          pantsDetect_apply, toAdd_seamLinearForm, coneX_pow_self]
    · simp [twoFillingDetect, firstFillingEdge, onceFilledAbelian, onceFilledDetect,
        seamLinearForm_apply]

def twoFillingAbelian (p₁ p₂ : ℕ) (q₁ r₁ s₁ q₂ r₂ s₂ : ℤ) :
    TwoFillingGroup p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ →* TwoFillingTarget p₁ p₂ :=
  Monoid.PushoutI.lift (twoFillingDetect p₁ p₂ q₁ r₁ s₁ q₂ r₂ s₂) _
    (twoFillingDetect_comp p₁ p₂ q₁ r₁ s₁ q₂ r₂ s₂)

theorem twoFillingAbelian_port (p₁ p₂ : ℕ) (q₁ r₁ s₁ q₂ r₂ s₂ : ℤ) (v : SeamGroup) :
    twoFillingAbelian p₁ p₂ q₁ r₁ s₁ q₂ r₂ s₂ (twoFillingPort p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ v) =
      pantsDetect p₁ p₂ q₁ q₂ ((FreeGroup.of 0 * FreeGroup.of 1) ^ toAdd v.1, v.2) := by
  simp [twoFillingAbelian, twoFillingPort, twoFillingDetect, onceFilledAbelian,
    onceFilledDetect]
  rfl

theorem twoFillingPort_injective {p₁ p₂ : ℕ} (hp₁ : 2 ≤ p₁) (hp₂ : 2 ≤ p₂)
    (q₁ r₁ s₁ q₂ r₂ s₂ : ℤ) :
    Function.Injective (twoFillingPort p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂) := by
  intro v v' h
  have h' := congrArg (twoFillingAbelian p₁ p₂ q₁ r₁ s₁ q₂ r₂ s₂) h
  rw [twoFillingAbelian_port, twoFillingAbelian_port, pantsDetect_apply,
    pantsDetect_apply] at h'
  have h2 := congrArg Prod.snd h'
  simp only [map_zpow, map_mul, FreeGroup.lift_apply_of] at h2
  have hm : toAdd v.1 = toAdd v'.1 := coneXY_zpow_injective hp₁ hp₂ h2
  have h1 := congrArg (fun z => toAdd z.1) h'
  simp only [map_zpow, map_mul, FreeGroup.lift_apply_of, toAdd_mul, toAdd_zpow, toAdd_ofAdd,
    hm] at h1
  have hp : ((p₁ : ℤ) * p₂) ≠ 0 := by positivity
  have hn : toAdd v.2 = toAdd v'.2 := mul_left_cancel₀ hp (by linarith)
  exact Prod.ext (toAdd.injective hm) (toAdd.injective hn)

theorem twistedIBundlePort_injective (r₁ s₁ r₂ s₂ : ℤ) :
    Function.Injective (twoFillingPort 2 1 r₁ s₁ 2 (-1) r₂ s₂) :=
  twoFillingPort_injective (p₁ := 2) (p₂ := 2) le_rfl le_rfl 1 r₁ s₁ (-1) r₂ s₂

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (G : TorusPresentation W) (j : Fin G.pairing.count)

theorem cutMap_mem_seamSurface_of_mem_block' {x : G.cutCarrier.Carrier}
    (hx : x ∈ G.pairing.gluing.block j) : G.cutMap x ∈ G.seamSurface j := by
  rcases hx with hx | hx
  · refine ⟨(G.pairing.leftParam j).symm ⟨x, hx⟩, ?_⟩
    rw [seamTorus_eq_cutMap, Homeomorph.apply_symm_apply]
  · refine ⟨(G.pairing.matching j).symm ((G.pairing.rightParam j).symm ⟨x, hx⟩), ?_⟩
    rw [seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem pieceImage_inter_pieceComplImage_subset_of_owned (i : Fin G.components.count)
    (hown : ∀ s : G.OwnedSide i, s.val = .inl j) :
    G.pieceImage i ∩ G.pieceComplImage i ⊆ G.seamSurface j := by
  rintro w ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  rcases Quotient.exact (G.reconstruction.injective hxy.symm) with h | ⟨k, hk, -⟩
  · exact (hy (h ▸ hx)).elim
  · rcases hk with hkl | hkr
    · have hi : G.leftPiece k = i := G.eq_of_mem_piece (G.left_owned k hkl) hx
      have hs := hown ⟨.inl k, hi⟩
      simp only [Sum.inl.injEq] at hs
      subst hs
      exact G.cutMap_mem_seamSurface_of_mem_block' k (Or.inl hkl)
    · have hi : G.rightPiece k = i := G.eq_of_mem_piece (G.right_owned k hkr) hx
      exact absurd (hown ⟨.inr (.inl k), hi⟩) Sum.inr_ne_inl

theorem pathComponentIn_subset_pieceImage_of_inter {i : Fin G.components.count}
    (hS : G.pieceImage i ∩ G.pieceComplImage i ⊆ G.seamSurface j) {p : W.Carrier}
    (hp : p ∈ G.pieceImage i) (hpS : p ∉ G.seamSurface j) :
    pathComponentIn (G.seamSurface j)ᶜ p ⊆ G.pieceImage i := by
  have hcover : pathComponentIn (G.seamSurface j)ᶜ p ⊆ G.pieceImage i ∪ G.pieceComplImage i := by
    intro w _
    obtain ⟨x, rfl⟩ := G.surjective_cutMap w
    by_cases hx : x ∈ G.components.piece i
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  have hempty : pathComponentIn (G.seamSurface j)ᶜ p ∩
      (G.pieceImage i ∩ G.pieceComplImage i) = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun w hw => pathComponentIn_subset hw.1 (hS hw.2)
  rcases isPreconnected_iff_subset_of_disjoint_closed.1
    (isPathConnected_pathComponentIn hpS).isConnected.isPreconnected _ _
    (G.isClosed_pieceImage _) (G.isClosed_pieceComplImage _) hcover hempty with h | h
  · exact h
  · exact (hpS (hS ⟨hp, h (mem_pathComponentIn_self hpS)⟩)).elim

theorem isSeparating_of_owned (hown : ∀ s : G.OwnedSide (G.leftPiece j), s.val = .inl j)
    (hLR : G.leftPiece j ≠ G.rightPiece j) : G.IsSeparating j := by
  have hS := G.pieceImage_inter_pieceComplImage_subset_of_owned j _ hown
  rw [isSeparating_iff]
  intro h
  exact G.rightPoint_mem_compl j (hS ⟨G.pathComponentIn_subset_pieceImage_of_inter j hS
    (G.leftPoint_mem_pieceImage j) (G.leftPoint_mem_compl j) h,
      G.pieceImage_subset_pieceComplImage hLR (G.rightPoint_mem_pieceImage j)⟩)

end TorusPresentation

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem connectedSpace (B : SeifertBlock W d) : ConnectedSpace W.Carrier := by
  have himage : ∀ i, IsConnected (B.presentation.pieceImage i) := fun i =>
    (isConnected_iff_connectedSpace.mpr (B.presentation.components.connected i)).image _
      B.presentation.continuous_cutMap.continuousOn
  let s : Option (Fin d.fillingCount) → Set W.Carrier := fun o =>
    B.presentation.pieceImage (B.piece none) ∪ B.presentation.pieceImage (B.piece o)
  have hs : ∀ o, IsPreconnected (s o) := by
    intro o
    cases o with
    | none => simpa [s] using (himage (B.piece none)).isPreconnected
    | some m =>
      refine ((himage _).union ⟨B.presentation.seamTorus (B.seam m) torusBase, ?_, ?_⟩
        (himage _)).isPreconnected
      · rw [← B.rightPiece_seam m]
        exact ⟨_, B.presentation.right_owned _ (B.presentation.pairing.rightParam _ _).2,
          (B.presentation.seamTorus_eq_cutMap_right _ _).symm⟩
      · rw [← B.leftPiece_seam m]
        exact ⟨_, B.presentation.left_owned _ (B.presentation.pairing.leftParam _ _).2,
          (B.presentation.seamTorus_eq_cutMap _ _).symm⟩
  obtain ⟨w₀, hw₀⟩ := (himage (B.piece none)).nonempty
  have hU : (⋃ o, s o) = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨x, rfl⟩ := B.presentation.surjective_cutMap w
    obtain ⟨i, hi⟩ :=
      Set.mem_iUnion.1 (B.presentation.components.covers.symm ▸ Set.mem_univ x)
    refine Set.mem_iUnion.2 ⟨B.piece.symm i, Or.inr ⟨x, ?_, rfl⟩⟩
    rwa [Equiv.apply_symm_apply]
  have hpre : IsPreconnected (Set.univ : Set W.Carrier) :=
    hU ▸ isPreconnected_iUnion ⟨w₀, Set.mem_iInter.2 fun o => Or.inl hw₀⟩ hs
  exact { toPreconnectedSpace := ⟨hpre⟩, toNonempty := ⟨w₀⟩ }

theorem isSeparating_seam (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.IsSeparating (B.seam m) := by
  refine B.presentation.isSeparating_of_owned (B.seam m) (fun s => ?_) ?_
  · have hsub := (B.solid m).subsingleton_ownedSide
    have h := congrArg Subtype.val (Subsingleton.elim
      (⟨s.val, s.property.trans (B.leftPiece_seam m)⟩ : B.presentation.OwnedSide _)
      ((B.solid m).port 0))
    rw [B.solid_port] at h
    exact h
  · rw [B.leftPiece_seam, B.rightPiece_seam]
    exact fun h => Option.some_ne_none _ (B.piece.injective h)

def TwoFillingDetection (B : SeifertBlock W d) : Prop :=
  ∀ r : Fin d.ports, ∃ (p₁ p₂ : ℕ) (q₁ r₁ s₁ q₂ r₂ s₂ : ℤ)
    (Φ : FundamentalGroup W.Carrier (B.presentation.external.boundaryMap (B.free r) torusBase) →*
      TwoFillingGroup p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂) (A : SeamGroup →* SeamGroup),
    2 ≤ p₁ ∧ 2 ≤ p₂ ∧ Function.Injective A ∧ ∀ g,
      Φ (FundamentalGroup.map (B.presentation.external.boundaryMap (B.free r)) torusBase g) =
        twoFillingPort p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ (A (GC.Topology.torusFundamentalGroup g))

theorem isGoodBlock_of_twoFillingDetection (B : SeifertBlock W d) (H : B.TwoFillingDetection) :
    B.IsGoodBlock := by
  refine B.isGoodBlock_iff.2 fun r x => ?_
  obtain ⟨p₁, p₂, q₁, r₁, s₁, q₂, r₂, s₂, Φ, A, hp₁, hp₂, hA, hΦ⟩ := H r
  rw [← GC.Topology.injective_fundamentalGroup_map_iff _ torusBase x]
  intro g g' h
  have h' := congrArg Φ h
  rw [hΦ, hΦ] at h'
  exact GC.Topology.torusFundamentalGroup.injective
    (hA (twoFillingPort_injective hp₁ hp₂ _ _ _ _ _ _ h'))

theorem twistedIBundle_isGoodBlock (B : TwistedIBundle W) (H : B.TwoFillingDetection) :
    B.IsGoodBlock :=
  B.isGoodBlock_of_twoFillingDetection H

end SeifertBlock

theorem twistedIBundleData_fillingCount : twistedIBundleData.fillingCount = 2 :=
  rfl

theorem filledBlockGoodness_of_twoFillingDetection
    (H : ∀ (W : CompactCarrier.{u}) (d : SeifertData) (B : SeifertBlock W d),
      d.fillingCount = 2 → B.TwoFillingDetection) : FilledBlockGoodness.{u} := by
  intro W d B hports hst
  by_cases h1 : d.fillingCount ≤ 1
  · exact B.isGoodBlock_of_fillingCount_le_one hports hst h1
  · have hk := d.ports_add_fillingCount
    have hk3 := d.k_le_three
    exact B.isGoodBlock_of_twoFillingDetection (H W d B (by omega))

end GC.Seifert
