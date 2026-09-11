import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactPathAvoidance

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {X : Type*} [PseudoMetricSpace X]

theorem eVariationOn_extend_trans_eq {x y z : X} (p : Path x y) (q : Path y z) :
    eVariationOn (p.trans q).extend (Icc (0 : ℝ) 1) =
      eVariationOn p.extend (Icc (0 : ℝ) 1) +
        eVariationOn q.extend (Icc (0 : ℝ) 1) := by
  have hsplit := eVariationOn.Icc_add_Icc (⇑(p.trans q).extend)
    (s := Set.univ) (a := (0 : ℝ)) (b := 1 / 2) (c := 1)
    (by norm_num) (by norm_num) (Set.mem_univ _)
  simp only [Set.univ_inter] at hsplit
  have himg₁ : (fun t : ℝ => 2 * t) '' Icc (0 : ℝ) (1 / 2) = Icc (0 : ℝ) 1 := by
    ext v
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨hv0, hv1⟩
      exact ⟨v / 2, ⟨by linarith, by linarith⟩, by linarith⟩
  have himg₂ : (fun t : ℝ => 2 * t - 1) '' Icc (1 / 2 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    ext v
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨hv0, hv1⟩
      exact ⟨(v + 1) / 2, ⟨by linarith, by linarith⟩, by linarith⟩
  have hmono₁ : MonotoneOn (fun t : ℝ => 2 * t) (Icc (0 : ℝ) (1 / 2)) :=
    fun _ _ _ _ huv => by linarith
  have hmono₂ : MonotoneOn (fun t : ℝ => 2 * t - 1) (Icc (1 / 2 : ℝ) 1) :=
    fun _ _ _ _ huv => by linarith
  have heq₁ : EqOn (⇑(p.trans q).extend)
      ((⇑p.extend) ∘ fun t : ℝ => 2 * t) (Icc (0 : ℝ) (1 / 2)) :=
    fun _ ht => Path.extend_trans_of_le_half p q ht.2
  have heq₂ : EqOn (⇑(p.trans q).extend)
      ((⇑q.extend) ∘ fun t : ℝ => 2 * t - 1) (Icc (1 / 2 : ℝ) 1) :=
    fun _ ht => Path.extend_trans_of_half_le p q ht.1
  rw [eVariationOn.eq_of_eqOn heq₁,
    eVariationOn.comp_eq_of_monotoneOn (⇑p.extend) _ hmono₁, himg₁,
    eVariationOn.eq_of_eqOn heq₂,
    eVariationOn.comp_eq_of_monotoneOn (⇑q.extend) _ hmono₂, himg₂] at hsplit
  exact hsplit.symm

theorem collar_excursion_length_lower {x y : X} (p : Path x y)
    {r : ℝ} (hr : 0 ≤ r) (s : unitInterval)
    (hleft : ENNReal.ofReal r ≤ edist x (p s))
    (hright : ENNReal.ofReal r ≤ edist (p s) y) :
    ENNReal.ofReal (2 * r) ≤ eVariationOn p.extend (Icc (0 : ℝ) 1) := by
  have hsplit := eVariationOn.Icc_add_Icc (⇑p.extend)
    (s := Set.univ) s.2.1 s.2.2 (Set.mem_univ _)
  simp only [Set.univ_inter] at hsplit
  have h₁ := eVariationOn.edist_le (⇑p.extend)
    (show (0 : ℝ) ∈ Icc 0 (s : ℝ) from ⟨le_rfl, s.2.1⟩)
    (show (s : ℝ) ∈ Icc 0 (s : ℝ) from ⟨s.2.1, le_rfl⟩)
  have h₂ := eVariationOn.edist_le (⇑p.extend)
    (show (s : ℝ) ∈ Icc (s : ℝ) 1 from ⟨le_rfl, s.2.2⟩)
    (show (1 : ℝ) ∈ Icc (s : ℝ) 1 from ⟨s.2.2, le_rfl⟩)
  rw [Path.extend_zero, Path.extend_extends'] at h₁
  rw [Path.extend_extends', Path.extend_one] at h₂
  calc
    ENNReal.ofReal (2 * r) = ENNReal.ofReal r + ENNReal.ofReal r := by
      rw [two_mul, ENNReal.ofReal_add hr hr]
    _ ≤ _ := add_le_add (hleft.trans h₁) (hright.trans h₂)
    _ = _ := hsplit

theorem exists_shorter_path_of_collar_excursion {a x y b : X}
    (prefixPath : Path a x) (excursion : Path x y) (suffix : Path y b)
    (hprefix : BoundedVariationOn prefixPath.extend (Icc (0 : ℝ) 1))
    (hsuffix : BoundedVariationOn suffix.extend (Icc (0 : ℝ) 1))
    {r D delta : ℝ} (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hgap : D + delta < 2 * r) (s : unitInterval)
    (hleft : ENNReal.ofReal r ≤ edist x (excursion s))
    (hright : ENNReal.ofReal r ≤ edist (excursion s) y)
    (shortcut : Path x y)
    (hshort : eVariationOn shortcut.extend (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal D)
    (hdelta : 0 ≤ delta) :
    ∃ replacement : Path a b,
      Set.range replacement ⊆ Set.range prefixPath ∪ Set.range shortcut ∪ Set.range suffix ∧
      eVariationOn replacement.extend (Icc (0 : ℝ) 1) + ENNReal.ofReal delta <
        eVariationOn ((prefixPath.trans excursion).trans suffix).extend (Icc (0 : ℝ) 1) := by
  have hmiddle : eVariationOn shortcut.extend (Icc (0 : ℝ) 1) + ENNReal.ofReal delta <
      eVariationOn excursion.extend (Icc (0 : ℝ) 1) := by
    calc
      _ ≤ ENNReal.ofReal D + ENNReal.ofReal delta := add_le_add hshort le_rfl
      _ = ENNReal.ofReal (D + delta) := (ENNReal.ofReal_add hD hdelta).symm
      _ < ENNReal.ofReal (2 * r) := ENNReal.ofReal_lt_ofReal_iff
        (lt_of_le_of_lt (add_nonneg hD hdelta) hgap) |>.2 hgap
      _ ≤ _ := collar_excursion_length_lower excursion hr s hleft hright
  refine ⟨(prefixPath.trans shortcut).trans suffix, ?_, ?_⟩
  · rw [Path.trans_range, Path.trans_range]
  · rw [eVariationOn_extend_trans_eq, eVariationOn_extend_trans_eq,
      eVariationOn_extend_trans_eq, eVariationOn_extend_trans_eq]
    calc
      _ = (eVariationOn prefixPath.extend (Icc (0 : ℝ) 1) +
          (eVariationOn shortcut.extend (Icc (0 : ℝ) 1) + ENNReal.ofReal delta)) +
          eVariationOn suffix.extend (Icc (0 : ℝ) 1) := by ac_rfl
      _ < _ := ENNReal.add_lt_add_right hsuffix
        (ENNReal.add_lt_add_left hprefix hmiddle)

theorem no_collar_return_of_near_minimal {x y : X} (p : Path x y)
    {r D delta : ℝ} (hr : 0 ≤ r) (hD : 0 ≤ D) (hdelta : 0 ≤ delta)
    (hgap : D + delta < 2 * r)
    (hminimal : ∀ q : Path x y,
      eVariationOn p.extend (Icc (0 : ℝ) 1) ≤
        eVariationOn q.extend (Icc (0 : ℝ) 1) + ENNReal.ofReal delta)
    (shortcut : Path x y)
    (hshort : eVariationOn shortcut.extend (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal D) :
    ¬ ∃ s : unitInterval, ENNReal.ofReal r ≤ edist x (p s) ∧
      ENNReal.ofReal r ≤ edist (p s) y := by
  rintro ⟨s, hleft, hright⟩
  have hcost := collar_excursion_length_lower p hr s hleft hright
  have hbudget := (hminimal shortcut).trans (add_le_add hshort le_rfl)
  rw [← ENNReal.ofReal_add hD hdelta] at hbudget
  have hlt : ENNReal.ofReal (D + delta) < ENNReal.ofReal (2 * r) :=
    (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (add_nonneg hD hdelta) hgap)).2 hgap
  exact (not_lt_of_ge (hcost.trans hbudget)) hlt

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
