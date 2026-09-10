import DifferentialGeometry.Topology.Morse.InteriorCellAttachment
import DifferentialGeometry.Topology.Morse.InteriorSublevelDeformation
import DifferentialGeometry.Topology.Cell.AttachmentEuler
import Mathlib.Data.Finset.Max

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ContinuousMap
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Homotopy
namespace Poincare.Morse

private theorem exists_last_critical_band {A : Type} (f : A → ℝ) (s : Finset A)
    (p : A) (hp : p ∈ s) (hinj : InjOn f (s : Set A))
    (hmax : ∀ x ∈ s, f x ≤ f p) {a b : ℝ} (ha : a < f p) (hb : f p < b) :
    ∃ δ : ℝ, 0 < δ ∧ a < f p - δ ∧ f p + δ < b ∧
      ∀ x ∈ s, x ≠ p → f x < f p - δ := by
  classical
  let t := insert a ((s.erase p).image f)
  have ht : t.Nonempty := Finset.insert_nonempty _ _
  let c := t.max' ht
  have hc : c < f p := by
    apply (Finset.max'_lt_iff _ _).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ha
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact lt_of_le_of_ne (hmax x (Finset.mem_of_mem_erase hx))
        (fun h => (Finset.ne_of_mem_erase hx) (hinj (Finset.mem_of_mem_erase hx) hp h))
  have hac : a ≤ c := t.le_max' a (Finset.mem_insert_self _ _)
  let δ := min (f p - c) (b - f p) / 2
  have hδ : 0 < δ := half_pos (lt_min (sub_pos.mpr hc) (sub_pos.mpr hb))
  have hδc : δ < f p - c := by dsimp [δ]; linarith [min_le_left (f p - c) (b - f p)]
  have hδb : δ < b - f p := by dsimp [δ]; linarith [min_le_right (f p - c) (b - f p)]
  refine ⟨δ, hδ, by linarith, by linarith, ?_⟩
  intro x hx hxp
  have hxc : f x ≤ c := t.le_max' (f x)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxp, hx⟩, rfl⟩))
  linarith

variable {m : ℕ} {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem regularBandEuler (K : Type) [Field K]
    (e : E ≃L[ℝ] MorseModel (m + 1)) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hr : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x)
    (hinterior : sublevel f b ⊆ I.interior M)
    (hfin : Poincare.Homology.finiteHomologyType K (TopCat.of (SublevelSpace f a))) :
    Poincare.Homology.finiteHomologyType K (TopCat.of (SublevelSpace f b)) ∧
      Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f b)) =
        Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f a)) := by
  obtain ⟨h, _⟩ := exists_sublevelHomotopyEquivUnder_of_interiorSublevel I e hf hab
    hcompact hr hinterior (ContinuousMap.id (SublevelSpace f a))
  exact ⟨(Poincare.Homology.finiteHomologyType_iff_of_homotopyEquiv K
    (X := TopCat.of (SublevelSpace f b)) (Y := TopCat.of (SublevelSpace f a))
    h.toHomotopyEquiv).mpr hfin,
    Poincare.Homology.eulerChar_eq_of_homotopyEquiv K h.toHomotopyEquiv⟩

private theorem finiteBandEulerAux (K : Type) [Field K]
    (e : E ≃L[ℝ] MorseModel (m + 1)) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (s : Finset M) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hinterior : sublevel f b ⊆ I.interior M)
    (hs : ∀ x, x ∈ s ↔ f x ∈ Icc a b ∧ IsCriticalPointAt I f x)
    (ha : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (hb : ∀ x, f x = b → ¬ IsCriticalPointAt I f x)
    (hnd : ∀ x ∈ s, IsNondegenerateCriticalPointAt I f x)
    (hinj : InjOn f (s : Set M))
    (hfin : Poincare.Homology.finiteHomologyType K (TopCat.of (SublevelSpace f a))) :
    Poincare.Homology.finiteHomologyType K (TopCat.of (SublevelSpace f b)) ∧
      Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f b)) =
        Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f a)) +
          ∑ p ∈ s, (-1 : ℤ) ^ sigNeg (chartHessianAt
            (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
  classical
  induction s using Finset.strongInductionOn generalizing a b
  rename_i s ih
  by_cases hsempty : s = ∅
  · have hr : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x := by
      intro x hx hc
      have hxs := (hs x).mpr ⟨hx, hc⟩
      simp only [hsempty, Finset.notMem_empty] at hxs
    simpa only [hsempty, Finset.sum_empty, add_zero] using
      regularBandEuler I K e hf hab hcompact hr hinterior hfin
  obtain ⟨p, hp, hmax⟩ := s.exists_max_image f (Finset.nonempty_iff_ne_empty.mpr hsempty)
  have hps := (hs p).mp hp
  have hpa : a < f p := lt_of_le_of_ne hps.1.1 (fun he => ha p he.symm hps.2)
  have hpb : f p < b := lt_of_le_of_ne hps.1.2 (fun he => hb p he hps.2)
  obtain ⟨δ, hδ, haδ, hδb, hgap⟩ := exists_last_critical_band f s p hp hinj hmax hpa hpb
  have hcδ : IsCompact (f ⁻¹' Icc (f p - δ) (f p + δ)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (fun _ hx => ⟨haδ.le.trans hx.1, hx.2.trans hδb.le⟩)
  have huδ : sublevel f (f p + δ) ⊆ I.interior M :=
    fun _ hx => hinterior (hx.trans hδb.le)
  have huniq : ∀ x, f x ∈ Icc (f p - δ) (f p + δ) →
      x = p ∨ ¬ IsCriticalPointAt I f x := by
    intro x hx
    by_cases hxp : x = p
    · exact Or.inl hxp
    · right
      intro hc
      have hxs := (hs x).mpr ⟨⟨haδ.le.trans hx.1, hx.2.trans hδb.le⟩, hc⟩
      exact (not_lt_of_ge hx.1) (hgap x hxs hxp)
  let Q := chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)
  let d := sigNeg Q
  let _ : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  have hd : d ≤ m + 1 := by
    have hd' := sigPos_le_finrank (-Q)
    have he := e.toLinearEquiv.finrank_eq
    simp only [Module.finrank_pi, Fintype.card_fin] at he
    simpa only [d, sigNeg, he] using hd'
  obtain ⟨ε, hε, hεδ, φ, ⟨hφ⟩⟩ := one_critical_point_cell_attachment_of_interiorSublevel
    I e f hf p d hd (hnd p hp) rfl δ hδ hcδ huniq huδ
  have haε : a < f p - ε := by linarith
  have hεb : f p + ε < b := by linarith
  have hsmall (x : M) (hx : x ∈ s.erase p) : f x < f p - ε := by
    have hg := hgap x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    linarith
  have hslo : ∀ x, x ∈ s.erase p ↔ f x ∈ Icc a (f p - ε) ∧ IsCriticalPointAt I f x := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨((hs x).mp (Finset.mem_of_mem_erase hx)).1.1, (hsmall x hx).le⟩,
        ((hs x).mp (Finset.mem_of_mem_erase hx)).2⟩
    · rintro ⟨hx, hc⟩
      refine Finset.mem_erase.mpr ⟨?_, (hs x).mpr ⟨⟨hx.1, by linarith [hx.2]⟩, hc⟩⟩
      rintro rfl
      linarith [hx.2]
  have hreglo : ∀ x, f x = f p - ε → ¬ IsCriticalPointAt I f x := by
    intro x hx hc
    have hxs := (hslo x).mpr ⟨⟨by linarith, hx.le⟩, hc⟩
    exact (ne_of_lt (hsmall x hxs)) hx
  have hclo : IsCompact (f ⁻¹' Icc a (f p - ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (fun _ hx => ⟨hx.1, by linarith [hx.2]⟩)
  have hulo : sublevel f (f p - ε) ⊆ I.interior M :=
    fun x hx => hinterior ((show f x ≤ f p - ε from hx).trans (by linarith))
  obtain ⟨hfinlo, heulerlo⟩ := ih (s.erase p) (Finset.erase_ssubset hp) haε.le hclo hulo hslo
    ha hreglo (fun x hx => hnd x (Finset.mem_of_mem_erase hx))
    (hinj.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))) hfin
  have hfinadj := Poincare.Cell.finiteHomologyType_cellAdjunction d φ K hfinlo
  have hfinmid := (Poincare.Homology.finiteHomologyType_iff_of_homotopyEquiv K
    (X := TopCat.of (SublevelSpace f (f p + ε)))
    (Y := TopCat.of (CellAdjunctionSpace d φ)) hφ.toHomotopyEquiv).mpr hfinadj
  have heulermid : Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f (f p + ε))) =
      Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f (f p - ε))) + (-1 : ℤ)^d :=
    (Poincare.Homology.eulerChar_eq_of_homotopyEquiv K hφ.toHomotopyEquiv).trans
      (Poincare.Cell.eulerChar_cellAdjunction d φ K hfinlo)
  have hcup : IsCompact (f ⁻¹' Icc (f p + ε) b) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (fun _ hx => ⟨by linarith [hx.1], hx.2⟩)
  have hregup : ∀ x ∈ f ⁻¹' Icc (f p + ε) b, ¬ IsCriticalPointAt I f x := by
    intro x hx hc
    have hxs := (hs x).mpr ⟨⟨by linarith [hx.1], hx.2⟩, hc⟩
    linarith [hmax x hxs, hx.1]
  obtain ⟨hfinup, heulerup⟩ := regularBandEuler I K e hf hεb.le hcup hregup hinterior hfinmid
  refine ⟨hfinup, ?_⟩
  rw [heulerup, heulermid, heulerlo, add_assoc]
  congr 1
  exact Finset.sum_erase_add _ _ hp

theorem finiteHomologyType_and_eulerChar_of_finite_morse_band (K : Type) [Field K]
    (e : E ≃L[ℝ] MorseModel (m + 1)) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hinterior : sublevel f b ⊆ I.interior M)
    (ha : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (hb : ∀ x, f x = b → ¬ IsCriticalPointAt I f x)
    (hfinite : {x | f x ∈ Icc a b ∧ IsCriticalPointAt I f x}.Finite)
    (hnd : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x →
      IsNondegenerateCriticalPointAt I f x)
    (hinj : InjOn f {x | f x ∈ Icc a b ∧ IsCriticalPointAt I f x})
    (hfin : Poincare.Homology.finiteHomologyType K (TopCat.of (SublevelSpace f a))) :
    Poincare.Homology.finiteHomologyType K (TopCat.of (SublevelSpace f b)) ∧
      Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f b)) =
        Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f a)) +
          ∑ p ∈ hfinite.toFinset, (-1 : ℤ) ^ sigNeg (chartHessianAt
            (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
  classical
  exact finiteBandEulerAux I K e hf hfinite.toFinset hab hcompact hinterior
    (fun x => hfinite.mem_toFinset) ha hb
    (fun x hx => hnd x (hfinite.mem_toFinset.mp hx).1 (hfinite.mem_toFinset.mp hx).2)
    (by simpa only [hfinite.coe_toFinset] using hinj) hfin

theorem finiteHomologyType_and_eulerChar_of_finite_morse_sublevel (K : Type) [Field K]
    (e : E ≃L[ℝ] MorseModel (m + 1)) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (b : ℝ)
    (hcompact : IsCompact (sublevel f b))
    (hinterior : sublevel f b ⊆ I.interior M)
    (hfinite : {x | IsCriticalPointAt I f x}.Finite)
    (hnd : ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    (hinj : InjOn f {x | IsCriticalPointAt I f x})
    (hbelow : ∀ x, IsCriticalPointAt I f x → f x < b) :
    Poincare.Homology.finiteHomologyType K (TopCat.of (SublevelSpace f b)) ∧
      Poincare.Homology.eulerChar K (TopCat.of (SublevelSpace f b)) =
        ∑ p ∈ hfinite.toFinset, (-1 : ℤ) ^ sigNeg (chartHessianAt
          (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
  classical
  obtain ⟨A, hA⟩ := (hcompact.image hf.continuous).bddBelow
  let a := min (A - 1) (b - 1)
  have hab : a < b := lt_of_le_of_lt (min_le_right _ _) (sub_one_lt b)
  have halower : ∀ x, a < f x := by
    intro x
    by_cases hx : f x ≤ b
    · have hxA := hA (mem_image_of_mem f hx)
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · exact hab.trans (lt_of_not_ge hx)
  let _ : IsEmpty (SublevelSpace f a) := ⟨fun x => not_le_of_gt (halower x) x.property⟩
  have hcritset : {x | f x ∈ Icc a b ∧ IsCriticalPointAt I f x} =
      {x | IsCriticalPointAt I f x} := by
    ext x
    exact ⟨And.right, fun hc => ⟨⟨(halower x).le, (hbelow x hc).le⟩, hc⟩⟩
  have hband : IsCompact (f ⁻¹' Icc a b) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous) (fun _ hx => hx.2)
  have hbandfinite : {x | f x ∈ Icc a b ∧ IsCriticalPointAt I f x}.Finite :=
    hcritset.symm ▸ hfinite
  obtain ⟨hfin, hχ⟩ := finiteHomologyType_and_eulerChar_of_finite_morse_band I K e hf hab.le
    hband hinterior (fun x hx => False.elim ((ne_of_gt (halower x)) hx))
    (fun x hx hc => (ne_of_lt (hbelow x hc)) hx) hbandfinite
    (fun x _ hx => hnd x hx) (fun _ hx _ hy he => hinj hx.2 hy.2 he)
    (Poincare.Homology.finiteHomologyType_of_subsingleton K)
  refine ⟨hfin, ?_⟩
  rw [Poincare.Homology.eulerChar_of_isEmpty K (X := TopCat.of (SublevelSpace f a)), zero_add] at hχ
  convert hχ using 1
  congr 1
  exact Set.Finite.toFinset_inj.mpr hcritset.symm

end Poincare.Morse
