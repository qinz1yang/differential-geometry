import DifferentialGeometry.Topology.Morse.SurfaceEulerCharacteristic
import DifferentialGeometry.Topology.Morse.SublevelComponents
import DifferentialGeometry.Topology.Morse.ExtremumComponents

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

local notation "S₂" => sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem subsingleton_index_zero_or_index_two_of_one_saddle
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hone : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1) :
    {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 0}.Subsingleton ∨
      {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
        (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 2}.Subsingleton := by
  let C := {p | IsCriticalPointAt (𝓡 2) f p}
  let T := fun k => {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
    (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = k}
  have hfin : C.Finite := DifferentialGeometry.Morse.finite_criticalPoints_of_isCompact hf isCompact_univ
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => mem_univ _) hnd
  have hsub (k : ℕ) : T k ⊆ C := fun _ hp => hp.1
  have hTfin (k : ℕ) : (T k).Finite := hfin.subset (hsub k)
  have hCcard : C.ncard = 4 := by
    change {p | IsCriticalPointAt (𝓡 2) f p}.ncard = 4
    rw [ncard_criticalPoints_sphere_two hf hnd hinj, hone]
  have hdisj : Disjoint (T 0) (T 2) := disjoint_left.mpr (fun _ hp hq => by
    have h := hp.2.symm.trans hq.2
    norm_num at h)
  have hsum : (T 0).ncard + (T 2).ncard ≤ 3 := by
    rw [← ncard_union_eq hdisj (hTfin 0) (hTfin 2)]
    have hsubset : T 0 ∪ T 2 ⊆ C \ T 1 := by
      rintro p (hp | hp)
      · exact ⟨hp.1, fun h => by have hp2 := hp.2; have h2 := h.2; omega⟩
      · exact ⟨hp.1, fun h => by have hp2 := hp.2; have h2 := h.2; omega⟩
    have hle := ncard_le_ncard hsubset hfin.sdiff
    rw [ncard_sdiff (hsub 1) (hTfin 1), hCcard, hone] at hle
    exact hle
  by_cases hzero : (T 0).Subsingleton
  · exact Or.inl hzero
  · right
    have hzeroCard : 1 < (T 0).ncard := lt_of_not_ge (fun h => hzero ((ncard_le_one (hTfin 0)).mp h))
    exact (ncard_le_one (hTfin 2)).mp (by omega)

theorem isPreconnected_sublevel_or_superlevel_of_one_saddle
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hone : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1) :
    (∀ a : ℝ, IsPreconnected {x | f x < a}) ∨
      (∀ a : ℝ, IsPreconnected {x | a < f x}) := by
  rcases subsingleton_index_zero_or_index_two_of_one_saddle hf hnd hinj hone with hzero | htwo
  · left
    intro a
    apply isPreconnected_lt_of_subsingleton_index_zero hf
      ((isClosed_le hf.continuous continuous_const).isCompact) (fun p _ => hnd p)
    intro p hp q hq
    exact hzero hp.2 hq.2
  · right
    intro a
    apply isPreconnected_gt_of_subsingleton_index_finrank hf
      ((isClosed_le continuous_const hf.continuous).isCompact) (fun p _ => hnd p)
    intro p hp q hq
    exact htwo ⟨hp.2.1, by simpa using hp.2.2⟩ ⟨hq.2.1, by simpa using hq.2.2⟩

theorem exists_min_saddle_two_max_of_one_saddle
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hone : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | f x < a}) :
    ∃ m s p q : S₂,
      f m < f s ∧ f m < f p ∧ f p < f q ∧ f s < f q ∧
      IsMinOn f univ m ∧ IsMaxOn f univ q ∧ IsLocalMax f p ∧
      {x | IsCriticalPointAt (𝓡 2) f x} = {m, s, p, q} ∧
      sigNeg (chartHessianAt (fun y => f ((extChartAt (𝓡 2) m).symm y))
        (extChartAt (𝓡 2) m m)) = 0 ∧
      sigNeg (chartHessianAt (fun y => f ((extChartAt (𝓡 2) s).symm y))
        (extChartAt (𝓡 2) s s)) = 1 ∧
      sigNeg (chartHessianAt (fun y => f ((extChartAt (𝓡 2) p).symm y))
        (extChartAt (𝓡 2) p p)) = 2 ∧
      sigNeg (chartHessianAt (fun y => f ((extChartAt (𝓡 2) q).symm y))
        (extChartAt (𝓡 2) q q)) = 2 := by
  classical
  let C := {x | IsCriticalPointAt (𝓡 2) f x}
  let index (x : S₂) := sigNeg (chartHessianAt
    (fun y => f ((extChartAt (𝓡 2) x).symm y)) (extChartAt (𝓡 2) x x))
  have hCcard : C.ncard = 4 := by
    change {x | IsCriticalPointAt (𝓡 2) f x}.ncard = 4
    rw [ncard_criticalPoints_sphere_two hf hnd hinj, hone]
  obtain ⟨s, hsset⟩ := ncard_eq_one.mp hone
  let : Nonempty S₂ := ⟨s⟩
  obtain ⟨m, q, hbounds, _, _, hm, hq⟩ :=
    exists_unique_min_max_of_injOn_criticalPoints hf.continuous hinj
  have hmmin : IsLocalMin f m := Filter.Eventually.of_forall (fun x => (hbounds x).1)
  have hqmax : IsLocalMax f q := Filter.Eventually.of_forall (fun x => (hbounds x).2)
  have hmindex : index m = 0 := minimum_morse_index_eq_zero hf (hnd m hm) hmmin
  have hqindex : index q = 2 := by
    simpa [index] using maximum_morse_index_eq_finrank hf (hnd q hq) hqmax
  have hs : s ∈ {x | IsCriticalPointAt (𝓡 2) f x ∧ index x = 1} := by
    rw [hsset]
    exact mem_singleton s
  have hsm : s ≠ m := by intro h; have hh := h ▸ hs.2; omega
  have hsq : s ≠ q := by intro h; have hh := h ▸ hs.2; omega
  have hmq : m ≠ q := by intro h; have hh := h ▸ hmindex; omega
  have hsub : ({m, s, q} : Set S₂) ⊆ C := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact hm
    · exact hs.1
    · exact hq
  have hthree : ({m, s, q} : Set S₂).ncard = 3 := by
    simp [ncard_insert_of_notMem, hsm.symm, hsq, hmq]
  have hrest : (C \ {m, s, q}).ncard = 1 := by
    rw [ncard_sdiff hsub (toFinite _), hCcard, hthree]
  obtain ⟨p, hpset⟩ := ncard_eq_one.mp hrest
  have hp : p ∈ C \ {m, s, q} := by rw [hpset]; exact mem_singleton p
  have hpm : p ≠ m := fun h => hp.2 (by simp [h])
  have hps : p ≠ s := fun h => hp.2 (by simp [h])
  have hpq : p ≠ q := fun h => hp.2 (by simp [h])
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  have hpindex : index p = 2 := by
    have hbound : index p ≤ 2 := by
      have h := sigPos_le_finrank (-chartHessianAt
        (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p))
      change index p ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) at h
      rwa [hdim] at h
    have hnzero : index p ≠ 0 := by
      intro hz
      have hmin := (isLocalMin_iff_morse_index_eq_zero hf (hnd p hp.1)).mpr hz
      have hglobal := isMinOn_univ_of_isPreconnected_lt hf (hnd p hp.1) hmin hconn
      exact hpm (eq_of_isMin_of_injOn_criticalPoints hinj
        (fun x => hglobal (mem_univ x)) (fun x => (hbounds x).1))
    have hnone : index p ≠ 1 := by
      intro hone'
      have hmem : p ∈ {x | IsCriticalPointAt (𝓡 2) f x ∧ index x = 1} := ⟨hp.1, hone'⟩
      rw [hsset] at hmem
      exact hps hmem
    omega
  have hpmax : IsLocalMax f p :=
    (isLocalMax_iff_morse_index_eq_finrank hf (hnd p hp.1)).mpr (by rw [hdim]; exact hpindex)
  have hmp : f m < f p := lt_of_le_of_ne (hbounds p).1
    (fun heq => hpm (hinj hm hp.1 heq).symm)
  have hms : f m < f s := lt_of_le_of_ne (hbounds s).1
    (fun heq => hsm (hinj hm hs.1 heq).symm)
  have hpqlt : f p < f q := lt_of_le_of_ne (hbounds p).2
    (fun heq => hpq (hinj hp.1 hq heq))
  have hsqlt : f s < f q := lt_of_le_of_ne (hbounds s).2
    (fun heq => hsq (hinj hs.1 hq heq))
  have hCeq : C = {m, s, p, q} := by
    ext x
    constructor
    · intro hx
      by_cases hxm : x = m
      · simp [hxm]
      by_cases hxs : x = s
      · simp [hxs]
      by_cases hxq : x = q
      · simp [hxq]
      have hxrest : x ∈ C \ {m, s, q} := ⟨hx, by simp [hxm, hxs, hxq]⟩
      rw [hpset] at hxrest
      simp [mem_singleton_iff.mp hxrest]
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hm
      · exact hs.1
      · exact hp.1
      · exact hq
  exact ⟨m, s, p, q, hms, hmp, hpqlt, hsqlt,
    fun x _ => (hbounds x).1, fun x _ => (hbounds x).2,
    hpmax, hCeq, hmindex, hs.2, hpindex, hqindex⟩

theorem not_isLocalMax_of_lt_of_one_saddle
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hone : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    {p : S₂} (hp : IsLocalMax f p) (hpglobal : ¬ IsMaxOn f univ p)
    {x : S₂} (hx : f x < f p) : ¬ IsLocalMax f x := by
  have hpc := isCriticalPointAt_of_isLocalMax (I := 𝓡 2) hp BoundarylessManifold.isInteriorPoint
  have hconn : ∀ a : ℝ, IsPreconnected {x | f x < a} :=
    (isPreconnected_sublevel_or_superlevel_of_one_saddle hf hnd hinj hone).resolve_right
      (fun hgt => hpglobal (isMaxOn_univ_of_isPreconnected_gt hf (hnd p hpc) hp hgt))
  obtain ⟨m, s, p₀, q, _, _, hpq, _, _, hq, _, hC, hmindex, hsindex, _, _⟩ :=
    exists_min_saddle_two_max_of_one_saddle hf hnd hinj hone hconn
  have hmax (y : S₂) (hy : IsLocalMax f y) : y = p₀ ∨ y = q := by
    have hyc := isCriticalPointAt_of_isLocalMax (I := 𝓡 2) hy BoundarylessManifold.isInteriorPoint
    have hyindex : sigNeg (chartHessianAt
        (fun z => f ((extChartAt (𝓡 2) y).symm z)) (extChartAt (𝓡 2) y y)) = 2 := by
      simpa using maximum_morse_index_eq_finrank hf (hnd y hyc) hy
    have hymem := hC.subset hyc
    rcases hymem with rfl | rfl | rfl | rfl
    · omega
    · omega
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hpp₀ : p = p₀ := (hmax p hp).resolve_right (fun hpq => hpglobal (hpq.symm ▸ hq))
  intro hxmax
  rcases hmax x hxmax with rfl | rfl
  · rw [hpp₀] at hx
    exact lt_irrefl _ hx
  · rw [hpp₀] at hx
    exact (not_lt_of_ge hpq.le) hx

end DifferentialGeometry.Topology.Morse
