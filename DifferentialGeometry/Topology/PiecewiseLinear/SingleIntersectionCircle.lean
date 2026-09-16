import DifferentialGeometry.Topology.PiecewiseLinear.CircleMap
import DifferentialGeometry.Topology.PiecewiseLinear.OpenPLPath
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem exists_piecewiseAffineOn_circle_single_intersection
    {S : Set E} (hS : IsPLSphere 1 S) {p q : E} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    {T : Set F} (hT : IsClosed T) (hconn : IsPreconnected Tᶜ)
    {x v : F} {r : ℝ} (hr : 0 < r)
    (hline : ∀ t ∈ Icc (-r) r, x + t • v ∈ T ↔ t = 0) :
    ∃ (A B : Set E) (γ δ : ℝ → E) (H : E → F),
      IsPLHomeomorphOn γ (Icc 0 1) A ∧ IsPLHomeomorphOn δ (Icc 0 1) B ∧
        A ∪ B = S ∧ A ∩ B = {γ 0, γ 1} ∧ IsPiecewiseAffineOn H univ ∧
          (∀ t ∈ Icc 0 1, H (γ t) = x + (r * t - r / 2) • v) ∧
            MapsTo H B Tᶜ ∧ S ∩ H ⁻¹' T = {γ (1 / 2)} := by
  let a := x + (-r / 2) • v
  let b := x + (r / 2) • v
  have ha : a ∈ Tᶜ := by
    intro h
    have := (hline (-r / 2) ⟨by linarith, by linarith⟩).mp h
    linarith
  have hb : b ∈ Tᶜ := by
    intro h
    have := (hline (r / 2) ⟨by linarith, by linarith⟩).mp h
    linarith
  obtain ⟨g, hg, hg0, hg1, hgT⟩ := exists_piecewiseAffine_path_of_isOpen
    hT.isOpen_compl hconn ha hb
  let f := AffineMap.lineMap (k := ℝ) a b
  have hf : IsPiecewiseAffineOn f (Icc 0 1) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope f isHPolytope_Icc
  have hfval : ∀ t, f t = x + (r * t - r / 2) • v := by
    intro t
    change AffineMap.lineMap (k := ℝ) (x + (-r / 2) • v) (x + (r / 2) • v) t = _
    rw [AffineMap.lineMap_apply_module, smul_add, smul_add, smul_smul, smul_smul,
      add_add_add_comm, ← add_smul, sub_add_cancel, one_smul, ← add_smul]
    congr 2
    ring
  obtain ⟨A, B, γ, δ, H, hγ, hδ, hγ0, hγ1, _, _, hunion, hinter, hH, hHγ, hHδ⟩ :=
    exists_piecewiseAffineOn_circle_of_paths hS hp hq hpq hf hg
      (by simpa only [f, AffineMap.lineMap_apply_zero] using hg0.symm)
      (by simpa only [f, AffineMap.lineMap_apply_one] using hg1.symm)
  obtain ⟨G, _, hG, _, hfix, _, _⟩ :=
    hH.exists_lipschitz_extension hS.isPolyhedron isOpen_univ (subset_univ S)
  have hGA : ∀ t ∈ Icc 0 1, G (γ t) = x + (r * t - r / 2) • v := by
    intro t ht
    rw [hfix (hunion.subset (Or.inl (hγ.bijOn.mapsTo ht))), hHγ t ht, hfval]
  have hGB : MapsTo G B Tᶜ := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hδ.bijOn.surjOn hz
    rw [hfix (hunion.subset (Or.inr (hδ.bijOn.mapsTo ht))), hHδ t ht]
    exact hgT ht
  refine ⟨A, B, γ, δ, G, hγ, hδ, hunion, by simpa only [hγ0, hγ1] using hinter,
    hG, hGA, hGB, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzT⟩
    rcases hunion.symm.subset hz with hzA | hzB
    · obtain ⟨t, ht, rfl⟩ := hγ.bijOn.surjOn hzA
      rw [mem_preimage, hGA t ht] at hzT
      have htr : r * t - r / 2 ∈ Icc (-r) r := by
        constructor <;> nlinarith [ht.1, ht.2]
      have ht0 := (hline _ htr).mp hzT
      have htval : t = 1 / 2 := by nlinarith
      simp only [htval, mem_singleton_iff]
    · exact (hGB hzB hzT).elim
  · rintro rfl
    refine ⟨hunion.subset (Or.inl (hγ.bijOn.mapsTo (by norm_num))), ?_⟩
    rw [mem_preimage, hGA _ (by norm_num)]
    have heq : r * (1 / 2) - r / 2 = 0 := by ring
    rw [heq]
    exact (hline 0 ⟨by linarith, hr.le⟩).mpr rfl


open Classical in
omit [FiniteDimensional ℝ E] in
theorem exists_translate_circle_single_intersection_avoiding_finite
    {A B S Z : Set E} {γ : ℝ → E} {H : E → F}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hB : IsCompact B) (hunion : A ∪ B = S)
    (hH : Continuous H) {T : Set F} (hT : IsClosed T) (hHB : MapsTo H B Tᶜ)
    {x v : F} {r : ℝ} (hr : 0 < r)
    (hA : ∀ t ∈ Icc 0 1, H (γ t) = x + (r * t - r / 2) • v)
    (hline : ∀ t ∈ Icc (-r) r, x + t • v ∈ T ↔ t = 0) (hZ : Z.Finite) :
    ∃ a t : ℝ, t ∈ Ioo 0 1 ∧ γ t ∉ Z ∧ a = r / 2 - r * t ∧
      MapsTo (fun z => H z + a • v) B Tᶜ ∧
        S ∩ (fun z => H z + a • v) ⁻¹' T = {γ t} := by
  have hevent : ∀ᶠ t : ℝ in nhds (1 / 2), ∀ z ∈ B, H z + (r / 2 - r * t) • v ∈ Tᶜ := by
    apply hB.eventually_forall_of_forall_eventually
    intro z hz
    have hc : Continuous (fun w : ℝ × E => H w.2 + (r / 2 - r * w.1) • v) := by fun_prop
    have heq : r / 2 - r * (1 / 2) = 0 := by ring
    exact
      (hc.tendsto (1 / 2, z)).eventually (hT.isOpen_compl.mem_nhds (by
        simpa only [heq, zero_smul, add_zero] using hHB hz))
  have hnhds : {t : ℝ | (∀ z ∈ B, H z + (r / 2 - r * t) • v ∈ Tᶜ) ∧ t ∈ Ioo 0 1} ∈
      nhds (1 / 2) := Filter.inter_mem hevent (isOpen_Ioo.mem_nhds (by norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hbad : (Function.invFunOn γ (Icc 0 1) '' Z).Finite := hZ.image _
  obtain ⟨t, ht, havoid⟩ := ((Set.Ioo_infinite
    (show (1 / 2 : ℝ) - ε < 1 / 2 + ε by linarith)).sdiff hbad).nonempty
  have htball : t ∈ Metric.ball (1 / 2 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨hBt, ht01⟩ := hball htball
  have htcc : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht01
  have htZ : γ t ∉ Z := by
    intro h
    exact havoid ⟨γ t, h, hγ.bijOn.invOn_invFunOn.1 htcc⟩
  refine ⟨r / 2 - r * t, t, ht01, htZ, rfl, hBt, ?_⟩
  have hvalue : ∀ u ∈ Icc 0 1,
      H (γ u) + (r / 2 - r * t) • v = x + (r * (u - t)) • v := by
    intro u hu
    rw [hA u hu, add_assoc, ← add_smul]
    congr 2
    ring
  ext z
  constructor
  · rintro ⟨hz, hzT⟩
    rcases hunion.symm.subset hz with hzA | hzB
    · obtain ⟨u, hu, rfl⟩ := hγ.bijOn.surjOn hzA
      rw [mem_preimage, hvalue u hu] at hzT
      have hrut : r * (u - t) ∈ Icc (-r) r := by
        constructor <;> nlinarith [hu.1, hu.2, ht01.1, ht01.2]
      have heq := (hline _ hrut).mp hzT
      have hut : u = t := by nlinarith
      simp only [hut, mem_singleton_iff]
    · exact (hBt z hzB hzT).elim
  · rintro rfl
    refine ⟨hunion.subset (Or.inl (hγ.bijOn.mapsTo htcc)), ?_⟩
    rw [mem_preimage, hvalue t htcc, sub_self, mul_zero]
    exact (hline 0 ⟨by linarith, hr.le⟩).mpr rfl

end DifferentialGeometry.Topology.PiecewiseLinear
