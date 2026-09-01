import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp

set_option autoImplicit false

namespace DifferentialGeometry
namespace HCGCompactness

open scoped ContDiff Topology

variable {E' P Q : Type*}
  [NormedAddCommGroup E'] [NormedSpace Real E']
  [NormedAddCommGroup P] [NormedSpace Real P]
  [NormedAddCommGroup Q] [NormedSpace Real Q]

omit [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup Q] [NormedSpace Real Q] in
theorem mapCInf_comp_pair_dist_tail
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} {V : Set F} (hV : IsOpen V)
    (B : ℕ → E → F) (Binf : E → F) (A : ℕ → F → E) (Ainf : F → E)
    (hB : MapCInfConvOnCompacts U B Binf) (hA : MapCInfConvOnCompacts V A Ainf)
    (hBcont : ContinuousOn Binf U) (hAcont : ContinuousOn Ainf V)
    (hid : ∀ x ∈ U, Binf x ∈ V → Ainf (Binf x) = x)
    {K : Set E} (hKcpt : IsCompact K) (hKU : K ⊆ U)
    (hKV : ∀ x ∈ K, Binf x ∈ V) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ K,
      dist (A l (B k x)) x < ε := by
  intro ε hε
  have hBKcpt : IsCompact (Binf '' K) :=
    hKcpt.image_of_continuousOn (hBcont.mono hKU)
  have hBKV : Binf '' K ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKV x hx
  obtain ⟨δ₀, hδ₀pos, hδ₀V⟩ := hBKcpt.exists_cthickening_subset_open hV hBKV
  set K' : Set F := Metric.cthickening δ₀ (Binf '' K) with hK'def
  have hK'cpt : IsCompact K' := hBKcpt.cthickening
  have hK'V : K' ⊆ V := hδ₀V
  have huc : UniformContinuousOn Ainf K' :=
    hK'cpt.uniformContinuousOn_of_continuous (hAcont.mono hK'V)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc (ε / 2) (by positivity)
  have hA₀ : TendstoUniformlyOn A Ainf Filter.atTop K' :=
    tendstoUniformlyOn_of_cPConv (hA K' hK'cpt hK'V 0)
  rw [Metric.tendstoUniformlyOn_iff] at hA₀
  obtain ⟨NA, hNA⟩ := Filter.eventually_atTop.mp (hA₀ (ε / 2) (by positivity))
  have hB₀ : TendstoUniformlyOn B Binf Filter.atTop K :=
    tendstoUniformlyOn_of_cPConv (hB K hKcpt hKU 0)
  rw [Metric.tendstoUniformlyOn_iff] at hB₀
  obtain ⟨NB, hNB⟩ := Filter.eventually_atTop.mp (hB₀ (min δ δ₀) (by positivity))
  refine ⟨max NA NB, fun k hk l hl x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hBxV : Binf x ∈ V := hKV x hx
  have hBkx : dist (Binf x) (B k x) < min δ δ₀ :=
    hNB k (le_trans (le_max_right _ _) hk) x hx
  have hBkxK' : B k x ∈ K' :=
    Metric.mem_cthickening_of_dist_le (B k x) (Binf x) δ₀ (Binf '' K)
      ⟨x, hx, rfl⟩
      (by rw [dist_comm]; exact le_of_lt (lt_of_lt_of_le hBkx (min_le_right _ _)))
  have hBinfxK' : Binf x ∈ K' :=
    Metric.self_subset_cthickening _ ⟨x, hx, rfl⟩
  calc
    dist (A l (B k x)) x = dist (A l (B k x)) (Ainf (Binf x)) := by
      rw [hid x hxU hBxV]
    _ ≤ dist (A l (B k x)) (Ainf (B k x)) +
        dist (Ainf (B k x)) (Ainf (Binf x)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      · rw [dist_comm]
        exact hNA l (le_trans (le_max_left _ _) hl) (B k x) hBkxK'
      · refine hδ (B k x) hBkxK' (Binf x) hBinfxK' ?_
        rw [dist_comm]
        exact lt_of_lt_of_le hBkx (min_le_left _ _)
    _ = ε := by ring

theorem mapCInfConvOnCompacts_comp_prodMk_id {U : Set E'} {V : Set (P × Q)}
    (hU : IsOpen U) (hV : IsOpen V) [ProperSpace (P × Q)]
    {u : Nat → E' → P} {uinf : E' → P}
    {v : Nat → E' → Q} {vinf : E' → Q} {Φ : P × Q → E'}
    (hu : MapCInfConvOnCompacts U u uinf)
    (hv : MapCInfConvOnCompacts U v vinf)
    (huc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn Real (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U)
    (hΦc : ContDiffOn Real (∞ : WithTop ℕ∞) Φ V)
    (hmapk : ∀ k, Set.MapsTo (fun y => (u k y, v k y)) U V)
    (hmap : Set.MapsTo (fun y => (uinf y, vinf y)) U V)
    (hdiag : ∀ y ∈ U, Φ (uinf y, vinf y) = y) :
    MapCInfConvOnCompacts U (fun k y => Φ (u k y, v k y)) (fun y => y) := by
  have hpair := mapCInfConv_prodMk hU hu hv huc huinfc hvc hvinfc
  have hpairc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun y => (u k y, v k y)) U :=
    fun k => (huc k).prodMk (hvc k)
  have hpairinfc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun y => (uinf y, vinf y)) U :=
    huinfc.prodMk hvinfc
  have hcomp := MapCInfConvOnCompacts.comp hU hV hpair
    (mapCInfConv_const (U := V) Φ) hpairc hpairinfc
    (fun _ => hΦc) hΦc hmap hmapk
  exact hcomp.congr hU (fun _ => Set.eqOn_refl _ _) (fun y hy => (hdiag y hy).symm)

theorem mapCInfConvOnCompacts_comp_tendsto_atTop_id {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace Real F'] [ProperSpace F']
    {U : Set E'} {V : Set F'} (hU : IsOpen U) (hV : IsOpen V)
    {B : Nat → E' → F'} {Binf : E' → F'}
    {A : Nat → F' → E'} {Ainf : F' → E'}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hA : MapCInfConvOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hAc : ∀ l, ContDiffOn Real (∞ : WithTop ℕ∞) (A l) V)
    (hAinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V)
    (hid : ∀ y ∈ U, Ainf (Binf y) = y)
    (kn ln : Nat → Nat) (hkn : Filter.Tendsto kn Filter.atTop Filter.atTop)
    (hln : Filter.Tendsto ln Filter.atTop Filter.atTop) :
    MapCInfConvOnCompacts U (fun n y => A (ln n) (B (kn n) y)) (fun y => y) := by
  have hB' : MapCInfConvOnCompacts U (fun n => B (kn n)) Binf :=
    hB.comp_tendsto_atTop hkn
  have hA' : MapCInfConvOnCompacts V (fun n => A (ln n)) Ainf :=
    hA.comp_tendsto_atTop hln
  have hcomp := MapCInfConvOnCompacts.comp hU hV hB' hA'
    (fun n => hBc (kn n)) hBinfc (fun n => hAc (ln n)) hAinfc
    hmap (fun n => hmapk (kn n))
  exact hcomp.congr hU (fun _ => Set.eqOn_refl _ _) (fun y hy => (hid y hy).symm)

omit [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup Q] [NormedSpace Real Q] in
theorem mapCInf_comp_pair_tail
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (B : ℕ → E → F) (Binf : E → F) (A : ℕ → F → E) (Ainf : F → E)
    (hB : MapCInfConvOnCompacts U B Binf) (hA : MapCInfConvOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (⊤ : ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (⊤ : ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V)
    (hid : ∀ x ∈ U, Ainf (Binf x) = x)
    {K : Set E} (hKcpt : IsCompact K) (hKU : K ⊆ U) :
    ∀ p : ℕ, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ r ≤ p, ∀ x ∈ K,
      mapDerivNorm r (fun y => A l (B k y)) (fun y : E => y) x ≤ ε := by
  intro p
  apply mapCInf_pair_tail
    (U := U) (Φ := fun k l y => A l (B k y)) (Φinf := fun y : E => y)
      ?_ hKcpt hKU p
  intro kn ln hkn hln
  exact mapCInfConvOnCompacts_comp_tendsto_atTop_id
    (E' := E) hU hV hB hA hBc hBinfc hAc hAinfc hmap hmapk hid
    kn ln hkn hln

theorem mapCInfConvOnCompacts_pi_comp_tendsto_atTop_id
    {ι : Type*} [Fintype ι] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace Real F'] [ProperSpace F']
    {U : Set E'} {V : ι → Set F'} (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    {B : ι → Nat → E' → F'} {Binf : ι → E' → F'}
    {A : ι → Nat → F' → E'} {Ainf : ι → F' → E'}
    (hB : ∀ i, MapCInfConvOnCompacts U (B i) (Binf i))
    (hA : ∀ i, MapCInfConvOnCompacts (V i) (A i) (Ainf i))
    (hBc : ∀ i k, ContDiffOn Real (∞ : WithTop ℕ∞) (B i k) U)
    (hBinfc : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (Binf i) U)
    (hAc : ∀ i l, ContDiffOn Real (∞ : WithTop ℕ∞) (A i l) (V i))
    (hAinfc : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (Ainf i) (V i))
    (hmap : ∀ i, Set.MapsTo (Binf i) U (V i))
    (hmapk : ∀ i k, Set.MapsTo (B i k) U (V i))
    (hid : ∀ i, ∀ y ∈ U, Ainf i (Binf i y) = y)
    (kn ln : Nat → Nat) (hkn : Filter.Tendsto kn Filter.atTop Filter.atTop)
    (hln : Filter.Tendsto ln Filter.atTop Filter.atTop) :
    MapCInfConvOnCompacts U (fun n y (i : ι) => A i (ln n) (B i (kn n) y))
      (fun y (_ : ι) => y) := by
  have hslot : ∀ i, MapCInfConvOnCompacts U
      (fun n y => A i (ln n) (B i (kn n) y)) (fun y => y) := fun i =>
    mapCInfConvOnCompacts_comp_tendsto_atTop_id
      hU (hV i) (hB i) (hA i) (hBc i) (hBinfc i) (hAc i) (hAinfc i)
      (hmap i) (hmapk i) (hid i) kn ln hkn hln
  have hslotc : ∀ i n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun y => A i (ln n) (B i (kn n) y)) U := fun i n =>
    (hAc i (ln n)).comp (hBc i (kn n)) (hmapk i (kn n))
  exact mapCInfConv_pi hU hslot hslotc (fun _ => contDiffOn_id)

theorem mapCInf_comp_prodMk_pair_tail {U : Set E'} {V : Set (P × Q)}
    (hU : IsOpen U) (hV : IsOpen V) [ProperSpace (P × Q)]
    {u : Nat → Nat → E' → P} {uinf : E' → P}
    {v : Nat → Nat → E' → Q} {vinf : E' → Q} {Φ : P × Q → E'}
    (hu : ∀ kn ln : Nat → Nat, Filter.Tendsto kn Filter.atTop Filter.atTop →
      Filter.Tendsto ln Filter.atTop Filter.atTop →
      MapCInfConvOnCompacts U (fun n => u (kn n) (ln n)) uinf)
    (hv : ∀ kn ln : Nat → Nat, Filter.Tendsto kn Filter.atTop Filter.atTop →
      Filter.Tendsto ln Filter.atTop Filter.atTop →
      MapCInfConvOnCompacts U (fun n => v (kn n) (ln n)) vinf)
    (huc : ∀ k l, ContDiffOn Real (∞ : WithTop ℕ∞) (u k l) U)
    (huinfc : ContDiffOn Real (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k l, ContDiffOn Real (∞ : WithTop ℕ∞) (v k l) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U)
    (hΦc : ContDiffOn Real (∞ : WithTop ℕ∞) Φ V)
    (hmapk : ∀ k l, Set.MapsTo (fun y => (u k l y, v k l y)) U V)
    (hmap : Set.MapsTo (fun y => (uinf y, vinf y)) U V)
    (hdiag : ∀ y ∈ U, Φ (uinf y, vinf y) = y)
    {K : Set E'} (hK : IsCompact K) (hKU : K ⊆ U) (p : Nat) :
    ∀ ε > 0, ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ r ≤ p, ∀ x ∈ K,
      mapDerivNorm r (fun y => Φ (u k l y, v k l y)) (fun y => y) x ≤ ε := by
  apply mapCInf_pair_tail
    (U := U) (Φ := fun k l y => Φ (u k l y, v k l y))
      (Φinf := fun y => y) ?_ hK hKU p
  intro kn ln hkn hln
  exact mapCInfConvOnCompacts_comp_prodMk_id hU hV
    (hu kn ln hkn hln) (hv kn ln hkn hln)
    (fun n => huc (kn n) (ln n)) huinfc
    (fun n => hvc (kn n) (ln n)) hvinfc hΦc
    (fun n => hmapk (kn n) (ln n)) hmap hdiag

theorem mapCInf_comp_prodMk_pi_pair_tail
    {ι : Type*} [Fintype ι] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace Real F'] [ProperSpace F']
    {U : Set E'} {V : ι → Set F'} {W : Set (P × (ι → E'))}
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hW : IsOpen W)
    [ProperSpace (P × (ι → E'))]
    {w : Nat → Nat → E' → P} {winf : E' → P}
    {B : ι → Nat → E' → F'} {Binf : ι → E' → F'}
    {A : ι → Nat → F' → E'} {Ainf : ι → F' → E'}
    {Φ : P × (ι → E') → E'}
    (hw : ∀ kn ln : Nat → Nat, Filter.Tendsto kn Filter.atTop Filter.atTop →
      Filter.Tendsto ln Filter.atTop Filter.atTop →
      MapCInfConvOnCompacts U (fun n => w (kn n) (ln n)) winf)
    (hwc : ∀ k l, ContDiffOn Real (∞ : WithTop ℕ∞) (w k l) U)
    (hwinfc : ContDiffOn Real (∞ : WithTop ℕ∞) winf U)
    (hB : ∀ i, MapCInfConvOnCompacts U (B i) (Binf i))
    (hA : ∀ i, MapCInfConvOnCompacts (V i) (A i) (Ainf i))
    (hBc : ∀ i k, ContDiffOn Real (∞ : WithTop ℕ∞) (B i k) U)
    (hBinfc : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (Binf i) U)
    (hAc : ∀ i l, ContDiffOn Real (∞ : WithTop ℕ∞) (A i l) (V i))
    (hAinfc : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (Ainf i) (V i))
    (hmapBV : ∀ i, Set.MapsTo (Binf i) U (V i))
    (hmapBVk : ∀ i k, Set.MapsTo (B i k) U (V i))
    (hid : ∀ i, ∀ y ∈ U, Ainf i (Binf i y) = y)
    (hΦc : ContDiffOn Real (∞ : WithTop ℕ∞) Φ W)
    (hmapk : ∀ k l, Set.MapsTo
      (fun y => (w k l y, fun i : ι => A i l (B i k y))) U W)
    (hmap : Set.MapsTo (fun y => (winf y, fun _ : ι => y)) U W)
    (hdiag : ∀ y ∈ U, Φ (winf y, fun _ : ι => y) = y)
    {K : Set E'} (hK : IsCompact K) (hKU : K ⊆ U) (p : Nat) :
    ∀ ε > 0, ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ r ≤ p, ∀ x ∈ K,
      mapDerivNorm r (fun y => Φ (w k l y, fun i : ι => A i l (B i k y)))
        (fun y => y) x ≤ ε :=
  mapCInf_comp_prodMk_pair_tail (v := fun k l y (i : ι) => A i l (B i k y))
    (vinf := fun y (_ : ι) => y) hU hW hw
    (fun kn ln hkn hln => mapCInfConvOnCompacts_pi_comp_tendsto_atTop_id
      hU hV hB hA hBc hBinfc hAc hAinfc
      hmapBV hmapBVk hid kn ln hkn hln)
    hwc hwinfc
    (fun k l => contDiffOn_pi.mpr fun i => (hAc i l).comp (hBc i k) (hmapBVk i k))
    (contDiffOn_pi.mpr fun _ => contDiffOn_id)
    hΦc hmapk hmap hdiag hK hKU p

end HCGCompactness
end DifferentialGeometry
