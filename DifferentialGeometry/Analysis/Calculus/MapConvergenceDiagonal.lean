import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp

set_option autoImplicit false

namespace DifferentialGeometry
namespace HCGCompactness

open scoped ContDiff Topology

variable {E' P Q : Type*}
  [NormedAddCommGroup E'] [NormedSpace Real E']
  [NormedAddCommGroup P] [NormedSpace Real P]
  [NormedAddCommGroup Q] [NormedSpace Real Q]

theorem averagedCInf_id {U : Set E'} {V : Set (P × Q)}
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

theorem compDiagConvId {F' : Type*}
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

theorem targetsDiagConv {ι : Type*} [Fintype ι] {F' : Type*}
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
    compDiagConvId hU (hV i) (hB i) (hA i) (hBc i) (hBinfc i) (hAc i) (hAinfc i)
      (hmap i) (hmapk i) (hid i) kn ln hkn hln
  have hslotc : ∀ i n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun y => A i (ln n) (B i (kn n) y)) U := fun i n =>
    (hAc i (ln n)).comp (hBc i (kn n)) (hmapk i (kn n))
  exact mapCInfConv_pi hU hslot hslotc (fun _ => contDiffOn_id)

theorem averagedCInf_id₂ {U : Set E'} {V : Set (P × Q)}
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
  classical
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk hbad using hbad
  choose l hl hbad using hbad
  choose r hr hbad using hbad
  choose x hx hbad using hbad
  have hk_tendsto : Filter.Tendsto k Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hk Filter.tendsto_id
  have hl_tendsto : Filter.Tendsto l Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hl Filter.tendsto_id
  have hconv : MapCInfConvOnCompacts U
      (fun n y => Φ (u (k n) (l n) y, v (k n) (l n) y)) (fun y => y) :=
    averagedCInf_id hU hV (hu k l hk_tendsto hl_tendsto)
      (hv k l hk_tendsto hl_tendsto)
      (fun n => huc (k n) (l n)) huinfc (fun n => hvc (k n) (l n)) hvinfc hΦc
      (fun n => hmapk (k n) (l n)) hmap hdiag
  obtain ⟨N, hN⟩ := hconv K hK hKU p ε hε
  exact not_lt_of_ge (hN N le_rfl (r N) (hr N) (x N) (hx N)) (hbad N)

theorem averagedTargets₂ {ι : Type*} [Fintype ι] {F' : Type*}
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
  averagedCInf_id₂ (v := fun k l y (i : ι) => A i l (B i k y))
    (vinf := fun y (_ : ι) => y) hU hW hw
    (fun kn ln hkn hln => targetsDiagConv hU hV hB hA hBc hBinfc hAc hAinfc
      hmapBV hmapBVk hid kn ln hkn hln)
    hwc hwinfc
    (fun k l => contDiffOn_pi.mpr fun i => (hAc i l).comp (hBc i k) (hmapBVk i k))
    (contDiffOn_pi.mpr fun _ => contDiffOn_id)
    hΦc hmapk hmap hdiag hK hKU p

end HCGCompactness
end DifferentialGeometry
