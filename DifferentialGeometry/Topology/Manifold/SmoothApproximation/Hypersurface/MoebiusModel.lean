import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.OneSidedConsumers
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalLineBundle
import DifferentialGeometry.Topology.Manifold.AddCircle.Descent
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Ehresmann.SublevelTransport

/-!
# A concrete one-sided model: the core circle of the open Möbius band

The open Möbius band is lane CMS-T's normal line bundle with holonomy `-1`,
`NormalLineBundle (-1) = (ℝ × ℝ) / ((t + 1, h) ∼ (t, -h))`. Its core circle is one-sided. The
data of W-SUB's `exists_smooth_hypersurface_one_sided` are realised by

* the double cover `Sc = ℝ/ℤ` with the deck involution `σ [s] = [s + 1/2]` (`moebiusHalf`),
* the base `S = ℝ/ℤ` with the double cover `π [s] = [2 s]` (`moebiusDouble`),
* the tube `Φ ([s], t) = [2 s, t]` (`moebiusTube`), a local diffeomorphism, equivariant
  (`Φ (σ v, -t) = Φ (v, t)`) and injective modulo `(v, t) ↦ (σ v, -t)`.

`moebius_one_sided_data` collects these facts (the consumer
`exists_smooth_moebius_core_hypersurface` applies the one-sided smoothing theorem to them).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.Geometry.FiniteSoul
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Topology

/-- Lowering the class of a local diffeomorphism. -/
theorem isLocalDiffeomorphAt_of_le_top {E F H G M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace G] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {f : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J ∞ f x) (n : ℕ) :
    IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨Φ, hx, heq⟩ := hf
  have hn : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  exact ⟨{ toPartialEquiv := Φ.toPartialEquiv
           open_source := Φ.open_source
           open_target := Φ.open_target
           contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le hn
           contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le hn }, hx, heq⟩

theorem holonomyPow_neg_one_even (m : ℤ) : holonomyPow (-1) (2 * m) = 1 := by
  unfold holonomyPow
  rw [zpow_mul, show ((-1 : ℤˣ) ^ (2 : ℤ)) = 1 from by
    rw [zpow_two]
    exact Int.units_mul_self (-1), one_zpow]
  simp

theorem holonomyPow_neg_one_odd (m : ℤ) : holonomyPow (-1) (2 * m + 1) = -1 := by
  rw [holonomyPow_add, holonomyPow_neg_one_even, holonomyPow_one]
  simp

theorem addCircle_coe_add_int (s : ℝ) (m : ℤ) :
    (((s + m : ℝ)) : AddCircle (1 : ℝ)) = (s : AddCircle (1 : ℝ)) := by
  rw [QuotientAddGroup.eq]
  exact ⟨-m, by simp⟩

/-- The deck involution `[s] ↦ [s + 1/2]` of the double cover `ℝ/ℤ → ℝ/ℤ`. -/
def moebiusHalf (x : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) :=
  x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ))

/-- The double cover `[s] ↦ [2 s]` of the base circle. -/
def moebiusDouble (x : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) := x + x

theorem moebiusTube_periodic (t : ℝ) :
    Periodic (fun s : ℝ => NormalLineBundle.mk (-1) (2 * s) t) 1 := by
  intro s
  have h := NormalLineBundle.mk_add_int (-1) (2 * s) t 2
  rw [show (2 : ℤ) = 2 * 1 from rfl, holonomyPow_neg_one_even, one_mul] at h
  change NormalLineBundle.mk (-1) (2 * (s + 1)) t = NormalLineBundle.mk (-1) (2 * s) t
  rw [← h]
  congr 1
  push_cast
  ring

/-- The tube of the core circle of the Möbius band over its double cover:
`Φ ([s], t) = [2 s, t]`. -/
def moebiusTube (p : AddCircle (1 : ℝ) × ℝ) : NormalLineBundle (-1) :=
  (moebiusTube_periodic p.2).lift p.1

theorem moebiusTube_coe (s t : ℝ) :
    moebiusTube ((s : AddCircle (1 : ℝ)), t) = NormalLineBundle.mk (-1) (2 * s) t := rfl

theorem moebiusHalf_coe (s : ℝ) :
    moebiusHalf (s : AddCircle (1 : ℝ)) = ((s + 1 / 2 : ℝ) : AddCircle (1 : ℝ)) := rfl

theorem moebiusHalf_moebiusHalf (v : AddCircle (1 : ℝ)) : moebiusHalf (moebiusHalf v) = v := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective v
  change ((s + 1 / 2 + 1 / 2 : ℝ) : AddCircle (1 : ℝ)) = (s : AddCircle (1 : ℝ))
  have h := addCircle_coe_add_int s 1
  rw [show s + 1 / 2 + 1 / 2 = s + ((1 : ℤ) : ℝ) by push_cast; ring]
  exact h

theorem continuous_moebiusHalf : Continuous moebiusHalf := continuous_id.add continuous_const

theorem moebiusTube_equiv (v : AddCircle (1 : ℝ)) (t : ℝ) :
    moebiusTube (moebiusHalf v, -t) = moebiusTube (v, t) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective v
  change NormalLineBundle.mk (-1) (2 * (s + 1 / 2)) (-t) = NormalLineBundle.mk (-1) (2 * s) t
  have h := NormalLineBundle.mk_add_int (-1) (2 * s) t (2 * 0 + 1)
  rw [holonomyPow_neg_one_odd] at h
  rw [← h]
  congr 1
  · push_cast
    ring
  · ring

/-- Parity split of an integer translate on the circle `ℝ/ℤ` seen through doubling. -/
theorem coe_eq_or_moebiusHalf_of_two_mul {s s' : ℝ} {n : ℤ} (h : 2 * s' = 2 * s + n) :
    ((s' : AddCircle (1 : ℝ)) = s ∧ Even n) ∨
      ((s' : AddCircle (1 : ℝ)) = moebiusHalf (s : AddCircle (1 : ℝ)) ∧ Odd n) := by
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    refine ⟨?_, ⟨m, by ring⟩⟩
    rw [show s' = s + ((m : ℤ) : ℝ) by push_cast at h; linarith]
    exact addCircle_coe_add_int s m
  · right
    refine ⟨?_, ⟨m, rfl⟩⟩
    rw [moebiusHalf_coe, show s' = s + 1 / 2 + ((m : ℤ) : ℝ) by push_cast at h; linarith]
    exact addCircle_coe_add_int _ m

theorem moebiusTube_inj {p q : AddCircle (1 : ℝ) × ℝ} (h : moebiusTube p = moebiusTube q) :
    q = p ∨ q = (moebiusHalf p.1, -p.2) := by
  obtain ⟨⟨s, t⟩, rfl⟩ : ∃ a : ℝ × ℝ, ((a.1 : AddCircle (1 : ℝ)), a.2) = p :=
    ⟨((QuotientAddGroup.mk_surjective p.1).choose, p.2),
      Prod.ext (QuotientAddGroup.mk_surjective p.1).choose_spec rfl⟩
  obtain ⟨⟨s', t'⟩, rfl⟩ : ∃ a : ℝ × ℝ, ((a.1 : AddCircle (1 : ℝ)), a.2) = q :=
    ⟨((QuotientAddGroup.mk_surjective q.1).choose, q.2),
      Prod.ext (QuotientAddGroup.mk_surjective q.1).choose_spec rfl⟩
  change NormalLineBundle.mk (-1) (2 * s) t = NormalLineBundle.mk (-1) (2 * s') t' at h
  obtain ⟨n, hn1, hn2⟩ := NormalLineBundle.mk_eq_mk_iff.mp h
  rcases coe_eq_or_moebiusHalf_of_two_mul hn1 with ⟨hs, m, rfl⟩ | ⟨hs, m, rfl⟩
  · left
    rw [show m + m = 2 * m by ring, holonomyPow_neg_one_even, one_mul] at hn2
    exact Prod.ext hs hn2
  · right
    rw [holonomyPow_neg_one_odd, neg_one_mul] at hn2
    exact Prod.ext hs hn2

theorem moebiusDouble_coe (s : ℝ) :
    moebiusDouble (s : AddCircle (1 : ℝ)) = ((2 * s : ℝ) : AddCircle (1 : ℝ)) := by
  change ((s + s : ℝ) : AddCircle (1 : ℝ)) = _
  rw [two_mul]

theorem surjective_moebiusDouble : Surjective moebiusDouble := by
  intro w
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective w
  refine ⟨((s / 2 : ℝ) : AddCircle (1 : ℝ)), ?_⟩
  rw [moebiusDouble_coe]
  congr 1
  ring

theorem moebiusDouble_eq_iff {v w : AddCircle (1 : ℝ)} :
    moebiusDouble v = moebiusDouble w ↔ w = v ∨ w = moebiusHalf v := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨s', rfl⟩ := QuotientAddGroup.mk_surjective w
  rw [moebiusDouble_coe, moebiusDouble_coe]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (QuotientAddGroup.eq).mp h
    have hk' : 2 * s' = 2 * s + k := by
      simp only [zsmul_eq_mul, mul_one] at hk
      linarith
    rcases coe_eq_or_moebiusHalf_of_two_mul hk' with ⟨hs, -⟩ | ⟨hs, -⟩
    · exact Or.inl hs
    · exact Or.inr hs
  · rintro (h | h)
    · have h2 := congrArg moebiusDouble h
      rw [moebiusDouble_coe, moebiusDouble_coe] at h2
      exact h2.symm
    · have h2 := congrArg moebiusDouble h
      rw [moebiusDouble_coe, moebiusHalf_coe, moebiusDouble_coe] at h2
      rw [h2, show 2 * (s + 1 / 2) = 2 * s + ((1 : ℤ) : ℝ) by push_cast; ring]
      exact (addCircle_coe_add_int _ 1).symm

section Smooth

/-- The covering of the tube domain by the plane. -/
theorem isLocalDiffeomorph_coe_prodMap :
    IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (Prod.map (fun s : ℝ => (s : AddCircle (1 : ℝ))) (id : ℝ → ℝ)) :=
  AddCircle.isLocalDiffeomorph_coe.prodMap (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph

theorem moebiusTube_comp_cover :
    moebiusTube ∘ Prod.map (fun s : ℝ => (s : AddCircle (1 : ℝ))) (id : ℝ → ℝ) =
      NormalLineBundle.proj (-1) ∘
        (fun p : ℝ × ℝ => NormalCover.mk (-1) (2 * p.1) p.2) := rfl

theorem contMDiff_doubleCover :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => NormalCover.mk (-1) (2 * p.1) p.2) := by
  have h : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => ((2 * p.1, p.2) : ℝ × ℝ)) :=
    (contMDiff_const.mul contMDiff_fst).prodMk_space contMDiff_snd
  exact h

theorem contMDiff_moebiusTube :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ moebiusTube := by
  apply isLocalDiffeomorph_coe_prodMap.contMDiff_of_comp_of_surjective
  · intro y
    obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective y.1
    exact ⟨(s, y.2), Prod.ext hs rfl⟩
  · rw [moebiusTube_comp_cover]
    exact (NormalLineBundle.isLocalDiffeomorph_proj (-1) ∞).contMDiff.comp contMDiff_doubleCover

theorem injective_mfderiv_doubleCover (p : ℝ × ℝ) :
    Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun p : ℝ × ℝ => NormalCover.mk (-1) (2 * p.1) p.2) p) := by
  have hd : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun p : ℝ × ℝ => ((2 * p.1, p.2) : ℝ × ℝ)) p :=
    (contMDiff_doubleCover p).mdifferentiableAt (by simp)
  have h1 : ∀ v, (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun p : ℝ × ℝ => ((2 * p.1, p.2) : ℝ × ℝ)) p v).1 = 2 * v.1 := by
    intro v
    rw [DifferentialGeometry.Topology.Ehresmann.mfderiv_apply_fst_of_prodSpace hd v]
    have hf := ((hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) p).const_smul (2 : ℝ))
    change mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((2 : ℝ) • Prod.fst) p v = _
    rw [hf.mfderiv]
    rfl
  have h2 : ∀ v, (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun p : ℝ × ℝ => ((2 * p.1, p.2) : ℝ × ℝ)) p v).2 = v.2 := by
    intro v
    rw [DifferentialGeometry.Topology.Ehresmann.mfderiv_apply_snd_of_prodSpace hd v]
    change mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd p v = _
    rw [mfderiv_snd]
    rfl
  intro v w hvw
  have e1 := congrArg Prod.fst hvw
  have e2 := congrArg Prod.snd hvw
  change (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun p : ℝ × ℝ => ((2 * p.1, p.2) : ℝ × ℝ)) p v).1 =
    (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun p : ℝ × ℝ => ((2 * p.1, p.2) : ℝ × ℝ)) p w).1 at e1
  change (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun p : ℝ × ℝ => ((2 * p.1, p.2) : ℝ × ℝ)) p v).2 =
    (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun p : ℝ × ℝ => ((2 * p.1, p.2) : ℝ × ℝ)) p w).2 at e2
  rw [h1, h1] at e1
  rw [h2, h2] at e2
  exact Prod.ext (by linarith) e2

/-- Immersion test through a cover: if `f ∘ c` has injective differential at `p` and `c` has
surjective differential at `p`, then `f` has injective differential at `c p`. -/
theorem injective_mfderiv_of_comp_cover {E₁ E₂ E₃ H₁ H₂ H₃ M₁ M₂ M₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace H₃] {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {I₃ : ModelWithCorners ℝ E₃ H₃} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
    {c : M₁ → M₂} {f : M₂ → M₃} {p : M₁} (hc : MDifferentiableAt I₁ I₂ c p)
    (hf : MDifferentiableAt I₂ I₃ f (c p)) (hcs : Surjective (mfderiv I₁ I₂ c p))
    (hinj : Injective (mfderiv I₁ I₃ (f ∘ c) p)) : Injective (mfderiv I₂ I₃ f (c p)) := by
  intro w₁ w₂ h
  obtain ⟨u₁, rfl⟩ := hcs w₁
  obtain ⟨u₂, rfl⟩ := hcs w₂
  have hcomp := mfderiv_comp p hf hc
  have hu : u₁ = u₂ := hinj (by rw [hcomp]; exact h)
  rw [hu]

theorem isLocalDiffeomorph_moebiusTube :
    IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ moebiusTube := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    contMDiff_moebiusTube _ rfl
  intro y
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective y.1
  have hy : y = Prod.map (fun s : ℝ => (s : AddCircle (1 : ℝ))) (id : ℝ → ℝ) (s, y.2) :=
    Prod.ext hs.symm rfl
  rw [hy]
  have hc := isLocalDiffeomorph_coe_prodMap (s, y.2)
  have hcs : Surjective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (Prod.map (fun s : ℝ => (s : AddCircle (1 : ℝ))) (id : ℝ → ℝ)) (s, y.2)) := by
    obtain ⟨e, he⟩ := hc.isInvertible_mfderiv (by simp)
    rw [← he]
    exact e.surjective
  apply injective_mfderiv_of_comp_cover (hc.mdifferentiableAt (by simp))
    ((contMDiff_moebiusTube _).mdifferentiableAt (by simp)) hcs
  rw [moebiusTube_comp_cover]
  have hp := (NormalLineBundle.isLocalDiffeomorph_proj (-1) ∞)
    (NormalCover.mk (-1) (2 * s) y.2)
  have hpi : Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (NormalLineBundle.proj (-1))
      (NormalCover.mk (-1) (2 * s) y.2)) := by
    obtain ⟨e, he⟩ := hp.isInvertible_mfderiv (by simp)
    rw [← he]
    exact e.injective
  rw [mfderiv_comp (s, y.2) (hp.mdifferentiableAt (by simp))
    ((contMDiff_doubleCover (s, y.2)).mdifferentiableAt (by simp))]
  exact hpi.comp (injective_mfderiv_doubleCover (s, y.2))

theorem moebiusDouble_comp_coe :
    moebiusDouble ∘ (fun s : ℝ => (s : AddCircle (1 : ℝ))) =
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) ∘ (fun s : ℝ => 2 * s) := by
  funext s
  exact moebiusDouble_coe s

theorem contMDiff_moebiusDouble : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ moebiusDouble := by
  apply AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
    QuotientAddGroup.mk_surjective
  rw [moebiusDouble_comp_coe]
  exact AddCircle.contMDiff_coe.comp (contMDiff_const.mul contMDiff_id)

theorem isLocalDiffeomorph_moebiusDouble :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ moebiusDouble := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    contMDiff_moebiusDouble _ rfl
  intro y
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hc := AddCircle.isLocalDiffeomorph_coe s
  have hcs : Surjective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) s) := by
    obtain ⟨e, he⟩ := hc.isInvertible_mfderiv (by simp)
    rw [← he]
    exact e.surjective
  apply injective_mfderiv_of_comp_cover (hc.mdifferentiableAt (by simp))
    ((contMDiff_moebiusDouble _).mdifferentiableAt (by simp)) hcs
  rw [moebiusDouble_comp_coe]
  have hc2 := AddCircle.isLocalDiffeomorph_coe (2 * s)
  have hlin : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => 2 * s) s :=
    ((contMDiff_const.mul contMDiff_id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => 2 * s))
      s).mdifferentiableAt (by simp)
  have hc2i : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ)))
      (2 * s)) := by
    obtain ⟨e, he⟩ := hc2.isInvertible_mfderiv (by simp)
    rw [← he]
    exact e.injective
  rw [mfderiv_comp s (hc2.mdifferentiableAt (by simp)) hlin]
  refine hc2i.comp ?_
  rw [mfderiv_eq_fderiv]
  intro v w hvw
  have hf : HasFDerivAt (fun s : ℝ => 2 * s) ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) s := by
    simpa using (hasFDerivAt_id s).const_mul (2 : ℝ)
  rw [hf.fderiv] at hvw
  have hinj2 : Injective ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) := by
    intro a b hab
    have h2 : (2 : ℝ) * a = 2 * b := hab
    linarith
  exact ((NormedSpace.fromTangentSpace (2 * s)).symm.injective.comp
    (hinj2.comp (NormedSpace.fromTangentSpace s).injective)) hvw

end Smooth

/-- **The Möbius data of the one-sided smoothing theorem.** The tube `Φ ([s], t) = [2 s, t]` is a
`C^n` local diffeomorphism on `Sc × (-ε, ε)`, equivariant for `(v, t) ↦ (σ v, -t)` and injective
modulo it; the double cover `π [s] = [2 s]` is a surjective `C^n` local diffeomorphism whose fibres
are the `σ`-orbits. -/
theorem moebius_one_sided_data (n : ℕ) (ε : ℝ) :
    IsLocalDiffeomorphOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) n moebiusTube
        (univ ×ˢ Ioo (-ε) ε) ∧
      Continuous moebiusHalf ∧ (∀ v, moebiusHalf (moebiusHalf v) = v) ∧
      (∀ v t, moebiusTube (moebiusHalf v, -t) = moebiusTube (v, t)) ∧
      (∀ p ∈ (univ : Set (AddCircle (1 : ℝ))) ×ˢ Ioo (-ε) ε, ∀ q ∈ (univ : Set _) ×ˢ Ioo (-ε) ε,
        moebiusTube p = moebiusTube q → q = p ∨ q = (moebiusHalf p.1, -p.2)) ∧
      IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n moebiusDouble ∧ Surjective moebiusDouble ∧
      ∀ v w, moebiusDouble v = moebiusDouble w ↔ w = v ∨ w = moebiusHalf v :=
  ⟨fun x => isLocalDiffeomorphAt_of_le_top (isLocalDiffeomorph_moebiusTube x) n,
    continuous_moebiusHalf, moebiusHalf_moebiusHalf, moebiusTube_equiv,
    fun _ _ _ _ h => moebiusTube_inj h,
    fun x => isLocalDiffeomorphAt_of_le_top (isLocalDiffeomorph_moebiusDouble x) n,
    surjective_moebiusDouble, fun _ _ => moebiusDouble_eq_iff⟩

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
