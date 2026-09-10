import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Abelian

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits

namespace Poincare.Topology.SphereSeparation

variable {R : Type*} [CommRing R]

def ModuleEndomorphism.IsLocallyNilpotent {M : ModuleCat R} (f : M ⟶ M) : Prop :=
  ∀ x : M, ∃ k : ℕ, (f^[k]) x = 0

namespace ModuleEndomorphism

theorem IsLocallyNilpotent.congr {M : ModuleCat R} {f g : M ⟶ M}
    (hf : IsLocallyNilpotent f) (hfg : f = g) : IsLocallyNilpotent g := by
  subst hfg
  exact hf

theorem iterate_zero {M : ModuleCat R} (f : M ⟶ M) (k : ℕ) :
    (f^[k]) (0 : M) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_zero, ih]

theorem iterate_add {M : ModuleCat R} (f : M ⟶ M) (k : ℕ) (x y : M) :
    (f^[k]) (x + y) = (f^[k]) x + (f^[k]) y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, map_add, ih,
        Function.iterate_succ_apply, Function.iterate_succ_apply]

theorem iterate_smul {M : ModuleCat R} (f : M ⟶ M) (k : ℕ) (r : R) (x : M) :
    (f^[k]) (r • x) = r • (f^[k]) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, map_smul, ih,
        Function.iterate_succ_apply]

def locallyNilpotentSubmodule {M : ModuleCat R} (f : M ⟶ M) :
    Submodule R M where
  carrier := {x | ∃ k : ℕ, (f^[k]) x = 0}
  zero_mem' := ⟨0, rfl⟩
  add_mem' {x y} hx hy := by
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨k + l, ?_⟩
    rw [iterate_add]
    have hx' : (f^[k + l]) x = 0 := by
      rw [Nat.add_comm, Function.iterate_add_apply, hk,
        iterate_zero]
    have hy' : (f^[k + l]) y = 0 := by
      rw [Function.iterate_add_apply, hl, iterate_zero]
    rw [hx', hy', add_zero]
  smul_mem' r x hx := by
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    rw [iterate_smul, hk, smul_zero]

@[simp]
theorem mem_locallyNilpotentSubmodule_iff {M : ModuleCat R} (f : M ⟶ M)
    (x : M) :
    x ∈ locallyNilpotentSubmodule f ↔ ∃ k : ℕ, (f^[k]) x = 0 :=
  Iff.rfl


theorem isLocallyNilpotent_of_span
    {M : ModuleCat R} (f : M ⟶ M) (S : Set M)
    (hspan : Submodule.span R S = ⊤)
    (hS : ∀ x ∈ S, ∃ k : ℕ, (f^[k]) x = 0) :
    IsLocallyNilpotent f := by
  intro x
  have hle : Submodule.span R S ≤ locallyNilpotentSubmodule f :=
    Submodule.span_le.2 (fun y hy ↦ hS y hy)
  exact hle (by rw [hspan]; exact Submodule.mem_top)

end ModuleEndomorphism

variable {K : ChainComplex (ModuleCat R) ℕ}

theorem locallyNilpotent_cyclesMap_of_f
    (T : K ⟶ K) (n : ℕ)
    (hT : ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    ModuleEndomorphism.IsLocallyNilpotent
      (HomologicalComplex.cyclesMap T n) := by
  intro z
  obtain ⟨k, hk⟩ := hT (K.iCycles n z)
  refine ⟨k, ?_⟩
  apply ((ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance)
  rw [map_zero]
  have hiterate : ∀ (j : ℕ) (w : K.cycles n),
      K.iCycles n (((HomologicalComplex.cyclesMap T n)^[j]) w) =
        ((T.f n)^[j]) (K.iCycles n w) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
        congr 1
        exact DFunLike.congr_fun
          (congrArg ModuleCat.Hom.hom
            (HomologicalComplex.cyclesMap_i (K := K) (L := K)
              (i := n) (φ := T))) w
  rw [hiterate, hk]


theorem locallyNilpotent_homologyMap_of_cyclesMap
    (T : K ⟶ K) (n : ℕ)
    (hT : ModuleEndomorphism.IsLocallyNilpotent
      (HomologicalComplex.cyclesMap T n)) :
    ModuleEndomorphism.IsLocallyNilpotent
      (HomologicalComplex.homologyMap T n) := by
  intro x
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance x
  obtain ⟨k, hk⟩ := hT z
  refine ⟨k, ?_⟩
  have hiterate : ∀ (j : ℕ) (w : K.cycles n),
      ((HomologicalComplex.homologyMap T n)^[j]) (K.homologyπ n w) =
        K.homologyπ n (((HomologicalComplex.cyclesMap T n)^[j]) w) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        rw [show HomologicalComplex.homologyMap T n (K.homologyπ n w) =
            K.homologyπ n (HomologicalComplex.cyclesMap T n w) by
          exact DFunLike.congr_fun
            (congrArg ModuleCat.Hom.hom
              (HomologicalComplex.homologyπ_naturality (φ := T) (i := n))) w]
        exact ih _
  rw [hiterate, hk, map_zero]

theorem locallyNilpotent_homologyMap_of_f
    (T : K ⟶ K) (n : ℕ)
    (hT : ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    ModuleEndomorphism.IsLocallyNilpotent
      (HomologicalComplex.homologyMap T n) :=
  locallyNilpotent_homologyMap_of_cyclesMap T n
    (locallyNilpotent_cyclesMap_of_f T n hT)

theorem exactAt_of_homotopic_id_of_locallyNilpotent
    (T : K ⟶ K) (h : _root_.Homotopy T (𝟙 K)) (n : ℕ)
    (hT : ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y ↦ ?_⟩
  have hmap : HomologicalComplex.homologyMap T n = 𝟙 _ := by
    simpa using h.homologyMap_eq n
  have hnil := locallyNilpotent_homologyMap_of_f T n hT
  have hx : x = 0 := by
    obtain ⟨k, hk⟩ := hnil x
    simpa [hmap] using hk
  have hy : y = 0 := by
    obtain ⟨k, hk⟩ := hnil y
    simpa [hmap] using hk
  rw [hx, hy]

theorem exact_of_homotopic_id_of_degreewiseLocallyNilpotent
    (T : K ⟶ K) (h : _root_.Homotopy T (𝟙 K))
    (hT : ∀ n : ℕ, ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    ∀ n : ℕ, K.ExactAt n :=
  fun n ↦ exactAt_of_homotopic_id_of_locallyNilpotent T h n (hT n)



noncomputable def chainCokernelSequence
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

theorem chainCokernelSequence_shortExact
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) [Mono i] :
    (chainCokernelSequence i).ShortExact := by
  change (ShortComplex.cokernelSequence i).ShortExact
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.cokernelSequence_exact i
  · change Mono i
    infer_instance
  · infer_instance

noncomputable def chainCokernelEndomorphism
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B)
    (TA : A ⟶ A) (TB : B ⟶ B) (h : i ≫ TB = TA ≫ i) :
    cokernel i ⟶ cokernel i :=
  cokernel.map i i TA TB h

@[reassoc (attr := simp)]
theorem chainCokernelProjection_naturality
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B)
    (TA : A ⟶ A) (TB : B ⟶ B) (h : i ≫ TB = TA ≫ i) :
    cokernel.π i ≫ chainCokernelEndomorphism i TA TB h =
      TB ≫ cokernel.π i := by
  simp [chainCokernelEndomorphism]

theorem locallyNilpotent_chainCokernelEndomorphism
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B)
    (TA : A ⟶ A) (TB : B ⟶ B) (h : i ≫ TB = TA ≫ i)
    (n : ℕ)
    (heventual : ∀ x : B.X n, ∃ k : ℕ,
      (cokernel.π i).f n (((TB.f n)^[k]) x) = 0) :
    ModuleEndomorphism.IsLocallyNilpotent
      ((chainCokernelEndomorphism i TA TB h).f n) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((cokernel.π i).f n)).1 inferInstance y
  obtain ⟨k, hk⟩ := heventual x
  refine ⟨k, ?_⟩
  have hbase : ∀ w : B.X n,
      (chainCokernelEndomorphism i TA TB h).f n ((cokernel.π i).f n w) =
        (cokernel.π i).f n (TB.f n w) := by
    intro w
    exact DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom
        (HomologicalComplex.congr_hom
          (chainCokernelProjection_naturality i TA TB h) n)) w
  have hiterate : ∀ (j : ℕ) (w : B.X n),
      (((chainCokernelEndomorphism i TA TB h).f n)^[j])
          ((cokernel.π i).f n w) =
        (cokernel.π i).f n (((TB.f n)^[j]) w) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
          hbase, ih]
  rw [hiterate, hk]

theorem quasiIso_of_cokernel_acyclic
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) [Mono i]
    (hQ : ∀ n : ℕ, (cokernel i).ExactAt n) :
    QuasiIso i := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap i n) := by
    have hzero := (hQ (n + 1)).isZero_homology
    apply ((chainCokernelSequence_shortExact i).homology_exact₁
      (n + 1) n (by simp)).mono_g
    exact hzero.eq_of_src _ _
  have hepi : Epi (HomologicalComplex.homologyMap i n) := by
    have hzero := (hQ n).isZero_homology
    apply ((chainCokernelSequence_shortExact i).homology_exact₂ n).epi_f
    exact hzero.eq_of_tgt _ _
  let _ : Mono (HomologicalComplex.homologyMap i n) := hmono
  let _ : Epi (HomologicalComplex.homologyMap i n) := hepi
  exact isIso_of_mono_of_epi _

theorem quasiIso_of_cokernel_locallyNilpotent_homotopic_id
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) [Mono i]
    (T : cokernel i ⟶ cokernel i)
    (h : _root_.Homotopy T (𝟙 (cokernel i)))
    (hT : ∀ n : ℕ, ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    QuasiIso i :=
  quasiIso_of_cokernel_acyclic i
    (exact_of_homotopic_id_of_degreewiseLocallyNilpotent T h hT)

theorem quasiIso_of_cokernelSubdivision_eventually_zero
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) [Mono i]
    (TA : A ⟶ A) (TB : B ⟶ B) (hcomm : i ≫ TB = TA ≫ i)
    (hhom : _root_.Homotopy
      (chainCokernelEndomorphism i TA TB hcomm) (𝟙 (cokernel i)))
    (heventual : ∀ (n : ℕ) (x : B.X n), ∃ k : ℕ,
      (cokernel.π i).f n (((TB.f n)^[k]) x) = 0) :
    QuasiIso i :=
  quasiIso_of_cokernel_locallyNilpotent_homotopic_id i
    (chainCokernelEndomorphism i TA TB hcomm) hhom
    (fun n ↦ locallyNilpotent_chainCokernelEndomorphism
      i TA TB hcomm n (heventual n))

end Poincare.Topology.SphereSeparation
