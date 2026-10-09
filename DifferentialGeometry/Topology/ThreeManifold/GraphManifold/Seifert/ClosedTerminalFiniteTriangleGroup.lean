import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

/-!
# The finite spherical triangle quotient

The canonical presentation has generators x and y with relators x^p, y^q and (y*x)^r.
Explicit relator deductions certify finite word normal forms for the exceptional spherical
triples. Generator substitutions transport the presentation through parameter permutations.
This is a quotient-group backend and makes no claim about a central extension of this group.
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace GC.Seifert

def sphericalTriangleRelators (p q r : ℕ) : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of 0 ^ p, FreeGroup.of 1 ^ q, (FreeGroup.of 1 * FreeGroup.of 0) ^ r}

abbrev SphericalTriangleGroup (p q r : ℕ) := PresentedGroup (sphericalTriangleRelators p q r)

abbrev sphericalTriangleGenerator (p q r : ℕ) (i : Fin 2) : SphericalTriangleGroup p q r :=
  PresentedGroup.of (rels := sphericalTriangleRelators p q r) i

abbrev sphericalTriangleX (p q r : ℕ) : SphericalTriangleGroup p q r :=
  sphericalTriangleGenerator p q r 0

abbrev sphericalTriangleY (p q r : ℕ) : SphericalTriangleGroup p q r :=
  sphericalTriangleGenerator p q r 1

theorem sphericalTriangleX_pow (p q r : ℕ) : sphericalTriangleX p q r ^ p = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := sphericalTriangleRelators p q r) (x := FreeGroup.of 0 ^ p)
      (by simp [sphericalTriangleRelators])
  simpa only [map_pow, sphericalTriangleX, sphericalTriangleY,
    sphericalTriangleGenerator, PresentedGroup.of] using h

theorem sphericalTriangleY_pow (p q r : ℕ) : sphericalTriangleY p q r ^ q = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := sphericalTriangleRelators p q r) (x := FreeGroup.of 1 ^ q)
      (by simp [sphericalTriangleRelators])
  simpa only [map_pow, sphericalTriangleX, sphericalTriangleY,
    sphericalTriangleGenerator, PresentedGroup.of] using h

theorem sphericalTriangleYX_pow (p q r : ℕ) :
    (sphericalTriangleY p q r * sphericalTriangleX p q r) ^ r = 1 := by
  have h := PresentedGroup.one_of_mem (rels := sphericalTriangleRelators p q r)
    (x := (FreeGroup.of 1 * FreeGroup.of 0) ^ r) (by simp [sphericalTriangleRelators])
  simpa only [map_pow, map_mul, sphericalTriangleX, sphericalTriangleY,
    sphericalTriangleGenerator, PresentedGroup.of] using h

def sphericalTriangleWord (p q r : ℕ) (w : List (Fin 2)) : SphericalTriangleGroup p q r :=
  (w.map (sphericalTriangleGenerator p q r)).prod

theorem sphericalTriangleWord_append (p q r : ℕ) (a b : List (Fin 2)) :
    sphericalTriangleWord p q r (a ++ b) =
      sphericalTriangleWord p q r a * sphericalTriangleWord p q r b := by
  simp only [sphericalTriangleWord, List.map_append, List.prod_append]

theorem sphericalTriangleWord_singleton (p q r : ℕ) (i : Fin 2) :
    sphericalTriangleWord p q r [i] = sphericalTriangleGenerator p q r i := by
  simp [sphericalTriangleWord]

theorem sphericalTriangleWord_replace (p q r : ℕ) (pre post : List (Fin 2))
    {a b : List (Fin 2)} (h : sphericalTriangleWord p q r a = sphericalTriangleWord p q r b) :
    sphericalTriangleWord p q r (pre ++ a ++ post) =
      sphericalTriangleWord p q r (pre ++ b ++ post) := by
  simp only [sphericalTriangleWord_append]
  rw [h]

theorem finite_of_sphericalTriangleNormalWords (p q r : ℕ) (hp : 0 < p) (hq : 0 < q)
    {ι : Type*} [Finite ι] (words : ι → List (Fin 2)) (hzero : ∃ i, words i = [])
    (hstep : ∀ i (a : Fin 2), ∃ j,
      sphericalTriangleWord p q r (words i) * sphericalTriangleGenerator p q r a =
        sphericalTriangleWord p q r (words j)) : Finite (SphericalTriangleGroup p q r) := by
  obtain ⟨i₀, hi₀⟩ := hzero
  have hword : ∀ w : List (Fin 2), ∀ i, ∃ j,
      sphericalTriangleWord p q r (words i) * sphericalTriangleWord p q r w =
        sphericalTriangleWord p q r (words j) := by
    intro w
    induction w with
    | nil => intro i; exact ⟨i, mul_one _⟩
    | cons a w ih =>
      intro i
      obtain ⟨j, hj⟩ := hstep i a
      obtain ⟨k, hk⟩ := ih j
      refine ⟨k, ?_⟩
      change sphericalTriangleWord p q r (words i) *
        (sphericalTriangleGenerator p q r a * sphericalTriangleWord p q r w) = _
      rw [← mul_assoc, hj, hk]
  have heval : ∀ w, ∃ i, sphericalTriangleWord p q r w =
      sphericalTriangleWord p q r (words i) := by
    intro w
    obtain ⟨i, hi⟩ := hword w i₀
    rw [hi₀] at hi
    exact ⟨i, (one_mul _).symm.trans hi⟩
  have hmul : ∀ a b, (∃ i, a = sphericalTriangleWord p q r (words i)) →
      (∃ i, b = sphericalTriangleWord p q r (words i)) →
      ∃ i, a * b = sphericalTriangleWord p q r (words i) := by
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    exact hword (words j) i
  have hinv : ∀ i : Fin 2, ∃ j,
      (sphericalTriangleGenerator p q r i)⁻¹ = sphericalTriangleWord p q r (words j) := by
    intro i
    fin_cases i
    · have he : (sphericalTriangleX p q r)⁻¹ = sphericalTriangleX p q r ^ (p - 1) := by
        rw [pow_sub _ (by omega), sphericalTriangleX_pow, pow_one, one_mul]
      obtain ⟨j, hj⟩ := heval (List.replicate (p - 1) 0)
      exact ⟨j, he.trans (by simpa [sphericalTriangleWord] using hj)⟩
    · have he : (sphericalTriangleY p q r)⁻¹ = sphericalTriangleY p q r ^ (q - 1) := by
        rw [pow_sub _ (by omega), sphericalTriangleY_pow, pow_one, one_mul]
      obtain ⟨j, hj⟩ := heval (List.replicate (q - 1) 1)
      exact ⟨j, he.trans (by simpa [sphericalTriangleWord] using hj)⟩
  apply Finite.of_surjective (fun i => sphericalTriangleWord p q r (words i))
  intro g
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective (sphericalTriangleRelators p q r) g
  have hall : ∀ w : FreeGroup (Fin 2), ∃ i,
      PresentedGroup.mk (sphericalTriangleRelators p q r) w =
        sphericalTriangleWord p q r (words i) := by
    intro w
    induction w with
    | one => exact ⟨i₀, by simp [hi₀, sphericalTriangleWord]⟩
    | of a => simpa only [sphericalTriangleWord_singleton, sphericalTriangleGenerator,
        PresentedGroup.of] using heval [a]
    | inv_of a ha =>
      simpa only [map_inv, sphericalTriangleGenerator, PresentedGroup.of] using hinv a
    | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
  obtain ⟨i, hi⟩ := hall w
  exact ⟨i, hi.symm⟩

private abbrev TW3 (w : List (Fin 2)) := sphericalTriangleWord 2 3 3 w

private theorem triangleRule3_0 : TW3 [0, 0] = TW3 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleX_pow 2 3 3

private theorem triangleRule3_1 : TW3 [1, 1, 1] = TW3 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleY_pow 2 3 3

private theorem triangleRule3_2 : TW3 [1, 0, 1, 0, 1, 0] = TW3 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleYX_pow 2 3 3

private theorem triangleRule3_3 : TW3 [0, 1, 0, 1, 0] = TW3 [1, 1] := by
  calc
    TW3 [0, 1, 0, 1, 0] = TW3 [1, 1, 1, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 3 [] [0, 1, 0, 1, 0]
          (a := [1, 1, 1]) (b := []) triangleRule3_1).symm
    _ = TW3 [1, 1] :=
      sphericalTriangleWord_replace 2 3 3 [1, 1] []
          (a := [1, 0, 1, 0, 1, 0]) (b := []) triangleRule3_2

private theorem triangleRule3_4 : TW3 [1, 0, 1, 0, 1] = TW3 [0] := by
  calc
    TW3 [1, 0, 1, 0, 1] = TW3 [1, 0, 1, 0, 1, 0, 0] :=
      (sphericalTriangleWord_replace 2 3 3 [1, 0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule3_0).symm
    _ = TW3 [0] :=
      sphericalTriangleWord_replace 2 3 3 [] [0]
          (a := [1, 0, 1, 0, 1, 0]) (b := []) triangleRule3_2

private theorem triangleRule3_5 : TW3 [0, 1, 0, 1] = TW3 [1, 1, 0] := by
  calc
    TW3 [0, 1, 0, 1] = TW3 [0, 1, 0, 1, 0, 0] :=
      (sphericalTriangleWord_replace 2 3 3 [0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule3_0).symm
    _ = TW3 [1, 1, 0] :=
      sphericalTriangleWord_replace 2 3 3 [] [0]
          (a := [0, 1, 0, 1, 0]) (b := [1, 1]) triangleRule3_3

private theorem triangleRule3_6 : TW3 [1, 0, 1, 0] = TW3 [0, 1, 1] := by
  calc
    TW3 [1, 0, 1, 0] = TW3 [0, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 3 [] [1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule3_0).symm
    _ = TW3 [0, 1, 1] :=
      sphericalTriangleWord_replace 2 3 3 [0] []
          (a := [0, 1, 0, 1, 0]) (b := [1, 1]) triangleRule3_3

private theorem triangleRule3_7 : TW3 [1, 1, 0, 1, 1] = TW3 [0, 1, 0] := by
  calc
    TW3 [1, 1, 0, 1, 1] = TW3 [0, 1, 0, 1, 1, 1] :=
      (sphericalTriangleWord_replace 2 3 3 [] [1, 1]
          (a := [0, 1, 0, 1]) (b := [1, 1, 0]) triangleRule3_5).symm
    _ = TW3 [0, 1, 0] :=
      sphericalTriangleWord_replace 2 3 3 [0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule3_1

private theorem triangleRule3_8 : TW3 [0, 1, 1, 0] = TW3 [1, 0, 1] := by
  calc
    TW3 [0, 1, 1, 0] = TW3 [0, 0, 1, 0, 1] :=
      (sphericalTriangleWord_replace 2 3 3 [0] []
          (a := [0, 1, 0, 1]) (b := [1, 1, 0]) triangleRule3_5).symm
    _ = TW3 [1, 0, 1] :=
      sphericalTriangleWord_replace 2 3 3 [] [1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule3_0

private def triangleNormals3 (i : Fin 12) : List (Fin 2) :=
  match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [0, 1]
  | 4 => [1, 0]
  | 5 => [1, 1]
  | 6 => [0, 1, 0]
  | 7 => [0, 1, 1]
  | 8 => [1, 0, 1]
  | 9 => [1, 1, 0]
  | 10 => [1, 0, 1, 1]
  | 11 => [1, 1, 0, 1]
  | _ => []

private theorem triangleNormalStep3_0 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 0) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨1, ?_⟩
    change TW3 [] * sphericalTriangleGenerator 2 3 3 0 = TW3 [0]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [] [0]]
    change TW3 [0] = TW3 [0]
    rfl
  · refine ⟨2, ?_⟩
    change TW3 [] * sphericalTriangleGenerator 2 3 3 1 = TW3 [1]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [] [1]]
    change TW3 [1] = TW3 [1]
    rfl

private theorem triangleNormalStep3_1 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 1) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨0, ?_⟩
    change TW3 [0] * sphericalTriangleGenerator 2 3 3 0 = TW3 []
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [0] [0]]
    change TW3 [0, 0] = TW3 []
    exact sphericalTriangleWord_replace 2 3 3 [] []
          (a := [0, 0]) (b := []) triangleRule3_0
  · refine ⟨3, ?_⟩
    change TW3 [0] * sphericalTriangleGenerator 2 3 3 1 = TW3 [0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [0] [1]]
    change TW3 [0, 1] = TW3 [0, 1]
    rfl

private theorem triangleNormalStep3_2 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 2) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨4, ?_⟩
    change TW3 [1] * sphericalTriangleGenerator 2 3 3 0 = TW3 [1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [1] [0]]
    change TW3 [1, 0] = TW3 [1, 0]
    rfl
  · refine ⟨5, ?_⟩
    change TW3 [1] * sphericalTriangleGenerator 2 3 3 1 = TW3 [1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [1] [1]]
    change TW3 [1, 1] = TW3 [1, 1]
    rfl

private theorem triangleNormalStep3_3 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 3) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨6, ?_⟩
    change TW3 [0, 1] * sphericalTriangleGenerator 2 3 3 0 = TW3 [0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [0, 1] [0]]
    change TW3 [0, 1, 0] = TW3 [0, 1, 0]
    rfl
  · refine ⟨7, ?_⟩
    change TW3 [0, 1] * sphericalTriangleGenerator 2 3 3 1 = TW3 [0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [0, 1] [1]]
    change TW3 [0, 1, 1] = TW3 [0, 1, 1]
    rfl

private theorem triangleNormalStep3_4 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 4) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨2, ?_⟩
    change TW3 [1, 0] * sphericalTriangleGenerator 2 3 3 0 = TW3 [1]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [1, 0] [0]]
    change TW3 [1, 0, 0] = TW3 [1]
    exact sphericalTriangleWord_replace 2 3 3 [1] []
          (a := [0, 0]) (b := []) triangleRule3_0
  · refine ⟨8, ?_⟩
    change TW3 [1, 0] * sphericalTriangleGenerator 2 3 3 1 = TW3 [1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [1, 0] [1]]
    change TW3 [1, 0, 1] = TW3 [1, 0, 1]
    rfl

private theorem triangleNormalStep3_5 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 5) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨9, ?_⟩
    change TW3 [1, 1] * sphericalTriangleGenerator 2 3 3 0 = TW3 [1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [1, 1] [0]]
    change TW3 [1, 1, 0] = TW3 [1, 1, 0]
    rfl
  · refine ⟨0, ?_⟩
    change TW3 [1, 1] * sphericalTriangleGenerator 2 3 3 1 = TW3 []
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [1, 1] [1]]
    change TW3 [1, 1, 1] = TW3 []
    exact sphericalTriangleWord_replace 2 3 3 [] []
          (a := [1, 1, 1]) (b := []) triangleRule3_1

private theorem triangleNormalStep3_6 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 6) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨3, ?_⟩
    change TW3 [0, 1, 0] * sphericalTriangleGenerator 2 3 3 0 = TW3 [0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [0, 1, 0] [0]]
    change TW3 [0, 1, 0, 0] = TW3 [0, 1]
    exact sphericalTriangleWord_replace 2 3 3 [0, 1] []
          (a := [0, 0]) (b := []) triangleRule3_0
  · refine ⟨9, ?_⟩
    change TW3 [0, 1, 0] * sphericalTriangleGenerator 2 3 3 1 = TW3 [1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [0, 1, 0] [1]]
    change TW3 [0, 1, 0, 1] = TW3 [1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 3 [] []
          (a := [0, 1, 0, 1]) (b := [1, 1, 0]) triangleRule3_5

private theorem triangleNormalStep3_7 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 7) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨8, ?_⟩
    change TW3 [0, 1, 1] * sphericalTriangleGenerator 2 3 3 0 = TW3 [1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [0, 1, 1] [0]]
    change TW3 [0, 1, 1, 0] = TW3 [1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 3 [] []
          (a := [0, 1, 1, 0]) (b := [1, 0, 1]) triangleRule3_8
  · refine ⟨1, ?_⟩
    change TW3 [0, 1, 1] * sphericalTriangleGenerator 2 3 3 1 = TW3 [0]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [0, 1, 1] [1]]
    change TW3 [0, 1, 1, 1] = TW3 [0]
    exact sphericalTriangleWord_replace 2 3 3 [0] []
          (a := [1, 1, 1]) (b := []) triangleRule3_1

private theorem triangleNormalStep3_8 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 8) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨7, ?_⟩
    change TW3 [1, 0, 1] * sphericalTriangleGenerator 2 3 3 0 = TW3 [0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [1, 0, 1] [0]]
    change TW3 [1, 0, 1, 0] = TW3 [0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 3 [] []
          (a := [1, 0, 1, 0]) (b := [0, 1, 1]) triangleRule3_6
  · refine ⟨10, ?_⟩
    change TW3 [1, 0, 1] * sphericalTriangleGenerator 2 3 3 1 = TW3 [1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [1, 0, 1] [1]]
    change TW3 [1, 0, 1, 1] = TW3 [1, 0, 1, 1]
    rfl

private theorem triangleNormalStep3_9 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 9) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨5, ?_⟩
    change TW3 [1, 1, 0] * sphericalTriangleGenerator 2 3 3 0 = TW3 [1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [1, 1, 0] [0]]
    change TW3 [1, 1, 0, 0] = TW3 [1, 1]
    exact sphericalTriangleWord_replace 2 3 3 [1, 1] []
          (a := [0, 0]) (b := []) triangleRule3_0
  · refine ⟨11, ?_⟩
    change TW3 [1, 1, 0] * sphericalTriangleGenerator 2 3 3 1 = TW3 [1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [1, 1, 0] [1]]
    change TW3 [1, 1, 0, 1] = TW3 [1, 1, 0, 1]
    rfl

private theorem triangleNormalStep3_10 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 10) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨11, ?_⟩
    change TW3 [1, 0, 1, 1] * sphericalTriangleGenerator 2 3 3 0 = TW3 [1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [1, 0, 1, 1] [0]]
    change TW3 [1, 0, 1, 1, 0] = TW3 [1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 3 [1] []
          (a := [0, 1, 1, 0]) (b := [1, 0, 1]) triangleRule3_8
  · refine ⟨4, ?_⟩
    change TW3 [1, 0, 1, 1] * sphericalTriangleGenerator 2 3 3 1 = TW3 [1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [1, 0, 1, 1] [1]]
    change TW3 [1, 0, 1, 1, 1] = TW3 [1, 0]
    exact sphericalTriangleWord_replace 2 3 3 [1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule3_1

private theorem triangleNormalStep3_11 (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 11) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases g
  · refine ⟨10, ?_⟩
    change TW3 [1, 1, 0, 1] * sphericalTriangleGenerator 2 3 3 0 = TW3 [1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 3 0,
      ← sphericalTriangleWord_append 2 3 3 [1, 1, 0, 1] [0]]
    change TW3 [1, 1, 0, 1, 0] = TW3 [1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 3 [1] []
          (a := [1, 0, 1, 0]) (b := [0, 1, 1]) triangleRule3_6
  · refine ⟨6, ?_⟩
    change TW3 [1, 1, 0, 1] * sphericalTriangleGenerator 2 3 3 1 = TW3 [0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 3 1,
      ← sphericalTriangleWord_append 2 3 3 [1, 1, 0, 1] [1]]
    change TW3 [1, 1, 0, 1, 1] = TW3 [0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 3 [] []
          (a := [1, 1, 0, 1, 1]) (b := [0, 1, 0]) triangleRule3_7

private theorem triangleNormals3_closed (i : Fin 12) (g : Fin 2) :
    ∃ j : Fin 12, TW3 (triangleNormals3 i) * sphericalTriangleGenerator 2 3 3 g =
      TW3 (triangleNormals3 j) := by
  fin_cases i
  · exact triangleNormalStep3_0 g
  · exact triangleNormalStep3_1 g
  · exact triangleNormalStep3_2 g
  · exact triangleNormalStep3_3 g
  · exact triangleNormalStep3_4 g
  · exact triangleNormalStep3_5 g
  · exact triangleNormalStep3_6 g
  · exact triangleNormalStep3_7 g
  · exact triangleNormalStep3_8 g
  · exact triangleNormalStep3_9 g
  · exact triangleNormalStep3_10 g
  · exact triangleNormalStep3_11 g

theorem finite_sphericalTriangleGroup_2_3_3 : Finite (SphericalTriangleGroup 2 3 3) :=
  finite_of_sphericalTriangleNormalWords 2 3 3 (by decide) (by decide)
    triangleNormals3 ⟨0, rfl⟩ triangleNormals3_closed

private abbrev TW4 (w : List (Fin 2)) := sphericalTriangleWord 2 3 4 w

private theorem triangleRule4_0 : TW4 [0, 0] = TW4 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleX_pow 2 3 4

private theorem triangleRule4_1 : TW4 [1, 1, 1] = TW4 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleY_pow 2 3 4

private theorem triangleRule4_2 : TW4 [1, 0, 1, 0, 1, 0, 1, 0] = TW4 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleYX_pow 2 3 4

private theorem triangleRule4_3 : TW4 [0, 1, 0, 1, 0, 1, 0] = TW4 [1, 1] := by
  calc
    TW4 [0, 1, 0, 1, 0, 1, 0] = TW4 [1, 1, 1, 0, 1, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 4 [] [0, 1, 0, 1, 0, 1, 0]
          (a := [1, 1, 1]) (b := []) triangleRule4_1).symm
    _ = TW4 [1, 1] :=
      sphericalTriangleWord_replace 2 3 4 [1, 1] []
          (a := [1, 0, 1, 0, 1, 0, 1, 0]) (b := []) triangleRule4_2

private theorem triangleRule4_4 : TW4 [1, 0, 1, 0, 1, 0, 1] = TW4 [0] := by
  calc
    TW4 [1, 0, 1, 0, 1, 0, 1] = TW4 [1, 0, 1, 0, 1, 0, 1, 0, 0] :=
      (sphericalTriangleWord_replace 2 3 4 [1, 0, 1, 0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0).symm
    _ = TW4 [0] :=
      sphericalTriangleWord_replace 2 3 4 [] [0]
          (a := [1, 0, 1, 0, 1, 0, 1, 0]) (b := []) triangleRule4_2

private theorem triangleRule4_5 : TW4 [0, 1, 0, 1, 0, 1] = TW4 [1, 1, 0] := by
  calc
    TW4 [0, 1, 0, 1, 0, 1] = TW4 [0, 1, 0, 1, 0, 1, 0, 0] :=
      (sphericalTriangleWord_replace 2 3 4 [0, 1, 0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0).symm
    _ = TW4 [1, 1, 0] :=
      sphericalTriangleWord_replace 2 3 4 [] [0]
          (a := [0, 1, 0, 1, 0, 1, 0]) (b := [1, 1]) triangleRule4_3

private theorem triangleRule4_6 : TW4 [1, 0, 1, 0, 1, 0] = TW4 [0, 1, 1] := by
  calc
    TW4 [1, 0, 1, 0, 1, 0] = TW4 [0, 0, 1, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 4 [] [1, 0, 1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule4_0).symm
    _ = TW4 [0, 1, 1] :=
      sphericalTriangleWord_replace 2 3 4 [0] []
          (a := [0, 1, 0, 1, 0, 1, 0]) (b := [1, 1]) triangleRule4_3

private theorem triangleRule4_7 : TW4 [1, 1, 0, 1, 1] = TW4 [0, 1, 0, 1, 0] := by
  calc
    TW4 [1, 1, 0, 1, 1] = TW4 [0, 1, 0, 1, 0, 1, 1, 1] :=
      (sphericalTriangleWord_replace 2 3 4 [] [1, 1]
          (a := [0, 1, 0, 1, 0, 1]) (b := [1, 1, 0]) triangleRule4_5).symm
    _ = TW4 [0, 1, 0, 1, 0] :=
      sphericalTriangleWord_replace 2 3 4 [0, 1, 0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule4_1

private theorem triangleRule4_8 : TW4 [1, 0, 1, 0, 1] = TW4 [0, 1, 1, 0] := by
  calc
    TW4 [1, 0, 1, 0, 1] = TW4 [0, 0, 1, 0, 1, 0, 1] :=
      (sphericalTriangleWord_replace 2 3 4 [] [1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule4_0).symm
    _ = TW4 [0, 1, 1, 0] :=
      sphericalTriangleWord_replace 2 3 4 [0] []
          (a := [0, 1, 0, 1, 0, 1]) (b := [1, 1, 0]) triangleRule4_5

private theorem triangleRule4_9 : TW4 [0, 1, 0, 1, 1, 0, 1, 0] = TW4 [1, 0, 1, 1, 0, 1] := by
  calc
    TW4 [0, 1, 0, 1, 1, 0, 1, 0] = TW4 [0, 1, 0, 1, 0, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 4 [0, 1, 0, 1] [1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule4_0).symm
    _ = TW4 [1, 1, 0, 1, 1, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 4 [] [0, 1, 0, 1, 0]
          (a := [1, 1, 0, 1, 1]) (b := [0, 1, 0, 1, 0]) triangleRule4_7).symm
    _ = TW4 [1, 1, 0, 1, 0, 1, 1] :=
      sphericalTriangleWord_replace 2 3 4 [1, 1, 0, 1] []
          (a := [1, 0, 1, 0, 1, 0]) (b := [0, 1, 1]) triangleRule4_6
    _ = TW4 [1, 0, 1, 1, 0, 1] :=
      sphericalTriangleWord_replace 2 3 4 [1] [1]
          (a := [1, 0, 1, 0, 1]) (b := [0, 1, 1, 0]) triangleRule4_8

private theorem triangleRule4_10 : TW4 [1, 0, 1, 1, 0, 1, 0] = TW4 [0, 1, 0, 1, 1, 0, 1] := by
  calc
    TW4 [1, 0, 1, 1, 0, 1, 0] = TW4 [1, 0, 1, 0, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 4 [1, 0, 1] [1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule4_0).symm
    _ = TW4 [1, 0, 1, 0, 1, 1, 0, 1, 1] :=
      (sphericalTriangleWord_replace 2 3 4 [1, 0, 1, 0] []
          (a := [1, 1, 0, 1, 1]) (b := [0, 1, 0, 1, 0]) triangleRule4_7).symm
    _ = TW4 [0, 1, 1, 0, 1, 0, 1, 1] :=
      sphericalTriangleWord_replace 2 3 4 [] [1, 0, 1, 1]
          (a := [1, 0, 1, 0, 1]) (b := [0, 1, 1, 0]) triangleRule4_8
    _ = TW4 [0, 1, 0, 1, 1, 0, 1] :=
      sphericalTriangleWord_replace 2 3 4 [0, 1] [1]
          (a := [1, 0, 1, 0, 1]) (b := [0, 1, 1, 0]) triangleRule4_8

private def triangleNormals4 (i : Fin 24) : List (Fin 2) :=
  match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [0, 1]
  | 4 => [1, 0]
  | 5 => [1, 1]
  | 6 => [0, 1, 0]
  | 7 => [0, 1, 1]
  | 8 => [1, 0, 1]
  | 9 => [1, 1, 0]
  | 10 => [0, 1, 0, 1]
  | 11 => [0, 1, 1, 0]
  | 12 => [1, 0, 1, 0]
  | 13 => [1, 0, 1, 1]
  | 14 => [1, 1, 0, 1]
  | 15 => [0, 1, 0, 1, 0]
  | 16 => [0, 1, 0, 1, 1]
  | 17 => [0, 1, 1, 0, 1]
  | 18 => [1, 0, 1, 1, 0]
  | 19 => [1, 1, 0, 1, 0]
  | 20 => [0, 1, 0, 1, 1, 0]
  | 21 => [0, 1, 1, 0, 1, 0]
  | 22 => [1, 0, 1, 1, 0, 1]
  | 23 => [0, 1, 0, 1, 1, 0, 1]
  | _ => []

private theorem triangleNormalStep4_0 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 0) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨1, ?_⟩
    change TW4 [] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [] [0]]
    change TW4 [0] = TW4 [0]
    rfl
  · refine ⟨2, ?_⟩
    change TW4 [] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [] [1]]
    change TW4 [1] = TW4 [1]
    rfl

private theorem triangleNormalStep4_1 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 1) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨0, ?_⟩
    change TW4 [0] * sphericalTriangleGenerator 2 3 4 0 = TW4 []
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0] [0]]
    change TW4 [0, 0] = TW4 []
    exact sphericalTriangleWord_replace 2 3 4 [] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨3, ?_⟩
    change TW4 [0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0] [1]]
    change TW4 [0, 1] = TW4 [0, 1]
    rfl

private theorem triangleNormalStep4_2 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 2) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨4, ?_⟩
    change TW4 [1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1] [0]]
    change TW4 [1, 0] = TW4 [1, 0]
    rfl
  · refine ⟨5, ?_⟩
    change TW4 [1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1] [1]]
    change TW4 [1, 1] = TW4 [1, 1]
    rfl

private theorem triangleNormalStep4_3 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 3) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨6, ?_⟩
    change TW4 [0, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1] [0]]
    change TW4 [0, 1, 0] = TW4 [0, 1, 0]
    rfl
  · refine ⟨7, ?_⟩
    change TW4 [0, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1] [1]]
    change TW4 [0, 1, 1] = TW4 [0, 1, 1]
    rfl

private theorem triangleNormalStep4_4 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 4) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨2, ?_⟩
    change TW4 [1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 0] [0]]
    change TW4 [1, 0, 0] = TW4 [1]
    exact sphericalTriangleWord_replace 2 3 4 [1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨8, ?_⟩
    change TW4 [1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 0] [1]]
    change TW4 [1, 0, 1] = TW4 [1, 0, 1]
    rfl

private theorem triangleNormalStep4_5 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 5) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨9, ?_⟩
    change TW4 [1, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 1] [0]]
    change TW4 [1, 1, 0] = TW4 [1, 1, 0]
    rfl
  · refine ⟨0, ?_⟩
    change TW4 [1, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 []
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 1] [1]]
    change TW4 [1, 1, 1] = TW4 []
    exact sphericalTriangleWord_replace 2 3 4 [] []
          (a := [1, 1, 1]) (b := []) triangleRule4_1

private theorem triangleNormalStep4_6 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 6) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨3, ?_⟩
    change TW4 [0, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0] [0]]
    change TW4 [0, 1, 0, 0] = TW4 [0, 1]
    exact sphericalTriangleWord_replace 2 3 4 [0, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨10, ?_⟩
    change TW4 [0, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0] [1]]
    change TW4 [0, 1, 0, 1] = TW4 [0, 1, 0, 1]
    rfl

private theorem triangleNormalStep4_7 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 7) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨11, ?_⟩
    change TW4 [0, 1, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 1] [0]]
    change TW4 [0, 1, 1, 0] = TW4 [0, 1, 1, 0]
    rfl
  · refine ⟨1, ?_⟩
    change TW4 [0, 1, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 1] [1]]
    change TW4 [0, 1, 1, 1] = TW4 [0]
    exact sphericalTriangleWord_replace 2 3 4 [0] []
          (a := [1, 1, 1]) (b := []) triangleRule4_1

private theorem triangleNormalStep4_8 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 8) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨12, ?_⟩
    change TW4 [1, 0, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1] [0]]
    change TW4 [1, 0, 1, 0] = TW4 [1, 0, 1, 0]
    rfl
  · refine ⟨13, ?_⟩
    change TW4 [1, 0, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1] [1]]
    change TW4 [1, 0, 1, 1] = TW4 [1, 0, 1, 1]
    rfl

private theorem triangleNormalStep4_9 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 9) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨5, ?_⟩
    change TW4 [1, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 1, 0] [0]]
    change TW4 [1, 1, 0, 0] = TW4 [1, 1]
    exact sphericalTriangleWord_replace 2 3 4 [1, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨14, ?_⟩
    change TW4 [1, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 1, 0] [1]]
    change TW4 [1, 1, 0, 1] = TW4 [1, 1, 0, 1]
    rfl

private theorem triangleNormalStep4_10 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 10) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨15, ?_⟩
    change TW4 [0, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1] [0]]
    change TW4 [0, 1, 0, 1, 0] = TW4 [0, 1, 0, 1, 0]
    rfl
  · refine ⟨16, ?_⟩
    change TW4 [0, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1] [1]]
    change TW4 [0, 1, 0, 1, 1] = TW4 [0, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep4_11 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 11) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨7, ?_⟩
    change TW4 [0, 1, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 1, 0] [0]]
    change TW4 [0, 1, 1, 0, 0] = TW4 [0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 4 [0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨17, ?_⟩
    change TW4 [0, 1, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 1, 0] [1]]
    change TW4 [0, 1, 1, 0, 1] = TW4 [0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep4_12 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 12) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨8, ?_⟩
    change TW4 [1, 0, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1, 0] [0]]
    change TW4 [1, 0, 1, 0, 0] = TW4 [1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 4 [1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨11, ?_⟩
    change TW4 [1, 0, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1, 0] [1]]
    change TW4 [1, 0, 1, 0, 1] = TW4 [0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 4 [] []
          (a := [1, 0, 1, 0, 1]) (b := [0, 1, 1, 0]) triangleRule4_8

private theorem triangleNormalStep4_13 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 13) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨18, ?_⟩
    change TW4 [1, 0, 1, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1, 1] [0]]
    change TW4 [1, 0, 1, 1, 0] = TW4 [1, 0, 1, 1, 0]
    rfl
  · refine ⟨4, ?_⟩
    change TW4 [1, 0, 1, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1, 1] [1]]
    change TW4 [1, 0, 1, 1, 1] = TW4 [1, 0]
    exact sphericalTriangleWord_replace 2 3 4 [1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule4_1

private theorem triangleNormalStep4_14 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 14) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨19, ?_⟩
    change TW4 [1, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 1, 0, 1] [0]]
    change TW4 [1, 1, 0, 1, 0] = TW4 [1, 1, 0, 1, 0]
    rfl
  · refine ⟨15, ?_⟩
    change TW4 [1, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 1, 0, 1] [1]]
    change TW4 [1, 1, 0, 1, 1] = TW4 [0, 1, 0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 4 [] []
          (a := [1, 1, 0, 1, 1]) (b := [0, 1, 0, 1, 0]) triangleRule4_7

private theorem triangleNormalStep4_15 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 15) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨10, ?_⟩
    change TW4 [0, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1, 0] [0]]
    change TW4 [0, 1, 0, 1, 0, 0] = TW4 [0, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 4 [0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨9, ?_⟩
    change TW4 [0, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1, 0] [1]]
    change TW4 [0, 1, 0, 1, 0, 1] = TW4 [1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 4 [] []
          (a := [0, 1, 0, 1, 0, 1]) (b := [1, 1, 0]) triangleRule4_5

private theorem triangleNormalStep4_16 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 16) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨20, ?_⟩
    change TW4 [0, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1, 1] [0]]
    change TW4 [0, 1, 0, 1, 1, 0] = TW4 [0, 1, 0, 1, 1, 0]
    rfl
  · refine ⟨6, ?_⟩
    change TW4 [0, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1, 1] [1]]
    change TW4 [0, 1, 0, 1, 1, 1] = TW4 [0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 4 [0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule4_1

private theorem triangleNormalStep4_17 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 17) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨21, ?_⟩
    change TW4 [0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 1, 0, 1] [0]]
    change TW4 [0, 1, 1, 0, 1, 0] = TW4 [0, 1, 1, 0, 1, 0]
    rfl
  · refine ⟨12, ?_⟩
    change TW4 [0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 1, 0, 1] [1]]
    change TW4 [0, 1, 1, 0, 1, 1] = TW4 [1, 0, 1, 0]
    calc
      TW4 [0, 1, 1, 0, 1, 1] = TW4 [0, 0, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 4 [0] []
          (a := [1, 1, 0, 1, 1]) (b := [0, 1, 0, 1, 0]) triangleRule4_7
      _ = TW4 [1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 4 [] [1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule4_0

private theorem triangleNormalStep4_18 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 18) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨13, ?_⟩
    change TW4 [1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1, 1, 0] [0]]
    change TW4 [1, 0, 1, 1, 0, 0] = TW4 [1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 4 [1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨22, ?_⟩
    change TW4 [1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1, 1, 0] [1]]
    change TW4 [1, 0, 1, 1, 0, 1] = TW4 [1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep4_19 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 19) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨14, ?_⟩
    change TW4 [1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 1, 0, 1, 0] [0]]
    change TW4 [1, 1, 0, 1, 0, 0] = TW4 [1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 4 [1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨18, ?_⟩
    change TW4 [1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 1, 0, 1, 0] [1]]
    change TW4 [1, 1, 0, 1, 0, 1] = TW4 [1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 4 [1] []
          (a := [1, 0, 1, 0, 1]) (b := [0, 1, 1, 0]) triangleRule4_8

private theorem triangleNormalStep4_20 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 20) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨16, ?_⟩
    change TW4 [0, 1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1, 1, 0] [0]]
    change TW4 [0, 1, 0, 1, 1, 0, 0] = TW4 [0, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 4 [0, 1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨23, ?_⟩
    change TW4 [0, 1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1, 1, 0] [1]]
    change TW4 [0, 1, 0, 1, 1, 0, 1] = TW4 [0, 1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep4_21 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 21) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨17, ?_⟩
    change TW4 [0, 1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 1, 0, 1, 0] [0]]
    change TW4 [0, 1, 1, 0, 1, 0, 0] = TW4 [0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 4 [0, 1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule4_0
  · refine ⟨20, ?_⟩
    change TW4 [0, 1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 1, 0, 1, 0] [1]]
    change TW4 [0, 1, 1, 0, 1, 0, 1] = TW4 [0, 1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 4 [0, 1] []
          (a := [1, 0, 1, 0, 1]) (b := [0, 1, 1, 0]) triangleRule4_8

private theorem triangleNormalStep4_22 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 22) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨23, ?_⟩
    change TW4 [1, 0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1, 1, 0, 1] [0]]
    change TW4 [1, 0, 1, 1, 0, 1, 0] = TW4 [0, 1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 4 [] []
          (a := [1, 0, 1, 1, 0, 1, 0]) (b := [0, 1, 0, 1, 1, 0, 1]) triangleRule4_10
  · refine ⟨19, ?_⟩
    change TW4 [1, 0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [1, 0, 1, 1, 0, 1] [1]]
    change TW4 [1, 0, 1, 1, 0, 1, 1] = TW4 [1, 1, 0, 1, 0]
    calc
      TW4 [1, 0, 1, 1, 0, 1, 1] = TW4 [1, 0, 0, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 4 [1, 0] []
          (a := [1, 1, 0, 1, 1]) (b := [0, 1, 0, 1, 0]) triangleRule4_7
      _ = TW4 [1, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 4 [1] [1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule4_0

private theorem triangleNormalStep4_23 (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 23) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases g
  · refine ⟨22, ?_⟩
    change TW4 [0, 1, 0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 0 = TW4 [1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 4 0,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1, 1, 0, 1] [0]]
    change TW4 [0, 1, 0, 1, 1, 0, 1, 0] = TW4 [1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 4 [] []
          (a := [0, 1, 0, 1, 1, 0, 1, 0]) (b := [1, 0, 1, 1, 0, 1]) triangleRule4_9
  · refine ⟨21, ?_⟩
    change TW4 [0, 1, 0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 4 1 = TW4 [0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 4 1,
      ← sphericalTriangleWord_append 2 3 4 [0, 1, 0, 1, 1, 0, 1] [1]]
    change TW4 [0, 1, 0, 1, 1, 0, 1, 1] = TW4 [0, 1, 1, 0, 1, 0]
    calc
      TW4 [0, 1, 0, 1, 1, 0, 1, 1] = TW4 [0, 1, 0, 0, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 4 [0, 1, 0] []
          (a := [1, 1, 0, 1, 1]) (b := [0, 1, 0, 1, 0]) triangleRule4_7
      _ = TW4 [0, 1, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 4 [0, 1] [1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule4_0

private theorem triangleNormals4_closed (i : Fin 24) (g : Fin 2) :
    ∃ j : Fin 24, TW4 (triangleNormals4 i) * sphericalTriangleGenerator 2 3 4 g =
      TW4 (triangleNormals4 j) := by
  fin_cases i
  · exact triangleNormalStep4_0 g
  · exact triangleNormalStep4_1 g
  · exact triangleNormalStep4_2 g
  · exact triangleNormalStep4_3 g
  · exact triangleNormalStep4_4 g
  · exact triangleNormalStep4_5 g
  · exact triangleNormalStep4_6 g
  · exact triangleNormalStep4_7 g
  · exact triangleNormalStep4_8 g
  · exact triangleNormalStep4_9 g
  · exact triangleNormalStep4_10 g
  · exact triangleNormalStep4_11 g
  · exact triangleNormalStep4_12 g
  · exact triangleNormalStep4_13 g
  · exact triangleNormalStep4_14 g
  · exact triangleNormalStep4_15 g
  · exact triangleNormalStep4_16 g
  · exact triangleNormalStep4_17 g
  · exact triangleNormalStep4_18 g
  · exact triangleNormalStep4_19 g
  · exact triangleNormalStep4_20 g
  · exact triangleNormalStep4_21 g
  · exact triangleNormalStep4_22 g
  · exact triangleNormalStep4_23 g

theorem finite_sphericalTriangleGroup_2_3_4 : Finite (SphericalTriangleGroup 2 3 4) :=
  finite_of_sphericalTriangleNormalWords 2 3 4 (by decide) (by decide)
    triangleNormals4 ⟨0, rfl⟩ triangleNormals4_closed

private abbrev TW5 (w : List (Fin 2)) := sphericalTriangleWord 2 3 5 w

private theorem triangleRule5_0 : TW5 [0, 0] = TW5 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleX_pow 2 3 5

private theorem triangleRule5_1 : TW5 [1, 1, 1] = TW5 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleY_pow 2 3 5

private theorem triangleRule5_2 : TW5 [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] = TW5 [] := by
  simpa [sphericalTriangleWord, pow_succ, mul_assoc] using sphericalTriangleYX_pow 2 3 5

private theorem triangleRule5_3 : TW5 [0, 1, 0, 1, 0, 1, 0, 1, 0] = TW5 [1, 1] := by
  calc
    TW5 [0, 1, 0, 1, 0, 1, 0, 1, 0] = TW5 [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [] [0, 1, 0, 1, 0, 1, 0, 1, 0]
          (a := [1, 1, 1]) (b := []) triangleRule5_1).symm
    _ = TW5 [1, 1] :=
      sphericalTriangleWord_replace 2 3 5 [1, 1] []
          (a := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]) (b := []) triangleRule5_2

private theorem triangleRule5_4 : TW5 [1, 0, 1, 0, 1, 0, 1, 0, 1] = TW5 [0] := by
  calc
    TW5 [1, 0, 1, 0, 1, 0, 1, 0, 1] = TW5 [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 0, 1, 0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0).symm
    _ = TW5 [0] :=
      sphericalTriangleWord_replace 2 3 5 [] [0]
          (a := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]) (b := []) triangleRule5_2

private theorem triangleRule5_5 : TW5 [0, 1, 0, 1, 0, 1, 0, 1] = TW5 [1, 1, 0] := by
  calc
    TW5 [0, 1, 0, 1, 0, 1, 0, 1] = TW5 [0, 1, 0, 1, 0, 1, 0, 1, 0, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0).symm
    _ = TW5 [1, 1, 0] :=
      sphericalTriangleWord_replace 2 3 5 [] [0]
          (a := [0, 1, 0, 1, 0, 1, 0, 1, 0]) (b := [1, 1]) triangleRule5_3

private theorem triangleRule5_6 : TW5 [1, 0, 1, 0, 1, 0, 1, 0] = TW5 [0, 1, 1] := by
  calc
    TW5 [1, 0, 1, 0, 1, 0, 1, 0] = TW5 [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 0, 1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule5_0).symm
    _ = TW5 [0, 1, 1] :=
      sphericalTriangleWord_replace 2 3 5 [0] []
          (a := [0, 1, 0, 1, 0, 1, 0, 1, 0]) (b := [1, 1]) triangleRule5_3

private theorem triangleRule5_7 : TW5 [0, 1, 0, 1, 0, 1, 0] = TW5 [1, 1, 0, 1, 1] := by
  calc
    TW5 [0, 1, 0, 1, 0, 1, 0] = TW5 [0, 1, 0, 1, 0, 1, 0, 1, 1, 1] :=
      (sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1).symm
    _ = TW5 [1, 1, 0, 1, 1] :=
      sphericalTriangleWord_replace 2 3 5 [] [1, 1]
          (a := [0, 1, 0, 1, 0, 1, 0, 1]) (b := [1, 1, 0]) triangleRule5_5

private theorem triangleRule5_8 : TW5 [1, 0, 1, 0, 1, 0, 1] = TW5 [0, 1, 1, 0] := by
  calc
    TW5 [1, 0, 1, 0, 1, 0, 1] = TW5 [0, 0, 1, 0, 1, 0, 1, 0, 1] :=
      (sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0).symm
    _ = TW5 [0, 1, 1, 0] :=
      sphericalTriangleWord_replace 2 3 5 [0] []
          (a := [0, 1, 0, 1, 0, 1, 0, 1]) (b := [1, 1, 0]) triangleRule5_5

private theorem triangleRule5_9 : TW5 [1, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 1, 0, 1] := by
  calc
    TW5 [1, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 1, 0, 1, 0, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [] [0]
          (a := [0, 1, 0, 1, 0, 1, 0]) (b := [1, 1, 0, 1, 1]) triangleRule5_7).symm
    _ = TW5 [0, 1, 0, 1, 0, 1] :=
      sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0

private theorem triangleRule5_10 : TW5 [1, 0, 1, 0, 1, 0] = TW5 [0, 1, 1, 0, 1, 1] := by
  calc
    TW5 [1, 0, 1, 0, 1, 0] = TW5 [0, 0, 1, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule5_0).symm
    _ = TW5 [0, 1, 1, 0, 1, 1] :=
      sphericalTriangleWord_replace 2 3 5 [0] []
          (a := [0, 1, 0, 1, 0, 1, 0]) (b := [1, 1, 0, 1, 1]) triangleRule5_7

private theorem triangleRule5_11 :
    TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [1, 1, 0, 1, 0, 1, 1, 0] := by
  calc
    TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] :=
      (sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 0, 1]
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9).symm
    _ = TW5 [1, 1, 0, 1, 0, 1, 1, 0] :=
      sphericalTriangleWord_replace 2 3 5 [1, 1, 0, 1] []
          (a := [1, 0, 1, 0, 1, 0, 1]) (b := [0, 1, 1, 0]) triangleRule5_8

private theorem triangleRule5_12 :
    TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0] := by
  calc
    TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1] :=
      (sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 0, 1] [1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0).symm
    _ = TW5 [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 0, 1, 0] []
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9).symm
    _ = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0] :=
      sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 1, 0]
          (a := [1, 0, 1, 0, 1, 0, 1]) (b := [0, 1, 1, 0]) triangleRule5_8

private theorem triangleRule5_13 :
    TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0] := by
  calc
    TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [1, 1, 0, 1, 1, 0, 1, 0, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [1, 1, 0, 1] []
          (a := [1, 0, 1, 0, 1, 0]) (b := [0, 1, 1, 0, 1, 1]) triangleRule5_10).symm
    _ = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0] :=
      sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 0]
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9

private theorem triangleRule5_14 :
    TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] := by
  calc
    TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [1] [1, 0]
          (a := [1, 0, 1, 0, 1, 1, 0, 1, 0, 1])
            (b := [0, 1, 1, 0, 1, 0, 1, 1, 0]) triangleRule5_12).symm
    _ = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] :=
      (sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 1, 0]
          (a := [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1])
            (b := [1, 1, 0, 1, 0, 1, 1, 0]) triangleRule5_11).symm
    _ = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1] :=
      sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0] []
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9
    _ = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1] :=
      sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1] [1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0
    _ = TW5 [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1] :=
      sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0] [1, 0, 1]
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9
    _ = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] :=
      sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1] [1, 0, 1, 0, 1, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0

private def triangleNormals5 (i : Fin 60) : List (Fin 2) :=
  match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [0, 1]
  | 4 => [1, 0]
  | 5 => [1, 1]
  | 6 => [0, 1, 0]
  | 7 => [0, 1, 1]
  | 8 => [1, 0, 1]
  | 9 => [1, 1, 0]
  | 10 => [0, 1, 0, 1]
  | 11 => [0, 1, 1, 0]
  | 12 => [1, 0, 1, 0]
  | 13 => [1, 0, 1, 1]
  | 14 => [1, 1, 0, 1]
  | 15 => [0, 1, 0, 1, 0]
  | 16 => [0, 1, 0, 1, 1]
  | 17 => [0, 1, 1, 0, 1]
  | 18 => [1, 0, 1, 0, 1]
  | 19 => [1, 0, 1, 1, 0]
  | 20 => [1, 1, 0, 1, 0]
  | 21 => [1, 1, 0, 1, 1]
  | 22 => [0, 1, 0, 1, 0, 1]
  | 23 => [0, 1, 0, 1, 1, 0]
  | 24 => [0, 1, 1, 0, 1, 0]
  | 25 => [0, 1, 1, 0, 1, 1]
  | 26 => [1, 0, 1, 0, 1, 1]
  | 27 => [1, 0, 1, 1, 0, 1]
  | 28 => [1, 1, 0, 1, 0, 1]
  | 29 => [0, 1, 0, 1, 0, 1, 1]
  | 30 => [0, 1, 0, 1, 1, 0, 1]
  | 31 => [0, 1, 1, 0, 1, 0, 1]
  | 32 => [1, 0, 1, 0, 1, 1, 0]
  | 33 => [1, 0, 1, 1, 0, 1, 0]
  | 34 => [1, 0, 1, 1, 0, 1, 1]
  | 35 => [1, 1, 0, 1, 0, 1, 1]
  | 36 => [0, 1, 0, 1, 0, 1, 1, 0]
  | 37 => [0, 1, 0, 1, 1, 0, 1, 0]
  | 38 => [0, 1, 0, 1, 1, 0, 1, 1]
  | 39 => [0, 1, 1, 0, 1, 0, 1, 1]
  | 40 => [1, 0, 1, 0, 1, 1, 0, 1]
  | 41 => [1, 0, 1, 1, 0, 1, 0, 1]
  | 42 => [1, 1, 0, 1, 0, 1, 1, 0]
  | 43 => [0, 1, 0, 1, 0, 1, 1, 0, 1]
  | 44 => [0, 1, 0, 1, 1, 0, 1, 0, 1]
  | 45 => [0, 1, 1, 0, 1, 0, 1, 1, 0]
  | 46 => [1, 0, 1, 0, 1, 1, 0, 1, 0]
  | 47 => [1, 0, 1, 0, 1, 1, 0, 1, 1]
  | 48 => [1, 0, 1, 1, 0, 1, 0, 1, 1]
  | 49 => [1, 1, 0, 1, 0, 1, 1, 0, 1]
  | 50 => [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]
  | 51 => [0, 1, 0, 1, 0, 1, 1, 0, 1, 1]
  | 52 => [0, 1, 0, 1, 1, 0, 1, 0, 1, 1]
  | 53 => [0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
  | 54 => [1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
  | 55 => [1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
  | 56 => [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
  | 57 => [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
  | 58 => [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
  | 59 => [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
  | _ => []

private theorem triangleNormalStep5_0 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 0) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨1, ?_⟩
    change TW5 [] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [] [0]]
    change TW5 [0] = TW5 [0]
    rfl
  · refine ⟨2, ?_⟩
    change TW5 [] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [] [1]]
    change TW5 [1] = TW5 [1]
    rfl

private theorem triangleNormalStep5_1 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 1) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨0, ?_⟩
    change TW5 [0] * sphericalTriangleGenerator 2 3 5 0 = TW5 []
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0] [0]]
    change TW5 [0, 0] = TW5 []
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨3, ?_⟩
    change TW5 [0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0] [1]]
    change TW5 [0, 1] = TW5 [0, 1]
    rfl

private theorem triangleNormalStep5_2 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 2) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨4, ?_⟩
    change TW5 [1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1] [0]]
    change TW5 [1, 0] = TW5 [1, 0]
    rfl
  · refine ⟨5, ?_⟩
    change TW5 [1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1] [1]]
    change TW5 [1, 1] = TW5 [1, 1]
    rfl

private theorem triangleNormalStep5_3 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 3) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨6, ?_⟩
    change TW5 [0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1] [0]]
    change TW5 [0, 1, 0] = TW5 [0, 1, 0]
    rfl
  · refine ⟨7, ?_⟩
    change TW5 [0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1] [1]]
    change TW5 [0, 1, 1] = TW5 [0, 1, 1]
    rfl

private theorem triangleNormalStep5_4 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 4) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨2, ?_⟩
    change TW5 [1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0] [0]]
    change TW5 [1, 0, 0] = TW5 [1]
    exact sphericalTriangleWord_replace 2 3 5 [1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨8, ?_⟩
    change TW5 [1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0] [1]]
    change TW5 [1, 0, 1] = TW5 [1, 0, 1]
    rfl

private theorem triangleNormalStep5_5 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 5) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨9, ?_⟩
    change TW5 [1, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1] [0]]
    change TW5 [1, 1, 0] = TW5 [1, 1, 0]
    rfl
  · refine ⟨0, ?_⟩
    change TW5 [1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 []
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1] [1]]
    change TW5 [1, 1, 1] = TW5 []
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_6 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 6) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨3, ?_⟩
    change TW5 [0, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0] [0]]
    change TW5 [0, 1, 0, 0] = TW5 [0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨10, ?_⟩
    change TW5 [0, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0] [1]]
    change TW5 [0, 1, 0, 1] = TW5 [0, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_7 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 7) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨11, ?_⟩
    change TW5 [0, 1, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1] [0]]
    change TW5 [0, 1, 1, 0] = TW5 [0, 1, 1, 0]
    rfl
  · refine ⟨1, ?_⟩
    change TW5 [0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1] [1]]
    change TW5 [0, 1, 1, 1] = TW5 [0]
    exact sphericalTriangleWord_replace 2 3 5 [0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_8 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 8) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨12, ?_⟩
    change TW5 [1, 0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1] [0]]
    change TW5 [1, 0, 1, 0] = TW5 [1, 0, 1, 0]
    rfl
  · refine ⟨13, ?_⟩
    change TW5 [1, 0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1] [1]]
    change TW5 [1, 0, 1, 1] = TW5 [1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_9 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 9) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨5, ?_⟩
    change TW5 [1, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0] [0]]
    change TW5 [1, 1, 0, 0] = TW5 [1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨14, ?_⟩
    change TW5 [1, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0] [1]]
    change TW5 [1, 1, 0, 1] = TW5 [1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_10 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 10) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨15, ?_⟩
    change TW5 [0, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1] [0]]
    change TW5 [0, 1, 0, 1, 0] = TW5 [0, 1, 0, 1, 0]
    rfl
  · refine ⟨16, ?_⟩
    change TW5 [0, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1] [1]]
    change TW5 [0, 1, 0, 1, 1] = TW5 [0, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_11 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 11) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨7, ?_⟩
    change TW5 [0, 1, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0] [0]]
    change TW5 [0, 1, 1, 0, 0] = TW5 [0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨17, ?_⟩
    change TW5 [0, 1, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0] [1]]
    change TW5 [0, 1, 1, 0, 1] = TW5 [0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_12 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 12) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨8, ?_⟩
    change TW5 [1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0] [0]]
    change TW5 [1, 0, 1, 0, 0] = TW5 [1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨18, ?_⟩
    change TW5 [1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0] [1]]
    change TW5 [1, 0, 1, 0, 1] = TW5 [1, 0, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_13 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 13) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨19, ?_⟩
    change TW5 [1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1] [0]]
    change TW5 [1, 0, 1, 1, 0] = TW5 [1, 0, 1, 1, 0]
    rfl
  · refine ⟨4, ?_⟩
    change TW5 [1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1] [1]]
    change TW5 [1, 0, 1, 1, 1] = TW5 [1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_14 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 14) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨20, ?_⟩
    change TW5 [1, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1] [0]]
    change TW5 [1, 1, 0, 1, 0] = TW5 [1, 1, 0, 1, 0]
    rfl
  · refine ⟨21, ?_⟩
    change TW5 [1, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1] [1]]
    change TW5 [1, 1, 0, 1, 1] = TW5 [1, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_15 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 15) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨10, ?_⟩
    change TW5 [0, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0] [0]]
    change TW5 [0, 1, 0, 1, 0, 0] = TW5 [0, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨22, ?_⟩
    change TW5 [0, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0] [1]]
    change TW5 [0, 1, 0, 1, 0, 1] = TW5 [0, 1, 0, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_16 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 16) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨23, ?_⟩
    change TW5 [0, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1] [0]]
    change TW5 [0, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 1, 1, 0]
    rfl
  · refine ⟨6, ?_⟩
    change TW5 [0, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1] [1]]
    change TW5 [0, 1, 0, 1, 1, 1] = TW5 [0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_17 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 17) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨24, ?_⟩
    change TW5 [0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1] [0]]
    change TW5 [0, 1, 1, 0, 1, 0] = TW5 [0, 1, 1, 0, 1, 0]
    rfl
  · refine ⟨25, ?_⟩
    change TW5 [0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1] [1]]
    change TW5 [0, 1, 1, 0, 1, 1] = TW5 [0, 1, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_18 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 18) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨25, ?_⟩
    change TW5 [1, 0, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1] [0]]
    change TW5 [1, 0, 1, 0, 1, 0] = TW5 [0, 1, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [1, 0, 1, 0, 1, 0]) (b := [0, 1, 1, 0, 1, 1]) triangleRule5_10
  · refine ⟨26, ?_⟩
    change TW5 [1, 0, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1] [1]]
    change TW5 [1, 0, 1, 0, 1, 1] = TW5 [1, 0, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_19 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 19) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨13, ?_⟩
    change TW5 [1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0] [0]]
    change TW5 [1, 0, 1, 1, 0, 0] = TW5 [1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨27, ?_⟩
    change TW5 [1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0] [1]]
    change TW5 [1, 0, 1, 1, 0, 1] = TW5 [1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_20 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 20) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨14, ?_⟩
    change TW5 [1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0] [0]]
    change TW5 [1, 1, 0, 1, 0, 0] = TW5 [1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨28, ?_⟩
    change TW5 [1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0] [1]]
    change TW5 [1, 1, 0, 1, 0, 1] = TW5 [1, 1, 0, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_21 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 21) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨22, ?_⟩
    change TW5 [1, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 1] [0]]
    change TW5 [1, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9
  · refine ⟨9, ?_⟩
    change TW5 [1, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 1] [1]]
    change TW5 [1, 1, 0, 1, 1, 1] = TW5 [1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [1, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_22 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 22) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨21, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1] [0]]
    change TW5 [0, 1, 0, 1, 0, 1, 0] = TW5 [1, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [0, 1, 0, 1, 0, 1, 0]) (b := [1, 1, 0, 1, 1]) triangleRule5_7
  · refine ⟨29, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1] [1]]
    change TW5 [0, 1, 0, 1, 0, 1, 1] = TW5 [0, 1, 0, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_23 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 23) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨16, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0] [0]]
    change TW5 [0, 1, 0, 1, 1, 0, 0] = TW5 [0, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨30, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0] [1]]
    change TW5 [0, 1, 0, 1, 1, 0, 1] = TW5 [0, 1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_24 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 24) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨17, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0] [0]]
    change TW5 [0, 1, 1, 0, 1, 0, 0] = TW5 [0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨31, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0] [1]]
    change TW5 [0, 1, 1, 0, 1, 0, 1] = TW5 [0, 1, 1, 0, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_25 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 25) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨18, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 1] [0]]
    change TW5 [0, 1, 1, 0, 1, 1, 0] = TW5 [1, 0, 1, 0, 1]
    calc
      TW5 [0, 1, 1, 0, 1, 1, 0] = TW5 [0, 0, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [0] []
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9
      _ = TW5 [1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨11, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 1] [1]]
    change TW5 [0, 1, 1, 0, 1, 1, 1] = TW5 [0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_26 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 26) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨32, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1] [0]]
    change TW5 [1, 0, 1, 0, 1, 1, 0] = TW5 [1, 0, 1, 0, 1, 1, 0]
    rfl
  · refine ⟨12, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1] [1]]
    change TW5 [1, 0, 1, 0, 1, 1, 1] = TW5 [1, 0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_27 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 27) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨33, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1] [0]]
    change TW5 [1, 0, 1, 1, 0, 1, 0] = TW5 [1, 0, 1, 1, 0, 1, 0]
    rfl
  · refine ⟨34, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1] [1]]
    change TW5 [1, 0, 1, 1, 0, 1, 1] = TW5 [1, 0, 1, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_28 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 28) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨34, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1] [0]]
    change TW5 [1, 1, 0, 1, 0, 1, 0] = TW5 [1, 0, 1, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1] []
          (a := [1, 0, 1, 0, 1, 0]) (b := [0, 1, 1, 0, 1, 1]) triangleRule5_10
  · refine ⟨35, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1] [1]]
    change TW5 [1, 1, 0, 1, 0, 1, 1] = TW5 [1, 1, 0, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_29 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 29) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨36, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1] [0]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 1, 0, 1, 1, 0]
    rfl
  · refine ⟨15, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1] [1]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 1] = TW5 [0, 1, 0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_30 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 30) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨37, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1] [0]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0] = TW5 [0, 1, 0, 1, 1, 0, 1, 0]
    rfl
  · refine ⟨38, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1] [1]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 1] = TW5 [0, 1, 0, 1, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_31 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 31) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨38, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1] [0]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 0] = TW5 [0, 1, 0, 1, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1] []
          (a := [1, 0, 1, 0, 1, 0]) (b := [0, 1, 1, 0, 1, 1]) triangleRule5_10
  · refine ⟨39, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1] [1]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1] = TW5 [0, 1, 1, 0, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_32 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 32) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨26, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1, 0] [0]]
    change TW5 [1, 0, 1, 0, 1, 1, 0, 0] = TW5 [1, 0, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨40, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1, 0] [1]]
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1] = TW5 [1, 0, 1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_33 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 33) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨27, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0] [0]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 0] = TW5 [1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨41, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0] [1]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1] = TW5 [1, 0, 1, 1, 0, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_34 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 34) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨28, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 1] [0]]
    change TW5 [1, 0, 1, 1, 0, 1, 1, 0] = TW5 [1, 1, 0, 1, 0, 1]
    calc
      TW5 [1, 0, 1, 1, 0, 1, 1, 0] = TW5 [1, 0, 0, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [1, 0] []
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9
      _ = TW5 [1, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [1] [1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨19, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 1] [1]]
    change TW5 [1, 0, 1, 1, 0, 1, 1, 1] = TW5 [1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_35 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 35) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨42, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1, 1] [0]]
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0] = TW5 [1, 1, 0, 1, 0, 1, 1, 0]
    rfl
  · refine ⟨20, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1, 1] * sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1, 1] [1]]
    change TW5 [1, 1, 0, 1, 0, 1, 1, 1] = TW5 [1, 1, 0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [1, 1, 0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_36 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 36) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨29, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0] [0]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 0] = TW5 [0, 1, 0, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨43, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0] [1]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1] = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_37 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 37) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨30, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0] [0]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 0] = TW5 [0, 1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨44, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0] [1]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_38 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 38) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨31, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 1] [0]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 1, 0] = TW5 [0, 1, 1, 0, 1, 0, 1]
    calc
      TW5 [0, 1, 0, 1, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 0, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [0, 1, 0] []
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9
      _ = TW5 [0, 1, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [0, 1] [1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨23, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 1] [1]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 1, 1] = TW5 [0, 1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_39 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 39) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨45, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1] [0]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0] = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0]
    rfl
  · refine ⟨24, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1] [1]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 1] = TW5 [0, 1, 1, 0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 1, 0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_40 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 40) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨46, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1, 0, 1] [0]]
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0]
    rfl
  · refine ⟨47, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1, 0, 1] [1]]
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_41 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 41) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨47, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1] [0]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 0] = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1] []
          (a := [1, 0, 1, 0, 1, 0]) (b := [0, 1, 1, 0, 1, 1]) triangleRule5_10
  · refine ⟨48, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1] [1]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1] = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_42 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 42) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨35, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1, 1, 0] [0]]
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 0] = TW5 [1, 1, 0, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 1, 0, 1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨49, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1, 1, 0] [1]]
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1] = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_43 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 43) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨50, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1] [0]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rfl
  · refine ⟨51, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1] [1]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_44 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 44) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨51, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1] [0]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 0] = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1] []
          (a := [1, 0, 1, 0, 1, 0]) (b := [0, 1, 1, 0, 1, 1]) triangleRule5_10
  · refine ⟨52, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1] [1]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1]
    rfl

private theorem triangleNormalStep5_45 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 45) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨39, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1, 0] [0]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 0] = TW5 [0, 1, 1, 0, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨53, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1, 0] [1]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1] = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_46 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 46) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨40, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1, 0, 1, 0] [0]]
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0, 0] = TW5 [1, 0, 1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 0, 1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨45, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1, 0, 1, 0] [1]]
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [1, 0, 1, 0, 1, 1, 0, 1, 0, 1]) (b := [0, 1, 1, 0, 1, 0, 1, 1, 0]) triangleRule5_12

private theorem triangleNormalStep5_47 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 47) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨41, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1, 0, 1, 1] [0]]
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1, 0] = TW5 [1, 0, 1, 1, 0, 1, 0, 1]
    calc
      TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1, 0] = TW5 [1, 0, 1, 0, 0, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 0] []
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9
      _ = TW5 [1, 0, 1, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [1, 0, 1] [1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨32, ?_⟩
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 0, 1, 1, 0, 1, 1] [1]]
    change TW5 [1, 0, 1, 0, 1, 1, 0, 1, 1, 1] = TW5 [1, 0, 1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 0, 1, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_48 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 48) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨54, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1, 1] [0]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0] = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
    rfl
  · refine ⟨33, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1, 1] [1]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 1] = TW5 [1, 0, 1, 1, 0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 1, 0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_49 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 49) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨55, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1, 1, 0, 1] [0]]
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rfl
  · refine ⟨50, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1, 1, 0, 1] [1]]
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [1, 1, 0, 1, 0, 1, 1, 0, 1, 1])
            (b := [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]) triangleRule5_13

private theorem triangleNormalStep5_50 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 50) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨43, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0] [0]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] = TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨42, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0] [1]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [1, 1, 0, 1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]) (b := [1, 1, 0, 1, 0, 1, 1, 0]) triangleRule5_11

private theorem triangleNormalStep5_51 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 51) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨44, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1] [0]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1]
    calc
      TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0] []
          (a := [1, 1, 0, 1, 1, 0]) (b := [0, 1, 0, 1, 0, 1]) triangleRule5_9
      _ = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1] [1, 0, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨36, ?_⟩
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1] [1]]
    change TW5 [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1] = TW5 [0, 1, 0, 1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 0, 1, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_52 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 52) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨56, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1] [0]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
    rfl
  · refine ⟨37, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1] [1]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1] = TW5 [0, 1, 0, 1, 1, 0, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0] []
          (a := [1, 1, 1]) (b := []) triangleRule5_1

private theorem triangleNormalStep5_53 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 53) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨57, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1] [0]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rfl
  · refine ⟨46, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1] [1]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0]
    calc
      TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 5 [0] []
          (a := [1, 1, 0, 1, 0, 1, 1, 0, 1, 1])
            (b := [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]) triangleRule5_13
      _ = TW5 [1, 0, 1, 0, 1, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 0, 1, 1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule5_0

private theorem triangleNormalStep5_54 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 54) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨48, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0] [0]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨58, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0] [1]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_55 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 55) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨49, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0] [0]]
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [1, 1, 0, 1, 0, 1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨54, ?_⟩
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0] [1]]
    change TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [1] []
          (a := [1, 0, 1, 0, 1, 1, 0, 1, 0, 1]) (b := [0, 1, 1, 0, 1, 0, 1, 1, 0]) triangleRule5_12

private theorem triangleNormalStep5_56 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 56) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨52, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0] [0]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨59, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0] [1]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rfl

private theorem triangleNormalStep5_57 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 57) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨53, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] [0]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1] []
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨56, ?_⟩
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] [1]]
    change TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]
    exact sphericalTriangleWord_replace 2 3 5 [0, 1] []
          (a := [1, 0, 1, 0, 1, 1, 0, 1, 0, 1]) (b := [0, 1, 1, 0, 1, 0, 1, 1, 0]) triangleRule5_12

private theorem triangleNormalStep5_58 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 58) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨59, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] [0]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    exact sphericalTriangleWord_replace 2 3 5 [] []
          (a := [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0])
            (b := [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]) triangleRule5_14
  · refine ⟨55, ?_⟩
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] [1]]
    change TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    calc
      TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 5 [1, 0] []
          (a := [1, 1, 0, 1, 0, 1, 1, 0, 1, 1])
            (b := [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]) triangleRule5_13
      _ = TW5 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 5 [1] [1, 0, 1, 0, 1, 1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule5_0

private theorem triangleNormalStep5_59 (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 59) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases g
  · refine ⟨58, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 0 = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    rw [← sphericalTriangleWord_singleton 2 3 5 0,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] [0]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
    calc
      TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] = TW5 [0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [0] []
          (a := [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0])
            (b := [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]) triangleRule5_14
      _ = TW5 [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] :=
        sphericalTriangleWord_replace 2 3 5 [] [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
          (a := [0, 0]) (b := []) triangleRule5_0
  · refine ⟨57, ?_⟩
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] *
      sphericalTriangleGenerator 2 3 5 1 = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    rw [← sphericalTriangleWord_singleton 2 3 5 1,
      ← sphericalTriangleWord_append 2 3 5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] [1]]
    change TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]
    calc
      TW5 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = TW5 [0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 5 [0, 1, 0] []
          (a := [1, 1, 0, 1, 0, 1, 1, 0, 1, 1])
            (b := [0, 1, 0, 1, 0, 1, 1, 0, 1, 0]) triangleRule5_13
      _ = TW5 [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0] :=
        sphericalTriangleWord_replace 2 3 5 [0, 1] [1, 0, 1, 0, 1, 1, 0, 1, 0]
          (a := [0, 0]) (b := []) triangleRule5_0

private theorem triangleNormals5_closed (i : Fin 60) (g : Fin 2) :
    ∃ j : Fin 60, TW5 (triangleNormals5 i) * sphericalTriangleGenerator 2 3 5 g =
      TW5 (triangleNormals5 j) := by
  fin_cases i
  · exact triangleNormalStep5_0 g
  · exact triangleNormalStep5_1 g
  · exact triangleNormalStep5_2 g
  · exact triangleNormalStep5_3 g
  · exact triangleNormalStep5_4 g
  · exact triangleNormalStep5_5 g
  · exact triangleNormalStep5_6 g
  · exact triangleNormalStep5_7 g
  · exact triangleNormalStep5_8 g
  · exact triangleNormalStep5_9 g
  · exact triangleNormalStep5_10 g
  · exact triangleNormalStep5_11 g
  · exact triangleNormalStep5_12 g
  · exact triangleNormalStep5_13 g
  · exact triangleNormalStep5_14 g
  · exact triangleNormalStep5_15 g
  · exact triangleNormalStep5_16 g
  · exact triangleNormalStep5_17 g
  · exact triangleNormalStep5_18 g
  · exact triangleNormalStep5_19 g
  · exact triangleNormalStep5_20 g
  · exact triangleNormalStep5_21 g
  · exact triangleNormalStep5_22 g
  · exact triangleNormalStep5_23 g
  · exact triangleNormalStep5_24 g
  · exact triangleNormalStep5_25 g
  · exact triangleNormalStep5_26 g
  · exact triangleNormalStep5_27 g
  · exact triangleNormalStep5_28 g
  · exact triangleNormalStep5_29 g
  · exact triangleNormalStep5_30 g
  · exact triangleNormalStep5_31 g
  · exact triangleNormalStep5_32 g
  · exact triangleNormalStep5_33 g
  · exact triangleNormalStep5_34 g
  · exact triangleNormalStep5_35 g
  · exact triangleNormalStep5_36 g
  · exact triangleNormalStep5_37 g
  · exact triangleNormalStep5_38 g
  · exact triangleNormalStep5_39 g
  · exact triangleNormalStep5_40 g
  · exact triangleNormalStep5_41 g
  · exact triangleNormalStep5_42 g
  · exact triangleNormalStep5_43 g
  · exact triangleNormalStep5_44 g
  · exact triangleNormalStep5_45 g
  · exact triangleNormalStep5_46 g
  · exact triangleNormalStep5_47 g
  · exact triangleNormalStep5_48 g
  · exact triangleNormalStep5_49 g
  · exact triangleNormalStep5_50 g
  · exact triangleNormalStep5_51 g
  · exact triangleNormalStep5_52 g
  · exact triangleNormalStep5_53 g
  · exact triangleNormalStep5_54 g
  · exact triangleNormalStep5_55 g
  · exact triangleNormalStep5_56 g
  · exact triangleNormalStep5_57 g
  · exact triangleNormalStep5_58 g
  · exact triangleNormalStep5_59 g

theorem finite_sphericalTriangleGroup_2_3_5 : Finite (SphericalTriangleGroup 2 3 5) :=
  finite_of_sphericalTriangleNormalWords 2 3 5 (by decide) (by decide)
    triangleNormals5 ⟨0, rfl⟩ triangleNormals5_closed

def sphericalTriangleHom {G : Type*} [Group G] (p q r : ℕ) (x y : G)
    (hx : x ^ p = 1) (hy : y ^ q = 1) (hxy : (y * x) ^ r = 1) :
    SphericalTriangleGroup p q r →* G :=
  PresentedGroup.toGroup (f := ![x, y]) (by
    intro w hw
    simp only [sphericalTriangleRelators, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero] using hx
    · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hy
    · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of,
        Matrix.cons_val_zero, Matrix.cons_val_one] using hxy)

@[simp] theorem sphericalTriangleHom_X {G : Type*} [Group G] (p q r : ℕ) (x y : G)
    (hx : x ^ p = 1) (hy : y ^ q = 1) (hxy : (y * x) ^ r = 1) :
    sphericalTriangleHom p q r x y hx hy hxy (sphericalTriangleX p q r) = x := by
  exact PresentedGroup.toGroup.of _

@[simp] theorem sphericalTriangleHom_Y {G : Type*} [Group G] (p q r : ℕ) (x y : G)
    (hx : x ^ p = 1) (hy : y ^ q = 1) (hxy : (y * x) ^ r = 1) :
    sphericalTriangleHom p q r x y hx hy hxy (sphericalTriangleY p q r) = y := by
  exact PresentedGroup.toGroup.of _

private def triangleSwapFirst (p q r : ℕ) :
    SphericalTriangleGroup p q r →* SphericalTriangleGroup q p r :=
  sphericalTriangleHom p q r (sphericalTriangleY q p r)⁻¹ (sphericalTriangleX q p r)⁻¹
    (by rw [inv_pow, sphericalTriangleY_pow, inv_one])
    (by rw [inv_pow, sphericalTriangleX_pow, inv_one])
    (by rw [← mul_inv_rev, inv_pow, sphericalTriangleYX_pow, inv_one])

private theorem triangleSwapFirst_left (p q r : ℕ) :
    (triangleSwapFirst q p r).comp (triangleSwapFirst p q r) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  fin_cases i <;> simp [triangleSwapFirst, MonoidHom.comp_apply]

private def triangleSwapLast (p q r : ℕ) :
    SphericalTriangleGroup p q r →* SphericalTriangleGroup p r q :=
  sphericalTriangleHom p q r (sphericalTriangleX p r q)⁻¹
    (sphericalTriangleY p r q * sphericalTriangleX p r q)
    (by rw [inv_pow, sphericalTriangleX_pow, inv_one])
    (sphericalTriangleYX_pow p r q)
    (by simpa only [mul_assoc, mul_inv_cancel, mul_one] using sphericalTriangleY_pow p r q)

private theorem triangleSwapLast_left (p q r : ℕ) :
    (triangleSwapLast p r q).comp (triangleSwapLast p q r) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  fin_cases i <;> simp [triangleSwapLast, MonoidHom.comp_apply, mul_assoc]

def sphericalTriangleSwapFirst (p q r : ℕ) :
    SphericalTriangleGroup p q r ≃* SphericalTriangleGroup q p r where
  toFun := triangleSwapFirst p q r
  invFun := triangleSwapFirst q p r
  left_inv g := congrArg (fun f => f g) (triangleSwapFirst_left p q r)
  right_inv g := congrArg (fun f => f g) (triangleSwapFirst_left q p r)
  map_mul' := (triangleSwapFirst p q r).map_mul

def sphericalTriangleSwapLast (p q r : ℕ) :
    SphericalTriangleGroup p q r ≃* SphericalTriangleGroup p r q where
  toFun := triangleSwapLast p q r
  invFun := triangleSwapLast p r q
  left_inv g := congrArg (fun f => f g) (triangleSwapLast_left p q r)
  right_inv g := congrArg (fun f => f g) (triangleSwapLast_left p r q)
  map_mul' := (triangleSwapLast p q r).map_mul

private theorem triangle_involution_inv {G : Type*} [Group G] {x : G} (hx : x ^ 2 = 1) :
    x⁻¹ = x := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using hx

private theorem triangle_involution_rotation {G : Type*} [Group G] {x y : G}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (k : ℤ) :
    x * (y * x) ^ k = (y * x) ^ (-k) * x := by
  have hxi := triangle_involution_inv hx
  have hyi := triangle_involution_inv hy
  have hconj : x * (y * x) * x⁻¹ = (y * x)⁻¹ := by
    simp [mul_assoc, mul_inv_rev, hxi, hyi, ← pow_two, hx]
  have h := congrArg (fun g => g * x)
    (@conj_zpow G _ k x (y * x)).symm
  rw [hconj, inv_zpow, ← zpow_neg] at h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

theorem finite_sphericalTriangleGroup_2_2 (n : ℕ) (hn : 0 < n) :
    Finite (SphericalTriangleGroup 2 2 n) := by
  let x := sphericalTriangleX 2 2 n
  let y := sphericalTriangleY 2 2 n
  let z := y * x
  have hx : x ^ 2 = 1 := sphericalTriangleX_pow 2 2 n
  have hy : y ^ 2 = 1 := sphericalTriangleY_pow 2 2 n
  have hz : z ^ n = 1 := sphericalTriangleYX_pow 2 2 n
  have hfinite : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hz⟩
  have hnormal : ∀ g : SphericalTriangleGroup 2 2 n,
      ∃ k : ℤ, ∃ b : Bool, g = z ^ k * (if b then x else 1) := by
    intro g
    obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective (sphericalTriangleRelators 2 2 n) g
    have hfree : ∀ w : FreeGroup (Fin 2), ∃ k : ℤ, ∃ b : Bool,
        PresentedGroup.mk (sphericalTriangleRelators 2 2 n) w =
          z ^ k * (if b then x else 1) := by
      intro w
      induction w with
      | one => exact ⟨0, false, by simp⟩
      | of a =>
        fin_cases a
        · exact ⟨0, true, by simp [x, PresentedGroup.of]⟩
        · exact ⟨1, true, by simp [z, y, mul_assoc, ← pow_two, hx,
            PresentedGroup.of]⟩
      | inv_of a ha =>
        obtain ⟨k, b, hb⟩ := ha
        have hi : (PresentedGroup.mk (sphericalTriangleRelators 2 2 n) (FreeGroup.of a))⁻¹ =
            PresentedGroup.mk (sphericalTriangleRelators 2 2 n) (FreeGroup.of a) := by
          fin_cases a
          · exact triangle_involution_inv hx
          · exact triangle_involution_inv hy
        exact ⟨k, b, by rw [map_inv, hi, hb]⟩
      | mul a b ha hb =>
        obtain ⟨k, c, hk⟩ := ha
        obtain ⟨l, e, hl⟩ := hb
        rw [map_mul, hk, hl]
        cases c <;> cases e
        · exact ⟨k + l, false, by simp [zpow_add]⟩
        · exact ⟨k + l, true, by simp [zpow_add, mul_assoc]⟩
        · refine ⟨k - l, true, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
          rw [mul_assoc, triangle_involution_rotation hx hy, ← mul_assoc, ← zpow_add]
          simp only [sub_eq_add_neg]
        · refine ⟨k - l, false, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
          rw [mul_assoc, ← mul_assoc x, triangle_involution_rotation hx hy,
            mul_assoc _ _ x, ← pow_two, hx, mul_one, ← zpow_add]
          simp only [sub_eq_add_neg]
    exact hfree w
  let : Finite (Subgroup.zpowers z) :=
    (hfinite.powers_eq_zpowers ▸ hfinite.finite_powers).to_subtype
  apply Finite.of_surjective (fun a : Subgroup.zpowers z × Bool =>
    a.1.val * (if a.2 then x else 1))
  intro g
  obtain ⟨k, b, rfl⟩ := hnormal g
  exact ⟨(⟨z ^ k, Subgroup.zpow_mem_zpowers z k⟩, b), rfl⟩

private theorem triangle_reciprocal_le (m n : ℕ) (hn : 0 < n) (h : n ≤ m) :
    (1 : ℚ) / m ≤ 1 / n :=
  one_div_le_one_div_of_le (by exact_mod_cast hn) (by exact_mod_cast h)

private theorem finite_triangle_2_3 (r : ℕ) (hr : 3 ≤ r)
    (hchi : (1 : ℚ) < 1 / 2 + 1 / 3 + 1 / r) :
    Finite (SphericalTriangleGroup 2 3 r) := by
  have hb : r ≤ 5 := by
    by_contra h
    have he := triangle_reciprocal_le r 6 (by decide) (by omega)
    norm_num at he hchi
    linarith
  have he : r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases he with rfl | rfl | rfl
  · exact finite_sphericalTriangleGroup_2_3_3
  · exact finite_sphericalTriangleGroup_2_3_4
  · exact finite_sphericalTriangleGroup_2_3_5

private theorem finite_triangle_2 (q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hchi : (1 : ℚ) < 1 / 2 + 1 / q + 1 / r) :
    Finite (SphericalTriangleGroup 2 q r) := by
  by_cases hq2 : q = 2
  · subst q
    exact finite_sphericalTriangleGroup_2_2 r (by omega)
  by_cases hr2 : r = 2
  · subst r
    have : Finite (SphericalTriangleGroup 2 2 q) :=
      finite_sphericalTriangleGroup_2_2 q (by omega)
    exact Finite.of_equiv _ (sphericalTriangleSwapLast 2 2 q).toEquiv
  have hq3 : 3 ≤ q := by omega
  have hr3 : 3 ≤ r := by omega
  have he : q = 3 ∨ r = 3 := by
    by_contra! h
    have heq := triangle_reciprocal_le q 4 (by decide) (by omega)
    have her := triangle_reciprocal_le r 4 (by decide) (by omega)
    norm_num at heq her hchi
    linarith
  rcases he with rfl | rfl
  · exact finite_triangle_2_3 r hr3 hchi
  · have : Finite (SphericalTriangleGroup 2 3 q) :=
      finite_triangle_2_3 q hq3 (by linarith)
    exact Finite.of_equiv _ (sphericalTriangleSwapLast 2 3 q).toEquiv

theorem finite_sphericalTriangleGroup (p q r : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hchi : (1 : ℚ) < 1 / p + 1 / q + 1 / r) :
    Finite (SphericalTriangleGroup p q r) := by
  have he : p = 2 ∨ q = 2 ∨ r = 2 := by
    by_contra! h
    have hep := triangle_reciprocal_le p 3 (by decide) (by omega)
    have heq := triangle_reciprocal_le q 3 (by decide) (by omega)
    have her := triangle_reciprocal_le r 3 (by decide) (by omega)
    norm_num at hep heq her hchi
    linarith
  rcases he with rfl | rfl | rfl
  · exact finite_triangle_2 q r hq hr hchi
  · have : Finite (SphericalTriangleGroup 2 p r) :=
      finite_triangle_2 p r hp hr (by linarith)
    exact Finite.of_equiv _ (sphericalTriangleSwapFirst 2 p r).toEquiv
  · have : Finite (SphericalTriangleGroup 2 p q) :=
      finite_triangle_2 p q hp hq (by linarith)
    exact Finite.of_equiv _ ((sphericalTriangleSwapFirst 2 p q).trans
      (sphericalTriangleSwapLast p 2 q)).toEquiv

end GC.Seifert
