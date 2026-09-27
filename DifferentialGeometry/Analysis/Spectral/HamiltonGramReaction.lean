import DifferentialGeometry.Analysis.Spectral.HamiltonGram

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Spectral

open scoped BigOperators

private theorem swap_sum {α β R : Type*} [Fintype α] [Fintype β] [AddCommMonoid R]
    (f : α → β → R) : (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  exact @Finset.sum_comm β R α _ Finset.univ Finset.univ f

private theorem swap_first3 {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (f : ι → ι → ι → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ b, ∑ c, f b a c := by
  calc
    _ = ∑ b, ∑ a, ∑ c, f a b c := swap_sum (fun a b => ∑ c, f a b c)
    _ = ∑ a, ∑ b, ∑ c, f b a c := by
      rfl

private theorem sum_congr3 {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    {f g : ι → ι → ι → R} (h : ∀ a b c, f a b c = g a b c) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ b, ∑ c, g a b c := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => h a b c)

private theorem const_mul_sum2 {ι R : Type*} [Fintype ι] [Ring R]
    (k : R) (f : ι → ι → R) :
    (∑ a, ∑ b, k * f a b) = k * (∑ a, ∑ b, f a b) := by
  calc
    _ = ∑ a, k * (∑ b, f a b) := by
      refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum (Finset.univ) _ _).symm
    _ = k * (∑ a, ∑ b, f a b) := by rw [Finset.mul_sum]

private theorem neg_sum3 {ι R : Type*} [Fintype ι] [Ring R]
    (f : ι → ι → ι → R) :
    (∑ a, ∑ b, ∑ c, -f a b c) = -(∑ a, ∑ b, ∑ c, f a b c) := by
  simp only [Finset.sum_neg_distrib]

private theorem sum_congr5 {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    {f g : ι → ι → ι → ι → ι → R}
    (h : ∀ a b c d e, f a b c d e = g a b c d e) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, g a b c d e := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine Finset.sum_congr rfl (fun e _ => h a b c d e)

private theorem neg_sum1 {ι R : Type*} [Fintype ι] [Ring R]
    (f : ι → R) : (∑ a, -f a) = -(∑ a, f a) := by
  simp only [Finset.sum_neg_distrib]

private theorem neg_sum5 {ι R : Type*} [Fintype ι] [Ring R]
    (f : ι → ι → ι → ι → ι → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, -f a b c d e) =
      -(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) := by
  simp only [Finset.sum_neg_distrib]

private theorem reaction_reduce {κ : Type*} [Fintype κ]
    (A C : κ → κ → Real) (hC : ∀ r s, C s r = -C r s) :
    (∑ r, ∑ s, (A r s - A s r - 2 * C r s) ^ 2) =
      2 * (∑ r, ∑ s, A r s ^ 2) -
        2 * (∑ r, ∑ s, A r s * A s r) +
        4 * (∑ r, ∑ s, C r s ^ 2) -
        8 * (∑ r, ∑ s, A r s * C r s) := by
  have hAsq : (∑ r, ∑ s, (A s r) ^ 2) = ∑ r, ∑ s, (A r s) ^ 2 := by
    simpa using (swap_sum (fun r s => (A s r) ^ 2))
  have hACswap : (∑ r, ∑ s, A s r * C r s) =
      -(∑ r, ∑ s, A r s * C r s) := by
    calc
      _ = ∑ s, ∑ r, A r s * C s r := by
        rfl
      _ = ∑ s, ∑ r, -(A r s * C r s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hC r s]
        ring
      _ = -(∑ r, ∑ s, A r s * C r s) := by
        simp only [Finset.sum_neg_distrib]
        congr 1
        simpa using (swap_sum (fun r s => A r s * C r s)).symm
  have h4c : (∑ r, ∑ s, 4 * C r s ^ 2) =
      4 * (∑ r, ∑ s, C r s ^ 2) := const_mul_sum2 4 _
  have h2aa : (∑ r, ∑ s, 2 * (A r s * A s r)) =
      2 * (∑ r, ∑ s, A r s * A s r) := const_mul_sum2 2 _
  have h4ac : (∑ r, ∑ s, 4 * (A r s * C r s)) =
      4 * (∑ r, ∑ s, A r s * C r s) := const_mul_sum2 4 _
  have h4swap : (∑ r, ∑ s, 4 * (A s r * C r s)) =
      4 * (∑ r, ∑ s, A s r * C r s) := const_mul_sum2 4 _
  have hsq (r s : κ) :
      (A r s - A s r - 2 * C r s) ^ 2 =
        A r s ^ 2 + A s r ^ 2 + 4 * C r s ^ 2 -
          2 * (A r s * A s r) - 4 * (A r s * C r s) +
          4 * (A s r * C r s) := by ring
  calc
    _ = (∑ r, ∑ s, A r s ^ 2) + (∑ r, ∑ s, A s r ^ 2) +
          (∑ r, ∑ s, 4 * C r s ^ 2) -
          (∑ r, ∑ s, 2 * (A r s * A s r)) -
          (∑ r, ∑ s, 4 * (A r s * C r s)) +
          (∑ r, ∑ s, 4 * (A s r * C r s)) := by
      simp_rw [hsq]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 2 * (∑ r, ∑ s, A r s ^ 2) -
          2 * (∑ r, ∑ s, A r s * A s r) +
          4 * (∑ r, ∑ s, C r s ^ 2) -
          8 * (∑ r, ∑ s, A r s * C r s) := by
      rw [h4c, h2aa, h4ac, h4swap, hAsq, hACswap]
      ring

private theorem move3 {α β γ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid R]
    (f : α → β → γ → R) : (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  calc
    _ = ∑ b, ∑ a, ∑ c, f a b c := swap_sum (fun a b => ∑ c, f a b c)
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      refine Finset.sum_congr rfl fun b _ => swap_sum _

private theorem move4 {α β γ δ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid R] (f : α → β → γ → δ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := swap_sum (fun a b => ∑ c, ∑ d, f a b c d)
    _ = ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := by
      refine Finset.sum_congr rfl fun b _ => swap_sum (fun a c => ∑ d, f a b c d)
    _ = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => swap_sum _

private theorem move5 {α β γ δ ε R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] [AddCommMonoid R] (f : α → β → γ → δ → ε → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, f a b c d e := swap_sum (fun a b => ∑ c, ∑ d, ∑ e, f a b c d e)
    _ = ∑ b, ∑ c, ∑ a, ∑ d, ∑ e, f a b c d e := by
      refine Finset.sum_congr rfl fun b _ => swap_sum (fun a c => ∑ d, ∑ e, f a b c d e)
    _ = ∑ b, ∑ c, ∑ d, ∑ a, ∑ e, f a b c d e := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => swap_sum _

private theorem move6 {α β γ δ ε ζ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] [Fintype ζ] [AddCommMonoid R] (f : α → β → γ → δ → ε → ζ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, f a b c d e z) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ a, f a b c d e z := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, ∑ z, f a b c d e z := swap_sum (fun a b => ∑ c, ∑ d, ∑ e, ∑ z, f a b c d e z)
    _ = ∑ b, ∑ c, ∑ a, ∑ d, ∑ e, ∑ z, f a b c d e z := by
      refine Finset.sum_congr rfl fun b _ => swap_sum (fun a c => ∑ d, ∑ e, ∑ z, f a b c d e z)
    _ = ∑ b, ∑ c, ∑ d, ∑ a, ∑ e, ∑ z, f a b c d e z := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, ∑ z, f a b c d e z := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ a, f a b c d e z := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun e _ => swap_sum _

private theorem move7 {α β γ δ ε ζ η R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] [Fintype ζ] [Fintype η] [AddCommMonoid R]
    (f : α → β → γ → δ → ε → ζ → η → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, f a b c d e z q) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, ∑ a, f a b c d e z q := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, f a b c d e z q := swap_sum (fun a b => ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, f a b c d e z q)
    _ = ∑ b, ∑ c, ∑ a, ∑ d, ∑ e, ∑ z, ∑ q, f a b c d e z q := by
      refine Finset.sum_congr rfl fun b _ => swap_sum (fun a c => ∑ d, ∑ e, ∑ z, ∑ q, f a b c d e z q)
    _ = ∑ b, ∑ c, ∑ d, ∑ a, ∑ e, ∑ z, ∑ q, f a b c d e z q := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, ∑ z, ∑ q, f a b c d e z q := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ a, ∑ q, f a b c d e z q := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun e _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, ∑ a, f a b c d e z q := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun e _ => ?_
      refine Finset.sum_congr rfl fun z _ => swap_sum _

private theorem move8 {α β γ δ ε ζ η θ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] [Fintype ζ] [Fintype η] [Fintype θ] [AddCommMonoid R]
    (f : α → β → γ → δ → ε → ζ → η → θ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, ∑ p, f a b c d e z q p) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, ∑ p, ∑ a, f a b c d e z q p := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, ∑ p, f a b c d e z q p := swap_sum (fun a b => ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, ∑ p, f a b c d e z q p)
    _ = ∑ b, ∑ c, ∑ a, ∑ d, ∑ e, ∑ z, ∑ q, ∑ p, f a b c d e z q p := by
      refine Finset.sum_congr rfl fun b _ => swap_sum (fun a c => ∑ d, ∑ e, ∑ z, ∑ q, ∑ p, f a b c d e z q p)
    _ = ∑ b, ∑ c, ∑ d, ∑ a, ∑ e, ∑ z, ∑ q, ∑ p, f a b c d e z q p := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, ∑ z, ∑ q, ∑ p, f a b c d e z q p := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ a, ∑ q, ∑ p, f a b c d e z q p := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun e _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, ∑ a, ∑ p, f a b c d e z q p := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun e _ => ?_
      refine Finset.sum_congr rfl fun z _ => swap_sum _
    _ = ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ q, ∑ p, ∑ a, f a b c d e z q p := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun e _ => ?_
      refine Finset.sum_congr rfl fun z _ => ?_
      refine Finset.sum_congr rfl fun q _ => swap_sum _

private theorem reorder6_rs {ι κ R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (f : κ → κ → ι → ι → ι → ι → R) :
    (∑ r, ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, f r s a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, ∑ s, f r s a b c d := by
  calc
    _ = ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, f r s a b c d := move6 _
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, ∑ s, f r s a b c d :=
      move6 (fun s a b c d r => f r s a b c d)

private theorem reorder7_rs {ι κ R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (f : κ → κ → ι → ι → ι → ι → ι → R) :
    (∑ r, ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f r s a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, ∑ s, f r s a b c d e := by
  calc
    _ = ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, f r s a b c d e := move7 _
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, ∑ s, f r s a b c d e :=
      move7 (fun s a b c d e r => f r s a b c d e)

private theorem reorder8_rs {ι κ R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (f : κ → κ → ι → ι → ι → ι → ι → ι → R) :
    (∑ r, ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ p, f r s a b c d e p) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ p, ∑ r, ∑ s, f r s a b c d e p := by
  calc
    _ = ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ p, ∑ r, f r s a b c d e p := move8 _
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ p, ∑ r, ∑ s, f r s a b c d e p :=
      move8 (fun s a b c d e p r => f r s a b c d e p)

private theorem reorder5_perm {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (f : ι → ι → ι → ι → ι → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f c a e b d := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, f a b c d e :=
      swap_sum (fun a b => ∑ c, ∑ d, ∑ e, f a b c d e)
    _ = ∑ b, ∑ c, ∑ a, ∑ d, ∑ e, f a b c d e := by
      refine Finset.sum_congr rfl fun b _ => swap_sum (fun a c => ∑ d, ∑ e, f a b c d e)
    _ = ∑ b, ∑ c, ∑ d, ∑ a, ∑ e, f a b c d e := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => swap_sum _
    _ = ∑ b, ∑ d, ∑ c, ∑ a, ∑ e, f a b c d e := by
      refine Finset.sum_congr rfl fun b _ => swap_sum (fun c d => ∑ a, ∑ e, f a b c d e)
    _ = ∑ b, ∑ d, ∑ a, ∑ c, ∑ e, f a b c d e := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun d _ => swap_sum _
    _ = ∑ b, ∑ d, ∑ a, ∑ e, ∑ c, f a b c d e := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun a _ => swap_sum _
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f c a e b d := by
      rfl

private theorem swap23_6 {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (f : ι → ι → ι → ι → ι → ι → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ k, f a b c d e k) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ k, f a c b d e k := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, ∑ k, f a b c d e k := by
      refine Finset.sum_congr rfl fun a _ => swap_sum (fun b c => ∑ d, ∑ e, ∑ k, f a b c d e k)
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ k, f a c b d e k := by
      rfl

theorem hamiltonGram_reaction_eq_hamiltonReactionPolynomial
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    hamiltonGramReaction Y X U W =
      hamiltonReactionPolynomial (hamiltonGramK Y) (hamiltonGramP Y X)
        (hamiltonGramM X) U W := by
  classical
  let A : κ → κ → Real := fun r s => ∑ a, ∑ c, Y r a c * X s c * W a
  let C : κ → κ → Real := fun r s => ∑ a, ∑ b, ∑ c,
    Y r a c * Y s b c * U a b
  have hCswap (r s : κ) : C s r = -C r s := by
    unfold C
    calc
      (∑ a, ∑ b, ∑ c, Y s a c * Y r b c * U a b) =
          ∑ a, ∑ b, ∑ c, Y s b c * Y r a c * U b a := by
        exact swap_first3 (fun a b c => Y s a c * Y r b c * U a b)
      _ = -(∑ a, ∑ b, ∑ c, Y r a c * Y s b c * U a b) := by
        calc
          _ = ∑ a, ∑ b, ∑ c,
              -(Y r a c * Y s b c * U a b) := by
            apply sum_congr3
            intro a b c
            rw [hU b a]
            ring
          _ = _ := neg_sum3 _
  have hrewrite : hamiltonGramReaction Y X U W =
      ∑ r, ∑ s, (A r s - A s r - 2 * C r s) ^ 2 := by
    rfl
  rw [hrewrite]
  rw [reaction_reduce A C hCswap]
  have hA2 :
      (∑ r, ∑ s, A r s ^ 2) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          (∑ r, Y r a c * Y r b d) *
            (∑ s, X s c * X s d) * W a * W b := by
    have hp (r s : κ) : A r s ^ 2 =
        ∑ a, ∑ b, ∑ c, ∑ d,
          Y r a c * X s c * W a *
            (Y r b d * X s d * W b) := by
      unfold A
      rw [pow_two, Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Fintype.sum_mul_sum]
    simp_rw [hp]
    rw [reorder6_rs]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    calc
      _ = ∑ r, ∑ s,
          (Y r a c * Y r b d) * (X s c * X s d) * W a * W b := by
        refine Finset.sum_congr rfl fun r _ => ?_
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      _ = ((∑ r, Y r a c * Y r b d) * ∑ s, X s c * X s d) * W a * W b := by
        calc
          _ = (∑ r, ∑ s,
              (W a * W b) * ((Y r a c * Y r b d) * (X s c * X s d))) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
          _ = (W a * W b) *
              (∑ r, ∑ s, (Y r a c * Y r b d) * (X s c * X s d)) :=
            const_mul_sum2 (W a * W b) _
          _ = ((∑ r, Y r a c * Y r b d) * ∑ s, X s c * X s d) * W a * W b := by
            rw [← Fintype.sum_mul_sum]
            ring
  have hAA :
      (∑ r, ∑ s, A r s * A s r) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          (∑ r, Y r a c * X r d) *
            (∑ s, Y s b d * X s c) * W a * W b := by
    have hp (r s : κ) : A r s * A s r =
        ∑ a, ∑ b, ∑ c, ∑ d,
          Y r a c * X s c * W a *
            (Y s b d * X r d * W b) := by
      unfold A
      rw [Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Fintype.sum_mul_sum]
    simp_rw [hp]
    rw [reorder6_rs]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    calc
      _ = ∑ r, ∑ s,
          (W a * W b) * ((Y r a c * X r d) * (Y s b d * X s c)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      _ = (W a * W b) *
          (∑ r, ∑ s, (Y r a c * X r d) * (Y s b d * X s c)) :=
        const_mul_sum2 (W a * W b) _
      _ = ((∑ r, Y r a c * X r d) * ∑ s, Y s b d * X s c) * W a * W b := by
        rw [← Fintype.sum_mul_sum]
        ring
  have hC2 :
      (∑ r, ∑ s, C r s ^ 2) =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          (∑ r, Y r a e * Y r b f) *
            (∑ s, Y s c e * Y s d f) * U a c * U b d := by
    have hp (r s : κ) : C r s ^ 2 =
        ∑ a, ∑ d, ∑ b, ∑ e, ∑ c, ∑ f,
          Y r a c * Y s b c * U a b *
            (Y r d f * Y s e f * U d e) := by
      unfold C
      rw [pow_two, Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Fintype.sum_mul_sum]
    simp_rw [hp]
    rw [reorder8_rs]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun f _ => ?_
    calc
      _ = ∑ r, ∑ s,
          (U a c * U b d) * ((Y r a e * Y r b f) * (Y s c e * Y s d f)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      _ = (U a c * U b d) *
          (∑ r, ∑ s, (Y r a e * Y r b f) * (Y s c e * Y s d f)) :=
        const_mul_sum2 (U a c * U b d) _
      _ = ((∑ r, Y r a e * Y r b f) * ∑ s, Y s c e * Y s d f) * U a c * U b d := by
        rw [← Fintype.sum_mul_sum]
        ring
  have hAC :
      (∑ r, ∑ s, A r s * C r s) =
        -(∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          (∑ r, Y r a d * Y r c e) *
            (∑ s, Y s d b * X s e) * U a b * W c) := by
    have hp (r s : κ) : A r s * C r s =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          Y r a c * X s c * W a *
            (Y r b e * Y s d e * U b d) := by
      unfold A C
      rw [Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hp]
    rw [reorder7_rs]
    let Fsource : ι → ι → ι → ι → ι → Real := fun a b c d e =>
      (∑ r, Y r a c * Y r b e) * (∑ s, X s c * Y s d e) * U b d * W a
    have hfactor :
        (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, ∑ s,
          Y r a c * X s c * W a * (Y r b e * Y s d e * U b d)) =
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, Fsource a b c d e := by
      apply sum_congr5
      intro a b c d e
      calc
        _ = (W a * U b d) *
            (∑ r, ∑ s, (Y r a c * Y r b e) * (X s c * Y s d e)) := by
          calc
            _ = ∑ r, ∑ s,
                (W a * U b d) * ((Y r a c * Y r b e) * (X s c * Y s d e)) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              refine Finset.sum_congr rfl fun s _ => ?_
              ring
            _ = _ := const_mul_sum2 (W a * U b d) _
        _ = (W a * U b d) *
            ((∑ r, Y r a c * Y r b e) * (∑ s, X s c * Y s d e)) := by
          rw [← Fintype.sum_mul_sum]
        _ = Fsource a b c d e := by
          dsimp [Fsource]
          ring
    rw [hfactor, reorder5_perm]
    rw [← neg_sum5 (fun a b c d e =>
      ((∑ r, Y r a d * Y r c e) * (∑ s, Y s d b * X s e) * U a b * W c))]
    apply sum_congr5
    intro a b c d e
    have hr : (∑ r, Y r c e * Y r a d) =
        ∑ r, Y r a d * Y r c e := by
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    have hs : (∑ s, X s e * Y s b d) =
        -(∑ s, Y s d b * X s e) := by
      calc
        _ = ∑ s, -(Y s d b * X s e) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hY s b d]
          ring
        _ = _ := neg_sum1 _
    dsimp [Fsource]
    rw [hr, hs]
    ring
  have hC2' :
      (∑ r, ∑ s, C r s ^ 2) =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          (∑ r, Y r a e * Y r c f) *
            (∑ s, Y s b e * Y s d f) * U a b * U c d := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          (∑ r, Y r a e * Y r b f) *
            (∑ s, Y s c e * Y s d f) * U a c * U b d := hC2
      _ = _ := by
        symm
        exact swap23_6 (fun a b c d e f =>
          (∑ r, Y r a e * Y r c f) *
            (∑ s, Y s b e * Y s d f) * U a b * U c d)
  unfold hamiltonReactionPolynomial hamiltonGramK hamiltonGramP hamiltonGramM
  rw [hA2, hAA, hC2', hAC]
  ring

theorem hamiltonReactionPolynomial_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonReactionPolynomial (hamiltonGramK Y) (hamiltonGramP Y X)
      (hamiltonGramM X) U W := by
  rw [← hamiltonGram_reaction_eq_hamiltonReactionPolynomial Y X U W hY hU]
  exact hamiltonGram_reaction_nonneg Y X U W

theorem hamiltonQuadraticForm_add_hamiltonReactionPolynomial_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonQuadraticForm (hamiltonGramK Y) (hamiltonGramP Y X)
      (hamiltonGramM X) U W +
      hamiltonReactionPolynomial (hamiltonGramK Y) (hamiltonGramP Y X)
        (hamiltonGramM X) U W := by
  rw [← hamiltonGram_quadratic_eq_hamiltonQuadraticForm Y X U W,
    ← hamiltonGram_reaction_eq_hamiltonReactionPolynomial Y X U W hY hU]
  exact hamiltonGram_reaction_tangent_nonneg Y X U W

end DifferentialGeometry.Analysis.Spectral
