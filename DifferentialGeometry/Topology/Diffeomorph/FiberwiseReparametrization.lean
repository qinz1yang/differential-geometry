import DifferentialGeometry.Topology.Diffeomorph.Fiberwise

open scoped Manifold ContDiff

namespace Diffeomorph

section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' P] {n : ℕ∞ω}

def fiberwiseReparametrization (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (h : P → P) (hh : ContMDiff K K n h) :
    (N × P) ≃ₘ^n⟮J.prod K, J.prod K⟯ (N × P) :=
  prodCongrLeft (fun p => (Φ.restrictFiber hΦ p).symm.trans (Φ.restrictFiber hΦ (h p)))
    ((Φ.contMDiff_restrictFiber hΦ).comp
      ((hh.comp contMDiff_snd).prodMk
        ((Φ.contMDiff_restrictFiber_symm hΦ).comp (contMDiff_snd.prodMk contMDiff_fst))))
    ((Φ.contMDiff_restrictFiber hΦ).comp
      (contMDiff_snd.prodMk
        ((Φ.contMDiff_restrictFiber_symm hΦ).comp
          ((hh.comp contMDiff_snd).prodMk contMDiff_fst))))

@[simp] theorem fiberwiseReparametrization_apply
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (h : P → P) (hh : ContMDiff K K n h) (q : N × P) :
    Φ.fiberwiseReparametrization hΦ h hh q = ((Φ ((Φ.symm q).1, h q.2)).1, q.2) := rfl

@[simp] theorem fiberwiseReparametrization_symm_apply
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (h : P → P) (hh : ContMDiff K K n h) (q : N × P) :
    (Φ.fiberwiseReparametrization hΦ h hh).symm q =
      ((Φ ((Φ.symm (q.1, h q.2)).1, q.2)).1, q.2) := rfl

theorem fiberwiseReparametrization_apply_of_eq
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (h : P → P) (hh : ContMDiff K K n h)
    (q : N × P) (hq : h q.2 = q.2) : Φ.fiberwiseReparametrization hΦ h hh q = q := by
  change (Φ.restrictFiber hΦ (h q.2) ((Φ.restrictFiber hΦ q.2).symm q.1), q.2) = q
  rw [hq, (Φ.restrictFiber hΦ q.2).apply_symm_apply]

@[simp] theorem fiberwiseReparametrization_id
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P)) (hΦ : ∀ q, (Φ q).2 = q.2) :
    Φ.fiberwiseReparametrization hΦ id contMDiff_id =
      Diffeomorph.refl (J.prod K) (N × P) n := by
  apply Diffeomorph.ext
  intro q
  exact Φ.fiberwiseReparametrization_apply_of_eq hΦ id contMDiff_id q rfl

theorem fiberwiseReparametrization_apply_comp
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (h : P → P) (hh : ContMDiff K K n h) (q : M × P) :
    Φ.fiberwiseReparametrization hΦ h hh (Φ q) = ((Φ (q.1, h q.2)).1, q.2) := by
  rw [fiberwiseReparametrization_apply, Φ.symm_apply_apply, hΦ]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {HV : Type*} [TopologicalSpace HV] {L : ModelWithCorners 𝕜 V HV}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HV Q]

theorem contMDiff_fiberwiseReparametrization
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (h : Q × P → P) (hh : ContMDiff (L.prod K) K n h) :
    ContMDiff (L.prod (J.prod K)) (J.prod K) n
      (fun z : Q × (N × P) =>
        Φ.fiberwiseReparametrization hΦ (fun p => h (z.1, p))
          (hh.comp (contMDiff_const.prodMk contMDiff_id)) z.2) :=
  (((Φ.contMDiff.comp
    (((Φ.symm.contMDiff.comp contMDiff_snd).fst).prodMk
      (hh.comp (contMDiff_fst.prodMk contMDiff_snd.snd)))).fst).prodMk contMDiff_snd.snd)

theorem contMDiff_fiberwiseReparametrization_symm
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (h : Q × P → P) (hh : ContMDiff (L.prod K) K n h) :
    ContMDiff (L.prod (J.prod K)) (J.prod K) n
      (fun z : Q × (N × P) =>
        (Φ.fiberwiseReparametrization hΦ (fun p => h (z.1, p))
          (hh.comp (contMDiff_const.prodMk contMDiff_id))).symm z.2) :=
  (((Φ.contMDiff.comp
    (((Φ.symm.contMDiff.comp
      (contMDiff_snd.fst.prodMk
        (hh.comp (contMDiff_fst.prodMk contMDiff_snd.snd))))).fst.prodMk
      contMDiff_snd.snd)).fst).prodMk contMDiff_snd.snd)

end Manifold

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}

def fiberwiseStraightening (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c u : 𝕜) : (F × 𝕜) ≃ₘ^n⟮𝓘(𝕜, F × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜) :=
  let Ψ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E).prod 𝓘(𝕜, 𝕜), 𝓘(𝕜, F).prod 𝓘(𝕜, 𝕜)⟯ (F × 𝕜) :=
    { toEquiv := Φ.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
          chartedSpaceSelf_prod]
        exact Φ.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
          chartedSpaceSelf_prod]
        exact Φ.symm.contMDiff }
  let T := Ψ.fiberwiseReparametrization hΦ (fun t => c + (1 - u) * (t - c))
    ((contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))).contMDiff)
  { toEquiv := T.toEquiv
    contMDiff_toFun := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact T.contMDiff
    contMDiff_invFun := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact T.symm.contMDiff }

@[simp] theorem fiberwiseStraightening_apply (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c u : 𝕜) (q : F × 𝕜) :
    Φ.fiberwiseStraightening hΦ c u q =
      ((Φ ((Φ.symm q).1, c + (1 - u) * (q.2 - c))).1, q.2) := rfl

@[simp] theorem fiberwiseStraightening_symm_apply
    (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c u : 𝕜) (q : F × 𝕜) :
    (Φ.fiberwiseStraightening hΦ c u).symm q =
      ((Φ ((Φ.symm (q.1, c + (1 - u) * (q.2 - c))).1, q.2)).1, q.2) := rfl

theorem contDiff_fiberwiseStraightening (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c : 𝕜) :
    ContDiff 𝕜 n (fun z : 𝕜 × (F × 𝕜) => Φ.fiberwiseStraightening hΦ c z.1 z.2) := by
  have hh : ContDiff 𝕜 n (fun z : 𝕜 × (F × 𝕜) => c + (1 - z.1) * (z.2.2 - c)) :=
    contDiff_const.add ((contDiff_const.sub contDiff_fst).mul
      (contDiff_snd.snd.sub contDiff_const))
  exact ((Φ.contDiff.comp ((Φ.symm.contDiff.comp contDiff_snd).fst.prodMk hh)).fst).prodMk
    contDiff_snd.snd

theorem contDiff_fiberwiseStraightening_symm (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c : 𝕜) :
    ContDiff 𝕜 n (fun z : 𝕜 × (F × 𝕜) => (Φ.fiberwiseStraightening hΦ c z.1).symm z.2) := by
  have hh : ContDiff 𝕜 n (fun z : 𝕜 × (F × 𝕜) => c + (1 - z.1) * (z.2.2 - c)) :=
    contDiff_const.add ((contDiff_const.sub contDiff_fst).mul
      (contDiff_snd.snd.sub contDiff_const))
  exact ((Φ.contDiff.comp
    ((Φ.symm.contDiff.comp (contDiff_snd.fst.prodMk hh)).fst.prodMk contDiff_snd.snd)).fst).prodMk
      contDiff_snd.snd

@[simp] theorem fiberwiseStraightening_zero (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c : 𝕜) :
    Φ.fiberwiseStraightening hΦ c 0 = Diffeomorph.refl 𝓘(𝕜, F × 𝕜) (F × 𝕜) n := by
  apply Diffeomorph.ext
  intro q
  have hi : (Φ.symm q).2 = q.2 :=
    (hΦ (Φ.symm q)).symm.trans (congrArg Prod.snd (Φ.apply_symm_apply q))
  rw [fiberwiseStraightening_apply]
  simp only [sub_zero, one_mul, add_sub_cancel]
  rw [← hi, Prod.eta, Φ.apply_symm_apply, hi]
  rfl

theorem fiberwiseStraightening_apply_base (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c u : 𝕜) (x : F) :
    Φ.fiberwiseStraightening hΦ c u (x, c) = (x, c) := by
  have hi : (Φ.symm (x, c)).2 = c :=
    (hΦ (Φ.symm (x, c))).symm.trans (congrArg Prod.snd (Φ.apply_symm_apply (x, c)))
  rw [fiberwiseStraightening_apply]
  simp only [sub_self, mul_zero, add_zero]
  have he : ((Φ.symm (x, c)).1, c) = Φ.symm (x, c) := Prod.ext rfl hi.symm
  rw [he, Φ.apply_symm_apply]

theorem fiberwiseStraightening_apply_comp (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c u : 𝕜) (q : E × 𝕜) :
    Φ.fiberwiseStraightening hΦ c u (Φ q) =
      ((Φ (q.1, c + (1 - u) * (q.2 - c))).1, q.2) := by
  rw [fiberwiseStraightening_apply, Φ.symm_apply_apply, hΦ]

theorem fiberwiseStraightening_one_apply_comp (Φ : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜))
    (hΦ : ∀ q, (Φ q).2 = q.2) (c : 𝕜) (q : E × 𝕜) :
    Φ.fiberwiseStraightening hΦ c 1 (Φ q) = ((Φ (q.1, c)).1, q.2) := by
  rw [fiberwiseStraightening_apply_comp]
  simp

end NormedSpace

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}

theorem exists_isotopy_straightening_graph
    (A : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) n)
    (hA : ∀ z, (A z).2 = z.2) (c : ℝ) (hfix : ∀ x, A (x, c) = (x, c))
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) (E × ℝ) F n)
    {k : X → F} {x : X → E} {g : X → ℝ} {S : Set X}
    (hgraph : ∀ z ∈ S, k z = Ψ (A (x z, g z))) :
    ∃ T : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F n,
      ContDiff ℝ n (fun z : ℝ × F => T z.1 z.2) ∧
      ContDiff ℝ n (fun z : ℝ × F => (T z.1).symm z.2) ∧
      T 0 = Diffeomorph.refl 𝓘(ℝ, F) F n ∧
      (∀ t y, (Ψ.symm (T t y)).2 = (Ψ.symm y).2) ∧
      (∀ t y, T t (Ψ (y, c)) = Ψ (y, c)) ∧
      ∀ z ∈ S, T 1 (k z) = Ψ (x z, g z) := by
  let R : ℝ → Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) n :=
    A.fiberwiseStraightening hA c
  have hR : ContDiff ℝ n (fun z : ℝ × (E × ℝ) => R z.1 z.2) :=
    A.contDiff_fiberwiseStraightening hA c
  have hRi : ContDiff ℝ n (fun z : ℝ × (E × ℝ) => (R z.1).symm z.2) :=
    A.contDiff_fiberwiseStraightening_symm hA c
  have hi : ContDiff ℝ n (fun z : ℝ × F => (z.1, Ψ.symm z.2)) :=
    contDiff_fst.prodMk (Ψ.symm.contDiff.comp contDiff_snd)
  let T := fun t => Ψ.symm.trans ((R t).trans Ψ)
  refine ⟨T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ n (fun z : ℝ × F => Ψ (R z.1 (Ψ.symm z.2)))
    have hj := hR.comp hi
    exact Ψ.contDiff.comp hj
  · change ContDiff ℝ n (fun z : ℝ × F => Ψ ((R z.1).symm (Ψ.symm z.2)))
    have hj := hRi.comp hi
    exact Ψ.contDiff.comp hj
  · apply Diffeomorph.ext
    intro y
    change Ψ (A.fiberwiseStraightening hA c 0 (Ψ.symm y)) = y
    rw [A.fiberwiseStraightening_zero]
    exact Ψ.apply_symm_apply y
  · intro t y
    change (Ψ.symm (Ψ (R t (Ψ.symm y)))).2 = _
    rw [Ψ.symm_apply_apply]
    rfl
  · intro t y
    change Ψ (R t (Ψ.symm (Ψ (y, c)))) = Ψ (y, c)
    rw [Ψ.symm_apply_apply, A.fiberwiseStraightening_apply_base]
  · intro z hz
    change Ψ (R 1 (Ψ.symm (k z))) = _
    rw [hgraph z hz, Ψ.symm_apply_apply, A.fiberwiseStraightening_one_apply_comp, hfix]

end Diffeomorph

open Set

namespace Diffeomorph

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}

theorem exists_diffeomorph_straightening_family
    (H : 𝕜 → E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F)
    (hH : ContDiff 𝕜 n (fun q : 𝕜 × E => H q.1 q.2))
    (hHi : ContDiff 𝕜 n (fun q : 𝕜 × F => (H q.1).symm q.2)) (a : 𝕜) :
    ∃ T : (F × 𝕜) ≃ₘ^n⟮𝓘(𝕜, F × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜),
      (∀ q, T q = (H a ((H q.2).symm q.1), q.2)) ∧
      (∀ q, T.symm q = (H q.2 ((H a).symm q.1), q.2)) ∧
      (∀ q, (T q).2 = q.2) ∧
      (∀ y, T (y, a) = (y, a)) ∧
      (∀ t x, T (H t x, t) = (H a x, t)) ∧
      (∀ K : Set E, ∀ J : Set 𝕜,
        T '' ((fun q : E × 𝕜 => (H q.2 q.1, q.2)) '' (K ×ˢ J)) = (H a '' K) ×ˢ J) ∧
      ∀ {M : Type*} (f : M → F × 𝕜) (K L : Set E) (J : Set 𝕜),
        (∀ t ∈ J, (H t '' K) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) = H t '' L) →
        ((H a '' K) ×ˢ J) ∩ range (T ∘ f) = (H a '' L) ×ˢ J := by
  let A : (E × 𝕜) ≃ₘ^n⟮𝓘(𝕜, E × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜) :=
    { toEquiv := Equiv.prodCongrLeft (fun t => (H t).toEquiv)
      contMDiff_toFun :=
        ((hH.comp (contDiff_snd.prodMk contDiff_fst)).prodMk contDiff_snd).contMDiff
      contMDiff_invFun :=
        ((hHi.comp (contDiff_snd.prodMk contDiff_fst)).prodMk contDiff_snd).contMDiff }
  have hA : ∀ q, (A q).2 = q.2 := fun _ => rfl
  let T := A.fiberwiseStraightening hA a 1
  have hT (q : F × 𝕜) : T q = (H a ((H q.2).symm q.1), q.2) := by
    dsimp only [T]
    rw [fiberwiseStraightening_apply]
    simp only [sub_self, zero_mul, add_zero]
    rfl
  have hTi (q : F × 𝕜) : T.symm q = (H q.2 ((H a).symm q.1), q.2) := by
    dsimp only [T]
    rw [fiberwiseStraightening_symm_apply]
    simp only [sub_self, zero_mul, add_zero]
    rfl
  have htrack (t : 𝕜) (x : E) : T (H t x, t) = (H a x, t) := by
    rw [hT, (H t).symm_apply_apply]
  have hsets (K : Set E) (J : Set 𝕜) :
      T '' ((fun q : E × 𝕜 => (H q.2 q.1, q.2)) '' (K ×ˢ J)) = (H a '' K) ×ˢ J := by
    ext q
    constructor
    · rintro ⟨_, ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, rfl⟩
      rw [htrack]
      exact ⟨⟨x, hx, rfl⟩, ht⟩
    · rintro ⟨⟨x, hx, hxq⟩, ht⟩
      refine ⟨(H q.2 x, q.2), ⟨(x, q.2), ⟨hx, ht⟩, rfl⟩, ?_⟩
      rw [htrack, hxq]
  refine ⟨T, hT, hTi, (fun q => by rw [hT]), ?_, htrack, hsets, ?_⟩
  · intro y
    rw [hT, (H a).apply_symm_apply]
  · intro M f K L J hlevels
    have hTin : Function.Injective (T : F × 𝕜 → F × 𝕜) := T.injective
    rw [← hsets K J, Set.range_comp, ← image_inter hTin,
      image_prod_inter_range f (fun t => H t) hlevels, hsets]

variable {X : Type*}

theorem exists_diffeomorph_straightening_family_eqOn
    (H : 𝕜 → E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F)
    (hH : ContDiff 𝕜 n (fun q : 𝕜 × E => H q.1 q.2))
    (hHi : ContDiff 𝕜 n (fun q : 𝕜 × F => (H q.1).symm q.2))
    (G : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ F) (P : 𝕜 → F → F)
    {ell t₀ : 𝕜} {J : Set 𝕜} (ht₀ : t₀ ∈ J)
    (hbase : ∀ y, P t₀ y = y)
    (hfamily : ∀ t ∈ J, ∀ x, H (ell + t) x = P t (G x))
    {γ : 𝕜 × X → F} (hγ : ∀ t ∈ J, ∀ u, P t (γ (t₀, u)) = γ (t, u))
    {U : Set F} (hfix : ∀ t ∈ J, EqOn (P t) id U) :
    ∃ T : (F × 𝕜) ≃ₘ^n⟮𝓘(𝕜, F × 𝕜), 𝓘(𝕜, F × 𝕜)⟯ (F × 𝕜),
      (∀ q, T q = (G ((H q.2).symm q.1), q.2)) ∧
      (∀ q, T.symm q = (H q.2 (G.symm q.1), q.2)) ∧
      (∀ q, (T q).2 = q.2) ∧
      (∀ y, T (y, ell + t₀) = (y, ell + t₀)) ∧
      (∀ t x, T (H t x, t) = (G x, t)) ∧
      (∀ K : Set E, ∀ S : Set 𝕜,
        T '' ((fun q : E × 𝕜 => (H q.2 q.1, q.2)) '' (K ×ˢ S)) = (G '' K) ×ˢ S) ∧
      (∀ {M : Type*} (f : M → F × 𝕜) (K L : Set E) (S : Set 𝕜),
        (∀ t ∈ S, (H t '' K) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) = H t '' L) →
        ((G '' K) ×ˢ S) ∩ range (T ∘ f) = (G '' L) ×ˢ S) ∧
      (∀ t ∈ J, ∀ u, T (γ (t, u), ell + t) = (γ (t₀, u), ell + t)) ∧
      T '' ((fun q : 𝕜 × X => (γ q, ell + q.1)) '' (J ×ˢ univ)) =
        range (fun u => γ (t₀, u)) ×ˢ ((fun t => ell + t) '' J) ∧
      EqOn T id (U ×ˢ ((fun t => ell + t) '' J)) ∧
      EqOn T.symm id (U ×ˢ ((fun t => ell + t) '' J)) := by
  have href : H (ell + t₀) = G := by
    ext x
    rw [hfamily t₀ ht₀, hbase]
  obtain ⟨T, hT, hTi, hTheight, hTbase, htrack, hsets, hwhole⟩ :=
    exists_diffeomorph_straightening_family H hH hHi (ell + t₀)
  rw [href] at hT hTi htrack hsets hwhole
  have hrelative (t : 𝕜) (ht : t ∈ J) (y : F) : T (P t y, ell + t) = (y, ell + t) := by
    have h := htrack (ell + t) (G.symm y)
    rw [hfamily t ht, G.apply_symm_apply] at h
    exact h
  have hcurve (t : 𝕜) (ht : t ∈ J) (u : X) :
      T (γ (t, u), ell + t) = (γ (t₀, u), ell + t) := by
    rw [← hγ t ht u]
    exact hrelative t ht (γ (t₀, u))
  have hcore : EqOn T id (U ×ˢ ((fun t => ell + t) '' J)) := by
    rintro ⟨y, v⟩ ⟨hy, t, ht, rfl⟩
    change T (y, ell + t) = (y, ell + t)
    have hyfix : P t y = y := hfix t ht hy
    simpa only [hyfix] using hrelative t ht y
  refine ⟨T, hT, hTi, hTheight, hTbase, htrack, hsets, hwhole, hcurve, ?_, hcore, ?_⟩
  · ext q
    constructor
    · rintro ⟨_, ⟨⟨t, u⟩, ⟨ht, _⟩, rfl⟩, rfl⟩
      rw [hcurve t ht]
      exact ⟨mem_range_self u, t, ht, rfl⟩
    · rintro ⟨⟨u, hu⟩, t, ht, hqt⟩
      refine ⟨(γ (t, u), ell + t), ⟨(t, u), ⟨ht, mem_univ u⟩, rfl⟩, ?_⟩
      rw [hcurve t ht]
      exact Prod.ext hu hqt
  · intro q hq
    apply T.injective
    change T (T.symm q) = T q
    exact (T.apply_symm_apply q).trans (hcore hq).symm


end Diffeomorph
