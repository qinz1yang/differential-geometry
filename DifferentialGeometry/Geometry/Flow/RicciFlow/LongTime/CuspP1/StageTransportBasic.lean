import DifferentialGeometry.Topology.FundamentalGroup.MarkedMapComposition

set_option autoImplicit false

namespace GC.LongTime.CuspP1

open Set
open DifferentialGeometry.Topology GC.Topology

section Family

variable {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

/-- The straight-line reparametrised homotopy between two members of a continuous family
over an order-connected parameter set. -/
def familyHomotopy {I : Set ℝ} (hI : I.OrdConnected) (c : ℝ → C(T, X))
    (hc : ContinuousOn (fun p : ℝ × T => c p.1 p.2) (I ×ˢ univ)) {s t : ℝ}
    (hs : s ∈ I) (ht : t ∈ I) : (c s).Homotopy (c t) where
  toFun := fun p => c (s + (p.1 : ℝ) * (t - s)) p.2
  continuous_toFun := by
    have hcont : Continuous (fun p : unitInterval × T => ((s + (p.1 : ℝ) * (t - s)), p.2)) := by
      fun_prop
    refine hc.comp_continuous hcont ?_
    intro p
    refine ⟨?_, mem_univ _⟩
    apply hI.uIcc_subset hs ht
    rcases le_total s t with h | h
    · rw [uIcc_of_le h]
      constructor <;> nlinarith [p.1.2.1, p.1.2.2]
    · rw [uIcc_of_ge h]
      constructor <;> nlinarith [p.1.2.1, p.1.2.2]
  map_zero_left := by intro y; simp
  map_one_left := by intro y; simp

/-- AT10/IMS01 smooth-segment core: for a family of maps `T → X`, continuous in the
parameter on an order-connected set `I`, and a fixed map `φ : X → Y`, the kernel of
`π₁ T → π₁ Y` induced by `φ ∘ c t` (at the fixed basepoint `x`) does not depend on `t ∈ I`. -/
theorem kernel_const_of_family {I : Set ℝ} (hI : I.OrdConnected) (c : ℝ → C(T, X))
    (hc : ContinuousOn (fun p : ℝ × T => c p.1 p.2) (I ×ˢ univ)) (φ : C(X, Y))
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (x : T) :
    (FundamentalGroup.map (φ.comp (c s)) x).ker =
      (FundamentalGroup.map (φ.comp (c t)) x).ker := by
  let H := familyHomotopy hI c hc hs ht
  exact homotopic_kernel (φ.comp (c s)) (φ.comp (c t))
    { toFun := fun p => φ (H p)
      continuous_toFun := φ.continuous.comp H.continuous
      map_zero_left := by intro y; simp [H]
      map_one_left := by intro y; have := H.apply_one y; simp [this] } x

/-- Same, with the transported maps `m t = E t ∘ φ ∘ c t` into varying targets `M t`, where
each `E t` is injective on `π₁` at the relevant point (e.g. a homeomorphism/identification of
the stage with the slice). The kernel of `π₁ T → π₁ (M t)` is constant. -/
theorem kernel_const_of_transported {I : Set ℝ} (hI : I.OrdConnected) (c : ℝ → C(T, X))
    (hc : ContinuousOn (fun p : ℝ × T => c p.1 p.2) (I ×ˢ univ)) (φ : C(X, Y))
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)] (E : ∀ t, C(Y, M t))
    (m : ∀ t, C(T, M t)) (hm : ∀ t ∈ I, m t = (E t).comp (φ.comp (c t))) (x : T)
    (hE : ∀ t ∈ I, Function.Injective (FundamentalGroup.map (E t) (φ (c t x))))
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    (FundamentalGroup.map (m s) x).ker = (FundamentalGroup.map (m t) x).ker := by
  have h1 : ∀ u ∈ I, (FundamentalGroup.map (m u) x).ker =
      (FundamentalGroup.map (φ.comp (c u)) x).ker := by
    intro u hu
    rw [hm u hu]
    exact composite_kernel (φ.comp (c u)) (E u) x (hE u hu)
  rw [h1 s hs, h1 t ht]
  exact kernel_const_of_family hI c hc φ hs ht x

end Family

section Homeo

variable {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

theorem fundamentalGroup_map_homeomorph_injective (e : X ≃ₜ Y) (x : X) :
    Function.Injective (FundamentalGroup.map (e : C(X, Y)) x) := by
  refine injective_inner_of_composite (e : C(X, Y)) (e.symm : C(Y, X)) x ?_
  have hc : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext y; simp
  rw [hc]
  intro a b hab
  have h2 : FundamentalGroup.map (ContinuousMap.id X) x = MonoidHom.id _ := by
    ext p
    simp only [FundamentalGroup.map]
    induction p using Quotient.inductionOn with
    | h q => exact congrArg Quotient.mk'' (Path.map_id q)
  rw [h2] at hab
  exact hab

/-- AT10 (kernel part): composing a torus map with a homeomorphism (e.g. a diffeomorphism
`F_t : X → M_t` parametrising a surgery-free stage) does not change the `π₁` kernel. -/
theorem kernel_comp_homeomorph (e : X ≃ₜ Y) (c : C(T, X)) (x : T) :
    (FundamentalGroup.map ((e : C(X, Y)).comp c) x).ker = (FundamentalGroup.map c x).ker :=
  composite_kernel c (e : C(X, Y)) x (fundamentalGroup_map_homeomorph_injective e (c x))

/-- AT10: kernels of `π₁ T → π₁ M_a` and `π₁ T → π₁ M_b` agree when `M_a`, `M_b` are both
parametrised by the same compact carrier `X` through homeomorphisms `F_a`, `F_b`
(equivalently, transported by `F_b F_a⁻¹`). -/
theorem kernel_transport_homeomorph {Ma Mb : Type*} [TopologicalSpace Ma] [TopologicalSpace Mb]
    (Fa : X ≃ₜ Ma) (Fb : X ≃ₜ Mb) (c : C(T, X)) (x : T) :
    (FundamentalGroup.map ((Fa : C(X, Ma)).comp c) x).ker =
      (FundamentalGroup.map ((Fb : C(X, Mb)).comp c) x).ker := by
  rw [kernel_comp_homeomorph, kernel_comp_homeomorph]

/-- AT11 (kernel preservation through a common core), in the exact blueprint shape:
`ker((j₋ a)_*) = ker(a_*) = ker((j₊ a)_*)` for `π₁`-injective core maps `j₋, j₊`, and the
variant where the two core maps of the torus are homotopic. -/
theorem kernel_common_core {C Xm Xp : Type*} [TopologicalSpace C] [TopologicalSpace Xm]
    [TopologicalSpace Xp] (a : C(T, C)) (jm : C(C, Xm)) (jp : C(C, Xp)) (x : T)
    (hm : Function.Injective (FundamentalGroup.map jm (a x)))
    (hp : Function.Injective (FundamentalGroup.map jp (a x))) :
    (FundamentalGroup.map (jm.comp a) x).ker = (FundamentalGroup.map a x).ker ∧
      (FundamentalGroup.map a x).ker = (FundamentalGroup.map (jp.comp a) x).ker :=
  ⟨composite_kernel a jm x hm, (composite_kernel a jp x hp).symm⟩

theorem kernel_common_core_homotopic {C Xm Xp : Type*} [TopologicalSpace C] [TopologicalSpace Xm]
    [TopologicalSpace Xp] (a b : C(T, C)) (H : a.Homotopy b) (jm : C(C, Xm)) (jp : C(C, Xp))
    (x : T) (hm : Function.Injective (FundamentalGroup.map jm (a x)))
    (hp : Function.Injective (FundamentalGroup.map jp (b x))) :
    (FundamentalGroup.map (jm.comp a) x).ker = (FundamentalGroup.map (jp.comp b) x).ker :=
  common_core_homotopic_kernel a b H jm jp x hm hp

end Homeo

end GC.LongTime.CuspP1
