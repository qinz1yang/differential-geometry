import DifferentialGeometry.Topology.Morse.ExcellentFamily
import DifferentialGeometry.Topology.Diffeomorph.LocalizedGraph
import DifferentialGeometry.Topology.Morse.EmbeddedNormalNeighborhood
import DifferentialGeometry.Topology.Morse.NormalForm.Derivative
import DifferentialGeometry.Topology.Morse.GraphReplacement
import DifferentialGeometry.Topology.Embedding.Diffeomorph

open Set Metric Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

open DifferentialGeometry.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_critical_value_shift
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {p : E}
    (hcrit : ∀ x, fderiv ℝ f x = 0 ↔ x = p)
    {U : Set E} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      ρ =ᶠ[𝓝 p] 1 ∧ ∃ ε > 0, ∀ s : ℝ, |s| < ε →
        ∀ x, fderiv ℝ (fun y => f y + s * ρ y) x = 0 ↔ x = p := by
  classical
  have hmodel (g : E → ℝ) (x : E) :
      IsCriticalPointAt 𝓘(ℝ, E) g x ↔ fderiv ℝ g x = 0 := by
    unfold IsCriticalPointAt
    rw [mfderiv_eq_fderiv]
    constructor <;> intro h <;> ext v <;> exact congrArg (fun L => L v) h
  have hcrit' (x : E) : IsCriticalPointAt 𝓘(ℝ, E) f x ↔ x = p :=
    (hmodel f x).trans (hcrit x)
  have hC : {x | IsCriticalPointAt 𝓘(ℝ, E) f x} = {p} := by
    ext x
    exact hcrit' x
  obtain ⟨n, e, φ, ε, _, heC, hφ, hgerm, hε, hcritical⟩ :=
    exists_critical_value_perturbation_family hf.contMDiff (hC ▸ finite_singleton p) hU
      (by rw [hC]; exact singleton_subset_iff.mpr hpU)
      (fun _ _ => BoundarylessManifold.isInteriorPoint)
  obtain ⟨i, hi⟩ := heC.symm.subset ((hcrit' p).mpr rfl)
  have hpert (s : ℝ) : finitePerturbation f φ (Pi.single i s) = fun y => f y + s * φ i y := by
    funext y
    simp [finitePerturbation, Pi.single_apply, Finset.sum_ite_eq']
  have hone : φ i =ᶠ[𝓝 p] 1 := by
    have hg := hgerm i (Pi.single i (1 : ℝ))
    rw [hi, hpert] at hg
    filter_upwards [hg] with y hy
    simp only [Pi.single_eq_same, one_mul] at hy
    exact add_left_cancel hy
  refine ⟨φ i, (hφ i).1.contDiff, (hφ i).2.1, (hφ i).2.2, hone, ε, hε, ?_⟩
  intro s hs x
  have hnorm : ‖(Pi.single i s : Fin n → ℝ)‖ < ε := by
    apply lt_of_le_of_lt (pi_norm_le_iff_of_nonneg (abs_nonneg s) |>.mpr ?_) hs
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Pi.single_eq_same, Real.norm_eq_abs, le_refl]
    · simp only [Pi.single_eq_of_ne hj, norm_zero, abs_nonneg]
  have hc := Set.ext_iff.mp (hcritical (Pi.single i s) hnorm) x
  rw [hpert] at hc
  exact (hmodel _ x).symm.trans (hc.trans (hcrit' x))

theorem exists_isotopy_graph_critical_value_shift
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {p : E}
    (hcrit : ∀ x, fderiv ℝ f x = 0 ↔ x = p)
    {U : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    {O : Set (E × ℝ)} (hO : IsOpen O) (hpO : (p, f p) ∈ O) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      ρ =ᶠ[𝓝 p] 1 ∧ ∃ ε > 0, ∀ s : ℝ, |s| < ε →
        (∀ x, fderiv ℝ (fun y => f y + s * ρ y) x = 0 ↔ x = p) ∧
        ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
          ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
          H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
          (∀ t z, (H t z).1 = z.1) ∧
          (∀ x, H 1 (x, f x) = (x, f x + s * ρ x)) ∧
          ∃ K : Set (E × ℝ), IsCompact K ∧ K ⊆ O ∧ ∀ t : ℝ,
            EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let V := U ∩ (fun x => (x, f x)) ⁻¹' O
  have hV : IsOpen V := hU.inter (hO.preimage (continuous_id.prodMk hf.continuous))
  obtain ⟨ρ, hρ, hρc, hρV, hρone, ε, hε, hcritical⟩ :=
    exists_critical_value_shift hf hcrit hV ⟨hpU, hpO⟩
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, ∀ x ∈ tsupport ρ, (x, f x + r * ρ x) ∈ O := by
    apply hρc.eventually_forall_of_forall_eventually
    intro x hx
    have hc : Continuous (fun q : ℝ × E => (q.2, f q.2 + q.1 * ρ q.2)) :=
      continuous_snd.prodMk ((hf.continuous.comp continuous_snd).add
        (continuous_fst.mul (hρ.continuous.comp continuous_snd)))
    exact hc.continuousAt.eventually (hO.mem_nhds (by simpa using (hρV hx).2))
  obtain ⟨δ, hδ, hδO⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ρ, hρ, hρc, hρV.trans inter_subset_left, hρone, min ε δ, lt_min hε hδ, ?_⟩
  intro s hs
  refine ⟨hcritical s (hs.trans_le (min_le_left _ _)), ?_⟩
  let G : ℝ × E → ℝ := fun q => f q.2 + (q.1 * s) * ρ q.2
  have hG : ContDiff ℝ ∞ G := (hf.comp contDiff_snd).add
    ((contDiff_fst.mul contDiff_const).mul (hρ.comp contDiff_snd))
  obtain ⟨H, hH, hHi, hH0, hHfst, hgraph, _, _, hsupport⟩ :=
    Diffeomorph.exists_isotopy_graphOn_endpoints_in_open hG hρc
      (fun t _ x hx => by
        simp only [G, image_eq_zero_of_notMem_tsupport hx, mul_zero, add_zero]) hO
      (fun t ht x hx => hδO (show t * s ∈ Metric.ball (0 : ℝ) δ from by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (abs_nonneg s) ht.2).trans_lt
          (hs.trans_le (min_le_right _ _))) x hx)
  refine ⟨H, hH, hHi, hH0, hHfst, ?_, hsupport⟩
  intro x
  simpa only [G, zero_mul, mul_zero, add_zero, one_mul] using hgraph x

theorem exists_isotopy_graph_regular_level
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {p : E}
    (hcrit : ∀ x, fderiv ℝ f x = 0 ↔ x = p)
    {U : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    {O : Set (E × ℝ)} (hO : IsOpen O) (hpO : (p, f p) ∈ O)
    {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < η ∧ ∃ g : E → ℝ,
      ContDiff ℝ ∞ g ∧ EqOn g f Uᶜ ∧ g =ᶠ[𝓝 p] (fun x => f x + s) ∧
      (∀ x, fderiv ℝ g x = 0 ↔ x = p) ∧
      (∀ x, g x = f p → fderiv ℝ g x ≠ 0) ∧
      ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
        H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
        (∀ t z, (H t z).1 = z.1) ∧ (∀ x, H 1 (x, f x) = (x, g x)) ∧
        ∃ K : Set (E × ℝ), IsCompact K ∧ K ⊆ O ∧ ∀ t : ℝ,
          EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ := by
  obtain ⟨ρ, hρ, _, hρU, hρone, ε, hε, hfamily⟩ :=
    exists_isotopy_graph_critical_value_shift hf hcrit hU hpU hO hpO
  let s := min η ε / 2
  have hs : 0 < s := half_pos (lt_min hη hε)
  have hsη : s < η := (half_lt_self (lt_min hη hε)).trans_le (min_le_left _ _)
  have hsε : |s| < ε := by
    rw [abs_of_pos hs]
    exact (half_lt_self (lt_min hη hε)).trans_le (min_le_right _ _)
  obtain ⟨hgc, H, hH, hHi, hH0, hHfst, hgraph, hsupport⟩ := hfamily s hsε
  let g : E → ℝ := fun x => f x + s * ρ x
  have hgerm : g =ᶠ[𝓝 p] (fun x => f x + s) := by
    filter_upwards [hρone] with x hx
    change f x + s * ρ x = f x + s
    rw [hx, Pi.one_apply, mul_one]
  refine ⟨s, hs, hsη, g, hf.add (contDiff_const.mul hρ), ?_, hgerm, hgc, ?_,
    H, hH, hHi, hH0, hHfst, hgraph, hsupport⟩
  · intro x hx
    have hxρ : x ∉ tsupport ρ := fun h => hx (hρU h)
    simp only [g, image_eq_zero_of_notMem_tsupport hxρ, mul_zero, add_zero]
  · intro x hx hzero
    have hxp := (hgc x).mp hzero
    subst x
    have hgp := hgerm.eq_of_nhds
    linarith

section Embedded

variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H}

private theorem critical_points_of_graph_neighborhood
    {e : M → EuclideanSpace ℝ (Fin n) × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e)
    (χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
      (EuclideanSpace ℝ (Fin n)) M ∞)
    {q g : EuclideanSpace ℝ (Fin n) → ℝ} {r t s : ℝ}
    (hr : 0 < r) (hχ : closedBall 0 r ⊆ χ.source)
    (hgraph : ∀ y ∈ closedBall 0 r, e (χ y) = (y, q y))
    (hset : (closedBall 0 r ×ˢ closedBall (q 0) t) ∩ range e =
      (fun y => (y, q y)) '' closedBall 0 r)
    (hqc : ∀ y, fderiv ℝ q y = 0 ↔ y = 0)
    (hgc : ∀ y, fderiv ℝ g y = 0 ↔ y = 0)
    (hgerm : g =ᶠ[𝓝 0] (fun y => q y + s))
    (D : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ))
    (hD : ∀ y, D (y, q y) = (y, g y))
    {K : Set (EuclideanSpace ℝ (Fin n) × ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ ball 0 r ×ˢ ball (q 0) t) (hfix : EqOn D id Kᶜ) :
    (∀ x, IsCriticalPointAt I (fun y => (D (e y)).2) x ↔
      IsCriticalPointAt I (fun y => (e y).2) x) ∧
    (fun y => (D (e y)).2) =ᶠ[𝓝 (χ 0)] (fun y => (e y).2 + s) ∧
    ∀ x, IsCriticalPointAt I (fun y => (e y).2) x → x ≠ χ 0 →
      (fun y => (D (e y)).2) =ᶠ[𝓝 x] (fun y => (e y).2) := by
  have hKset : K ∩ range e = K ∩ ((fun y => (y, q y)) '' ball 0 r) := by
    ext p
    constructor
    · intro hp
      obtain ⟨y, hy, hyp⟩ := hset.subset
        ⟨⟨ball_subset_closedBall (hKO hp.1).1, ball_subset_closedBall (hKO hp.1).2⟩, hp.2⟩
      have hypfst : y = p.1 := congrArg Prod.fst hyp
      exact ⟨hp.1, y, hypfst ▸ (hKO hp.1).1, hyp⟩
    · rintro ⟨hp, y, hy, hyp⟩
      exact ⟨hp, χ y, (hgraph y (ball_subset_closedBall hy)).trans hyp⟩
  have hgraph' := fun y hy => hgraph y (ball_subset_closedBall hy)
  obtain ⟨hnew, hout⟩ := criticalPoints_comp_eq_of_graph he.contMDiff he.isEmbedding.injective χ (by simp)
    isOpen_ball (fun _ hy => hχ (ball_subset_closedBall hy)) hgraph' D D.contDiff
    (fun y _ => hD y) hK.isClosed hKset hfix
  have hold := (criticalPoints_comp_eq_of_graph he.contMDiff he.isEmbedding.injective χ (by simp)
    isOpen_ball (fun _ hy => hχ (ball_subset_closedBall hy)) hgraph'
    (fun p => p) contDiff_id
    (fun _ _ => rfl) hK.isClosed hKset (fun _ _ => rfl)).1
  change criticalPoints I (fun y => (e y).2) = _ at hold
  have hqcrit : criticalPoints 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q = {0} := by
    ext y
    change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) q y = 0 ↔ y = 0
    rw [mfderiv_eq_fderiv]
    exact hqc y
  have hgcrit : criticalPoints 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) g = {0} := by
    ext y
    change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) g y = 0 ↔ y = 0
    rw [mfderiv_eq_fderiv]
    exact hgc y
  have heq : criticalPoints I (fun y => (D (e y)).2) =
      criticalPoints I (fun y => (e y).2) := by
    rw [hgcrit] at hnew
    rw [hqcrit] at hold
    exact hnew.trans hold.symm
  refine ⟨fun x => Set.ext_iff.mp heq x, ?_, ?_⟩
  · have hmap : Filter.map (χ : EuclideanSpace ℝ (Fin n) → M) (𝓝 0) = 𝓝 (χ 0) :=
      χ.toOpenPartialHomeomorph.map_nhds_eq (hχ (mem_closedBall_self hr.le))
    rw [← hmap]
    change ∀ᶠ y in 𝓝 0, (D (e (χ y))).2 = (e (χ y)).2 + s
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr), hgerm] with y hy hgy
    rw [hgraph y (ball_subset_closedBall hy), hD]
    exact hgy
  · intro x hc hne
    apply (hout x ?_).fun_comp Prod.snd
    intro hx
    have hmem : x ∈ criticalPoints I (fun y => (e y).2) := hc
    rw [hold, hqcrit] at hmem
    rcases hmem with h | ⟨y, ⟨_, hy⟩, hyx⟩
    · exact h.2 hx
    · exact hne (hyx.symm.trans (congrArg χ hy))

private theorem regular_height_of_graph_neighborhood
    {e : M → EuclideanSpace ℝ (Fin n) × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e)
    (χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
      (EuclideanSpace ℝ (Fin n)) M ∞)
    {q g : EuclideanSpace ℝ (Fin n) → ℝ} {r t : ℝ}
    (hr : 0 < r) (hχ : closedBall 0 r ⊆ χ.source)
    (hgraph : ∀ y ∈ closedBall 0 r, e (χ y) = (y, q y))
    (hset : (closedBall 0 r ×ˢ closedBall (q 0) t) ∩ range e =
      (fun y => (y, q y)) '' closedBall 0 r)
    (hunique : ∀ x, (e x).2 = q 0 →
      IsCriticalPointAt I (fun y => (e y).2) x → x = χ 0)
    (D : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ))
    (hD : ∀ y, D (y, q y) = (y, g y))
    (hg : ∀ y, g y = q 0 → fderiv ℝ g y ≠ 0) (hgp : g 0 ≠ q 0)
    {K : Set (EuclideanSpace ℝ (Fin n) × ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ ball 0 r ×ˢ ball (q 0) t) (hfix : EqOn D id Kᶜ) :
    ∀ x, (D (e x)).2 = q 0 →
      ¬ IsCriticalPointAt I (fun y => (D (e y)).2) x := by
  let f : M → ℝ := fun y => (D (e y)).2
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    contDiff_snd.contMDiff.comp (D.contMDiff.comp he.contMDiff)
  intro x hx hcritical
  by_cases hxK : e x ∈ K
  · have hxO := hKO hxK
    have hxset : e x ∈ (fun y => (y, q y)) '' closedBall 0 r :=
      hset.subset ⟨⟨ball_subset_closedBall hxO.1, ball_subset_closedBall hxO.2⟩, mem_range_self x⟩
    obtain ⟨y, hy, hyx⟩ := hxset
    have hχyx : χ y = x := he.isEmbedding.injective ((hgraph y hy).trans hyx)
    have hyball : y ∈ ball 0 r := by
      have hfirst : y = (e x).1 := congrArg Prod.fst hyx
      rw [hfirst]
      exact hxO.1
    have hgerm : (fun z => f (χ z)) =ᶠ[𝓝 y] g := by
      filter_upwards [isOpen_ball.mem_nhds hyball] with z hz
      change (D (e (χ z))).2 = g z
      rw [hgraph z (ball_subset_closedBall hz), hD]
    have hder : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ)
        (f ∘ χ) y = 0 := by
      have hc : mfderiv I 𝓘(ℝ, ℝ) f (χ y) = 0 := hχyx.symm ▸ hcritical
      rw [mfderiv_comp y (hf.mdifferentiableAt (by simp))
        (χ.mdifferentiableAt (by simp) (hχ hy)), hc]
      rfl
    have hgzero : fderiv ℝ g y = 0 := by
      have hm := hgerm.mfderiv_eq.symm.trans hder
      rw [mfderiv_eq_fderiv] at hm
      ext v
      exact congrArg (fun L => L v) hm
    apply hg y _ hgzero
    rw [← hχyx, hgraph y hy, hD] at hx
    exact hx
  · have hgerm : f =ᶠ[𝓝 x] (fun y => (e y).2) := by
      filter_upwards [he.contMDiff.continuous.continuousAt.eventually
        (hK.isClosed.isOpen_compl.mem_nhds hxK)] with y hy
      change (D (e y)).2 = (e y).2
      rw [hfix hy]
      rfl
    have hxeq : (e x).2 = q 0 := hgerm.eq_of_nhds.symm.trans hx
    have hxc : IsCriticalPointAt I (fun y => (e y).2) x :=
      hgerm.mfderiv_eq.symm.trans hcritical
    have hxp := hunique x hxeq hxc
    rw [hxp, hgraph 0 (mem_closedBall_self hr.le), hD] at hx
    exact hgp hx

theorem exists_ambient_isotopy_regular_height_of_graph_neighborhood
    {e : M → EuclideanSpace ℝ (Fin n) × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e)
    (χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
      (EuclideanSpace ℝ (Fin n)) M ∞)
    {q : EuclideanSpace ℝ (Fin n) → ℝ} (hq : ContDiff ℝ ∞ q)
    (hqc : ∀ y, fderiv ℝ q y = 0 ↔ y = 0) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hχ : closedBall 0 r ⊆ χ.source)
    (hgraph : ∀ y ∈ closedBall 0 r, e (χ y) = (y, q y))
    (hset : (closedBall 0 r ×ˢ closedBall (q 0) t) ∩ range e =
      (fun y => (y, q y)) '' closedBall 0 r)
    (hunique : ∀ x, (e x).2 = q 0 →
      IsCriticalPointAt I (fun y => (e y).2) x → x = χ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < η ∧ ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ g ∧ EqOn g q (ball 0 r)ᶜ ∧ g =ᶠ[𝓝 0] (fun y => q y + s) ∧
      ∃ Φ : ℝ → ((EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)),
        ContDiff ℝ ∞ (fun z : ℝ × (EuclideanSpace ℝ (Fin n) × ℝ) => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × (EuclideanSpace ℝ (Fin n) × ℝ) => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
          (EuclideanSpace ℝ (Fin n) × ℝ) ∞ ∧
        (∀ u z, (Φ u z).1 = z.1) ∧ (∀ y, Φ 1 (y, q y) = (y, g y)) ∧
        (∀ x, (Φ 1 (e x)).2 = q 0 →
          ¬ IsCriticalPointAt I (fun y => (Φ 1 (e y)).2) x) ∧
        ∃ K : Set (EuclideanSpace ℝ (Fin n) × ℝ), IsCompact K ∧
          K ⊆ ball 0 r ×ˢ ball (q 0) t ∧ ∀ u : ℝ,
            EqOn (Φ u) id Kᶜ ∧ EqOn (Φ u).symm id Kᶜ := by
  obtain ⟨s, hs, hsη, g, hg, hgeq, hgerm, _, hgreg, Φ, hΦ, hΦi, hΦ0,
    hΦfst, hΦgraph, K, hK, hKO, hfix⟩ := exists_isotopy_graph_regular_level hq hqc
      isOpen_ball (mem_ball_self hr) (isOpen_ball.prod isOpen_ball)
      ⟨mem_ball_self hr, mem_ball_self ht⟩ hη
  have hgp : g 0 ≠ q 0 := by
    have h := hgerm.eq_of_nhds
    linarith
  refine ⟨s, hs, hsη, g, hg, hgeq, hgerm, Φ, hΦ, hΦi, hΦ0, hΦfst, hΦgraph,
    regular_height_of_graph_neighborhood he χ hr hχ hgraph hset hunique
      (Φ 1) hΦgraph hgreg hgp hK hKO (hfix 1).1, K, hK, hKO, hfix⟩

variable [I.Boundaryless] [IsManifold I ∞ M]

open CellAttachment in
theorem exists_ambient_isotopy_critical_value_shift
    {e : M → EuclideanSpace ℝ (Fin n) × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e)
    {p : M} (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I (fun x => (e x).2) p)
    (hindex : sigNeg (chartHessianAt (fun y => (e ((extChartAt I p).symm y)).2)
      (extChartAt I p p)) = k)
    (hunique : ∀ x, (e x).2 = (e p).2 →
      IsCriticalPointAt I (fun y => (e y).2) x → x = p) :
    let q := fun y => morseNormalForm hk (e p).2 (EuclideanSpace.equiv (Fin n) ℝ y)
    ∃ r t : ℝ, 0 < r ∧ 0 < t ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (EuclideanSpace ℝ (Fin n)) M ∞,
        ∃ A : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ),
          closedBall 0 r ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, (A z).2 = z.2) ∧
          (∀ y ∈ closedBall 0 r, e (χ y) = A (y, q y)) ∧
          (closedBall 0 r ×ˢ closedBall (e p).2 t) ∩ range (A.symm ∘ e) =
            (fun y => (y, q y)) '' closedBall 0 r ∧
          ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ ball 0 r ∧
            ρ =ᶠ[𝓝 0] 1 ∧ ∃ ε > 0, ∀ s : ℝ, |s| < ε →
              (∀ y, fderiv ℝ (fun z => q z + s * ρ z) y = 0 ↔ y = 0) ∧
              ∃ Φ : ℝ → ((EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)),
                ContDiff ℝ ∞ (fun z : ℝ × (EuclideanSpace ℝ (Fin n) × ℝ) => Φ z.1 z.2) ∧
                ContDiff ℝ ∞ (fun z : ℝ × (EuclideanSpace ℝ (Fin n) × ℝ) => (Φ z.1).symm z.2) ∧
                Φ 0 = Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
                  (EuclideanSpace ℝ (Fin n) × ℝ) ∞ ∧
                (∀ y, Φ 1 (A (y, q y)) = A (y, q y + s * ρ y)) ∧
                (s ≠ 0 → ∀ x, (Φ 1 (e x)).2 = (e p).2 →
                  ¬ IsCriticalPointAt I (fun y => (Φ 1 (e y)).2) x) ∧
                (∀ x, IsCriticalPointAt I (fun y => (Φ 1 (e y)).2) x ↔
                  IsCriticalPointAt I (fun y => (e y).2) x) ∧
                (∀ x, IsCriticalPointAt I (fun y => (e y).2) x →
                  chartHessianAt (fun y => (Φ 1 (e ((extChartAt I x).symm y))).2)
                    (extChartAt I x x) =
                  chartHessianAt (fun y => (e ((extChartAt I x).symm y)).2)
                    (extChartAt I x x)) ∧
                (fun y => (Φ 1 (e y)).2) =ᶠ[𝓝 p] (fun y => (e y).2 + s) ∧
                (∀ x, IsCriticalPointAt I (fun y => (e y).2) x → x ≠ p →
                  (fun y => (Φ 1 (e y)).2) =ᶠ[𝓝 x] (fun y => (e y).2)) ∧
                ∃ K : Set (EuclideanSpace ℝ (Fin n) × ℝ), IsCompact K ∧
                  K ⊆ A '' (ball 0 r ×ˢ ball (e p).2 t) ∧ ∀ u : ℝ,
                    EqOn (Φ u) id Kᶜ ∧ EqOn (Φ u).symm id Kᶜ := by
  dsimp only
  let q := fun y => morseNormalForm hk (e p).2 (EuclideanSpace.equiv (Fin n) ℝ y)
  have hq0 : q 0 = (e p).2 := by simp [q, morseNormalForm]
  have hq : ContDiff ℝ ∞ q :=
    (contDiff_morseNormalForm hk (e p).2).comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  have hqc (y : EuclideanSpace ℝ (Fin n)) : fderiv ℝ q y = 0 ↔ y = 0 :=
    fderiv_morseNormalForm_euclidean_eq_zero_iff hk (e p).2 y
  obtain ⟨r, hr, t, ht, χ, A, hχ, hχ0, hAh, hgraph, _, hset⟩ :=
    exists_global_height_preserving_morse_normal_neighborhood he k hk hnd hindex
  let e' : M → EuclideanSpace ℝ (Fin n) × ℝ := A.symm ∘ e
  have he' : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e' :=
    he.diffeomorph_comp A.symm
  have hAi (z : EuclideanSpace ℝ (Fin n) × ℝ) : (A.symm z).2 = z.2 :=
    (hAh (A.symm z)).symm.trans (congrArg Prod.snd (A.apply_symm_apply z))
  have he'h : (fun x => (e' x).2) = fun x => (e x).2 := funext fun x => hAi (e x)
  have he'graph (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ closedBall 0 r) :
      e' (χ y) = (y, q y) := by
    change A.symm (e (χ y)) = (y, q y)
    rw [← hgraph y hy, A.symm_apply_apply]
  have huniq : ∀ x, (e' x).2 = q 0 →
      IsCriticalPointAt I (fun y => (e' y).2) x → x = χ 0 := by
    intro x hx hc
    rw [hχ0]
    rw [he'h] at hc
    exact hunique x ((hAi (e x)).symm.trans (hx.trans hq0)) hc
  obtain ⟨ρ, hρ, hρc, hρU, hρone, ε, hε, hfamily⟩ :=
    exists_isotopy_graph_critical_value_shift hq hqc isOpen_ball (mem_ball_self hr)
      (isOpen_ball.prod isOpen_ball) ⟨mem_ball_self hr, mem_ball_self ht⟩
  refine ⟨r, t, hr, ht, χ, A, hχ, hχ0, hAh, fun y hy => (hgraph y hy).symm,
    hset, ρ, hρ, hρc, hρU, hρone, ε, hε, ?_⟩
  intro s hs
  obtain ⟨hgc, G, hG, hGi, hG0, _, hGgraph, K, hK, hKO, hfix⟩ := hfamily s hs
  let g := fun y => q y + s * ρ y
  have hregular (hs0 : s ≠ 0) : ∀ x, (G 1 (e' x)).2 = q 0 →
      ¬ IsCriticalPointAt I (fun y => (G 1 (e' y)).2) x := by
    have hgp : g 0 ≠ q 0 := by
      have hρ0 : ρ 0 = 1 := hρone.eq_of_nhds
      simpa only [g, hρ0, mul_one, ne_eq, add_eq_left] using hs0
    have hg : ∀ y, g y = q 0 → fderiv ℝ g y ≠ 0 := by
      intro y hy hz
      exact hgp ((hgc y).mp hz ▸ hy)
    exact regular_height_of_graph_neighborhood he' χ hr hχ he'graph
      (by simpa only [hq0] using hset) huniq (G 1) hGgraph hg hgp hK hKO (hfix 1).1
  let Φ := fun u => A.symm.trans ((G u).trans A)
  have hΦh : (fun x => (Φ 1 (e x)).2) = fun x => (G 1 (e' x)).2 :=
    funext fun x => hAh (G 1 (e' x))
  have hgerm : g =ᶠ[𝓝 0] (fun y => q y + s) := by
    filter_upwards [hρone] with y hy
    change q y + s * ρ y = q y + s
    rw [hy, Pi.one_apply, mul_one]
  obtain ⟨hcritical, hpgerm, hother⟩ := critical_points_of_graph_neighborhood he' χ hr hχ
    he'graph (by simpa only [hq0] using hset) hqc hgc hgerm (G 1) hGgraph hK hKO (hfix 1).1
  have hcritical' (x : M) : IsCriticalPointAt I (fun y => (Φ 1 (e y)).2) x ↔
      IsCriticalPointAt I (fun y => (e y).2) x := by
    rw [hΦh, ← he'h]
    exact hcritical x
  have hpgerm' : (fun y => (Φ 1 (e y)).2) =ᶠ[𝓝 p] (fun y => (e y).2 + s) := by
    rw [hΦh, ← hχ0]
    filter_upwards [hpgerm] with y hy
    exact hy.trans (congrArg (fun z => z + s) (hAi (e y)))
  have hother' (x : M) (hx : IsCriticalPointAt I (fun y => (e y).2) x) (hxp : x ≠ p) :
      (fun y => (Φ 1 (e y)).2) =ᶠ[𝓝 x] (fun y => (e y).2) := by
    have hx' : IsCriticalPointAt I (fun y => (e' y).2) x := by rwa [he'h]
    simpa only [he'h, ← hΦh] using hother x hx' (by rwa [hχ0])
  have hhessian (x : M) (hx : IsCriticalPointAt I (fun y => (e y).2) x) :
      chartHessianAt (fun y => (Φ 1 (e ((extChartAt I x).symm y))).2) (extChartAt I x x) =
        chartHessianAt (fun y => (e ((extChartAt I x).symm y)).2) (extChartAt I x x) := by
    by_cases hxp : x = p
    · subst x
      exact chartHessianAt_eq_of_eventuallyEq_add_const BoundarylessManifold.isInteriorPoint hpgerm'
    · have hgerm0 : (fun y => (Φ 1 (e y)).2) =ᶠ[𝓝 x] (fun y => (e y).2 + 0) := by
        simpa only [add_zero] using hother' x hx hxp
      exact chartHessianAt_eq_of_eventuallyEq_add_const BoundarylessManifold.isInteriorPoint hgerm0
  refine ⟨hgc, Φ, ?_, ?_, ?_, ?_, ?_, hcritical', hhessian, hpgerm', hother',
    A '' K, hK.image A.contMDiff.continuous, ?_, ?_⟩
  · exact A.contMDiff.contDiff.comp
      (hG.comp (contDiff_fst.prodMk (A.symm.contMDiff.contDiff.comp contDiff_snd)))
  · exact A.contMDiff.contDiff.comp
      (hGi.comp (contDiff_fst.prodMk (A.symm.contMDiff.contDiff.comp contDiff_snd)))
  · apply Diffeomorph.ext
    intro z
    change A (G 0 (A.symm z)) = z
    rw [hG0]
    exact A.apply_symm_apply z
  · intro y
    change A (G 1 (A.symm (A (y, q y)))) = A (y, g y)
    rw [A.symm_apply_apply, hGgraph]
  · intro hs0 x hx hc
    have hxc : (G 1 (e' x)).2 = q 0 :=
      (congrFun hΦh x).symm.trans (hx.trans hq0.symm)
    apply hregular hs0 x hxc
    rwa [hΦh] at hc
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, by simpa only [hq0] using hKO hz, rfl⟩
  · intro u
    constructor
    · intro z hz
      have hi : A.symm z ∉ K := fun h => hz ⟨A.symm z, h, A.apply_symm_apply z⟩
      change A (G u (A.symm z)) = z
      rw [(hfix u).1 hi]
      exact A.apply_symm_apply z
    · intro z hz
      have hi : A.symm z ∉ K := fun h => hz ⟨A.symm z, h, A.apply_symm_apply z⟩
      change A ((G u).symm (A.symm z)) = z
      rw [(hfix u).2 hi]
      exact A.apply_symm_apply z

open CellAttachment in
theorem exists_ambient_isotopy_regular_critical_height
    {e : M → EuclideanSpace ℝ (Fin n) × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e)
    {p : M} (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I (fun x => (e x).2) p)
    (hindex : sigNeg (chartHessianAt (fun y => (e ((extChartAt I p).symm y)).2)
      (extChartAt I p p)) = k)
    (hunique : ∀ x, (e x).2 = (e p).2 →
      IsCriticalPointAt I (fun y => (e y).2) x → x = p)
    {η : ℝ} (hη : 0 < η) :
    let q := fun y => morseNormalForm hk (e p).2 (EuclideanSpace.equiv (Fin n) ℝ y)
    ∃ s r t : ℝ, 0 < s ∧ s < η ∧ 0 < r ∧ 0 < t ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (EuclideanSpace ℝ (Fin n)) M ∞,
        ∃ A : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ),
          closedBall 0 r ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, (A z).2 = z.2) ∧
          (∀ y ∈ closedBall 0 r, e (χ y) = A (y, q y)) ∧
          ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ ∞ g ∧ EqOn g q (ball 0 r)ᶜ ∧ g =ᶠ[𝓝 0] (fun y => q y + s) ∧
            ∃ Φ : ℝ → ((EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)),
              ContDiff ℝ ∞ (fun z : ℝ × (EuclideanSpace ℝ (Fin n) × ℝ) => Φ z.1 z.2) ∧
              ContDiff ℝ ∞ (fun z : ℝ × (EuclideanSpace ℝ (Fin n) × ℝ) => (Φ z.1).symm z.2) ∧
              Φ 0 = Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
                (EuclideanSpace ℝ (Fin n) × ℝ) ∞ ∧
              (∀ y ∈ closedBall 0 r, Φ 1 (e (χ y)) = A (y, g y)) ∧
              (∀ x, (Φ 1 (e x)).2 = (e p).2 →
                ¬ IsCriticalPointAt I (fun y => (Φ 1 (e y)).2) x) ∧
              ∃ K : Set (EuclideanSpace ℝ (Fin n) × ℝ), IsCompact K ∧
                K ⊆ A '' (ball 0 r ×ˢ ball (e p).2 t) ∧ ∀ u : ℝ,
                  EqOn (Φ u) id Kᶜ ∧ EqOn (Φ u).symm id Kᶜ := by
  dsimp only
  let q := fun y => morseNormalForm hk (e p).2 (EuclideanSpace.equiv (Fin n) ℝ y)
  have hq : ContDiff ℝ ∞ q :=
    (contDiff_morseNormalForm hk (e p).2).comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  obtain ⟨r, t, hr, ht, χ, A, hχ, hχ0, hAh, hgraph, _, ρ, hρ, _, hρU, hρone,
    ε, hε, hfamily⟩ := exists_ambient_isotopy_critical_value_shift he k hk hnd hindex hunique
  let s := min η ε / 2
  have hs : 0 < s := half_pos (lt_min hη hε)
  have hsη : s < η := (half_lt_self (lt_min hη hε)).trans_le (min_le_left _ _)
  have hsε : |s| < ε := by
    rw [abs_of_pos hs]
    exact (half_lt_self (lt_min hη hε)).trans_le (min_le_right _ _)
  obtain ⟨_, Φ, hΦ, hΦi, hΦ0, hΦgraph, hregular, _, _, _, _, hsupport⟩ := hfamily s hsε
  let g := fun y => q y + s * ρ y
  refine ⟨s, r, t, hs, hsη, hr, ht, χ, A, hχ, hχ0, hAh, hgraph,
    g, hq.add (contDiff_const.mul hρ), ?_, ?_, Φ, hΦ, hΦi, hΦ0,
    ?_, hregular hs.ne', hsupport⟩
  · intro y hy
    have hnot : y ∉ tsupport ρ := fun h => hy (hρU h)
    simp only [g, image_eq_zero_of_notMem_tsupport hnot, mul_zero, add_zero]
    rfl
  · filter_upwards [hρone] with y hy
    change q y + s * ρ y = q y + s
    rw [hy, Pi.one_apply, mul_one]
  · intro y hy
    rw [hgraph y hy]
    exact hΦgraph y

end Embedded

end DifferentialGeometry.Topology.Morse
