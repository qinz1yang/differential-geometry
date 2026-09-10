import DifferentialGeometry.Geometry.Neck.ControlledCollarPatch
import DifferentialGeometry.Geometry.Neck.RegularEndpoints
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import DifferentialGeometry.Topology.Ehresmann.BoundaryAnnulus

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Geometry.Affine Poincare.Geometry.Boundary
open Poincare.Topology.Manifold Poincare.Topology.Ehresmann

namespace Poincare.Geometry.Neck

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem subset_interior_of_closed_separator
    {X : Type*} [TopologicalSpace X] {S P K Q : Set X}
    (hK : IsClosed K) (hQ : IsClosed Q) (hcover : P ∪ K ∪ Q = univ)
    (hPQ : Disjoint P Q) (hSP : S ⊆ P) (hSK : Disjoint S K) : S ⊆ interior P := by
  intro x hx
  have hxO : x ∈ (K ∪ Q)ᶜ := by
    rintro (h | h)
    · exact Set.disjoint_left.mp hSK hx h
    · exact Set.disjoint_left.mp hPQ (hSP hx) h
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [(hK.union hQ).isOpen_compl.mem_nhds hxO] with y hy
  have hym : y ∈ P ∪ K ∪ Q := hcover.symm ▸ mem_univ y
  rcases hym with (hp | hk) | hq
  · exact hp
  · exact (hy (Or.inl hk)).elim
  · exact (hy (Or.inr hq)).elim

private theorem partition_sum_eq_of_one
    {κ X : Type*} [Fintype κ] [TopologicalSpace X]
    (ρ : PartitionOfUnity κ X) (v : κ → X → ℝ) (i : κ) (x : X) (hi : ρ i x = 1) :
    (∑ j, ρ j x * v j x) = v i x := by
  classical
  have hsum : ∑ j, ρ j x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  have hrest : ∑ j ∈ Finset.univ.erase i, ρ j x = 0 := by
    have h := Finset.sum_erase_add Finset.univ (fun j ↦ ρ j x) (Finset.mem_univ i)
    rw [hsum, hi] at h
    linarith only [h]
  have hz : ∀ j, j ≠ i → ρ j x = 0 := by
    intro j hj
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ ρ.nonneg j x)).mp hrest j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [hz j hj, zero_mul]) (by simp), hi, one_mul]

theorem exists_regular_data_of_controlled_collar_regions (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀
    {E H W : Type} {F G M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace W] [ChartedSpace H W] [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [T2Space W] [CompactSpace W] [PreconnectedSpace W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M],
    ∀ (n : ℕ) [NeZero n] (ι : W → M), ContMDiff I J ∞ ι →
    IsEmbedding ι → (∀ w, Function.Injective (mfderiv I J ι w)) →
    Module.finrank ℝ E = Module.finrank ℝ F →
    ∀ (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
      (U : ∀ i, Set (C i).domain), (∀ i, IsOpen (U i)) →
    ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ → (∀ i, (C i).metricCloseOn g ε (U i)) →
    ∀ (s c : Fin n → ℝ), (∀ j, s j = 1 ∨ s j = -1) →
    let a := finiteLineAffineAlignment s c
    let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
    let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
    ∀ (k : Fin n → Fin (n + 1)), (∀ j, k j = j.castSucc ∨ k j = j.succ) →
    ∀ (l r : Fin n → ℝ) (hwidth : ∀ j, 1 ≤ r j - l j),
    ∀ hcollar : ∀ j p t, t ∈ Icc (l j) (r j) → (p, (a (k j)).1 * t) ∈ (C (k j)).domain,
    let e := fun j (x : S² × Icc (l j) (r j)) ↦
      ((C (k j)).chart ⟨(x.1, (a (k j)).1 * (x.2 : ℝ)), hcollar j x.1 x.2 x.2.property⟩ : M)
    (∀ j x, e j x ∈ interior (range ι)) →
    ∀ P Q : Fin n → Set W,
    (∀ j, IsClosed (P j)) → (∀ j, IsClosed (Q j)) → (∀ j, Disjoint (P j) (Q j)) →
    (∀ j, P j ∪ ι ⁻¹' range (e j) ∪ Q j = univ) →
    (∀ j, P j ∩ ι ⁻¹' range (e j) ⊆
      ι ⁻¹' range (fun p : S² ↦ e j (p, ⟨l j, le_rfl, by linarith only [hwidth j]⟩))) →
    (∀ j, Q j ∩ ι ⁻¹' range (e j) ⊆
      ι ⁻¹' range (fun p : S² ↦ e j (p, ⟨r j, by linarith only [hwidth j], le_rfl⟩))) →
    (∀ i j, i < j → interior (Q i) ∪ interior (P j) = univ) →
    (∀ i w, (∀ j : Fin n, i = j.castSucc → w ∉ interior (Q j)) →
      (∀ j : Fin n, i = j.succ → w ∉ interior (P j)) → w ∈ V i) →
    (∀ j, ι ⁻¹' range (e j) ⊆ V j.castSucc ∩ V j.succ) →
    (∀ j, ∀ w ∈ ι ⁻¹' range (e j), |(C j.succ).axial (ι w) -
      (s j * (C j.castSucc).axial (ι w) + c j)| ≤ Cₒ * ε / Real.sqrt (C j.castSucc).scale) →
    (∀ j, ∀ w ∈ ι ⁻¹' range (e j),
      Real.sqrt (g.inner (ι w)
        (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))
        (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))) ≤ Cₒ * ε) →
    ∀ S₀ S₁ : Set W, I.boundary W = S₀ ∪ S₁ →
    S₀ ⊆ P ⟨0, NeZero.pos n⟩ → S₁ ⊆ Q ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by decide)⟩ →
    ∀ (t₀ t₁ : ℝ)
      (hsection₀ : ∀ p : S², (p, t₀) ∈ (C 0).domain)
      (hsection₁ : ∀ p : S², (p, t₁) ∈ (C (Fin.last n)).domain),
    (ι '' S₀ = range (fun p ↦ ((C 0).chart ⟨(p, t₀), hsection₀ p⟩ : M))) →
    (ι '' S₁ = range (fun p ↦ ((C (Fin.last n)).chart ⟨(p, t₁), hsection₁ p⟩ : M))) →
    ∀ (d : ℝ), 0 < d →
    ∀ hsegment : ∀ (p : S²) t, t ∈ Icc 0 d → (p, t₀ + (a 0).1 * t) ∈ (C 0).domain,
    (∀ (p : S²) t (ht : t ∈ Icc 0 d),
      ((C 0).chart ⟨(p, t₀ + (a 0).1 * t), hsegment p t ht⟩ : M) ∈ range ι) →
    ∃ (θ : Fin (n + 2) → C^∞⟮I, W; 𝓘(ℝ), ℝ⟯)
      (horder : ∀ w, Antitone (fun i ↦ θ i w))
      (hfirst : ∀ w, θ 0 w = 1) (hlast : ∀ w, θ (Fin.last (n + 1)) w = 0),
      let χ := orderedStepPartition θ horder hfirst hlast
      (∀ i, tsupport (χ i) ⊆ V i) ∧
      let u := fun w ↦ ∑ i, χ i w * v i w
      let b₀ := (a 0).1 * (Real.sqrt (C 0).scale)⁻¹ * t₀ + (a 0).2
      let b₁ := (a (Fin.last n)).1 * (Real.sqrt (C (Fin.last n)).scale)⁻¹ * t₁ + (a (Fin.last n)).2
      ∃ (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hb : b₀ < b₁)
        (hbdy : ∀ w, I.IsBoundaryPoint w → u w = b₀ ∨ u w = b₁),
        RegularIntervalDatum I u b₀ b₁ ∧
        u ⁻¹' ({b₀} : Set ℝ) = S₀ ∧ u ⁻¹' ({b₁} : Set ℝ) = S₁ ∧
        (∀ᶠ w in 𝓝ˢ S₀, χ 0 w = 1) ∧
        (∀ᶠ w in 𝓝ˢ S₁, χ (Fin.last n) w = 1) ∧
        (∀ᶠ w in 𝓝ˢ S₀, u w = v 0 w) ∧
        (∀ᶠ w in 𝓝ˢ S₁, u w = v (Fin.last n) w) ∧
        ∃ η₀ : S² ≃ₘ⟮𝓡 2, hI.boundaryI⟯
            boundaryLevel u b₀ b₁ hb.ne hu.continuous hbdy,
          (∀ p, ι (η₀ p).1.1 = ((C 0).chart ⟨(p, t₀), hsection₀ p⟩ : M)) ∧
          ∃ Ψ : (S² × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), I⟯ W,
            (∀ p, u (Ψ p) = b₀ + (b₁ - b₀) * (p.2 : ℝ)) ∧
            ∀ p, ι (Ψ (p, ⟨0, by norm_num⟩)) = ((C 0).chart ⟨(p, t₀), hsection₀ p⟩ : M) := by
  classical
  obtain ⟨ε₀, hε₀, hpatch⟩ := exists_regular_patch_of_controlled_collar_regions Cₒ hCₒ
  refine ⟨ε₀, hε₀, ?_⟩
  intro E H W F G M _ _ _ _ I _ _ hI _ _ _ _ _ _ _ _ J _ _ _ _ _
  specialize hpatch (W := W) (M := M) I J
  intro n hn ι hι hemb hfull hdim g C U hU ε hεnonneg hε hmetric s c hs
    a v V k hk l r hwidth hcollar e hinternal P Q hP hQ hPQ hcover hleft hright hsep
    hcontrolled hKV hvalue hgradient S₀ S₁ hboundary hS₀ hS₁ t₀ t₁
    hsection₀ hsection₁ himage₀ himage₁ d hd hsegment hinward
  obtain ⟨θ, horder, hfirst, hlast, hzero, hone, hsupp, hu, hreg⟩ :=
    hpatch n ι hι hemb hfull hdim g C U hU ε hεnonneg hε hmetric s c hs
      k hk l r hwidth hcollar hinternal P Q hP hQ hPQ hcover hleft hright hsep
      hcontrolled hKV hvalue hgradient
  let χ := orderedStepPartition θ horder hfirst hlast
  let u := fun w ↦ ∑ i, χ i w * v i w
  let j₀ : Fin n := ⟨0, NeZero.pos n⟩
  let j₁ : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by decide)⟩
  have hKclosed (j : Fin n) : IsClosed (ι ⁻¹' range (e j)) := by
    have he : Continuous (e j) := by
      exact continuous_subtype_val.comp ((C (k j)).chart.continuous.comp
        ((continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd))).subtype_mk _))
    exact (isCompact_range he).isClosed.preimage hι.continuous
  have hdisj (j : Fin n) : Disjoint (I.boundary W) (ι ⁻¹' range (e j)) := by
    apply Set.disjoint_left.mpr
    rintro w hw ⟨x, hx⟩
    have hi := isInteriorPoint_of_mem_interior_range_of_fullRank_embedding
      ι hι hemb hfull hdim (hx ▸ hinternal j x)
    have hb : w ∈ (I.interior W)ᶜ := by rw [I.compl_interior]; exact hw
    exact hb hi
  have hS₀int : S₀ ⊆ interior (P j₀) :=
    subset_interior_of_closed_separator (hKclosed j₀) (hQ j₀) (hcover j₀) (hPQ j₀)
      hS₀ ((hdisj j₀).mono_left (by intro w hw; rw [hboundary]; exact Or.inl hw))
  have hS₁int : S₁ ⊆ interior (Q j₁) :=
    subset_interior_of_closed_separator (hKclosed j₁) (hP j₁)
      (by rw [union_comm (Q j₁ ∪ _) (P j₁), union_comm (Q j₁) _, ← union_assoc]; exact hcover j₁)
      (hPQ j₁).symm hS₁
      ((hdisj j₁).mono_left (by intro w hw; rw [hboundary]; exact Or.inr hw))
  have hzero' : ∀ w ∈ P j₀, θ (0 : Fin (n + 1)).succ w = 0 := by
    intro w hw
    simpa only [show j₀.succ.castSucc = (0 : Fin (n + 1)).succ from Fin.ext rfl] using hzero j₀ w hw
  have hone' : ∀ w ∈ Q j₁, θ (Fin.last n).castSucc w = 1 := by
    intro w hw
    have hj : j₁.succ.castSucc = (Fin.last n).castSucc := by
      apply Fin.ext
      change n - 1 + 1 = n
      have := NeZero.pos n
      omega
    simpa only [hj] using hone j₁ w hw
  have hweight₀ : ∀ᶠ w in 𝓝ˢ S₀, χ 0 w = 1 := by
    apply mem_nhdsSet_iff_forall.mpr
    intro x hx
    exact orderedStepPartition_first_eq_one_near θ horder hfirst hlast hzero' (hS₀int hx)
  have hweight₁ : ∀ᶠ w in 𝓝ˢ S₁, χ (Fin.last n) w = 1 := by
    apply mem_nhdsSet_iff_forall.mpr
    intro x hx
    exact orderedStepPartition_last_eq_one_near θ horder hfirst hlast hone' (hS₁int hx)
  have hlocal₀ : ∀ᶠ w in 𝓝ˢ S₀, u w = v 0 w := by
    filter_upwards [hweight₀] with w hw
    exact partition_sum_eq_of_one χ.toPartitionOfUnity v 0 w hw
  have hlocal₁ : ∀ᶠ w in 𝓝ˢ S₁, u w = v (Fin.last n) w := by
    filter_upwards [hweight₁] with w hw
    exact partition_sum_eq_of_one χ.toPartitionOfUnity v (Fin.last n) w hw
  obtain ⟨hb, hbdy, hdata, hfiber₀, hfiber₁, hη₀⟩ := exists_regular_endpoints_of_extreme_neck_sections
    ι hι hemb hfull hdim (C 0) (C (Fin.last n)) t₀ t₁ (a 0).1 (a (Fin.last n)).1
    (a 0).2 (a (Fin.last n)).2 (finiteLineAffineAlignment_sign s c hs 0)
    S₀ S₁ hboundary hsection₀ hsection₁ himage₀ himage₁ u hu hreg hlocal₀ hlocal₁ d hd hsegment hinward
  obtain ⟨η₀, hη₀⟩ := hη₀
  obtain ⟨Ψ, hheight, hstart, _⟩ := exists_boundary_sphere_annulus hb hu hreg hbdy
    (hdata.range_eq.symm ▸ (show _ ∈ Icc _ _ from ⟨le_rfl, hb.le⟩))
    (hdata.range_eq.symm ▸ (show _ ∈ Icc _ _ from ⟨hb.le, le_rfl⟩)) η₀
  refine ⟨θ, horder, hfirst, hlast, hsupp, hu, hb, hbdy, hdata, hfiber₀, hfiber₁,
    hweight₀, hweight₁, hlocal₀, hlocal₁, η₀, hη₀, Ψ, hheight, ?_⟩
  intro p
  rw [hstart]
  exact hη₀ p

end Poincare.Geometry.Neck
