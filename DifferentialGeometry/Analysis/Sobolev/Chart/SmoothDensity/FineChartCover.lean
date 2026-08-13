import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.PouStrictCutoff
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

open Set Topology Bundle Manifold Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
def extChartOpenPartialHomeomorph (x : M) : OpenPartialHomeomorph M E where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

def chartBall (e : OpenPartialHomeomorph M E) (z : E) (r : ℝ) : Set M :=
  e.source ∩ e ⁻¹' Metric.ball z r

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [T2Space M] [SigmaCompactSpace M] in
theorem isOpen_chartBall (e : OpenPartialHomeomorph M E) (z : E) (r : ℝ) :
    IsOpen (chartBall e z r) :=
  e.isOpen_inter_preimage Metric.isOpen_ball

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [T2Space M] [SigmaCompactSpace M] in
theorem chartBall_mono (e : OpenPartialHomeomorph M E) (z : E)
    {r R : ℝ} (hrR : r ≤ R) :
    chartBall e z r ⊆ chartBall e z R := by
  intro x hx
  exact ⟨hx.1, Metric.ball_subset_ball hrR hx.2⟩

def chartClosedBall (e : PartialEquiv M E) (z : E) (r : ℝ) : Set M :=
  e.symm '' Metric.closedBall z r

omit [T2Space M] [SigmaCompactSpace M] in
theorem chartClosedBall_cpt_of_continuousOn
    (e : PartialEquiv M E) (z : E) (r : ℝ)
    (he : ContinuousOn e.symm e.target)
    (hball : Metric.closedBall z r ⊆ e.target) :
    IsCompact (chartClosedBall e z r) := by
  exact (isCompact_closedBall z r).image_of_continuousOn
    (he.mono hball)

omit [T2Space M] [SigmaCompactSpace M] in
theorem chartClosedBall_cpt (e : OpenPartialHomeomorph M E) (z : E) (r : ℝ)
    (hball : Metric.closedBall z r ⊆ e.target) :
    IsCompact (chartClosedBall e.toPartialEquiv z r) :=
  chartClosedBall_cpt_of_continuousOn e.toPartialEquiv z r
    e.continuousOn_symm hball

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
  [T2Space M] [SigmaCompactSpace M] in
theorem chartClosedBall_src (e : PartialEquiv M E) (z : E) (r : ℝ)
    (hball : Metric.closedBall z r ⊆ e.target) :
    chartClosedBall e z r ⊆ e.source := by
  rintro x ⟨y, hy, rfl⟩
  exact e.map_target (hball hy)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
  [T2Space M] [SigmaCompactSpace M] in
theorem chartClosedBall_map (e : PartialEquiv M E) (z : E) (r : ℝ)
    (hball : Metric.closedBall z r ⊆ e.target) {x : M}
    (hx : x ∈ chartClosedBall e z r) :
    e x ∈ Metric.closedBall z r := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [e.right_inv (hball hy)]
  exact hy

def chartBuffer (e : PartialEquiv M E) (K : Set M) (r : ℝ) : Set M :=
  e.symm '' Metric.cthickening r (e '' K)

omit [T2Space M] [SigmaCompactSpace M] in
theorem chartBuffer_cpt_of_continuousOn
    (e : PartialEquiv M E) {K : Set M} (r : ℝ)
    (he : ContinuousOn e e.source)
    (he_symm : ContinuousOn e.symm e.target)
    (hK : IsCompact K) (hKsrc : K ⊆ e.source)
    (hbuffer : Metric.cthickening r (e '' K) ⊆ e.target) :
    IsCompact (chartBuffer e K r) := by
  have hKimage : IsCompact (e '' K) :=
    hK.image_of_continuousOn (he.mono hKsrc)
  exact hKimage.cthickening.image_of_continuousOn
    (he_symm.mono hbuffer)

omit [T2Space M] [SigmaCompactSpace M] in
theorem chartBuffer_cpt (e : OpenPartialHomeomorph M E) {K : Set M} (r : ℝ)
    (hK : IsCompact K) (hKsrc : K ⊆ e.source)
    (hbuffer : Metric.cthickening r (e '' K) ⊆ e.target) :
    IsCompact (chartBuffer e.toPartialEquiv K r) :=
  chartBuffer_cpt_of_continuousOn e.toPartialEquiv r e.continuousOn
    e.continuousOn_symm hK hKsrc hbuffer

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
  [T2Space M] [SigmaCompactSpace M] in
theorem chartBuffer_src (e : PartialEquiv M E) (K : Set M) (r : ℝ)
    (hbuffer : Metric.cthickening r (e '' K) ⊆ e.target) :
    chartBuffer e K r ⊆ e.source := by
  rintro x ⟨y, hy, rfl⟩
  exact e.map_target (hbuffer hy)

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_chartBuffer_of_continuousOn
    (e : PartialEquiv M E) {K : Set M}
    (he : ContinuousOn e e.source)
    (he_symm : ContinuousOn e.symm e.target)
    (he_target : IsOpen e.target)
    (hK : IsCompact K) (hKsrc : K ⊆ e.source) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      Metric.cthickening r₀ (e '' K) ⊆ e.target ∧
      IsCompact (chartBuffer e K r₀) ∧
      chartBuffer e K r₀ ⊆ e.source := by
  have hKimage : IsCompact (e '' K) :=
    hK.image_of_continuousOn (he.mono hKsrc)
  have hKimage_target : e '' K ⊆ e.target := by
    rintro y ⟨x, hxK, rfl⟩
    exact e.map_source (hKsrc hxK)
  obtain ⟨r₀, hr₀, hbuffer⟩ :=
    hKimage.exists_cthickening_subset_open he_target hKimage_target
  exact ⟨r₀, hr₀, hbuffer,
    chartBuffer_cpt_of_continuousOn e r₀ he he_symm hK hKsrc hbuffer,
    chartBuffer_src e K r₀ hbuffer⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_chartBuffer
    (e : OpenPartialHomeomorph M E) {K : Set M}
    (hK : IsCompact K) (hKsrc : K ⊆ e.source) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      Metric.cthickening r₀ (e '' K) ⊆ e.target ∧
      IsCompact (chartBuffer e.toPartialEquiv K r₀) ∧
      chartBuffer e.toPartialEquiv K r₀ ⊆ e.source :=
  exists_chartBuffer_of_continuousOn e.toPartialEquiv e.continuousOn
    e.continuousOn_symm e.open_target hK hKsrc

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
  [T2Space M] [SigmaCompactSpace M] in
theorem outer_subset_buffer
    (e : PartialEquiv M E) {K : Set M} {x : M} (hx : x ∈ K)
    {R r₀ : ℝ} (hR : R ≤ r₀) :
    chartClosedBall e (e x) R ⊆ chartBuffer e K r₀ := by
  apply Set.image_mono
  have hex : e x ∈ e '' K := ⟨x, hx, rfl⟩
  exact (Metric.closedBall_subset_cthickening hex R).trans
    (Metric.cthickening_mono hR (e '' K))

omit [I.Boundaryless] in
theorem exists_fine_pou
    (e : OpenPartialHomeomorph M E) {K : Set M}
    (hK : IsCompact K) (hKsrc : K ⊆ e.source)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε ≤ r ∧
      ∃ S : Finset K,
        ∃ ρ : SmoothPartitionOfUnity S I M K,
          ρ.IsSubordinate
              (fun z : S => chartBall e (e (z.1 : K)) ε) ∧
            ∀ z : S,
              Metric.closedBall (e (z.1 : K)) (2 * ε) ⊆ e.target := by
  classical
  have hKimage : IsCompact (e '' K) :=
    hK.image_of_continuousOn (e.continuousOn.mono hKsrc)
  have hKimage_target : e '' K ⊆ e.target := by
    rintro y ⟨x, hxK, rfl⟩
    exact e.map_source (hKsrc hxK)
  obtain ⟨δ, hδ, hδtarget⟩ :=
    hKimage.exists_cthickening_subset_open e.open_target hKimage_target
  let ε : ℝ := min (δ / 4) (r / 4)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (div_pos hδ (by norm_num)) (div_pos hr (by norm_num))
  have hεδ : 2 * ε ≤ δ := by
    have hle : ε ≤ δ / 4 := min_le_left _ _
    linarith
  have hεr : 2 * ε ≤ r := by
    have hle : ε ≤ r / 4 := min_le_right _ _
    linarith
  let U : K → Set M := fun z => chartBall e (e (z : M)) ε
  have hUopen : ∀ z, IsOpen (U z) := by
    intro z
    exact isOpen_chartBall e (e (z : M)) ε
  have hKU : K ⊆ ⋃ z : K, U z := by
    intro x hxK
    refine mem_iUnion.mpr ⟨⟨x, hxK⟩, ?_⟩
    exact ⟨hKsrc hxK, Metric.mem_ball_self hε⟩
  obtain ⟨S, hScover⟩ := hK.elim_finite_subcover U hUopen hKU
  have hScover' : K ⊆ ⋃ z : S, chartBall e (e (z.1 : K)) ε := by
    intro x hxK
    obtain ⟨z, hzS, hxz⟩ := mem_iUnion₂.mp (hScover hxK)
    exact mem_iUnion.mpr ⟨⟨z, hzS⟩, hxz⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I) (M := M) hK.isClosed
    (fun z : S => chartBall e (e (z.1 : K)) ε)
    (fun z => isOpen_chartBall e (e (z.1 : K)) ε) hScover'
  refine ⟨ε, hε, hεr, S, ρ, hρ, ?_⟩
  intro z
  have hzKimage : e (z.1 : K) ∈ e '' K :=
    ⟨(z.1 : K), (z.1 : K).property, rfl⟩
  exact (Metric.closedBall_subset_cthickening hzKimage (2 * ε)).trans
    ((Metric.cthickening_mono hεδ (e '' K)).trans hδtarget)

omit [I.Boundaryless] in
theorem exists_fine_cutoffs [NormalSpace M]
    (e : OpenPartialHomeomorph M E) {K : Set M}
    (hK : IsCompact K) (hKsrc : K ⊆ e.source)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε ≤ r ∧
      ∃ S : Finset K,
        ∃ ρ : SmoothPartitionOfUnity S I M K,
          ∃ χ : S → M → ℝ,
            ρ.IsSubordinate
                (fun z : S => chartBall e (e (z.1 : K)) ε) ∧
            (∀ z : S,
              Metric.closedBall (e (z.1 : K)) (2 * ε) ⊆ e.target) ∧
            (∀ z, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ z)) ∧
            (∀ z, ∀ᶠ x in 𝓝ˢ
              (tsupport ((ρ z : C^∞⟮I, M; ℝ⟯) : M → ℝ)), χ z x = 1) ∧
            (∀ z x, χ z x ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z, ∀ᶠ x in 𝓝ˢ
              ((chartBall e (e (z.1 : K)) (2 * ε))ᶜ), χ z x = 0) ∧
            ∀ z, tsupport (χ z) ⊆
              chartBall e (e (z.1 : K)) (2 * ε) := by
  obtain ⟨ε, hε, hεr, S, ρ, hρ, houter⟩ :=
    exists_fine_pou (I := I) e hK hKsrc hr
  have hinnerOuter : ∀ z : S,
      chartBall e (e (z.1 : K)) ε ⊆
        chartBall e (e (z.1 : K)) (2 * ε) := by
    intro z
    exact chartBall_mono e (e (z.1 : K)) (by linarith)
  obtain ⟨χ, hχsmooth, hχone, hχrange, hχzero, hχsupp⟩ :=
    exists_pou_cutoff (I := I) ρ
      (fun z : S => chartBall e (e (z.1 : K)) ε)
      (fun z : S => chartBall e (e (z.1 : K)) (2 * ε))
      hρ hinnerOuter
      (fun z => isOpen_chartBall e (e (z.1 : K)) (2 * ε))
  exact ⟨ε, hε, hεr, S, ρ, χ, hρ, houter, hχsmooth, hχone,
    hχrange, hχzero, hχsupp⟩

omit [I.Boundaryless] in
theorem exists_fine_tricut [NormalSpace M]
    (e : OpenPartialHomeomorph M E) {K : Set M}
    (hK : IsCompact K) (hKsrc : K ⊆ e.source)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε ≤ r ∧
      ∃ S : Finset K,
        ∃ ρ : SmoothPartitionOfUnity S I M K,
          ∃ χ ψ : S → M → ℝ,
            ρ.IsSubordinate
                (fun z : S => chartBall e (e (z.1 : K)) ε) ∧
            (∀ z : S,
              Metric.closedBall (e (z.1 : K)) (2 * ε) ⊆ e.target) ∧
            (∀ z, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (χ z)) ∧
            (∀ z, ∀ᶠ x in nhdsSet
              (tsupport ((ρ z : C^∞⟮I, M; ℝ⟯) : M → ℝ)), χ z x = 1) ∧
            (∀ z x, χ z x ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z, tsupport (χ z) ⊆
              chartBall e (e (z.1 : K)) (2 * ε)) ∧
            (∀ z, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (ψ z)) ∧
            (∀ z, ∀ᶠ x in nhdsSet (tsupport (χ z)), ψ z x = 1) ∧
            (∀ z x, ψ z x ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z, ∀ᶠ x in nhdsSet
              ((chartBall e (e (z.1 : K)) (2 * ε))ᶜ), ψ z x = 0) ∧
            ∀ z, tsupport (ψ z) ⊆
              chartBall e (e (z.1 : K)) (2 * ε) := by
  classical
  obtain ⟨ε, hε, hεr, S, ρ, χ, hρ, houter, hχsmooth, hχone,
    hχrange, _hχzero, hχsupp⟩ :=
    exists_fine_cutoffs (I := I) e hK hKsrc hr
  have hψ : ∀ z : S, ∃ ψz : M → ℝ,
      ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ψz ∧
      (∀ᶠ x in nhdsSet (tsupport (χ z)), ψz x = 1) ∧
      (∀ x, ψz x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ᶠ x in nhdsSet
        ((chartBall e (e (z.1 : K)) (2 * ε))ᶜ), ψz x = 0) ∧
      tsupport ψz ⊆ chartBall e (e (z.1 : K)) (2 * ε) := by
    intro z
    exact exists_strict_cutoff (I := I) (χ z)
      (chartBall e (e (z.1 : K)) (2 * ε))
      (isOpen_chartBall e (e (z.1 : K)) (2 * ε)) (hχsupp z)
  let ψ : S → M → ℝ := fun z => Classical.choose (hψ z)
  have hψspec : ∀ z : S,
      ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (ψ z) ∧
      (∀ᶠ x in nhdsSet (tsupport (χ z)), ψ z x = 1) ∧
      (∀ x, ψ z x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ᶠ x in nhdsSet
        ((chartBall e (e (z.1 : K)) (2 * ε))ᶜ), ψ z x = 0) ∧
      tsupport (ψ z) ⊆ chartBall e (e (z.1 : K)) (2 * ε) :=
    fun z => Classical.choose_spec (hψ z)
  refine ⟨ε, hε, hεr, S, ρ, χ, ψ, hρ, houter, hχsmooth,
    hχone, hχrange, hχsupp, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun z => (hψspec z).1
  · exact fun z => (hψspec z).2.1
  · exact fun z => (hψspec z).2.2.1
  · exact fun z => (hψspec z).2.2.2.1
  · exact fun z => (hψspec z).2.2.2.2

structure FineChartData
    (e : OpenPartialHomeomorph M E) (K : Set M) (r : ℝ) where
  ε : ℝ
  ε_pos : 0 < ε
  double_le : 2 * ε ≤ r
  S : Finset K
  rho : SmoothPartitionOfUnity S I M K
  chi : S → C^∞⟮I, M; ℝ⟯
  psi : S → C^∞⟮I, M; ℝ⟯
  rho_sub : rho.IsSubordinate
    (fun z : S => chartBall e (e (z.1 : K)) ε)
  outer : ∀ z : S,
    Metric.closedBall (e (z.1 : K)) (2 * ε) ⊆ e.target
  chi_one : ∀ z : S, ∀ᶠ x in 𝓝ˢ
    (tsupport (((rho z : C^∞⟮I, M; ℝ⟯) : M → ℝ))),
      ((chi z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1
  chi_range : ∀ z : S, ∀ x,
    ((chi z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ∈ Set.Icc (0 : ℝ) 1
  chi_supp : ∀ z : S, tsupport
    (((chi z : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      chartBall e (e (z.1 : K)) (2 * ε)
  psi_one : ∀ z : S, ∀ᶠ x in 𝓝ˢ
    (tsupport (((chi z : C^∞⟮I, M; ℝ⟯) : M → ℝ))),
      ((psi z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1
  psi_range : ∀ z : S, ∀ x,
    ((psi z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ∈ Set.Icc (0 : ℝ) 1
  psi_zero : ∀ z : S, ∀ᶠ x in 𝓝ˢ
    ((chartBall e (e (z.1 : K)) (2 * ε))ᶜ),
      ((psi z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  psi_supp : ∀ z : S, tsupport
    (((psi z : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      chartBall e (e (z.1 : K)) (2 * ε)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [I.Boundaryless] in
theorem FineChartData.rho_sum
    {e : OpenPartialHomeomorph M E} {K : Set M} {r : ℝ}
    (D : FineChartData (I := I) e K r) {x : M} (hx : x ∈ K) :
    ∑ z : D.S, ((D.rho z : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using D.rho.sum_eq_one hx

omit [I.Boundaryless] in
theorem existsFineChart [NormalSpace M]
    (e : OpenPartialHomeomorph M E) {K : Set M}
    (hK : IsCompact K) (hKsrc : K ⊆ e.source)
    {r : ℝ} (hr : 0 < r) :
    Nonempty (FineChartData (I := I) e K r) := by
  classical
  obtain ⟨ε, hε, hεr, S, ρ, χ, ψ, hρ, houter, hχsmooth,
    hχone, hχrange, hχsupp, hψsmooth, hψone, hψrange, hψzero, hψsupp⟩ :=
    exists_fine_tricut (I := I) e hK hKsrc hr
  let χb : S → C^∞⟮I, M; ℝ⟯ := fun z => ⟨χ z, hχsmooth z⟩
  let ψb : S → C^∞⟮I, M; ℝ⟯ := fun z => ⟨ψ z, hψsmooth z⟩
  refine ⟨{
    ε := ε
    ε_pos := hε
    double_le := hεr
    S := S
    rho := ρ
    chi := χb
    psi := ψb
    rho_sub := hρ
    outer := houter
    chi_one := ?_
    chi_range := ?_
    chi_supp := ?_
    psi_one := ?_
    psi_range := ?_
    psi_zero := ?_
    psi_supp := ?_ }⟩
  · intro z
    simpa only [χb, ContMDiffMap.coeFn_mk] using hχone z
  · intro z x
    simpa only [χb, ContMDiffMap.coeFn_mk] using hχrange z x
  · intro z
    simpa only [χb, ContMDiffMap.coeFn_mk] using hχsupp z
  · intro z
    simpa only [χb, ψb, ContMDiffMap.coeFn_mk] using hψone z
  · intro z x
    simpa only [ψb, ContMDiffMap.coeFn_mk] using hψrange z x
  · intro z
    simpa only [ψb, ContMDiffMap.coeFn_mk] using hψzero z
  · intro z
    simpa only [ψb, ContMDiffMap.coeFn_mk] using hψsupp z

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
