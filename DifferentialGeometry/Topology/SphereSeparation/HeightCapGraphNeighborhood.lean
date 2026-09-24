import DifferentialGeometry.Topology.Diffeomorph.QuadraticCapProjection
import DifferentialGeometry.Analysis.ODE.QuadraticLevelScaling
import DifferentialGeometry.Topology.Embedding.GraphChartNeighborhood
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.LevelSet.QuadraticGraph
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.Clopen

open Set Manifold Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.ODE (quadraticLevelScaling)

namespace DifferentialGeometry.Topology.SphereSeparation

theorem eq_height_cap_vertex_of_image_connectedComponentIn_superlevel
    {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    (e : M → E × ℝ) (A D : E × ℝ → E × ℝ) (hA : ∀ z, (A z).2 = z.2)
    {p : M} {c r : ℝ} (hc : (e p).2 = c)
    (hcap : e '' connectedComponentIn {x | c - r ^ 2 / 2 ≤ (e x).2} p =
      (fun y => A (y, c + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r)
    (hhi : ∃ ρ > r, ∀ t, c - r ^ 2 / 2 ≤ t →
      ∀ x ∈ ball (0 : E) ρ, D (x, t) = A (x, t)) :
    e p = D (0, c) := by
  have hp : p ∈ connectedComponentIn {x | c - r ^ 2 / 2 ≤ (e x).2} p :=
    mem_connectedComponentIn
      (by change c - r ^ 2 / 2 ≤ (e p).2; rw [hc]; nlinarith [sq_nonneg r])
  have hmem := hcap.subset (mem_image_of_mem e hp)
  have hvertex : e p = A (0, c) :=
    Function.eq_vertex_of_mem_image_quadratic_graph A hA (by norm_num : (-1 : ℝ) ≠ 0) hmem hc
  obtain ⟨y, hy, _⟩ := hmem
  obtain ⟨ρ, hrρ, hDA⟩ := hhi
  have hρ : 0 < ρ := ((norm_nonneg y).trans (mem_closedBall_zero_iff.mp hy)).trans_lt hrρ
  exact hvertex.trans (hDA c (by nlinarith [sq_nonneg r]) 0 (mem_ball_self hρ)).symm

theorem exists_cthickening_height_cap_graph_neighborhood
    {E P H M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ P H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → E × ℝ} (he : IsSmoothEmbedding I 𝓘(ℝ, E × ℝ) ∞ e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ P)
    (D : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) {a c d : ℝ} (had : a < d)
    (hcap : (D '' {z | a ≤ z.2 ∧ z.2 ≤ c - ‖z.1‖ ^ 2 / 2}) ∩ range e =
      D '' {z | a ≤ z.2 ∧ z.2 = c - ‖z.1‖ ^ 2 / 2}) :
    ∃ V : Set (E × ℝ), IsOpen V ∧
      D '' {z | a < z.2 ∧ z.2 ≤ c - ‖z.1‖ ^ 2 / 2} ⊆ V ∧
      (∀ z ∈ V, (D.symm z).1 ∈ ball (0 : E) (Real.sqrt (2 * (c - a)))) ∧
      V ∩ range e = V ∩ D '' {z | z.2 = c - ‖z.1‖ ^ 2 / 2} ∧
      ∃ δ : ℝ, 0 < δ ∧
        cthickening δ (D '' {z | d ≤ z.2 ∧ z.2 ≤ c - ‖z.1‖ ^ 2 / 2}) ⊆ V := by
  let q : E → ℝ := fun y => c - ‖y‖ ^ 2 / 2
  let U : Set E := ball 0 (Real.sqrt (2 * (c - a)))
  let f := D.symm ∘ e
  have hq : ContDiff ℝ ∞ q := contDiff_const.sub ((contDiff_norm_sq ℝ).div_const 2)
  have hUiff (y : E) : y ∈ U ↔ a < q y := by
    rw [mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg y)]
    dsimp [q]
    constructor <;> intro h <;> linarith
  have hf : IsSmoothEmbedding I 𝓘(ℝ, E × ℝ) ∞ f := he.diffeomorph_comp D.symm
  have hgraph : (fun y => (y, q y)) '' U ⊆ range f := by
    rintro z ⟨y, hy, rfl⟩
    have hmem := hcap.symm.subset (mem_image_of_mem D
      (show (y, q y) ∈ {z : E × ℝ | a ≤ z.2 ∧ z.2 = q z.1} from
        ⟨(hUiff y).mp hy |>.le, rfl⟩))
    obtain ⟨x, hx⟩ := hmem.2
    exact ⟨x, by simp only [f, Function.comp_def, hx, D.symm_apply_apply]⟩
  obtain ⟨V₀, hV₀, hgraphV₀, hV₀U, hV₀eq⟩ :=
    hf.exists_isOpen_inter_range_eq_graph isOpen_ball hq.contDiffOn hdim hgraph
  let C : Set (E × ℝ) := {z | a < z.2 ∧ z.2 < q z.1}
  have hC : IsOpen C := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd (hq.continuous.comp continuous_fst))
  have hCU : C ⊆ U ×ˢ univ := fun z hz => ⟨(hUiff z.1).mpr (hz.1.trans hz.2), mem_univ _⟩
  have hclear (z : E × ℝ) (hz : z ∈ C) : z ∉ range f := by
    rintro ⟨x, hx⟩
    have hex : e x = D z := by
      have hh := congrArg D hx
      simpa only [f, Function.comp_def, D.apply_symm_apply] using hh
    have hmem := hcap.subset
      ⟨mem_image_of_mem D (show z ∈ {w : E × ℝ | a ≤ w.2 ∧ w.2 ≤ q w.1} from
        ⟨hz.1.le, hz.2.le⟩), x, hex⟩
    obtain ⟨w, hw, hwz⟩ := hmem
    have hwz' := D.injective hwz
    subst w
    exact hz.2.ne hw.2
  have hWeq : (V₀ ∪ C) ∩ range f = (V₀ ∪ C) ∩ {z | z.2 = q z.1} := by
    ext z
    constructor
    · rintro ⟨hz | hz, hfz⟩
      · exact ⟨Or.inl hz, (hV₀eq.subset ⟨hz, hfz⟩).2⟩
      · exact (hclear z hz hfz).elim
    · rintro ⟨hz | hz, hqz⟩
      · exact ⟨Or.inl hz, (hV₀eq.symm.subset ⟨hz, hqz⟩).2⟩
      · exact (hz.2.ne hqz).elim
  have hcontains : {z : E × ℝ | a < z.2 ∧ z.2 ≤ q z.1} ⊆ V₀ ∪ C := by
    intro z hz
    rcases hz.2.eq_or_lt with hqz | hqz
    · exact Or.inl (hgraphV₀ ⟨z.1, (hUiff z.1).mpr (hz.1.trans_eq hqz),
        Prod.ext rfl hqz.symm⟩)
    · exact Or.inr ⟨hz.1, hqz⟩
  let V := D '' (V₀ ∪ C)
  have hV : IsOpen V := D.toHomeomorph.isOpenMap _ (hV₀.union hC)
  have hDsub : D '' {z | a < z.2 ∧ z.2 ≤ q z.1} ⊆ V := image_mono hcontains
  have hrange : D '' range f = range e := by
    rw [← range_comp]
    congr 1
    funext x
    exact D.apply_symm_apply (e x)
  have hVeq : V ∩ range e = V ∩ D '' {z | z.2 = q z.1} := by
    change (D '' (V₀ ∪ C)) ∩ range e = (D '' (V₀ ∪ C)) ∩ D '' _
    have hinj : Function.Injective (D : E × ℝ → E × ℝ) := D.injective
    rw [← hrange, ← image_inter hinj, hWeq, image_inter hinj]
  have hcompact : IsCompact {z : E × ℝ | d ≤ z.2 ∧ z.2 ≤ q z.1} := by
    have hclosed : IsClosed {z : E × ℝ | d ≤ z.2 ∧ z.2 ≤ q z.1} :=
      (isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd (hq.continuous.comp continuous_fst))
    apply IsCompact.of_isClosed_subset
      ((isCompact_closedBall (0 : E) (Real.sqrt (2 * (c - d)))).prod
        (isCompact_Icc (a := d) (b := c))) hclosed
    intro z hz
    have hqn : z.2 ≤ c - ‖z.1‖ ^ 2 / 2 := hz.2
    exact ⟨mem_closedBall_zero_iff.mpr (Real.le_sqrt_of_sq_le (by linarith [hz.1])),
      hz.1, by linarith [sq_nonneg ‖z.1‖]⟩
  have hraised : {z : E × ℝ | d ≤ z.2 ∧ z.2 ≤ q z.1} ⊆
      {z | a < z.2 ∧ z.2 ≤ q z.1} := fun _ hz => ⟨had.trans_le hz.1, hz.2⟩
  obtain ⟨δ, hδ, hδV⟩ := (hcompact.image D.continuous).exists_cthickening_subset_open hV
    ((image_mono hraised).trans hDsub)
  refine ⟨V, hV, hDsub, ?_, hVeq, δ, hδ, hδV⟩
  rintro z ⟨w, hw, rfl⟩
  rw [D.symm_apply_apply]
  exact ((union_subset hV₀U hCU) hw).1

theorem image_connectedComponentIn_superlevel_eq_height_cap
    {E P H M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ P H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → E × ℝ} (he : IsSmoothEmbedding I 𝓘(ℝ, E × ℝ) ∞ e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ P)
    (D : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hD : ∀ z, (D z).2 = z.2)
    {a c d : ℝ} (had : a < d) (hdc : d ≤ c)
    (hcap : (D '' {z | a ≤ z.2 ∧ z.2 ≤ c - ‖z.1‖ ^ 2 / 2}) ∩ range e =
      D '' {z | a ≤ z.2 ∧ z.2 = c - ‖z.1‖ ^ 2 / 2})
    {p : M} (hp : e p = D (0, c)) :
    e '' connectedComponentIn {x | d ≤ (e x).2} p =
      D '' {z | d ≤ z.2 ∧ z.2 = c - ‖z.1‖ ^ 2 / 2} := by
  let q : E → ℝ := fun y => c - ‖y‖ ^ 2 / 2
  let X : Set (E × ℝ) := {z | d ≤ z.2 ∧ z.2 = q z.1}
  let K := e ⁻¹' (D '' X)
  let S := {x | d ≤ (e x).2}
  have hq : Continuous q := continuous_const.sub (continuous_norm.pow 2 |>.div_const 2)
  have hgraph : X = (fun y => (y, q y)) '' closedBall (0 : E) (Real.sqrt (2 * (c - d))) := by
    ext z
    constructor
    · intro hz
      refine ⟨z.1, mem_closedBall_zero_iff.mpr (Real.le_sqrt_of_sq_le ?_), ?_⟩
      · dsimp [X, q] at hz
        linarith
      · exact Prod.ext rfl hz.2.symm
    · rintro ⟨y, hy, rfl⟩
      have hy' : ‖y‖ ^ 2 ≤ 2 * (c - d) :=
        (Real.le_sqrt (norm_nonneg y) (by linarith : 0 ≤ 2 * (c - d))).mp
          (mem_closedBall_zero_iff.mp hy)
      exact ⟨by dsimp [q]; linarith, rfl⟩
  have hXcompact : IsCompact X := by
    rw [hgraph]
    exact (isCompact_closedBall (0 : E) (Real.sqrt (2 * (c - d)))).image
      (continuous_id.prodMk hq)
  have hXpre : IsPreconnected X := by
    rw [hgraph]
    exact (convex_closedBall (0 : E) _).isPreconnected.image _
      (continuous_id.prodMk hq).continuousOn
  have hXrange : D '' X ⊆ range e := by
    intro z hz
    have hz' : z ∈ D '' {z | a ≤ z.2 ∧ z.2 = q z.1} := by
      exact image_mono (show X ⊆ {z : E × ℝ | a ≤ z.2 ∧ z.2 = q z.1} from
        fun y hy => ⟨had.le.trans hy.1, hy.2⟩) hz
    exact (hcap.symm.subset hz').2
  have heK : e '' K = D '' X := by
    exact image_preimage_eq_of_subset hXrange
  have hKclosed : IsClosed K := (hXcompact.image D.continuous).isClosed.preimage he.contMDiff.continuous
  have hKpre : IsPreconnected K := he.isEmbedding.isInducing.isPreconnected_image.mp (by
    rw [heK]
    exact hXpre.image D D.continuous.continuousOn)
  have hpK : p ∈ K := by
    change e p ∈ D '' X
    rw [hp]
    exact mem_image_of_mem D ⟨hdc, by simp [q]⟩
  have hKS : K ⊆ S := by
    rintro x ⟨z, hz, hzx⟩
    change d ≤ (e x).2
    rw [← hzx, hD]
    exact hz.1
  obtain ⟨V, hV, hbodyV, _, hVeq, _⟩ :=
    exists_cthickening_height_cap_graph_neighborhood he hdim D had hcap
  have hKV : K = S ∩ e ⁻¹' V := by
    ext x
    constructor
    · intro hx
      refine ⟨hKS hx, ?_⟩
      obtain ⟨z, hz, hzx⟩ := hx
      exact hbodyV ⟨z, ⟨had.trans_le hz.1, hz.2.le⟩, hzx⟩
    · rintro ⟨hxS, hxV⟩
      have hm := (hVeq.subset ⟨hxV, mem_range_self x⟩).2
      obtain ⟨z, hz, hzx⟩ := hm
      refine ⟨z, ⟨?_, hz⟩, hzx⟩
      change d ≤ (e x).2 at hxS
      rwa [← hzx, hD] at hxS
  have hKclopen : IsClopen ((Subtype.val : S → M) ⁻¹' K) := by
    refine ⟨hKclosed.preimage continuous_subtype_val, ?_⟩
    have heq : (Subtype.val : S → M) ⁻¹' K = (fun x : S => e x) ⁻¹' V := by
      ext x
      simp only [mem_preimage, hKV, mem_inter_iff, x.property, true_and]
    rw [heq]
    exact hV.preimage (he.contMDiff.continuous.comp continuous_subtype_val)
  have hKcomp : K = connectedComponentIn S p := by
    apply Subset.antisymm (hKpre.subset_connectedComponentIn hpK hKS)
    rw [connectedComponentIn_eq_image (hKS hpK)]
    rintro x ⟨y, hy, rfl⟩
    exact hKclopen.connectedComponent_subset hpK hy
  rw [← hKcomp]
  exact heK

open DifferentialGeometry.Analysis.ODE in
theorem image_connectedComponentIn_superlevel_inter_level_eq_image_sphere
    {E P H M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ P H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → E × ℝ} (he : IsSmoothEmbedding I 𝓘(ℝ, E × ℝ) ∞ e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ P)
    (D : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hD : ∀ z, (D z).2 = z.2)
    {a b c d r : ℝ} (hr : 0 < r) (hb : b = c - r ^ 2 / 2)
    (had : a < d) (hdb : d ≤ b)
    (hcap : (D '' {z | a ≤ z.2 ∧ z.2 ≤ c - ‖z.1‖ ^ 2 / 2}) ∩ range e =
      D '' {z | a ≤ z.2 ∧ z.2 = c - ‖z.1‖ ^ 2 / 2})
    {p : M} (hp : e p = D (0, c)) (G : E → E)
    (hlo : ∀ y, D (quadraticLevelScaling b c y d, d) = (G y, d)) :
    (fun x => (e x).1) ''
      (connectedComponentIn {x | d ≤ (e x).2} p ∩ {x | (e x).2 = d}) =
        G '' sphere 0 r := by
  have hbc : b < c := by rw [hb]; nlinarith [sq_pos_of_pos hr]
  have hdc : d < c := hdb.trans_lt hbc
  have hratio : 0 < (d - c) / (b - c) :=
    div_pos_of_neg_of_neg (sub_neg.mpr hdc) (sub_neg.mpr hbc)
  have hscaleSphere :
      (fun y : E => quadraticLevelScaling b c y d) '' sphere 0 r =
        sphere 0 (Real.sqrt (2 * (c - d))) := by
    rw [quadraticLevelScaling_image_sphere b c hratio r]
    congr 1
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hr.le) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hratio.le, Real.sq_sqrt (by linarith : 0 ≤ 2 * (c - d)),
      div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hbc.ne), hb]
    ring
  have hcomponent := image_connectedComponentIn_superlevel_eq_height_cap
    he hdim D hD had hdc.le hcap hp
  apply Subset.antisymm
  · rintro z ⟨x, ⟨hx, hxd⟩, rfl⟩
    obtain ⟨w, ⟨_, hwq⟩, hw⟩ := hcomponent.subset (mem_image_of_mem e hx)
    have hwd : w.2 = d := (hD w).symm.trans ((congrArg Prod.snd hw).trans hxd)
    have hwSphere : w.1 ∈ sphere 0 (Real.sqrt (2 * (c - d))) := by
      rw [mem_sphere_zero_iff_norm]
      apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (by linarith : 0 ≤ 2 * (c - d))]
      rw [hwd] at hwq
      linarith
    obtain ⟨y, hy, hyscale⟩ := hscaleSphere.symm.subset hwSphere
    refine ⟨y, hy, ?_⟩
    have hweq : w = (quadraticLevelScaling b c y d, d) := Prod.ext hyscale.symm hwd
    rw [hweq, hlo] at hw
    exact congrArg Prod.fst hw
  · rintro z ⟨y, hy, rfl⟩
    have hwSphere := hscaleSphere.subset (mem_image_of_mem _ hy)
    have hwNorm : ‖quadraticLevelScaling b c y d‖ ^ 2 = 2 * (c - d) := by
      rw [mem_sphere_zero_iff_norm.mp hwSphere, Real.sq_sqrt (by linarith : 0 ≤ 2 * (c - d))]
    have hq : (quadraticLevelScaling b c y d, d) ∈
        {z : E × ℝ | d ≤ z.2 ∧ z.2 = c - ‖z.1‖ ^ 2 / 2} :=
      ⟨le_rfl, by dsimp only; linarith⟩
    obtain ⟨x, hx, hfx⟩ := hcomponent.symm.subset (mem_image_of_mem D hq)
    have heq : e x = (G y, d) := hfx.trans (hlo y)
    exact ⟨x, ⟨hx, congrArg Prod.snd heq⟩, congrArg Prod.fst heq⟩

theorem exists_isOpen_inter_range_eq_paraboloid_of_cylinder
    {E P H M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ P H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → E × ℝ} (he : IsSmoothEmbedding I 𝓘(ℝ, E × ℝ) ∞ e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ P)
    (Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (G : E ≃ E) (ψ : ℝ ≃ ℝ)
    {a d b m r : ℝ} (hdb : d ≤ b)
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    {A : Set E} (hA : IsClosed A)
    (hwall : (G '' sphere 0 r \ A) ×ˢ Ioo a d ⊆ range e) :
    ∃ W : Set (E × ℝ), IsOpen W ∧ Q '' ((G '' sphere 0 r \ A) ×ˢ Ioo a d) ⊆ W ∧
      W ∩ range (Q ∘ e) = W ∩ {z : E × ℝ | z.2 = m - ‖z.1‖ ^ 2 / 2} := by
  let q : E → ℝ := fun y => m - ‖y‖ ^ 2 / 2
  have hq : ContDiff ℝ ∞ q := contDiff_const.sub ((contDiff_norm_sq ℝ).div_const 2)
  let O : Set E := {y | ψ a < q y ∧ q y < ψ d ∧ (Q.symm (y, q y)).1 ∉ A}
  have hO : IsOpen O :=
    (isOpen_lt continuous_const hq.continuous).inter
      ((isOpen_lt hq.continuous continuous_const).inter
        (hA.isOpen_compl.preimage (Q.symm.continuous.comp (continuous_id.prodMk hq.continuous)).fst))
  have hψdb : ψ d ≤ b := by simpa only [hψb] using hψ.monotone hdb
  have himage := Diffeomorph.image_reference_cylinder Q G ψ hbm hr hrsq hψ hψb hQfull (j := a)
  have hQheight (z : E × ℝ) (hz : z.2 ≤ b) : (Q z).2 = ψ z.2 :=
    congrArg Prod.snd (hQfull z.2 hz z.1)
  have hgraphO : (fun y => (y, q y)) '' O ⊆ range (Q ∘ e) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hQz⟩ := himage.symm.subset
      (show (y, q y) ∈ {p : E × ℝ | ψ a ≤ p.2 ∧ p.2 ≤ b ∧ p.2 = m - ‖p.1‖ ^ 2 / 2}
        from ⟨hy.1.le, hy.2.1.le.trans hψdb, rfl⟩)
    have htime : ψ z.2 = q y := (hQheight z hz.2.2).symm.trans (congrArg Prod.snd hQz)
    have hzA : z.1 ∉ A := by
      have hsymm : Q.symm (y, q y) = z := by rw [← hQz, Q.symm_apply_apply]
      rw [← hsymm]
      exact hy.2.2
    have hzt : z.2 ∈ Ioo a d := by
      constructor
      · exact hψ.lt_iff_lt.mp (by rw [htime]; exact hy.1)
      · exact hψ.lt_iff_lt.mp (by rw [htime]; exact hy.2.1)
    obtain ⟨x, hx⟩ := hwall ⟨⟨hz.1, hzA⟩, hzt⟩
    exact ⟨x, (congrArg Q hx).trans hQz⟩
  obtain ⟨W, hW, hgraphW, _, hWeq⟩ := (he.diffeomorph_comp Q).exists_isOpen_inter_range_eq_graph
    hO hq.contDiffOn hdim hgraphO
  refine ⟨W, hW, ?_, hWeq⟩
  rintro _ ⟨z, hz, rfl⟩
  have hlevel : (Q z).2 = q (Q z).1 :=
    (himage.subset ⟨z, ⟨hz.1.1, hz.2.1.le, hz.2.2.le.trans hdb⟩, rfl⟩).2.2
  apply hgraphW
  refine ⟨(Q z).1, ?_, Prod.ext rfl hlevel.symm⟩
  change ψ a < q (Q z).1 ∧ q (Q z).1 < ψ d ∧ (Q.symm ((Q z).1, q (Q z).1)).1 ∉ A
  rw [← hlevel]
  refine ⟨?_, ?_, ?_⟩
  · rw [hQheight z (hz.2.2.le.trans hdb)]
    exact hψ hz.2.1
  · rw [hQheight z (hz.2.2.le.trans hdb)]
    exact hψ hz.2.2
  · simpa only [Prod.eta, Q.symm_apply_apply] using hz.1.2


end DifferentialGeometry.Topology.SphereSeparation
