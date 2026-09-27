import SigmaOpResolvent
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Order.Monotone
import SigmaOpNonnegativeResolvent
import SigmaOpCFCEigen
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace Sigma
noncomputable section
open Set
open scoped Classical
open Filter
open scoped Topology

/-- Resolvent compactification of a scalar function on the nonnegative ray. -/
def scalarResolventTransform (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 + f (r⁻¹ - 1))⁻¹

theorem scalar_resolvent_argument_nonneg {r : ℝ} (hr : r ∈ Ioc 0 1) :
    0 ≤ r⁻¹ - 1 := by
  have hi := (one_le_inv₀ hr.1).2 hr.2
  linarith

theorem scalar_resolvent_transform_pos (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) {r : ℝ} (hr : r ∈ Ioc 0 1) :
    0 < scalarResolventTransform f r := by
  exact inv_pos.mpr (by
    have h := hf _ (scalar_resolvent_argument_nonneg hr)
    linarith)

theorem scalar_resolvent_transform_strictMono (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hm : StrictMonoOn f (Ici 0)) :
    StrictMonoOn (scalarResolventTransform f) (Ioc 0 1) := by
  intro r hr s hs hrs
  have harg : s⁻¹ - 1 < r⁻¹ - 1 := by
    exact sub_lt_sub_right ((inv_lt_inv₀ hs.1 hr.1).2 hrs) 1
  have hfs := hf _ (scalar_resolvent_argument_nonneg hs)
  have hfr := hf _ (scalar_resolvent_argument_nonneg hr)
  apply (inv_lt_inv₀ (by linarith : 0 < 1 + f (r⁻¹ - 1))
    (by linarith : 0 < 1 + f (s⁻¹ - 1))).2
  exact add_lt_add_left (hm (scalar_resolvent_argument_nonneg hs)
    (scalar_resolvent_argument_nonneg hr) harg) 1

theorem scalar_resolvent_transform_continuous (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hc : ContinuousOn f (Ici 0)) :
    ContinuousOn (scalarResolventTransform f) (Ioc 0 1) := by
  have hi : ContinuousOn (fun r : ℝ => r⁻¹ - 1) (Ioc 0 1) := by
    intro r hr
    exact ((continuousAt_inv₀ hr.1.ne').sub continuousAt_const).continuousWithinAt
  have hcomp := hc.comp hi (fun r hr => scalar_resolvent_argument_nonneg hr)
  exact (continuousOn_const.add hcomp).inv₀ (fun r hr => by
    have h := hf _ (scalar_resolvent_argument_nonneg hr)
    simp only [Function.comp_apply]
    linarith)

/-- The value at the limiting spectral endpoint. It is positive when `f`
has bounded range and zero when that range is unbounded. Neither case is
discarded in the construction. -/
def scalarResolventEndpoint (f : ℝ → ℝ) : ℝ :=
  sInf (scalarResolventTransform f '' Ioo 0 1)

def scalarCompactResolventTransform (f : ℝ → ℝ) : ℝ → ℝ :=
  Function.update (scalarResolventTransform f) 0 (scalarResolventEndpoint f)

theorem scalar_resolvent_endpoint_le (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    scalarResolventEndpoint f ≤ scalarResolventTransform f r := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact
      (scalar_resolvent_transform_pos f hf ⟨hx.1, hx.2.le⟩).le⟩
  · exact ⟨r, hr, rfl⟩

theorem scalar_resolvent_endpoint_nonneg (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) : 0 ≤ scalarResolventEndpoint f := by
  apply le_csInf
  · exact ⟨scalarResolventTransform f (1 / 2), ⟨1 / 2, by norm_num, rfl⟩⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact (scalar_resolvent_transform_pos f hf ⟨hr.1, hr.2.le⟩).le

theorem scalar_compact_resolvent_transform_strictMono (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hm : StrictMonoOn f (Ici 0)) :
    StrictMonoOn (scalarCompactResolventTransform f) (Icc 0 1) := by
  intro r hr s hs hrs
  by_cases hr0 : r = 0
  · subst r
    have hs0 : 0 < s := hrs
    have ht : s / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hs.2]
    have hh := scalar_resolvent_endpoint_le f hf ht
    have hlt := scalar_resolvent_transform_strictMono f hf hm
      ⟨ht.1, ht.2.le⟩ ⟨hs0, hs.2⟩ (by linarith : s / 2 < s)
    simpa [scalarCompactResolventTransform, Function.update_noteq hs0.ne'] using
      hh.trans_lt hlt
  · have hs0 : s ≠ 0 := ne_of_gt (lt_of_le_of_lt hr.1 hrs)
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    simpa [scalarCompactResolventTransform, Function.update_noteq hr0,
      Function.update_noteq hs0] using
      scalar_resolvent_transform_strictMono f hf hm ⟨hrpos, hr.2⟩
        ⟨lt_trans hrpos hrs, hs.2⟩ hrs

theorem scalar_compact_resolvent_transform_continuous (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hc : ContinuousOn f (Ici 0))
    (hm : StrictMonoOn f (Ici 0)) :
    ContinuousOn (scalarCompactResolventTransform f) (Icc 0 1) := by
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    unfold scalarCompactResolventTransform
    rw [continuousWithinAt_update_same]
    have hd : Icc (0 : ℝ) 1 \ {0} = Ioc 0 1 := by
      ext x
      simp only [mem_diff, mem_Icc, mem_singleton_iff, mem_Ioc]
      constructor
      · rintro ⟨hx, hx0⟩
        exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩
      · intro hx
        exact ⟨⟨hx.1.le, hx.2⟩, hx.1.ne'⟩
    rw [hd, nhdsWithin_Ioc_eq_nhdsWithin_Ioi (by norm_num : (0 : ℝ) < 1)]
    exact (scalar_resolvent_transform_strictMono f hf hm).monotoneOn.mono
      Ioo_subset_Ioc_self |>.tendsto_nhdsWithin_Ioo_right
        (by exact ⟨1 / 2, by norm_num⟩)
        ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact
          (scalar_resolvent_transform_pos f hf ⟨hx.1, hx.2.le⟩).le⟩
  · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hcont := scalar_resolvent_transform_continuous f hf hc r ⟨hrpos, hr.2⟩
    have hpos : Ioc (0 : ℝ) 1 ∈ 𝓝[Icc 0 1] r := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds hrpos)] with x hx hxpos
      exact ⟨hxpos, hx.2⟩
    have hcont := hcont.mono_of_mem_nhdsWithin hpos
    apply hcont.congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hrpos)] with x hx
      simp [scalarCompactResolventTransform, Function.update_noteq hx.ne']
    · simp [scalarCompactResolventTransform, Function.update_noteq hr0]

theorem scalar_compact_resolvent_transform_bounds (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hm : StrictMonoOn f (Ici 0))
    {r : ℝ} (hr : r ∈ Icc 0 1) :
    0 ≤ scalarCompactResolventTransform f r ∧ scalarCompactResolventTransform f r ≤ 1 := by
  have hmono := (scalar_compact_resolvent_transform_strictMono f hf hm).monotoneOn
  have hzero : 0 ≤ scalarCompactResolventTransform f 0 := by
    simpa [scalarCompactResolventTransform] using scalar_resolvent_endpoint_nonneg f hf
  have hone : scalarCompactResolventTransform f 1 ≤ 1 := by
    have hf0 := hf 0 le_rfl
    simp only [scalarCompactResolventTransform, Function.update_noteq (by norm_num : (1 : ℝ) ≠ 0),
      scalarResolventTransform, inv_one, sub_self]
    exact (inv_le_one₀ (by linarith : 0 < 1 + f 0)).2 (by linarith)
  exact ⟨hzero.trans (hmono (by norm_num) hr hr.1),
    (hmono hr (by norm_num) hr.2).trans hone⟩

private def compactMonotoneHomeomorph (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc 0 1)) (hm : StrictMonoOn q (Icc 0 1)) :
    Icc (0 : ℝ) 1 ≃ₜ q '' Icc 0 1 := by
  let e : Icc (0 : ℝ) 1 ≃ q '' Icc 0 1 := hm.injOn.bijOn_image.equiv _
  have he : Continuous e := by
    exact hq.restrict.subtype_mk _
  exact Homeomorph.homeomorphOfContinuousClosed e he he.isClosedMap

/-- The inverse on the compact spectral range. Its value off that range is
irrelevant to functional calculus. The limiting endpoint is included. -/
def compactMonotoneInverse (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc 0 1)) (hm : StrictMonoOn q (Icc 0 1)) (y : ℝ) : ℝ :=
  if hy : y ∈ q '' Icc 0 1 then
    ((compactMonotoneHomeomorph q hq hm).symm ⟨y, hy⟩ : ℝ)
  else 0

theorem compact_monotone_inverse_continuous (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc 0 1)) (hm : StrictMonoOn q (Icc 0 1)) :
    ContinuousOn (compactMonotoneInverse q hq hm) (q '' Icc 0 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have h := continuous_subtype_val.comp (compactMonotoneHomeomorph q hq hm).symm.continuous
  convert h using 1
  funext y
  simp only [Set.restrict_apply, compactMonotoneInverse, dif_pos y.property]
  rfl

theorem compact_monotone_inverse_left (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc 0 1)) (hm : StrictMonoOn q (Icc 0 1))
    {x : ℝ} (hx : x ∈ Icc 0 1) : compactMonotoneInverse q hq hm (q x) = x := by
  have hxq : q x ∈ q '' Icc 0 1 := ⟨x, hx, rfl⟩
  simp only [compactMonotoneInverse, dif_pos hxq]
  have he := (compactMonotoneHomeomorph q hq hm).symm_apply_apply ⟨x, hx⟩
  exact congrArg Subtype.val he

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The native maximal inverse-minus-identity of an injective bounded map.
Its domain is its entire range, even when that range is not closed. -/
def operatorRangeGenerator (R : H →L[ℂ] H) (hi : Function.Injective R) :
    H →ₗ.[ℂ] H :=
  LinearPMap.mk (LinearMap.range R.toLinearMap)
    ((LinearEquiv.ofInjective R.toLinearMap hi).symm.toLinearMap -
      (LinearMap.range R.toLinearMap).subtype)

omit [CompleteSpace H] in
theorem operator_range_generator_domain (R : H →L[ℂ] H) (hi : Function.Injective R) :
    (operatorRangeGenerator R hi).domain = LinearMap.range R.toLinearMap := rfl

omit [CompleteSpace H] in
theorem operator_range_generator_apply (R : H →L[ℂ] H) (hi : Function.Injective R)
    (x : H) :
    operatorRangeGenerator R hi ⟨R x, ⟨x, rfl⟩⟩ = x - R x := by
  change (LinearEquiv.ofInjective R.toLinearMap hi).symm
    ((LinearEquiv.ofInjective R.toLinearMap hi) x) - R x = x - R x
  rw [LinearEquiv.symm_apply_apply]

omit [CompleteSpace H] in
theorem operator_range_generator_resolvent (R : H →L[ℂ] H) (hi : Function.Injective R) :
    OpIsResolvent (operatorRangeGenerator R hi) 1 R := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_, ?_⟩
  · intro x
    rw [operator_range_generator_apply, one_smul, sub_add_cancel]
  · rintro ⟨x, ⟨y, rfl⟩⟩
    change R (operatorRangeGenerator R hi ⟨R y, _⟩ + 1 • R y) = R y
    rw [operator_range_generator_apply, one_smul, sub_add_cancel]

theorem operator_range_generator_selfAdjoint (R : H →L[ℂ] H)
    (hi : Function.Injective R) (hs : IsSelfAdjoint R) (hd : DenseRange R) :
    IsSelfAdjoint (operatorRangeGenerator R hi) := by
  let A := operatorRangeGenerator R hi
  have hdom : Dense (A.domain : Set H) := by
    change Dense (LinearMap.range R.toLinearMap : Set H)
    exact hd
  have hsym : A.IsFormalAdjoint A := by
    rintro ⟨x, ⟨u, rfl⟩⟩ ⟨y, ⟨v, rfl⟩⟩
    change @inner ℂ H _ (operatorRangeGenerator R hi ⟨R u, _⟩) (R v) =
      @inner ℂ H _ (R u) (operatorRangeGenerator R hi ⟨R v, _⟩)
    rw [operator_range_generator_apply, operator_range_generator_apply,
      inner_sub_left, inner_sub_right]
    exact congrArg (fun z : ℂ => z - @inner ℂ H _ (R u) (R v))
      (hs.isSymmetric u v).symm
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      have ht := A.adjoint_isFormalAdjoint hdom
      have he : R (A.adjoint ⟨y, hy⟩ + y) = y := by
        apply ext_inner_right ℂ
        intro u
        have hh := ht ⟨y, hy⟩ ⟨R u, ⟨u, rfl⟩⟩
        change @inner ℂ H _ (A.adjoint ⟨y, hy⟩) (R u) =
          @inner ℂ H _ y (operatorRangeGenerator R hi ⟨R u, _⟩) at hh
        rw [operator_range_generator_apply] at hh
        rw [inner_sub_right] at hh
        rw [← R.adjoint_inner_right, hs.adjoint_eq, inner_add_left, hh,
          sub_add_cancel]
      exact ⟨_, he⟩
    · intro x y hxy
      apply hdom.eq_of_inner_left
      intro z
      have ht := A.adjoint_isFormalAdjoint hdom x z
      calc
        @inner ℂ H _ (A.adjoint x) z.val = @inner ℂ H _ x.val (A z) := ht
        _ = @inner ℂ H _ y.val (A z) := by rw [hxy]
        _ = @inner ℂ H _ (A y) z.val := (hsym y z).symm
  · exact hsym.le_adjoint hdom

/-- Total native inverse-minus-identity. The native inverse API has its
usual junk value on noninjective input; every input used below is proved
injective. No domain is supplied as additional data. -/
def operatorNativeRangeGenerator (R : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  -(LinearMap.id : H →ₗ[ℂ] H) +ᵥ (R.toLinearMap.toPMap ⊤).inverse

omit [CompleteSpace H] in
theorem operator_native_range_generator_resolvent (R : H →L[ℂ] H)
    (hi : Function.Injective R) : OpIsResolvent (operatorNativeRangeGenerator R) 1 R := by
  let T := R.toLinearMap.toPMap ⊤
  have hiT : LinearMap.ker T.toFun = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply Subtype.ext
    exact hi hxy
  have hmem (x : H) : R x ∈ T.inverse.domain := by
    rw [LinearPMap.inverse_domain]
    exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  have hact (x : H) : T.inverse ⟨R x, hmem x⟩ = x :=
    LinearPMap.inverse_apply_eq hiT (x := ⟨x, Submodule.mem_top⟩) rfl
  refine ⟨hmem, ?_, ?_⟩
  · intro x
    change -R x + T.inverse ⟨R x, hmem x⟩ + 1 • R x = x
    rw [hact, one_smul]
    abel
  · intro x
    have hx : x.val ∈ T.inverse.domain := x.property
    rw [LinearPMap.inverse_domain] at hx
    obtain ⟨y, hy⟩ := hx
    have hxval : x.val = R y.val := hy.symm
    have hsub : (⟨x.val, x.property⟩ : T.inverse.domain) = ⟨R y.val, hmem y.val⟩ :=
      Subtype.ext hxval
    change R (-x.val + T.inverse ⟨x.val, x.property⟩ + 1 • x.val) = x.val
    rw [hsub, hact, one_smul]
    rw [hxval]
    congr 1
    abel

omit [CompleteSpace H] in
theorem operator_native_range_generator_eq (R : H →L[ℂ] H) (hi : Function.Injective R) :
    operatorNativeRangeGenerator R = operatorRangeGenerator R hi :=
  operator_full_resolvent_unique _ _ 1 R (operator_native_range_generator_resolvent R hi)
    (operator_range_generator_resolvent R hi)

/-- Applying the continuous inverse to the actual bounded transformed
resolvent recovers the original operator on every vector. -/
theorem operator_compact_monotone_inverse (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hsp : spectrum ℝ R ⊆ Icc 0 1) (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc 0 1)) (hm : StrictMonoOn q (Icc 0 1)) :
    cfc (compactMonotoneInverse q hq hm) (cfc q R) = R := by
  rw [← cfc_comp (compactMonotoneInverse q hq hm) q R hR
    ((compact_monotone_inverse_continuous q hq hm).mono (image_mono hsp)) (hq.mono hsp)]
  calc
    cfc (compactMonotoneInverse q hq hm ∘ q) R = cfc (id : ℝ → ℝ) R := by
      apply cfc_congr
      intro x hx
      exact compact_monotone_inverse_left q hq hm (hsp hx)
    _ = R := cfc_id ℝ R hR

/-- The added endpoint of the compactified scalar range has no eigenspace.
Thus arbitrary endpoint values of an unbounded inverse do not create a
native operator domain or change its action. -/
theorem operator_compact_monotone_endpoint (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hi : Function.Injective R) (hsp : spectrum ℝ R ⊆ Icc 0 1)
    (q : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 1)) (hm : StrictMonoOn q (Icc 0 1))
    (x : H) (hx : cfc q R x = (q 0 : ℂ) • x) : x = 0 := by
  have hSf : IsSelfAdjoint (cfc q R) := cfc_predicate q R
  have hcont : ContinuousOn (compactMonotoneInverse q hq hm)
      (spectrum ℝ (cfc q R)) := by
    rw [cfc_map_spectrum q R hR (hq.mono hsp)]
    exact (compact_monotone_inverse_continuous q hq hm).mono (image_mono hsp)
  have hh := op_cfc_eigenvector_action (cfc q R) hSf (q 0) x hx
    (compactMonotoneInverse q hq hm) hcont
  rw [operator_compact_monotone_inverse R hR hsp q hq hm,
    compact_monotone_inverse_left q hq hm (by norm_num : (0 : ℝ) ∈ Icc 0 1),
    Complex.ofReal_zero, zero_smul] at hh
  exact hi (hh.trans (map_zero R).symm)

theorem operator_compact_monotone_injective (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hi : Function.Injective R) (hsp : spectrum ℝ R ⊆ Icc 0 1)
    (q : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 1)) (hm : StrictMonoOn q (Icc 0 1))
    (hq0 : 0 ≤ q 0) : Function.Injective (cfc q R : H →L[ℂ] H) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hxS : cfc q R x = 0 := LinearMap.mem_ker.mp hx
  by_cases hx0 : x = 0
  · exact hx0
  have hzero := op_eigenvalue_mem_spectrum (cfc q R) 0 x hx0 (by simpa using hxS)
  rw [cfc_map_spectrum q R hR (hq.mono hsp)] at hzero
  obtain ⟨r, hr, hqr⟩ := hzero
  have hrI := hsp hr
  have hqz : q 0 = 0 := by
    have hle := hm.monotoneOn (by norm_num : (0 : ℝ) ∈ Icc 0 1) hrI hrI.1
    rw [hqr] at hle
    exact le_antisymm hle hq0
  apply operator_compact_monotone_endpoint R hR hi hsp q hq hm x
  simpa [hqz] using hxS

theorem operator_selfAdjoint_dense_range (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hi : Function.Injective R) : DenseRange R := by
  change Dense (LinearMap.range R.toLinearMap : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hzero : R x = 0 := by
    apply ext_inner_right ℂ
    intro y
    have hh := (Submodule.mem_orthogonal' _ _).mp hx (R y)
      (LinearMap.mem_range_self R.toLinearMap y)
    rw [← R.adjoint_inner_right, hR.adjoint_eq]
    simpa using hh
  exact hi (hzero.trans (map_zero R).symm)

theorem op_nonnegative_resolvent_spectrum (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    spectrum ℝ (opNonnegativeResolvent B hsa hB) ⊆ Icc 0 1 := by
  intro r hr
  by_cases hsub : Subsingleton H
  · letI := hsub
    rw [spectrum.of_subsingleton] at hr
    exact hr.elim
  haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hsub
  have hn := spectrum_nonneg_of_nonneg (op_nonnegative_resolvent_nonneg B hsa hB) hr
  refine ⟨hn, ?_⟩
  calc
    r ≤ ‖r‖ := Real.le_norm_self r
    _ ≤ ‖opNonnegativeResolvent B hsa hB‖ := spectrum.norm_le_norm_of_mem hr
    _ ≤ 1 := op_nonnegative_resolvent_norm B hsa hB

/-- Actual bounded shifted resolvent of the continuous scalar calculus. -/
def opFunctionalResolvent (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B)
    (hB : OpNonnegative B) (f : ℝ → ℝ) : H →L[ℂ] H :=
  cfc (scalarCompactResolventTransform f) (opNonnegativeResolvent B hsa hB)

theorem op_functional_resolvent_injective (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B)
    (hB : OpNonnegative B) (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hc : ContinuousOn f (Ici 0)) (hm : StrictMonoOn f (Ici 0)) :
    Function.Injective (opFunctionalResolvent B hsa hB f) := by
  apply operator_compact_monotone_injective _
    (op_nonnegative_resolvent_selfAdjoint B hsa hB)
    (op_nonnegative_resolvent_injective B hsa hB)
    (op_nonnegative_resolvent_spectrum B hsa hB)
    (scalarCompactResolventTransform f)
    (scalar_compact_resolvent_transform_continuous f hf hc hm)
    (scalar_compact_resolvent_transform_strictMono f hf hm)
  simpa [scalarCompactResolventTransform] using scalar_resolvent_endpoint_nonneg f hf

/-- Native unbounded continuous functional calculus, constructed from the
bounded resolvent calculus on the full range of `(1+f(B))⁻¹`. -/
def opMonotoneFunctionalCalculus (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B)
    (hB : OpNonnegative B) (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hc : ContinuousOn f (Ici 0)) (hm : StrictMonoOn f (Ici 0)) : H →ₗ.[ℂ] H :=
  operatorRangeGenerator (opFunctionalResolvent B hsa hB f)
    (op_functional_resolvent_injective B hsa hB f hf hc hm)

theorem op_monotone_functional_calculus_selfAdjoint (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hc : ContinuousOn f (Ici 0))
    (hm : StrictMonoOn f (Ici 0)) :
    IsSelfAdjoint (opMonotoneFunctionalCalculus B hsa hB f hf hc hm) := by
  apply operator_range_generator_selfAdjoint _
  · exact cfc_predicate _ _
  · exact operator_selfAdjoint_dense_range _ (cfc_predicate _ _)
      (op_functional_resolvent_injective B hsa hB f hf hc hm)

theorem op_monotone_functional_calculus_resolvent (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hc : ContinuousOn f (Ici 0))
    (hm : StrictMonoOn f (Ici 0)) :
    OpIsResolvent (opMonotoneFunctionalCalculus B hsa hB f hf hc hm) 1
      (opFunctionalResolvent B hsa hB f) :=
  operator_range_generator_resolvent _ _

/-- The exact full domain is the range of the actual bounded transformed
resolvent, not a finite-span or algebraic-composition domain. -/
theorem op_monotone_functional_calculus_domain (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hc : ContinuousOn f (Ici 0))
    (hm : StrictMonoOn f (Ici 0)) :
    ((opMonotoneFunctionalCalculus B hsa hB f hf hc hm).domain : Set H) =
      range (opFunctionalResolvent B hsa hB f) :=
  operator_resolvent_domain _ 1 _ (op_monotone_functional_calculus_resolvent B hsa hB f hf hc hm)

theorem op_monotone_functional_calculus_nonnegative (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hc : ContinuousOn f (Ici 0))
    (hm : StrictMonoOn f (Ici 0)) :
    OpNonnegative (opMonotoneFunctionalCalculus B hsa hB f hf hc hm) := by
  let R := opNonnegativeResolvent B hsa hB
  let q := scalarCompactResolventTransform f
  let S := opFunctionalResolvent B hsa hB f
  have hcont : ContinuousOn q (spectrum ℝ R) :=
    (scalar_compact_resolvent_transform_continuous f hf hc hm).mono
      (op_nonnegative_resolvent_spectrum B hsa hB)
  have hpos : 0 ≤ S - S * S := by
    change 0 ≤ cfc q R - cfc q R * cfc q R
    rw [← cfc_mul q q R hcont hcont, ← cfc_sub q (fun r => q r * q r) R hcont
      (hcont.mul hcont)]
    apply cfc_nonneg
    intro r hr
    have hb := scalar_compact_resolvent_transform_bounds f hf hm
      (op_nonnegative_resolvent_spectrum B hsa hB hr)
    dsimp only [q]
    nlinarith [sq_nonneg (scalarCompactResolventTransform f r)]
  have hS : IsSelfAdjoint S := cfc_predicate q R
  rintro ⟨x, ⟨y, rfl⟩⟩
  change 0 ≤ (@inner ℂ H _ (S y) (operatorRangeGenerator S _ ⟨S y, _⟩)).re
  rw [operator_range_generator_apply, inner_sub_right, Complex.sub_re]
  have hinner := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos |>.inner_nonneg_left y
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    inner_sub_left, map_sub] at hinner
  have he := hS.isSymmetric (S y) y
  change @inner ℂ H _ (S (S y)) y = @inner ℂ H _ (S y) (S y) at he
  rw [he] at hinner
  exact hinner

/-- Equality of the actual transformed resolvents recovers equality of
native unbounded operators, including their complete domains. -/
theorem operator_compact_monotone_recovery
    (A B : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H)
    (hAR : OpIsResolvent A 1 R) (hBS : OpIsResolvent B 1 S)
    (hR : IsSelfAdjoint R) (hS : IsSelfAdjoint S)
    (hspR : spectrum ℝ R ⊆ Icc 0 1) (hspS : spectrum ℝ S ⊆ Icc 0 1)
    (q : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 1)) (hm : StrictMonoOn q (Icc 0 1))
    (hdata : cfc q R = cfc q S) : A = B := by
  have hRS : R = S := by
    calc
      R = cfc (compactMonotoneInverse q hq hm) (cfc q R) :=
        (operator_compact_monotone_inverse R hR hspR q hq hm).symm
      _ = cfc (compactMonotoneInverse q hq hm) (cfc q S) := by rw [hdata]
      _ = S := operator_compact_monotone_inverse S hS hspS q hq hm
  exact operator_full_resolvent_unique A B 1 R hAR (hRS.symm ▸ hBS)

omit [CompleteSpace H] in
theorem operator_shift_resolvent_unique (A : H →ₗ.[ℂ] H) (R S : H →L[ℂ] H)
    (hR : OpIsResolvent A 1 R) (hS : OpIsResolvent A 1 S) : R = S := by
  apply ContinuousLinearMap.ext
  intro x
  have h := hS.left_inverse ⟨R x, hR.image_mem x⟩
  rw [hR.right_inverse] at h
  exact h.symm

/-- The full self-adjoint operator `f(B)` determines every arbitrary
nonnegative self-adjoint `B`. There is no compactness or eigenbasis
hypothesis; continuity and strict increase of the known scalar function
are enough. -/
theorem op_monotone_functional_calculus_determines_operator
    (A B : H →ₗ.[ℂ] H) (hsaA : IsSelfAdjoint A) (hsaB : IsSelfAdjoint B)
    (hA : OpNonnegative A) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hc : ContinuousOn f (Ici 0))
    (hm : StrictMonoOn f (Ici 0))
    (hdata : opMonotoneFunctionalCalculus A hsaA hA f hf hc hm =
      opMonotoneFunctionalCalculus B hsaB hB f hf hc hm) : A = B := by
  have hJ : opFunctionalResolvent A hsaA hA f = opFunctionalResolvent B hsaB hB f := by
    apply operator_shift_resolvent_unique (opMonotoneFunctionalCalculus A hsaA hA f hf hc hm)
    · exact op_monotone_functional_calculus_resolvent A hsaA hA f hf hc hm
    · rw [hdata]
      exact op_monotone_functional_calculus_resolvent B hsaB hB f hf hc hm
  exact operator_compact_monotone_recovery A B
    (opNonnegativeResolvent A hsaA hA) (opNonnegativeResolvent B hsaB hB)
    (op_nonnegative_shift_resolvent A hsaA hA) (op_nonnegative_shift_resolvent B hsaB hB)
    (op_nonnegative_resolvent_selfAdjoint A hsaA hA)
    (op_nonnegative_resolvent_selfAdjoint B hsaB hB)
    (op_nonnegative_resolvent_spectrum A hsaA hA)
    (op_nonnegative_resolvent_spectrum B hsaB hB)
    (scalarCompactResolventTransform f)
    (scalar_compact_resolvent_transform_continuous f hf hc hm)
    (scalar_compact_resolvent_transform_strictMono f hf hm) hJ

/-- The actual continuous inverse calculus recovers the original shifted
resolvent on all vectors, including its limiting spectral endpoint. -/
theorem op_monotone_functional_calculus_inverse_resolvent
    (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hc : ContinuousOn f (Ici 0)) (hm : StrictMonoOn f (Ici 0)) :
    cfc (compactMonotoneInverse (scalarCompactResolventTransform f)
      (scalar_compact_resolvent_transform_continuous f hf hc hm)
      (scalar_compact_resolvent_transform_strictMono f hf hm))
        (opFunctionalResolvent B hsa hB f) = opNonnegativeResolvent B hsa hB :=
  operator_compact_monotone_inverse _ (op_nonnegative_resolvent_selfAdjoint B hsa hB)
    (op_nonnegative_resolvent_spectrum B hsa hB) _ _ _

/-- The limiting endpoint has zero spectral eigenspace, even for bounded
strictly increasing scalar functions. -/
theorem op_monotone_functional_calculus_endpoint
    (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hc : ContinuousOn f (Ici 0)) (hm : StrictMonoOn f (Ici 0))
    (x : H) (hx : opFunctionalResolvent B hsa hB f x =
      (scalarResolventEndpoint f : ℂ) • x) : x = 0 := by
  apply operator_compact_monotone_endpoint _ (op_nonnegative_resolvent_selfAdjoint B hsa hB)
    (op_nonnegative_resolvent_injective B hsa hB)
    (op_nonnegative_resolvent_spectrum B hsa hB)
    (scalarCompactResolventTransform f)
    (scalar_compact_resolvent_transform_continuous f hf hc hm)
    (scalar_compact_resolvent_transform_strictMono f hf hm) x
  simpa [opFunctionalResolvent, scalarCompactResolventTransform] using hx

/-- Reconstruction map from the observed full native operator and the
known scalar function. The inverse is implemented in bounded resolvent
coordinates, then returned to its complete native domain. -/
def opKnownMonotoneInverse (C : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint C)
    (hC : OpNonnegative C) (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hc : ContinuousOn f (Ici 0)) (hm : StrictMonoOn f (Ici 0)) : H →ₗ.[ℂ] H :=
  operatorNativeRangeGenerator
    (cfc (compactMonotoneInverse (scalarCompactResolventTransform f)
      (scalar_compact_resolvent_transform_continuous f hf hc hm)
      (scalar_compact_resolvent_transform_strictMono f hf hm))
        (opNonnegativeResolvent C hsa hC))

/-- Literal native operator reconstruction `B = f⁻¹(f(B))`, with equality
of the whole operators, hence their domains and actions. -/
theorem op_known_monotone_inverse_reconstruction
    (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hc : ContinuousOn f (Ici 0)) (hm : StrictMonoOn f (Ici 0)) :
    opKnownMonotoneInverse (opMonotoneFunctionalCalculus B hsa hB f hf hc hm)
      (op_monotone_functional_calculus_selfAdjoint B hsa hB f hf hc hm)
      (op_monotone_functional_calculus_nonnegative B hsa hB f hf hc hm)
      f hf hc hm = B := by
  let C := opMonotoneFunctionalCalculus B hsa hB f hf hc hm
  let hCs := op_monotone_functional_calculus_selfAdjoint B hsa hB f hf hc hm
  let hCp := op_monotone_functional_calculus_nonnegative B hsa hB f hf hc hm
  have hRf : opNonnegativeResolvent C hCs hCp = opFunctionalResolvent B hsa hB f :=
    operator_shift_resolvent_unique C _ _ (op_nonnegative_shift_resolvent C hCs hCp)
      (op_monotone_functional_calculus_resolvent B hsa hB f hf hc hm)
  change operatorNativeRangeGenerator (cfc _ (opNonnegativeResolvent C hCs hCp)) = B
  rw [hRf, op_monotone_functional_calculus_inverse_resolvent B hsa hB f hf hc hm]
  exact operator_full_resolvent_unique _ B 1 _
    (operator_native_range_generator_resolvent _ (op_nonnegative_resolvent_injective B hsa hB))
    (op_nonnegative_shift_resolvent B hsa hB)

theorem op_known_monotone_inverse_domain
    (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hc : ContinuousOn f (Ici 0)) (hm : StrictMonoOn f (Ici 0)) :
    (opKnownMonotoneInverse (opMonotoneFunctionalCalculus B hsa hB f hf hc hm)
      (op_monotone_functional_calculus_selfAdjoint B hsa hB f hf hc hm)
      (op_monotone_functional_calculus_nonnegative B hsa hB f hf hc hm)
      f hf hc hm).domain = B.domain := by
  rw [op_known_monotone_inverse_reconstruction B hsa hB f hf hc hm]

end
end Sigma
