import SigmaThomNativeBundles
import SigmaThomNativeProjective
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.Constructions
import Mathlib.Tactic

namespace Sigma
noncomputable section
open scoped LinearAlgebra.Projectivization BigOperators TensorProduct
open TensorProduct

/-- The actual real projective plane, with the quotient topology of nonzero vectors. -/
abbrev RealProjectivePlane := ℙ ℝ (Fin 3 → ℝ)

instance real_projective_plane_topology : TopologicalSpace RealProjectivePlane :=
  TopologicalSpace.coinduced (Projectivization.mk' ℝ) inferInstance

private def realVectorSquare (v : Fin 3 → ℝ) : ℝ := ∑ k, v k ^ 2

private theorem real_vector_square_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    0 < realVectorSquare v := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun k _ => sq_nonneg (v k)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

private theorem real_vector_square_smul (a : ℝ) (v : Fin 3 → ℝ) :
    realVectorSquare (a • v) = a ^ 2 * realVectorSquare v := by
  simp only [realVectorSquare, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- Entries of the orthogonal rank-one projector. They are independent of scale. -/
def realProjectiveProjector (p : RealProjectivePlane) (i j : Fin 3) : ℝ :=
  Projectivization.lift (fun v : {v : Fin 3 → ℝ // v ≠ 0} =>
    v.val i * v.val j / realVectorSquare v.val)
    (by
      intro v w a h
      have ha : a ≠ 0 := by
        intro ha
        apply v.property
        simpa [ha] using h
      have hv : v.val = a • w.val := h
      dsimp only
      rw [hv, real_vector_square_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hw := ne_of_gt (real_vector_square_pos w.property)
      field_simp
      ring) p

theorem real_projective_projector_mk (v : Fin 3 → ℝ) (hv : v ≠ 0) (i j : Fin 3) :
    realProjectiveProjector (Projectivization.mk ℝ v hv) i j =
      v i * v j / realVectorSquare v := rfl

theorem real_projective_projector_continuous (i j : Fin 3) :
    Continuous (fun p : RealProjectivePlane => realProjectiveProjector p i j) := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun v : {v : Fin 3 → ℝ // v ≠ 0} =>
    v.val i * v.val j / realVectorSquare v.val)
  apply ((continuous_apply i).comp continuous_subtype_val).mul
    ((continuous_apply j).comp continuous_subtype_val) |>.div
  · exact continuous_finset_sum _ (fun k _ =>
      ((continuous_apply k).comp continuous_subtype_val).pow 2)
  · intro v
    exact ne_of_gt (real_vector_square_pos v.property)

/-- The standard open chart where the i-th coordinate is nonzero. -/
def realProjectiveChart (i : Fin 3) : Set RealProjectivePlane :=
  {p | realProjectiveProjector p i i ≠ 0}

theorem real_projective_chart_mk (v : Fin 3 → ℝ) (hv : v ≠ 0) (i : Fin 3) :
    Projectivization.mk ℝ v hv ∈ realProjectiveChart i ↔ v i ≠ 0 := by
  simp [realProjectiveChart, real_projective_projector_mk,
    ne_of_gt (real_vector_square_pos hv)]

theorem real_projective_chart_open (i : Fin 3) : IsOpen (realProjectiveChart i) :=
  isOpen_ne.preimage (real_projective_projector_continuous i i)

/-- The i-th normalized coordinate vector, obtained without choosing a representative. -/
def realProjectiveCoordinate (i j : Fin 3) (p : RealProjectivePlane) : ℝ :=
  realProjectiveProjector p i j / realProjectiveProjector p i i

theorem real_projective_coordinate_mk (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (i j : Fin 3) (hi : v i ≠ 0) :
    realProjectiveCoordinate i j (Projectivization.mk ℝ v hv) = v j / v i := by
  dsimp [realProjectiveCoordinate]
  rw [real_projective_projector_mk, real_projective_projector_mk]
  have hn := ne_of_gt (real_vector_square_pos hv)
  field_simp
  ring

theorem real_projective_coordinate_continuousOn (i j : Fin 3) :
    ContinuousOn (realProjectiveCoordinate i j) (realProjectiveChart i) :=
  (real_projective_projector_continuous i j).continuousOn.div
    (real_projective_projector_continuous i i).continuousOn (fun _ h => h)

theorem real_projective_coordinate_self (i : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) : realProjectiveCoordinate i i p = 1 :=
  div_self hi

theorem real_projective_coordinate_cocycle (i j k : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) (hj : p ∈ realProjectiveChart j) :
    realProjectiveCoordinate j k p * realProjectiveCoordinate i j p =
      realProjectiveCoordinate i k p := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hi' := (real_projective_chart_mk v hv i).mp hi
    have hj' := (real_projective_chart_mk v hv j).mp hj
    rw [real_projective_coordinate_mk v hv j k hj',
      real_projective_coordinate_mk v hv i j hi',
      real_projective_coordinate_mk v hv i k hi']
    field_simp

private theorem real_projective_chart_cover (p : RealProjectivePlane) :
    ∃ i, p ∈ realProjectiveChart i := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hex : ∃ i, v i ≠ 0 := by
      by_contra h
      apply hv
      funext i
      simpa using not_exists.mp h i
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, (real_projective_chart_mk v hv i).mpr hi⟩

/-- Explicit complex line transition functions of the complexified real tautological line. -/
def realProjectiveComplexCore : VectorBundleCore ℂ RealProjectivePlane (Fin 1 → ℂ) (Fin 3) where
  baseSet := realProjectiveChart
  isOpen_baseSet := real_projective_chart_open
  indexAt p := (real_projective_chart_cover p).choose
  mem_baseSet_at p := (real_projective_chart_cover p).choose_spec
  coordChange i j p :=
    (realProjectiveCoordinate i j p : ℂ) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)
  coordChange_self i p hp z := by
    simp [real_projective_coordinate_self i p hp]
  continuousOn_coordChange i j := by
    exact ((Complex.continuous_ofReal.comp_continuousOn
      (real_projective_coordinate_continuousOn i j)).mono Set.inter_subset_left).smul
        continuousOn_const
  coordChange_comp i j k p hp z := by
    change ((realProjectiveCoordinate j k p : ℂ) •
      ((realProjectiveCoordinate i j p : ℂ) • z)) =
        (realProjectiveCoordinate i k p : ℂ) • z
    rw [smul_smul, ← Complex.ofReal_mul,
      real_projective_coordinate_cocycle i j k p hp.1.1 hp.1.2]

/-- The native topological complex line bundle on RP² constructed from its coordinate charts. -/
def realProjectiveComplexLine : NativeComplexBundle where
  base := TopCat.of RealProjectivePlane
  rank := 1
  Fiber := realProjectiveComplexCore.Fiber

/-- Complexification of the real coordinate vector space. -/
def realCoordinateComplexification :
    (Fin 3 → ℝ) →ₛₗ[Complex.ofRealHom] (Fin 3 → ℂ) where
  toFun v i := (v i : ℂ)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp

theorem real_coordinate_complexification_injective :
    Function.Injective realCoordinateComplexification := by
  intro v w h
  funext i
  exact Complex.ofReal_injective (congrFun h i)

/-- The actual real-to-complex projective map sends a real line to its complex span. -/
def realProjectiveComplexification : RealProjectivePlane → NativeProjectiveSpace 2 :=
  Projectivization.map realCoordinateComplexification real_coordinate_complexification_injective

theorem real_projective_complexification_mk (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    realProjectiveComplexification (Projectivization.mk ℝ v hv) =
      Projectivization.mk ℂ (realCoordinateComplexification v)
        (map_zero realCoordinateComplexification ▸
          real_coordinate_complexification_injective.ne hv) := rfl

theorem real_projective_complexification_continuous :
    Continuous realProjectiveComplexification := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun v : {v : Fin 3 → ℝ // v ≠ 0} =>
    Projectivization.mk' ℂ ⟨realCoordinateComplexification v.val, _⟩)
  apply continuous_coinduced_rng.comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val)

theorem real_projective_complexification_fiber (p : RealProjectivePlane) :
    (realProjectiveComplexification p).submodule =
      ℂ ∙ (realCoordinateComplexification p.rep) := by
  conv_lhs => rw [← p.mk_rep]
  rfl

private theorem real_projective_chart_rep (p : RealProjectivePlane) (i : Fin 3) :
    p ∈ realProjectiveChart i ↔ p.rep i ≠ 0 := by
  rw [← p.mk_rep, real_projective_chart_mk]
  simp

theorem real_projective_coordinate_rep (p : RealProjectivePlane) (i j : Fin 3)
    (hi : p ∈ realProjectiveChart i) :
    realProjectiveCoordinate i j p = p.rep j / p.rep i := by
  conv_lhs => rw [← p.mk_rep]
  exact real_projective_coordinate_mk _ _ _ _ ((real_projective_chart_rep p i).mp hi)

/-- The incidence vector represented by a fiber coordinate. -/
def realProjectiveComplexFiberMap (p : RealProjectivePlane) :
    realProjectiveComplexCore.Fiber p →ₗ[ℂ] (realProjectiveComplexification p).submodule where
  toFun z := ⟨fun k => z 0 * (realProjectiveCoordinate
    (realProjectiveComplexCore.indexAt p) k p : ℂ), by
      rw [real_projective_complexification_fiber, Submodule.mem_span_singleton]
      refine ⟨z 0 / (p.rep (realProjectiveComplexCore.indexAt p) : ℂ), ?_⟩
      ext k
      change (z 0 / (p.rep (realProjectiveComplexCore.indexAt p) : ℂ)) *
        (p.rep k : ℂ) = z 0 * (realProjectiveCoordinate _ _ p : ℂ)
      rw [real_projective_coordinate_rep p _ _ (realProjectiveComplexCore.mem_baseSet_at p)]
      push_cast
      ring⟩
  map_add' z w := by
    ext k
    change (z 0 + w 0) * _ = z 0 * _ + w 0 * _
    exact add_mul _ _ _
  map_smul' a z := by
    ext k
    change (a * z 0) * _ = a * (z 0 * _)
    exact mul_assoc _ _ _

theorem real_projective_complex_fiber_map_coordinate (p : RealProjectivePlane)
    (z : realProjectiveComplexCore.Fiber p) :
    (realProjectiveComplexFiberMap p z).val (realProjectiveComplexCore.indexAt p) = z 0 := by
  change z 0 * (realProjectiveCoordinate _ _ p : ℂ) = z 0
  rw [real_projective_coordinate_self _ p (realProjectiveComplexCore.mem_baseSet_at p)]
  simp

theorem real_projective_complex_fiber_map_bijective (p : RealProjectivePlane) :
    Function.Bijective (realProjectiveComplexFiberMap p) := by
  constructor
  · intro z w h
    have hc := congrArg (fun v => v.val (realProjectiveComplexCore.indexAt p)) h
    dsimp only at hc
    rw [real_projective_complex_fiber_map_coordinate,
      real_projective_complex_fiber_map_coordinate] at hc
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using hc
  · intro w
    have hw : w.val ∈ ℂ ∙ (realCoordinateComplexification p.rep) :=
      (congrArg (fun S : Submodule ℂ (Fin 3 → ℂ) => w.val ∈ S)
        (real_projective_complexification_fiber p)).mp w.property
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨c, hc⟩ := hw
    refine ⟨fun _ => c * (p.rep (realProjectiveComplexCore.indexAt p) : ℂ), ?_⟩
    apply Subtype.ext
    ext k
    change (c * (p.rep (realProjectiveComplexCore.indexAt p) : ℂ)) *
      (realProjectiveCoordinate (realProjectiveComplexCore.indexAt p) k p : ℂ) = w.val k
    rw [real_projective_coordinate_rep p _ _ (realProjectiveComplexCore.mem_baseSet_at p)]
    have hi : (p.rep (realProjectiveComplexCore.indexAt p) : ℂ) ≠ 0 := by
      exact_mod_cast (real_projective_chart_rep p _).mp
        (realProjectiveComplexCore.mem_baseSet_at p)
    rw [Complex.ofReal_div]
    have hck := congrFun hc k
    change c * (p.rep k : ℂ) = w.val k at hck
    calc
      _ = c * (p.rep k : ℂ) := by field_simp; ring
      _ = w.val k := hck

/-- Fiberwise identification of the native line bundle with the complex span of
the actual real tautological line. -/
def realProjectiveComplexFiberEquiv (p : RealProjectivePlane) :
    realProjectiveComplexCore.Fiber p ≃ₗ[ℂ] (realProjectiveComplexification p).submodule :=
  LinearEquiv.ofBijective _ (real_projective_complex_fiber_map_bijective p)

theorem real_projective_complex_fiber_finrank (p : RealProjectivePlane) :
    Module.finrank ℂ (realProjectiveComplexification p).submodule = 1 :=
  (realProjectiveComplexification p).finrank_submodule

/-- The actual incidence total space over the real projective plane. -/
def RealProjectiveComplexIncidence :=
  {q : RealProjectivePlane × (Fin 3 → ℂ) //
    q.2 ∈ (realProjectiveComplexification q.1).submodule}

instance real_projective_complex_incidence_topology :
    TopologicalSpace RealProjectiveComplexIncidence :=
  inferInstanceAs (TopologicalSpace {q : RealProjectivePlane × (Fin 3 → ℂ) //
    q.2 ∈ (realProjectiveComplexification q.1).submodule})

/-- The bundle total space and the concrete complex incidence space are identified. -/
def realProjectiveComplexIncidenceEquiv :
    realProjectiveComplexCore.TotalSpace ≃ RealProjectiveComplexIncidence where
  toFun x := ⟨(x.proj, (realProjectiveComplexFiberMap x.proj x.snd).val),
    (realProjectiveComplexFiberMap x.proj x.snd).property⟩
  invFun q := ⟨q.val.1, (realProjectiveComplexFiberEquiv q.val.1).symm ⟨q.val.2, q.property⟩⟩
  left_inv x := by
    cases x with
    | mk p z =>
      change Bundle.TotalSpace.mk p
        ((realProjectiveComplexFiberEquiv p).symm (realProjectiveComplexFiberEquiv p z)) = _
      simp
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change ((realProjectiveComplexFiberEquiv q.val.1)
        ((realProjectiveComplexFiberEquiv q.val.1).symm ⟨q.val.2, q.property⟩)).val = q.val.2
      simp

private theorem real_projective_complex_fiber_map_chart (p : RealProjectivePlane)
    (z : realProjectiveComplexCore.Fiber p) (i k : Fin 3) (hi : p ∈ realProjectiveChart i) :
    (realProjectiveComplexFiberMap p z).val k =
      ((realProjectiveComplexCore.localTriv i) ⟨p, z⟩).2 0 *
        (realProjectiveCoordinate i k p : ℂ) := by
  change z 0 * (realProjectiveCoordinate (realProjectiveComplexCore.indexAt p) k p : ℂ) =
    ((realProjectiveCoordinate (realProjectiveComplexCore.indexAt p) i p : ℂ) * z 0) *
      (realProjectiveCoordinate i k p : ℂ)
  rw [show ((realProjectiveCoordinate (realProjectiveComplexCore.indexAt p) i p : ℂ) * z 0) *
      (realProjectiveCoordinate i k p : ℂ) = z 0 *
        ((realProjectiveCoordinate i k p : ℂ) *
          (realProjectiveCoordinate (realProjectiveComplexCore.indexAt p) i p : ℂ)) by ring,
    ← Complex.ofReal_mul, real_projective_coordinate_cocycle _ _ _ p
      (realProjectiveComplexCore.mem_baseSet_at p) hi]

theorem real_projective_complex_incidence_equiv_continuous :
    Continuous realProjectiveComplexIncidenceEquiv := by
  apply Continuous.subtype_mk
  apply Continuous.prod_mk realProjectiveComplexCore.continuous_proj
  apply continuous_pi
  intro k
  apply continuous_iff_continuousAt.mpr
  intro x
  let i := realProjectiveComplexCore.indexAt x.proj
  have hxi : x.proj ∈ realProjectiveChart i := realProjectiveComplexCore.mem_baseSet_at x.proj
  have hproj := realProjectiveComplexCore.continuous_proj.continuousAt (x := x)
  have hc := (real_projective_coordinate_continuousOn i k).continuousAt
    ((real_projective_chart_open i).mem_nhds hxi)
  have he := (realProjectiveComplexCore.localTriv i).continuousAt
    ((realProjectiveComplexCore.mem_localTriv_source i x).mpr hxi)
  have hv : ContinuousAt (fun t : realProjectiveComplexCore.TotalSpace =>
      ((realProjectiveComplexCore.localTriv i) t).2 0 *
        (realProjectiveCoordinate i k t.proj : ℂ)) x :=
    ((continuous_apply 0).continuousAt.comp he.snd).mul
      (Complex.continuous_ofReal.continuousAt.comp (hc.comp hproj))
  apply hv.congr_of_eventuallyEq
  filter_upwards [hproj (real_projective_chart_open i |>.mem_nhds hxi)] with t ht
  exact real_projective_complex_fiber_map_chart t.proj t.snd i k ht

private theorem real_projective_complex_incidence_inverse_chart
    (q : RealProjectiveComplexIncidence) (i : Fin 3) (hi : q.val.1 ∈ realProjectiveChart i) :
    (realProjectiveComplexCore.localTriv i) (realProjectiveComplexIncidenceEquiv.symm q) =
      (q.val.1, fun _ => q.val.2 i) := by
  apply Prod.ext
  · rfl
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hf := real_projective_complex_fiber_map_chart q.val.1
      (realProjectiveComplexIncidenceEquiv.symm q).snd i i hi
    rw [real_projective_coordinate_self i q.val.1 hi] at hf
    simp only [Complex.ofReal_one, mul_one] at hf
    have he : realProjectiveComplexFiberMap q.val.1
        (realProjectiveComplexIncidenceEquiv.symm q).snd = ⟨q.val.2, q.property⟩ :=
      (realProjectiveComplexFiberEquiv q.val.1).apply_symm_apply _
    rw [he] at hf
    exact hf.symm

theorem real_projective_complex_incidence_inverse_continuous :
    Continuous realProjectiveComplexIncidenceEquiv.symm := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let i := realProjectiveComplexCore.indexAt q.val.1
  have hqi : q.val.1 ∈ realProjectiveChart i := realProjectiveComplexCore.mem_baseSet_at q.val.1
  have hp : Continuous (fun q : RealProjectiveComplexIncidence => q.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hmem : realProjectiveComplexIncidenceEquiv.symm ⁻¹'
      (realProjectiveComplexCore.localTriv i).source ∈ nhds q := by
    change (fun q : RealProjectiveComplexIncidence => q.val.1) ⁻¹' realProjectiveChart i ∈ nhds q
    exact hp.continuousAt ((real_projective_chart_open i).mem_nhds hqi)
  apply ((realProjectiveComplexCore.localTriv i).toPartialHomeomorph.continuousAt_iff_continuousAt_comp_left hmem).mpr
  have hv : Continuous (fun q : RealProjectiveComplexIncidence =>
      (q.val.1, fun _ : Fin 1 => q.val.2 i)) := by
    exact hp.prod_mk (continuous_pi (fun _ =>
      (continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)))
  apply hv.continuousAt.congr_of_eventuallyEq
  filter_upwards [hp.continuousAt ((real_projective_chart_open i).mem_nhds hqi)] with t ht
  exact real_projective_complex_incidence_inverse_chart t i ht

/-- This homeomorphism proves the topology is the concrete incidence topology,
not only a fiberwise algebraic identification. -/
def realProjectiveComplexIncidenceHomeomorph :
    realProjectiveComplexCore.TotalSpace ≃ₜ RealProjectiveComplexIncidence where
  toEquiv := realProjectiveComplexIncidenceEquiv
  continuous_toFun := real_projective_complex_incidence_equiv_continuous
  continuous_invFun := real_projective_complex_incidence_inverse_continuous

private def realTautologicalGenerator (p : RealProjectivePlane) : ℝ →ₗ[ℝ] p.submodule where
  toFun r := ⟨r • p.rep, by
    rw [p.submodule_eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
  map_add' r s := by apply Subtype.ext; exact add_smul _ _ _
  map_smul' r s := by apply Subtype.ext; exact mul_smul _ _ _

private theorem real_tautological_generator_bijective (p : RealProjectivePlane) :
    Function.Bijective (realTautologicalGenerator p) := by
  constructor
  · intro r s h
    exact smul_left_injective ℝ p.rep_nonzero (congrArg Subtype.val h)
  · intro v
    have hv : v.val ∈ ℝ ∙ p.rep :=
      (congrArg (fun S : Submodule ℝ (Fin 3 → ℝ) => v.val ∈ S) p.submodule_eq).mp v.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨r, Subtype.ext hr⟩

private def realTautologicalGeneratorEquiv (p : RealProjectivePlane) : ℝ ≃ₗ[ℝ] p.submodule :=
  LinearEquiv.ofBijective _ (real_tautological_generator_bijective p)

private def complexTautologicalGenerator (p : RealProjectivePlane) :
    ℂ →ₗ[ℂ] (realProjectiveComplexification p).submodule where
  toFun c := ⟨c • realCoordinateComplexification p.rep,
    (congrArg (fun S : Submodule ℂ (Fin 3 → ℂ) =>
      c • realCoordinateComplexification p.rep ∈ S) (real_projective_complexification_fiber p)).mpr
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))⟩
  map_add' r s := by apply Subtype.ext; exact add_smul _ _ _
  map_smul' r s := by apply Subtype.ext; exact mul_smul _ _ _

private theorem complex_tautological_generator_bijective (p : RealProjectivePlane) :
    Function.Bijective (complexTautologicalGenerator p) := by
  constructor
  · intro r s h
    have hv : realCoordinateComplexification p.rep ≠ 0 :=
      map_zero realCoordinateComplexification ▸ real_coordinate_complexification_injective.ne p.rep_nonzero
    exact smul_left_injective ℂ hv (congrArg Subtype.val h)
  · intro v
    have hv : v.val ∈ ℂ ∙ realCoordinateComplexification p.rep :=
      (congrArg (fun S : Submodule ℂ (Fin 3 → ℂ) => v.val ∈ S)
        (real_projective_complexification_fiber p)).mp v.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨r, Subtype.ext hr⟩

private def complexTautologicalGeneratorEquiv (p : RealProjectivePlane) :
    ℂ ≃ₗ[ℂ] (realProjectiveComplexification p).submodule :=
  LinearEquiv.ofBijective _ (complex_tautological_generator_bijective p)

/-- The actual fiber is the scalar extension ℂ ⊗ℝ of the real tautological fiber. -/
def realProjectiveComplexScalarExtension (p : RealProjectivePlane) :
    (ℂ ⊗[ℝ] p.submodule) ≃ₗ[ℂ] (realProjectiveComplexification p).submodule :=
  ((AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
    (realTautologicalGeneratorEquiv p).symm).trans
      (AlgebraTensorModule.rid ℝ ℂ ℂ)).trans (complexTautologicalGeneratorEquiv p)

theorem real_projective_complex_scalar_extension_tmul (p : RealProjectivePlane)
    (c : ℂ) (v : p.submodule) :
    (realProjectiveComplexScalarExtension p (c ⊗ₜ[ℝ] v)).val =
      c • realCoordinateComplexification v.val := by
  obtain ⟨r, hr⟩ := (realTautologicalGeneratorEquiv p).surjective v
  subst v
  simp only [realProjectiveComplexScalarExtension, LinearEquiv.trans_apply,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply,
    AlgebraTensorModule.rid_tmul]
  change ((r : ℂ) * c) • realCoordinateComplexification p.rep =
    c • realCoordinateComplexification (r • p.rep)
  rw [realCoordinateComplexification.map_smulₛₗ, smul_smul]
  congr 1
  exact mul_comm _ _

end
end Sigma
