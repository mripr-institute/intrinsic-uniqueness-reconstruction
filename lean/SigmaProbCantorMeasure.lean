import SigmaProbGamma
import Mathlib.Topology.Instances.CantorSet
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace Sigma
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

def cantorDigit (b : Bool) : ℝ := if b then 2/3 else 0

def cantorCode (b : ℕ → Bool) : ℝ := ∑' n : ℕ, cantorDigit (b n)*(1/3 : ℝ)^n

theorem cantor_geometric_mass : HasSum (fun n : ℕ => (2/3 : ℝ)*(1/3 : ℝ)^n) 1 := by
  have hh := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/3 : ℝ)‖ < 1)).mul_left (2/3 : ℝ)
  convert hh using 1
  norm_num

theorem cantor_code_summable (b : ℕ → Bool) :
    Summable (fun n : ℕ => cantorDigit (b n)*(1/3 : ℝ)^n) := by
  apply Summable.of_nonneg_of_le
    (fun n => by unfold cantorDigit; split_ifs <;> positivity) ?_ cantor_geometric_mass.summable
  intro n
  unfold cantorDigit
  split_ifs
  · exact le_rfl
  · simp only [zero_mul]
    positivity

theorem cantor_code_unit (b : ℕ → Bool) : cantorCode b ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply tsum_nonneg
    intro n
    unfold cantorDigit
    split_ifs <;> positivity
  · rw [← cantor_geometric_mass.tsum_eq]
    apply tsum_le_tsum (fun n => ?_) (cantor_code_summable b) cantor_geometric_mass.summable
    unfold cantorDigit
    split_ifs
    · exact le_rfl
    · simp only [zero_mul]
      positivity

theorem cantor_code_recursion (b : ℕ → Bool) :
    cantorCode b = cantorDigit (b 0) + cantorCode (fun n => b (n+1))/3 := by
  have hh := tsum_eq_zero_add (cantor_code_summable b)
  rw [cantorCode, hh]
  simp only [pow_zero, mul_one]
  congr 1
  rw [cantorCode, ← tsum_div_const]
  apply tsum_congr
  intro n
  rw [pow_succ]
  ring

theorem cantor_code_mem_precantor (b : ℕ → Bool) (n : ℕ) : cantorCode b ∈ preCantorSet n := by
  induction n generalizing b with
  | zero => exact cantor_code_unit b
  | succ n ih =>
    rw [preCantorSet_succ, cantor_code_recursion]
    cases hb : b 0
    · left
      refine ⟨cantorCode (fun n => b (n+1)), ih _, ?_⟩
      simp [cantorDigit, hb]
    · right
      refine ⟨cantorCode (fun n => b (n+1)), ih _, ?_⟩
      simp only [cantorDigit, hb, Bool.true_eq, ↓reduceIte]
      ring

theorem cantor_code_mem (b : ℕ → Bool) : cantorCode b ∈ cantorSet :=
  mem_iInter.mpr (cantor_code_mem_precantor b)

theorem cantor_code_head {b c : ℕ → Bool} (he : cantorCode b = cantorCode c) : b 0 = c 0 := by
  have hb := cantor_code_unit (fun n => b (n+1))
  have hc := cantor_code_unit (fun n => c (n+1))
  rw [cantor_code_recursion b, cantor_code_recursion c] at he
  cases h0 : b 0 <;> cases h1 : c 0 <;> simp only [cantorDigit, h0, h1, Bool.false_eq_true,
    ↓reduceIte] at he ⊢ <;> linarith [hb.1, hb.2, hc.1, hc.2]

theorem cantor_code_tail {b c : ℕ → Bool} (he : cantorCode b = cantorCode c) :
    cantorCode (fun n => b (n+1)) = cantorCode (fun n => c (n+1)) := by
  have h0 := cantor_code_head he
  rw [cantor_code_recursion b, cantor_code_recursion c, h0] at he
  linarith

theorem cantor_code_injective : Function.Injective cantorCode := by
  intro b c he
  funext n
  induction n generalizing b c with
  | zero => exact cantor_code_head he
  | succ n ih => exact ih (cantor_code_tail he)

theorem cantor_space_uncountable : Uncountable (ℕ → Bool) := by
  apply uncountable_iff_forall_not_surjective.mpr
  intro f hf
  obtain ⟨n, hn⟩ := hf (fun n => !(f n n))
  have hh := congrFun hn n
  cases h : f n n <;> simp [h] at hh

theorem cantor_set_uncountable : Uncountable cantorSet := by
  letI := cantor_space_uncountable
  have hinj : Function.Injective (fun b : ℕ → Bool => (⟨cantorCode b, cantor_code_mem b⟩ : cantorSet)) := by
    intro b c he
    exact cantor_code_injective (congrArg Subtype.val he)
  exact hinj.uncountable

instance cantor_set_standardBorel : StandardBorelSpace cantorSet :=
  isClosed_cantorSet.measurableSet.standardBorel

/-- A Borel equivalence transports a genuine atomless probability onto the
Cantor set. Uniformity of the Cantor distribution is unnecessary here. -/
def cantorBorelEquiv : ℝ ≃ᵐ cantorSet := by
  letI := cantor_set_uncountable
  exact PolishSpace.measurableEquivOfNotCountable not_countable not_countable

def cantorProbabilityEmbedding (x : ℝ) : ℝ := (cantorBorelEquiv x).val

theorem cantor_probability_embedding_measurable : Measurable cantorProbabilityEmbedding :=
  measurable_subtype_coe.comp cantorBorelEquiv.measurable

theorem cantor_probability_embedding_injective : Function.Injective cantorProbabilityEmbedding :=
  Subtype.val_injective.comp cantorBorelEquiv.injective

def cantorSingularProbability : Measure ℝ := gammaProbability.map cantorProbabilityEmbedding

instance cantor_singular_probability_isProbability : IsProbabilityMeasure cantorSingularProbability :=
  isProbabilityMeasure_map cantor_probability_embedding_measurable.aemeasurable

instance cantor_singular_probability_noAtoms : NoAtoms cantorSingularProbability := by
  letI : NoAtoms gammaProbability := ⟨gamma_probability_no_atom⟩
  constructor
  intro x
  rw [cantorSingularProbability, Measure.map_apply cantor_probability_embedding_measurable
    (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply cantor_probability_embedding_injective
  exact (mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm

theorem cantor_singular_probability_supported : cantorSingularProbability cantorSetᶜ = 0 := by
  rw [cantorSingularProbability, Measure.map_apply cantor_probability_embedding_measurable
    isClosed_cantorSet.measurableSet.compl]
  have he : cantorProbabilityEmbedding ⁻¹' cantorSetᶜ = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact hx (cantorBorelEquiv x).property
  rw [he, measure_empty]

theorem cantor_singular_probability_ae_mem : ∀ᵐ x ∂cantorSingularProbability, x ∈ cantorSet :=
  ae_iff.mpr cantor_singular_probability_supported

theorem cantor_probability_exists : ∃ μ : Measure ℝ,
    IsProbabilityMeasure μ ∧ NoAtoms μ ∧ μ cantorSetᶜ = 0 :=
  ⟨cantorSingularProbability, inferInstance, inferInstance,
    cantor_singular_probability_supported⟩

end
end Sigma
