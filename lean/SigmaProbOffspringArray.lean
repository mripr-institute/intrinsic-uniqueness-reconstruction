import SigmaProbNatSampler

namespace Sigma
noncomputable section
open MeasureTheory Measure Set
open ProbabilityTheory

/-- A concrete countable iid offspring array, using any embedding of the
vertex labels into the natural-number Haar coordinates. -/
def iidOffspringArray {ι : Type*} (q : PMF ℕ) (e : ι ↪ ℕ)
    (i : ι) (ω : PoissonClockSpace) : ℕ := natPMFSample q (ω (e i))

theorem iid_offspring_array_measurable {ι : Type*} (q : PMF ℕ) (e : ι ↪ ℕ) (i : ι) :
    Measurable (iidOffspringArray q e i) :=
  (nat_pmf_sample_measurable q).comp (measurable_pi_apply (e i))

theorem iid_offspring_array_law {ι : Type*} (q : PMF ℕ) (e : ι ↪ ℕ) (i : ι) :
    poissonClockProbability.map (iidOffspringArray q e i) = q.toMeasure := by
  change poissonClockProbability.map (natPMFSample q ∘ (fun ω => ω (e i))) = _
  rw [← Measure.map_map (nat_pmf_sample_measurable q) (measurable_pi_apply (e i)),
    poissonClockCoordinate_map,nat_pmf_sample_map]

theorem iid_offspring_nat_array_independent (q : PMF ℕ) :
    iIndepFun (fun _ : ℕ => inferInstance)
      (iidOffspringArray q (Function.Embedding.refl ℕ)) poissonClockProbability :=
  poissonClockCoordinates_independent.comp (fun _ => natPMFSample q)
    (fun _ => nat_pmf_sample_measurable q)

theorem iid_offspring_array_independent {ι : Type*} (q : PMF ℕ) (e : ι ↪ ℕ) :
    iIndepFun (fun _ : ι => inferInstance) (iidOffspringArray q e) poissonClockProbability := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  let g : ℕ → Set ℕ := Function.extend e sets (fun _ => univ)
  have hg (i : ι) : g (e i) = sets i := e.injective.extend_apply _ _ _
  have hmeas (n : ℕ) (hn : n ∈ S.map e) : MeasurableSet (g n) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hn
    rw [hg]
    exact hs i hi
  have hh := (iid_offspring_nat_array_independent q).measure_inter_preimage_eq_mul
    (S.map e) hmeas
  have hinter :
      (⋂ n ∈ S.map e, (iidOffspringArray q (Function.Embedding.refl ℕ) n) ⁻¹' g n) =
      ⋂ i ∈ S, (iidOffspringArray q e i) ⁻¹' sets i := by
    ext ω
    simp only [mem_iInter,mem_preimage]
    constructor
    · intro h i hi
      simpa only [hg,iidOffspringArray,Function.Embedding.refl_apply] using
        h (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    · intro h n hn
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hn
      simpa only [hg,iidOffspringArray,Function.Embedding.refl_apply] using h i hi
  rw [hinter,Finset.prod_map] at hh
  simpa only [hg,iidOffspringArray,Function.Embedding.refl_apply] using hh

end
end Sigma
