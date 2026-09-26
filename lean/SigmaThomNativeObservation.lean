import SigmaThomNativeUniversalLine

namespace Sigma
noncomputable section
open PowerSeries

/-- The complete finite-stage universal-line observation of a candidate unit.
No single finite stage is substituted for this full compatible observation. -/
def NativeUniversalLineObservation (L : NativeUniversalLine) (Q : (PowerSeries ℚ)ˣ) : Prop :=
  ∀ n, thomStageMap n (↑Q⁻¹ : PowerSeries ℚ) = (L.thom n).correction

theorem native_universal_line_observation_iff (L : NativeUniversalLine)
    (Q : (PowerSeries ℚ)ˣ) :
    NativeUniversalLineObservation L Q ↔ Q = formalToddUnitOver ℚ := by
  constructor
  · intro h
    apply L.todd_reconstruction Q
    apply thom_completion_map_injective
    apply Subtype.ext
    funext n
    exact (h n).trans (L.correctionSeries_stage n).symm
  · rintro rfl n
    exact (L.finite_correction_eq_inverseTodd n).symm

theorem native_universal_line_observation_exists_unique (L : NativeUniversalLine) :
    ∃! Q : (PowerSeries ℚ)ˣ, NativeUniversalLineObservation L Q :=
  ⟨formalToddUnitOver ℚ, (native_universal_line_observation_iff L _).mpr rfl,
    fun Q hQ => (native_universal_line_observation_iff L Q).mp hQ⟩

/-- The same full correction data explicitly recover the intrinsic exponential
series as well as the Todd unit. -/
theorem native_universal_line_exponential_reverse (L : NativeUniversalLine) :
    1 - X * L.correctionSeries = formalExponentialOver ℚ (-1) := by
  rw [L.correctionSeries_euler]
  ring

/-- Equivalence of complete correction observations with equality to the actual
completed correction, rather than an assumption about a finite-base value. -/
theorem native_universal_line_observation_completed (L : NativeUniversalLine)
    (Q : (PowerSeries ℚ)ˣ) : NativeUniversalLineObservation L Q ↔
      (↑Q⁻¹ : PowerSeries ℚ) = L.correctionSeries := by
  constructor
  · intro h
    rw [(native_universal_line_observation_iff L Q).mp h,
      L.correctionSeries_eq_inverseTodd]
  · intro h n
    rw [h, L.correctionSeries_stage]

end
end Sigma
