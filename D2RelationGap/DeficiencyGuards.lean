import D2RelationGap.DeficiencyZero

/-!
Non-vacuity guard for the deficiency statement: the quantifier form used in
`Targets.DeficiencyZeroTarget` holds for OpenAI's G (`DeficiencyZero.deficiency_zero`)
but FAILS for ℤ, which has the one-generator, zero-relator presentation. So the target
predicate genuinely distinguishes deficiency one from deficiency zero.
-/
noncomputable section
namespace D2RelationGap.DeficiencyGuards

/-- The universal part of `Targets.DeficiencyZeroTarget`, for an arbitrary group. -/
def NoPositiveDeficiency (H : Type) [Group H] : Prop :=
  ∀ (m k : ℕ) (q : FreeGroup (Fin m) →* H), Function.Surjective q →
    (∃ v : Fin k → FreeGroup (Fin m), Subgroup.normalClosure (Set.range v) = q.ker) → m ≤ k

theorem G_no_positive_deficiency : NoPositiveDeficiency Targets.G :=
  DeficiencyZero.deficiency_zero.2

theorem target_unfold : Targets.DeficiencyZeroTarget ↔
    Targets.HasNormalGenerators 5 ∧ NoPositiveDeficiency Targets.G := Iff.rfl

/-- Every element of the free group on one letter is a power of that letter. -/
theorem one_letter_pow (f : FreeGroup (Fin 1)) : ∃ n : ℤ, f = FreeGroup.of 0 ^ n := by
  induction f using FreeGroup.induction_on with
  | one => exact ⟨0, by simp⟩
  | of i => exact ⟨1, by rw [Subsingleton.elim i 0, zpow_one]⟩
  | inv_of i _ => exact ⟨-1, by rw [Subsingleton.elim i 0, zpow_neg_one]⟩
  | mul a b ha hb =>
    obtain ⟨n, rfl⟩ := ha
    obtain ⟨p, rfl⟩ := hb
    exact ⟨n + p, by rw [zpow_add]⟩

/-- Guard: ℤ (deficiency one) violates the predicate, so it is not vacuous. -/
theorem int_violates : ¬ NoPositiveDeficiency (Multiplicative ℤ) := by
  intro h
  let q : FreeGroup (Fin 1) →* Multiplicative ℤ := FreeGroup.lift (fun _ => Multiplicative.ofAdd 1)
  have hpow : ∀ n : ℤ, q (FreeGroup.of 0 ^ n) = Multiplicative.ofAdd n := by
    intro n
    rw [map_zpow]
    simp only [q, FreeGroup.lift_apply_of]
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
  have hq : Function.Surjective q := fun z => ⟨FreeGroup.of 0 ^ Multiplicative.toAdd z, by
    rw [hpow]; rfl⟩
  have hker : q.ker = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    obtain ⟨n, rfl⟩ := one_letter_pow f
    rw [MonoidHom.mem_ker, hpow] at hf
    have hn : n = 0 := by simpa using congrArg Multiplicative.toAdd hf
    rw [hn, zpow_zero]
    exact Subgroup.one_mem _
  have h10 := h 1 0 q hq ⟨Fin.elim0, by rw [hker, Set.range_eq_empty, Subgroup.normalClosure_empty]⟩
  omega

end D2RelationGap.DeficiencyGuards
